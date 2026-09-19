#!/usr/bin/env python3
"""Phase 4 orchestrator v4 -- unattended run on GB10 (v3 + four speedups).

Changes vs v3 (everything else, above all the verification policy, is v3):
  1. gmpy2 primality filter (fastsearch2._isp): 19x faster Miller-Rabin at
     600-1000 digits. Validated first (validate_gmpy2.py): every h, p, q of
     all accepted rungs still prime, products of accepted primes composite,
     no disagreement with pock.is_prime_mr on a sample. It is only a filter;
     the Lean kernel still certifies every rung.
  2. all 20 cores: the unit of work is now (branch i, block k) instead of a
     whole branch, so the five odd-i branches share a 20-worker pool.
     Semantics are unchanged: per branch the driver keeps the hit with the
     smallest block index, which is the largest h -- the same h the
     sequential top-down scan returns -- and never schedules a block past a
     hit it already holds. Stage 2 scans blocks 60..259 instead of 0..259
     (stage 1 already proved 0..59 empty).
  3. the lake build runs in a background thread while the search continues
     on the next batch. Never two builds at once (single Builder object,
     joined before the next one starts); the build works on a *copy* of the
     rows list taken at handoff, so the search only ever appends past it;
     only the build thread touches Lean files, P287.lean and the state file.
  4. bigger batches: hand off at BATCH_SIZE rows, keep searching while the
     build runs, hard cap MAX_PENDING_ROWS (then wait for the build slot).

Runs with nobody watching. A cron watchdog (phase3_watchdog.sh, every 10 min
and @reboot) restarts it from saved state. Only this process writes the
rungs file, the state file and P287.lean.

Loop:
  * at startup, if >= MIN_BUILD_ROWS_AT_START searched-but-unverified rows are
    pending (e.g. after a crash/restart), build+verify them first;
  * search a batch (BATCH_SIZE rungs or BATCH_TIME_S seconds);
  * build + kernel-verify all pending rows as Main{N} (N = last verified + 1).

A bound counts ONLY after: every chunk + Main/Records/Conditional builds with
"Build completed successfully", no `error:`, no `declaration uses 'sorry'`,
every required theorem's `#print axioms` line present and a subset of
[propext, Classical.choice, Quot.sound], then P287.lean wired and a full
`lake build` passing the same checks. Never file existence.

Failure policy:
  * resource-type failure (OOM kill, timeout, heartbeat/stack limits, lake
    failure without a Lean-located error): retry the unfinished targets ONCE
    at lower concurrency. If that fails: un-wire, log BUILD_SKIPPED, halve
    rows-per-chunk for next time, keep searching. The skipped rows stay
    pending and are included in the next build (the ladder must be contiguous).
  * correctness-type failure (Lean error at file:line:col that is not a
    resource message, `sorry`, a non-standard axiom, or missing axiom lines
    after a "successful" build) persisting after the retry: un-wire, write
    STOP_CORRECTNESS, exit. The watchdog will NOT restart until a human
    removes that file.
  * Python exception in search: exit non-zero; watchdog restarts (resume is
    exact: rungs file is checkpointed atomically after every rung).
  * create STOP_MANUAL to stop cleanly at the next batch boundary.

Search changes vs v2 (data-driven, see MORNING_SUMMARY.md):
  * even i dropped: for even i, c = 2^i = 1 (mod 3), so q = c*p+1 = p+1
    (mod 3); q prime forces p = 1 (mod 3), i.e. 3 | h*2^a, i.e. 3 | h, but h
    is prime and large. So even i can NEVER yield a rung (structural, not
    chance). Odd i: no mod-3 obstruction; for r >= 5 at most 2 of r-1 residues
    are excluded, so no other small-prime obstruction exists.
  * two-stage budget: 60 blocks first (Phase 2's setting, ~1 miss in 590
    rungs), full-window 260 only if all branches miss -- avoids waiting on an
    exhaustive scan of a losing branch for every rung.
"""
import fcntl
import glob
import json
import multiprocessing as mp
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import calendar
import time
import traceback
from math import factorial, log

WORK = os.environ.get("P3_WORK", "/home/zedgb10/p287work")
LEAN_DIR = os.environ.get("P3_LEAN_DIR", "/home/zedgb10/erdos287-verify/erdos-287-lean")
LEAN = LEAN_DIR + "/P287/"
LAKE = os.environ.get("P3_LAKE", "/home/zedgb10/.elan/bin/lake")
os.environ["PATH"] = "/home/zedgb10/.elan/bin:" + os.environ.get("PATH", "/usr/bin:/bin")

sys.path.insert(0, "/home/zedgb10/attempts/013-certladder")
sys.path.insert(0, "/home/zedgb10/p287work")
import fastsearch2 as fs  # noqa: E402
import gen_cert3  # noqa: E402
from gen_cert2 import cover  # noqa: E402
from fastsearch2 import PMAXH  # noqa: E402

RUNGS_PATH = f"{WORK}/rungs_extended.json"
STATE_PATH = f"{WORK}/phase3_state.json"
STATUS_LOG = f"{WORK}/phase3_status.log"
DETAIL_LOG = f"{WORK}/phase3_detail.log"
COST_CSV = f"{WORK}/phase3_cost_curve.csv"
SUMMARY = f"{WORK}/MORNING_SUMMARY.md"
PROGRESS = os.environ.get("P3_PROGRESS", "/home/zedgb10/erdos287-verify/PROGRESS.md")
BUILD_LOG_DIR = f"{WORK}/phase3_build_logs"
LOCK_PATH = f"{WORK}/phase3_orchestrator.lock"
PID_PATH = f"{WORK}/phase3.pid"
STOP_CORRECTNESS = f"{WORK}/STOP_CORRECTNESS"
STOP_EXHAUSTED = f"{WORK}/STOP_EXHAUSTED"
STOP_MANUAL = f"{WORK}/STOP_MANUAL"

BATCH_SIZE = int(os.environ.get("P3_BATCH_SIZE", 60))      # rows before a build is handed off
BATCH_TIME_S = int(os.environ.get("P3_BATCH_TIME_S", 2700))
MIN_BUILD_ROWS_AT_START = int(os.environ.get("P3_MIN_BUILD_ROWS", 30))
MAX_LOOPS = int(os.environ.get("P3_MAX_LOOPS", 0))          # 0 = forever (tests only)
MAX_PENDING_ROWS = int(os.environ.get("P4_MAX_PENDING", 150))   # stop searching, wait for the build
SEARCH_WORKERS = int(os.environ.get("P4_WORKERS", 20))
GEN_WORKERS = int(os.environ.get("P4_GEN_WORKERS", 8))       # parallel chunk-file generation
SEARCH_WORKERS_BUILDING = int(os.environ.get("P4_WORKERS_BUILDING", 12))  # leave cores for lean
OVERLAP = os.environ.get("P4_OVERLAP", "1") == "1"
MEM_START_LIMIT_GB = float(os.environ.get("P4_MEM_START_LIMIT", 40))     # do not start a build above this
MEM_WAIT_S = int(os.environ.get("P4_MEM_WAIT_S", 1800))
SIEVE_B = 100000
BUDGET_STAGES = (60, 260)
I_RANGE = [1, 3, 5, 7, 9]
TARGET_CHUNK_BYTES = 64 * 2 ** 20
MAX_CHUNK_ROWS = 15
MEM_BUDGET_GB = 75.0
MAX_BUILD_CONC = 8
BASE_GB_PER_PROC = 3.0
BUILD_TIMEOUT_S = 6 * 3600
CLEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

fs.set_B(SIEVE_B)
os.makedirs(BUILD_LOG_DIR, exist_ok=True)


# ----------------------------------------------------------------- logging
def ts():
    return time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime())


_lock = threading.Lock()
_last_status_time = time.time()
_current_phase = "starting"


def status(msg):
    global _last_status_time
    line = f"[{ts()} UTC] {msg}"
    print(line, flush=True)
    with open(STATUS_LOG, "a") as f:
        f.write(line + "\n")
    with _lock:
        _last_status_time = time.time()


def detail(msg):
    with open(DETAIL_LOG, "a") as f:
        f.write(f"[{ts()}] {msg}\n")


def set_phase(msg):
    global _current_phase
    with _lock:
        _current_phase = msg
    detail(f"phase: {msg}")


def heartbeat_loop(interval_s=3600, poll_s=300):
    while True:
        time.sleep(poll_s)
        with _lock:
            idle = time.time() - _last_status_time
            phase = _current_phase
        if idle > interval_s:
            status(f"heartbeat: alive, no milestone for {idle / 3600:.1f}h; phase: {phase}")


def sci(U):
    s = str(U)
    return s if len(s) <= 7 else f"{s[0]}.{s[1:7]}e+{len(s) - 1}"


def atomic_json(obj, path):
    tmp = f"{path}.tmp{os.getpid()}"
    with open(tmp, "w") as f:
        json.dump(obj, f)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


# ------------------------------------------------------------------- state
def load_rows():
    for p in (RUNGS_PATH, RUNGS_PATH + ".bak"):
        try:
            rows = json.load(open(p))
            if p != RUNGS_PATH:
                status(f"WARNING: {RUNGS_PATH} unreadable, recovered from {p}")
            return rows
        except Exception as e:  # noqa: BLE001
            detail(f"could not load {p}: {e!r}")
    raise RuntimeError("no readable rungs file")


def load_state(rows):
    st = json.load(open(STATE_PATH)) if os.path.exists(STATE_PATH) else {
        "version": 4, "batch_num": 0, "frontier_Y": 381955227123741088927564307036088981567052373337450950635383725237087693974855332435691045662989840261558548967445786887518494682456413097660959423602388741249457342676079609013194550951033589941476288935375191963575520963986106173336342868353615727493039925808212253434183765434043533942508100320147609162025673655923604928764288600845960267202822996236823079193153323100382133113784893435,
        "total_rungs": 929, "exported_rows": 590, "next_chunk_idx": 40}
    st.setdefault("est_bytes_per_row", 7.9e6)   # WideExt40-44: 114-128 MB / 15 rows at ~422 digits
    st.setdefault("est_bytes_digits", 422)
    st.setdefault("est_gb_per_mb", 0.16)        # Phase 2: ~34 GB for 2 files of ~105 MB
    st.setdefault("chunk_rows_cap", MAX_CHUNK_ROWS)
    st.setdefault("build_skips", 0)
    st.setdefault("consecutive_skips", 0)
    assert rows[st["exported_rows"] - 1][0] == st["frontier_Y"], \
        "state frontier does not match rungs file -- refusing to continue"
    return st


def save_state(st):
    atomic_json(st, STATE_PATH)


# ------------------------------------------------------------------ search
def branch_params(F, i):
    """Window for branch i at frontier F, or None if i is infeasible here."""
    c, tp = 2 ** i, 3 * 2 ** i
    side = tp * factorial(tp)
    nmax, nmin = F - 2, -(-(2 * F + 20) // 5)
    pmax, pmin = nmax // c, -(-nmin // c)
    pmin = max(pmin, side + 1)
    if pmin > pmax:
        return None
    a = max(2, pmax.bit_length() - 27)
    hlo, hhi = (pmin - 1) // 2 ** a + 1, (pmax - 1) // 2 ** a
    if hhi < 3 or hhi > PMAXH:
        return None
    return (hlo, hhi, a, c, side, tp)


def _worker_init():
    try:
        os.nice(10)          # lean (the critical path during an overlapped build) wins the CPU
    except Exception:        # noqa: BLE001
        pass


def _block_task(arg):
    """One block of one branch: (i, k, h or None, past_end_of_window)."""
    i, k, (hlo, hhi, a, c, side, tp) = arg
    h, ex = fs.scan(hlo, hhi, a, c, side, budget=10 ** 9, b_first=k, b_last=k + 1)
    return i, k, h, ex


def scan_stage(pool, params, k0, k1, nworkers):
    """Blocks [k0,k1) of every live branch, spread over the worker pool.

    Returns {i: h or None} where h is the largest h in that block range -- the
    hit with the smallest block index, which is what the sequential top-down
    scan of the same range returns, because blocks descend in h and each block
    is scanned downwards internally.
    """
    nxt = {i: k0 for i in params}
    hit = {i: None for i in params}          # i -> (block index, h)
    end = {i: k1 for i in params}            # first block known to be past the window
    inflight = []
    while True:
        while len(inflight) < nworkers:
            cand = [i for i in params if nxt[i] < min(end[i], k1)
                    and (hit[i] is None or nxt[i] < hit[i][0])]
            if not cand:
                break
            i = min(cand, key=lambda j: (nxt[j], j))
            k, nxt[i] = nxt[i], nxt[i] + 1
            inflight.append(pool.apply_async(_block_task, ((i, k, params[i]),)))
        if not inflight:
            return {i: (hit[i][1] if hit[i] else None) for i in params}
        ready = [ar for ar in inflight if ar.ready()]
        if not ready:
            time.sleep(0.003)
            continue
        for ar in ready:
            inflight.remove(ar)
            i, k, h, past = ar.get()
            if past:
                end[i] = min(end[i], k)
            if h is not None and (hit[i] is None or k < hit[i][0]):
                hit[i] = (k, h)


def find_rung(F, pool, nworkers=SEARCH_WORKERS):
    params = {}
    for i in I_RANGE:
        pr = branch_params(F, i)
        if pr is not None:
            params[i] = pr
    if not params:
        return None, BUDGET_STAGES[-1]
    k0 = 0
    for budget in BUDGET_STAGES:
        best = None
        for i, h in scan_stage(pool, params, k0, budget, nworkers).items():
            if h is None:
                continue
            hlo, hhi, a, c, side, tp = params[i]
            p = h * 2 ** a + 1
            U = cover(c, p)
            if U >= F and (best is None or U > best[0]):
                best = (U, c, i, h, a, p, c * p + 1, tp)
        if best is not None:
            return best, budget
        k0 = budget                     # stage 1 proved 0..k0 empty: do not rescan
    return None, BUDGET_STAGES[-1]


def search_one_batch(pool, rows, st, builder):
    """Search until the next build should be handed off (or we must stop).

    Keeps searching while a build runs; that overlap is the point. Stops early
    only at MAX_PENDING_ROWS, so one build never gets an unbounded batch.
    """
    n0, t_batch = len(rows), time.time()
    U_last = rows[-1][0]
    stalled = False
    while True:
        pending = len(rows) - st["exported_rows"]
        ready = (len(rows) - n0) >= BATCH_SIZE or time.time() - t_batch >= BATCH_TIME_S
        if builder.failed_correctness():
            return "BUILD_STOP"
        if os.path.exists(STOP_MANUAL):
            return "BATCH_DONE"
        if not builder.busy() and (ready or pending >= MAX_PENDING_ROWS):
            return "BATCH_DONE"
        if pending >= MAX_PENDING_ROWS:
            if not stalled:
                status(f"search paused at {pending} pending rows (cap {MAX_PENDING_ROWS}); waiting for "
                       f"the running build to finish before handing over the next batch")
                set_phase("waiting for the build slot (pending-row cap)")
                stalled = True
            time.sleep(5)
            continue
        F = U_last + 1
        t0 = time.time()
        try:
            r, budget = find_rung(F, pool,
                                  SEARCH_WORKERS_BUILDING if builder.busy() else SEARCH_WORKERS)
        except Exception as e:  # noqa: BLE001
            detail(f"EXCEPTION during search at F={sci(F)}: {e!r}\n{traceback.format_exc()}")
            return "EXCEPTION"
        dt = time.time() - t0
        if r is None:
            detail(f"GENUINE STOP at F={sci(F)}: no rung, all i in {I_RANGE}, full-window budget (dt={dt:.1f}s)")
            return "GENUINE_STOP"
        rows.append(list(r))
        atomic_json(rows, RUNGS_PATH)
        if len(rows) % 25 == 0:
            shutil.copyfile(RUNGS_PATH, RUNGS_PATH + ".bak")
        U_last = r[0]
        detail(f"rung {339 + len(rows)}: U={sci(r[0])} ({len(str(r[0]))}d) c={r[1]} i={r[2]} "
               f"budget={budget} dt={dt:.2f}s")


RUNG_RE = re.compile(r"rung (\d+): U=\S+ \((\d+)d\) c=(\d+) i=(\d+).*?dt=([\d.]+)s")


def rung_log_stats():
    """{rung_no: (digits, i, dt)} from the detail log (v2 and v3 lines)."""
    out = {}
    try:
        for line in open(DETAIL_LOG, errors="replace"):
            m = RUNG_RE.search(line)
            if m:
                out[int(m.group(1))] = (int(m.group(2)), int(m.group(4)), float(m.group(5)))
    except FileNotFoundError:
        pass
    return out


# ------------------------------------------------------------------- build
RESOURCE_PAT = re.compile(r"code 137|signal 9|SIGKILL|[Kk]illed|out of memory|bad_alloc|heartbeats|"
                          r"deterministic\) timeout|[Ss]tack overflow|maximum recursion|"
                          r"[Cc]annot allocate|memory exhausted|TIMEOUT", re.I)
LEAN_ERR = re.compile(r"error: .*\.lean:\d+:\d+:")
AX_LINE = re.compile(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]")
BUILT_RE = re.compile(r"Built P287\.(\w+) \(([^)]*)\)")


def required_theorems(target):
    if target.startswith("WideExt"):
        return [f"{target}.chunk_gap"]
    if target.startswith("Main"):
        return [f"{target}.erdos287_below"]
    if target.startswith("Records"):
        return [f"{target}.erdos287_n1", f"{target}.erdos287_k"]
    if target.startswith("Conditional"):
        return [f"{target}.erdos287_of_rung"]
    return []


def parse_dur(s):
    tot = 0.0
    for num, unit in re.findall(r"([\d.]+)\s*(ms|s|m|h)", s):
        tot += float(num) * {"ms": 1e-3, "s": 1, "m": 60, "h": 3600}[unit]
    return tot


class MemSampler(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self.peak = 0.0
        self.base = self.used()
        self._halt = threading.Event()

    @staticmethod
    def used():
        info = {}
        for line in open("/proc/meminfo"):
            k, v = line.split(":", 1)
            info[k] = int(v.split()[0])
        return (info["MemTotal"] - info["MemAvailable"]) / 2 ** 20  # GiB

    def run(self):
        while not self._halt.is_set():
            self.peak = max(self.peak, self.used())
            self._halt.wait(5)

    def stop(self):
        self._halt.set()


def run_lake(targets, tag):
    """One `lake build` invocation. Returns (verdict, why, text, per_target_s)."""
    path = f"{BUILD_LOG_DIR}/{time.strftime('%Y%m%d_%H%M%S', time.gmtime())}_{tag}.log"
    args = [LAKE, "build"] + [f"P287.{t}" for t in targets]
    detail(f"lake: {' '.join(args[1:]) if targets else 'build (full repo)'} -> {path}")
    with open(path, "w") as f:
        proc = subprocess.Popen(args, cwd=LEAN_DIR, stdout=f, stderr=subprocess.STDOUT,
                                start_new_session=True)
        try:
            rc = proc.wait(timeout=BUILD_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            rc = "TIMEOUT"
    text = open(path, errors="replace").read()
    per = {m.group(1): parse_dur(m.group(2)) for m in BUILT_RE.finditer(text)}
    completed = rc == 0 and "Build completed successfully" in text
    lean_errs = [ln for ln in text.splitlines() if LEAN_ERR.search(ln) and not RESOURCE_PAT.search(ln)]
    sorry = "declaration uses 'sorry'" in text
    found, bad_ax = {}, []
    for m in AX_LINE.finditer(text):
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        found[m.group(1)] = axs
        if not axs <= CLEAN_AXIOMS:
            bad_ax.append(f"{m.group(1)}: {sorted(axs)}")
    required = [thm for t in targets for thm in required_theorems(t)]
    missing = [thm for thm in required if thm not in found]
    if lean_errs or sorry or bad_ax:
        why = (f"lean errors={lean_errs[:5]} sorry={sorry} bad_axioms={bad_ax[:5]} log={path}")
        return "correctness", why, text, per
    if not completed or "error:" in text:
        tail = " | ".join(text.strip().splitlines()[-4:])[-600:]
        return "resource", f"rc={rc} (no Lean-located error) log={path} tail={tail}", text, per
    if missing:
        return "correctness", f"build green but #print axioms missing for {missing[:5]} log={path}", text, per
    return "ok", "", text, per


def build_targets(targets, conc, tag, extra_required=()):
    """Groups of `conc`; on the first failure, retry every unfinished target
    once at lower concurrency. Returns (verdict, why, per_target_s)."""
    per_all, done = {}, set()

    def group_run(group, label):
        v, why, text, per = run_lake(group, label)
        per_all.update(per)
        if v == "ok" and extra_required:
            found = {m.group(1) for m in AX_LINE.finditer(text)}
            miss = [x for x in extra_required if x not in found]
            if miss:
                return "correctness", f"full build green but axioms lines missing for {miss}"
        return v, why

    groups = [targets[k:k + conc] for k in range(0, len(targets), conc)] if targets else [[]]
    first_fail = None
    for gi, g in enumerate(groups):
        v, why = group_run(g, f"{tag}_try1_g{gi}")
        if v == "ok":
            done.update(g)
        else:
            first_fail = (v, why)
            break
    if first_fail is None:
        return "ok", "", per_all
    retry_conc = max(1, conc // 4)
    status(f"build {tag}: attempt 1 failed ({first_fail[0]}: {first_fail[1][:300]}); "
           f"retrying unfinished targets once at concurrency {retry_conc}")
    todo = [t for t in targets if t not in done] if targets else []
    groups = [todo[k:k + retry_conc] for k in range(0, len(todo), retry_conc)] if targets else [[]]
    for gi, g in enumerate(groups):
        v, why = group_run(g, f"{tag}_try2_g{gi}")
        if v != "ok":
            return v, why, per_all
    return "ok", "", per_all


# ---------------------------------------------------------- lean generation
def _emit_one(arg):
    name, chunk, start = arg
    lo, hi = gen_cert3.emit3(chunk, name, f"{LEAN}{name}.lean", start)
    return name, lo, hi


def gen_wide_ext_chunks(st, new_rows, rows_per_chunk):
    """Write the WideExt chunk files. emit3 returns (start, rungs[-1][0]), so
    chunk k+1's window start -- one past chunk k's last U -- is known before any
    file is written and the chunks can be generated in parallel (this was ~26 s
    per rung of single-threaded Python inside the build). Every file's window is
    re-checked against the prediction afterwards; a mismatch aborts the build
    rather than handing Lean a ladder with a gap. A `spawn` pool is used on
    purpose: this runs on the builder thread while the search threads hold
    locks, and spawn (unlike fork) cannot inherit a held lock.
    """
    start, idx, tasks, info = st["frontier_Y"] + 1, st["next_chunk_idx"], [], []
    for k in range(0, len(new_rows), rows_per_chunk):
        chunk = new_rows[k:k + rows_per_chunk]
        name = f"WideExt{idx}"
        tasks.append((name, chunk, start))
        info.append({"idx": idx, "name": name, "lo": start, "hi": chunk[-1][0], "rows": len(chunk)})
        start, idx = chunk[-1][0] + 1, idx + 1
    nw = min(GEN_WORKERS, len(tasks))
    if nw > 1:
        with mp.get_context("spawn").Pool(nw) as gp:
            out = {n: (lo, hi) for n, lo, hi in gp.map(_emit_one, tasks)}
    else:
        out = {n: (lo, hi) for n, lo, hi in map(_emit_one, tasks)}
    for c in info:
        lo, hi = out[c["name"]]
        if (lo, hi) != (c["lo"], c["hi"]):
            raise AssertionError(f"{c['name']}: emitted window [{lo},{hi}] != expected "
                                 f"[{c['lo']},{c['hi']}] -- refusing to build this batch")
    return info, idx


def gen_mainN(st, info, N):
    PREV, Y_prev, Y = st["version"], st["frontier_Y"], info[-1]["hi"]
    X = (100 * (Y + 2)) // 739
    assert 739 * X <= 100 * (Y + 2)
    K = (3 * Y - 20) // 10 + 1
    assert 10 * (K - 1) + 20 <= 3 * Y
    names = [c["name"] for c in info]
    L = [f"/- Erdos #287 kernel-verified for every largest term up to {sci(Y)}.",
         f"   Main{PREV} (M <= {sci(Y_prev)}) + {names[0]}..{names[-1]}",
         "   (Phase 3 extension, see PROGRESS.md). -/",
         f"import P287.Main{PREV}"] + [f"import P287.{nm}" for nm in names] + [
        "", f"namespace Main{N}", "",
        "/-- **Erdos #287 holds for every representation whose largest term is at most",
        f"    {Y}.** -/",
        "theorem erdos287_below {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)",
        "    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)",
        "    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)",
        f"    (hhi : s ⟨k - 1, by omega⟩ ≤ {Y}) :",
        "    3 ≤ PCI.max_gap k s := by",
        f"  by_cases b0 : s ⟨k - 1, by omega⟩ ≤ {Y_prev}",
        f"  · exact Main{PREV}.erdos287_below hk s hmono h1 hsum b0",
        "  push_neg at b0"]
    for j, c in enumerate(info):
        L += [f"  by_cases b{j + 1} : s ⟨k - 1, by omega⟩ ≤ {c['hi']}",
              f"  · exact {c['name']}.chunk_gap hk s hmono h1 hsum (by omega) b{j + 1}",
              f"  push_neg at b{j + 1}"]
    L += ["  omega", "", "#print axioms erdos287_below", "", f"end Main{N}"]
    open(f"{LEAN}Main{N}.lean", "w").write("\n".join(L) + "\n")

    R = ["/- The two records, restated against the extended range. -/",
         f"import P287.Main{N}", "import P287.Window4", "import P287.Lower",
         "import P287.Kbound", "", f"namespace Records{N}", "",
         f"/-- **Every counterexample to #287 has n1 > {X}**. -/",
         "theorem erdos287_n1 {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)",
         "    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)",
         "    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)",
         f"    (hn : s ⟨0, by omega⟩ ≤ {X}) :",
         "    3 ≤ PCI.max_gap k s := by",
         "  by_contra hc", "  push_neg at hc",
         "  have hg : PCI.max_gap k s ≤ 2 := by omega",
         "  have hw := Window4.window4 hk s hmono h1 hsum hg",
         f"  have hM : s ⟨k - 1, by omega⟩ ≤ {Y} := by omega",
         f"  have := Main{N}.erdos287_below hk s hmono h1 hsum hM", "  omega", "",
         f"/-- **Every counterexample to #287 has k > {K - 1}**. -/",
         "theorem erdos287_k {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)",
         "    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)",
         "    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)",
         f"    (hkle : k ≤ {K}) :",
         "    3 ≤ PCI.max_gap k s := by",
         "  by_contra hc", "  push_neg at hc",
         "  have hg : PCI.max_gap k s ≤ 2 := by omega",
         "  have h2 := Lower.lower hk s hmono h1 hsum",
         "  have h3 := Kbound.term_le s hk hg (k - 1) (by omega)",
         f"  have hM : s ⟨k - 1, by omega⟩ ≤ {Y} := by omega",
         f"  have := Main{N}.erdos287_below hk s hmono h1 hsum hM", "  omega", "",
         "#print axioms erdos287_n1", "#print axioms erdos287_k", "", f"end Records{N}"]
    open(f"{LEAN}Records{N}.lean", "w").write("\n".join(R) + "\n")

    C = ["/- Erdos #287 in full, conditional only above the extended range. -/",
         f"import P287.Main{N}", "import P287.StepA2", "", f"namespace Conditional{N}", "",
         "def rung (M : ℕ) : Prop :=",
         "  ∃ p q n a b tp tq : ℕ,",
         "    Nat.Prime p ∧ Nat.Prime q ∧ 1 ≤ tp ∧ 1 ≤ tq ∧",
         "    tp * Nat.factorial tp < p ∧ tq * Nat.factorial tq < q ∧",
         "    n = a * p ∧ n + 1 = b * q ∧",
         "    n + 2 ≤ M ∧ M < (tp + 1) * p ∧ M < (tq + 1) * q ∧ 2 * M + 20 ≤ 5 * n",
         "",
         "theorem erdos287_of_rung",
         f"    (H : ∀ M : ℕ, {Y} < M → rung M)",
         "    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)",
         "    (h1 : 1 < s ⟨0, by omega⟩)",
         "    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :",
         "    3 ≤ PCI.max_gap k s := by",
         f"  by_cases hM : s ⟨k - 1, by omega⟩ ≤ {Y}",
         f"  · exact Main{N}.erdos287_below hk s hmono h1 hsum hM",
         "  push_neg at hM",
         "  obtain ⟨p, q, n, a, b, tp, tq, hp, hq, htp, htq, hpf, hqf, hna, hnb,",
         "    hlo, hhip, hhiq, hint⟩ := H _ hM",
         "  exact StepA2.step_gap hp hq htp htq hpf hqf hna hnb hk s hmono h1 hsum",
         "    hlo hhip hhiq hint",
         "",
         "#print axioms erdos287_of_rung", "", f"end Conditional{N}"]
    open(f"{LEAN}Conditional{N}.lean", "w").write("\n".join(C) + "\n")
    return Y, X, K


def _import_lines(N):
    return [f"import P287.Main{N}\n", f"import P287.Records{N}\n", f"import P287.Conditional{N}\n"]


def wire(N):
    p = f"{LEAN_DIR}/P287.lean"
    text = open(p).read()
    if _import_lines(N)[0] in text:
        return
    marker = f"import P287.Conditional{N - 1}\n"
    assert marker in text, f"marker {marker!r} missing from P287.lean"
    open(p + ".tmp", "w").write(text.replace(marker, marker + "".join(_import_lines(N)), 1))
    os.replace(p + ".tmp", p)


def unwire(N):
    p = f"{LEAN_DIR}/P287.lean"
    lines = open(p).readlines()
    keep = [ln for ln in lines if ln not in _import_lines(N)]
    if len(keep) != len(lines):
        open(p + ".tmp", "w").writelines(keep)
        os.replace(p + ".tmp", p)


def olean_bytes(name):
    return sum(os.path.getsize(f) for f in glob.glob(f"{LEAN_DIR}/.lake/build/lib/lean/P287/{name}.*"))


# ------------------------------------------------------------ build batch
CSV_COLS = ["utc", "main_version", "result", "rows", "rung_first", "rung_last", "digits_end",
            "search_s_per_rung", "rows_per_chunk", "n_chunks", "build_conc", "lean_bytes_per_rung",
            "olean_bytes_per_rung", "gen_s", "chunk_build_cpu_s_per_rung", "build_wall_s",
            "build_wall_s_per_rung", "peak_mem_gb", "peak_mem_gb_per_proc", "disk_free_gb", "note"]


def append_csv(row):
    new = not os.path.exists(COST_CSV)
    with open(COST_CSV, "a") as f:
        if new:
            f.write(",".join(CSV_COLS) + "\n")
        f.write(",".join(str(row.get(c, "")).replace(",", ";").replace("\n", " ") for c in CSV_COLS) + "\n")


def plan_build(st, digits):
    bpr = st["est_bytes_per_row"] * (digits / st["est_bytes_digits"]) ** 2
    rows = max(1, min(MAX_CHUNK_ROWS, st["chunk_rows_cap"], int(TARGET_CHUNK_BYTES // bpr)))
    gb = BASE_GB_PER_PROC + st["est_gb_per_mb"] * rows * bpr / 2 ** 20
    conc = max(1, min(MAX_BUILD_CONC, int(MEM_BUDGET_GB // gb)))
    return rows, conc


LIVE_ROWS = None          # the appended-to list; the build works on a copy


TARGET_DIGITS = 1001             # 10^1000 is the first 1001-digit number
CROSSED_FLAG = f"{WORK}/CROSSED_1E1000"


def milestone_time(n):
    """UTC epoch of the MILESTONE line for Main{n} in the status log, or None."""
    stamp = None
    try:
        for ln in open(STATUS_LOG, errors="replace"):
            if ln.startswith("[") and f"MILESTONE: Main{n}." in ln:
                stamp = ln[1:20]
    except OSError:
        return None
    try:
        return calendar.timegm(time.strptime(stamp, "%Y-%m-%d %H:%M:%S")) if stamp else None
    except ValueError:
        return None


def build_batch(st, rows, reason):
    """`rows` is a snapshot: rows[exported:] is exactly what this build covers."""
    exported = st["exported_rows"]
    Y_before = st["frontier_Y"]
    new_rows = rows[exported:]
    if not new_rows:
        return "nothing"
    if st["consecutive_skips"] >= 3 and st["chunk_rows_cap"] == 1:
        status("BUILD LIMIT: 3 consecutive skipped builds already at 1 rung per chunk -- not "
               "attempting further builds (search continues). See MORNING_SUMMARY.md.")
        return "limit"
    N = st["version"] + 1
    r_first, r_last = 339 + exported + 1, 339 + len(rows)
    digits = len(str(new_rows[-1][0]))
    rpc, conc = plan_build(st, digits)
    status(f"Build Main{N}: rungs {r_first}-{r_last} ({len(new_rows)} rows, up to {digits} digits), "
           f"{rpc} rows/chunk, concurrency {conc} [{reason}]")
    row = {"utc": ts(), "main_version": N, "rows": len(new_rows), "rung_first": r_first,
           "rung_last": r_last, "digits_end": digits, "rows_per_chunk": rpc, "build_conc": conc,
           "note": "p4" + (" overlapped" if OVERLAP else "")}
    rs = rung_log_stats()
    dts = [rs[n][2] for n in range(r_first, r_last + 1) if n in rs]
    row["search_s_per_rung"] = f"{sum(dts) / len(dts):.2f}" if dts else ""

    sampler = MemSampler()
    sampler.start()
    t0 = time.time()
    verdict, why, Y, X, K, info = "resource", "", None, None, None, []
    try:
        set_phase(f"Main{N}: generating chunks")
        info, next_idx = gen_wide_ext_chunks(st, new_rows, rpc)
        row["gen_s"] = f"{time.time() - t0:.0f}"
        row["n_chunks"] = len(info)
        lean_bytes = sum(os.path.getsize(f"{LEAN}{c['name']}.lean") for c in info)
        row["lean_bytes_per_rung"] = int(lean_bytes / len(new_rows))
        set_phase(f"Main{N}: lake build {len(info)} chunks at concurrency {conc}")
        verdict, why, per = build_targets([c["name"] for c in info], conc, f"Main{N}_chunks")
        cpu = sum(per.get(c["name"], 0) for c in info)
        row["chunk_build_cpu_s_per_rung"] = f"{cpu / len(new_rows):.1f}" if cpu else ""
        if verdict == "ok":
            set_phase(f"Main{N}: generating + building Main/Records/Conditional")
            Y, X, K = gen_mainN(st, info, N)
            verdict, why, _ = build_targets([f"Main{N}", f"Records{N}", f"Conditional{N}"], 3,
                                            f"Main{N}_top")
        if verdict == "ok":
            set_phase(f"Main{N}: full repo lake build")
            wire(N)
            req = [x for t in (f"Main{N}", f"Records{N}", f"Conditional{N}") for x in required_theorems(t)]
            verdict, why, _ = build_targets([], 1, f"Main{N}_fullrepo", extra_required=req)
    except Exception as e:  # noqa: BLE001  (generation/python bug => not a certificate failure)
        verdict, why = "resource", f"python exception {e!r}"
        detail(traceback.format_exc())
    finally:
        sampler.stop()
    wall = time.time() - t0
    peak = max(0.0, sampler.peak - sampler.base)
    row.update({"build_wall_s": f"{wall:.0f}", "build_wall_s_per_rung": f"{wall / len(new_rows):.1f}",
                "peak_mem_gb": f"{peak:.1f}", "peak_mem_gb_per_proc": f"{peak / conc:.1f}",
                "disk_free_gb": f"{shutil.disk_usage(LEAN_DIR).free / 2 ** 30:.0f}"})

    if verdict == "ok":
        ob = sum(olean_bytes(c["name"]) for c in info)
        row["olean_bytes_per_rung"] = int(ob / len(new_rows))
        row["result"] = "VERIFIED"
        mean_mb = lean_bytes / len(info) / 2 ** 20
        st.update({"version": N, "batch_num": st["batch_num"] + 1, "frontier_Y": Y,
                   "total_rungs": r_last, "exported_rows": len(rows), "next_chunk_idx": next_idx,
                   "est_bytes_per_row": lean_bytes / len(new_rows), "est_bytes_digits": digits,
                   "consecutive_skips": 0})
        if mean_mb > 1:
            measured = max(0.0, peak / min(conc, len(info)) - BASE_GB_PER_PROC) / mean_mb
            st["est_gb_per_mb"] = max(0.08, measured)
        save_state(st)
        shutil.copyfile(RUNGS_PATH, f"{WORK}/rungs_snapshot_Main{N}.json")
        append_csv(row)
        status(f"MILESTONE: Main{N}.erdos287_below kernel-verified, M <= {sci(Y)} ({len(str(Y))} digits); "
               f"{r_last} rungs verified (+{len(new_rows)}); build {wall:.0f}s, peak mem {peak:.0f} GB; "
               f"full lake build green, axioms clean, no sorry. Records{N}: n1 > {sci(X)}, k > {sci(K - 1)}.")
        if len(str(Y)) >= TARGET_DIGITS > len(str(Y_before)) and not os.path.exists(CROSSED_FLAG):
            t14 = milestone_time(14)
            since = f" {(time.time() - t14) / 3600:.1f} h after Main14 was verified," if t14 else ""
            line = (f"*** 10^1000 CROSSED *** Main{N}.erdos287_below is kernel-verified at "
                    f"M <= {sci(Y)} ({len(str(Y))} digits), the first bound at or above 10^1000:"
                    f"{since} {r_last} rungs ({r_last - 1456} since Main14). Full lake build green, "
                    "axioms [propext, Classical.choice, Quot.sound], no sorry. Not a stop condition: "
                    "the run continues past it.")
            status(line)
            try:
                with open(CROSSED_FLAG, "w") as f:
                    f.write(f"[{ts()} UTC] {line}\n\nExact bound:\n{Y}\n")
            except OSError as e:  # noqa: BLE001
                detail(f"crossing flag write failed: {e!r}")
        try:
            with open(PROGRESS, "a") as f:
                f.write(f"\n- **[{ts()} UTC] Main{N} verified** (Phase 3, automatic): "
                        f"`Main{N}.erdos287_below` M <= {sci(Y)} ({len(str(Y))} digits), {r_last} rungs "
                        f"(rungs {r_first}-{r_last} in WideExt{info[0]['idx']}..WideExt{info[-1]['idx']}); "
                        f"`Records{N}.erdos287_n1`/`erdos287_k`, `Conditional{N}.erdos287_of_rung`; "
                        f"full `lake build` green, axioms [propext, Classical.choice, Quot.sound], no sorry. "
                        f"Build {wall:.0f}s, peak mem {peak:.0f} GB, {rpc} rows/chunk x{conc}.\n")
        except Exception as e:  # noqa: BLE001
            detail(f"PROGRESS.md append failed: {e!r}")
        write_summary(st, rows)
        return "ok"

    unwire(N)
    if verdict == "correctness":
        row["result"] = "CORRECTNESS_STOP"
        row["note"] = "p4 " + why[:290]
        append_csv(row)
        open(STOP_CORRECTNESS, "w").write(
            f"{ts()} UTC: correctness-level failure building Main{N} (rungs {r_first}-{r_last}).\n{why}\n"
            f"Main{N} imports were removed from P287.lean; last verified state is unchanged.\n"
            "The watchdog will not restart the orchestrator while this file exists.\n")
        status(f"CORRECTNESS STOP building Main{N}: {why[:800]} -- orchestrator exiting, needs a human "
               f"(see {STOP_CORRECTNESS}). Verified state unchanged: Main{st['version']}.")
        write_summary(st, rows)
        return "correctness"

    st["build_skips"] += 1
    st["consecutive_skips"] += 1
    st["chunk_rows_cap"] = max(1, rpc // 2)
    save_state(st)
    row["result"] = "SKIPPED"
    row["note"] = "p4 " + why[:290]
    append_csv(row)
    status(f"BUILD_SKIPPED Main{N} (rungs {r_first}-{r_last}) after retry: {why[:600]}. Un-wired; search "
           f"continues; these rows will be retried with the next batch at <= {st['chunk_rows_cap']} rows/chunk.")
    write_summary(st, rows)
    return "skipped"


# ---------------------------------------------------------------- summary
def _fit(pts):
    """Least-squares y = A * d^b on log-log; needs >= 2 distinct d."""
    pts = [(d, y) for d, y in pts if d > 0 and y > 0]
    if len({d for d, _ in pts}) < 2:
        return None
    xs, ys = [log(d) for d, _ in pts], [log(y) for _, y in pts]
    n, mx, my = len(xs), sum(xs) / len(xs), sum(ys) / len(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    return (2.718281828459045 ** (my - b * mx), b, n)


def _fit_guarded(pts):
    """_fit, but only trust a slope when the points span enough digits."""
    f = _fit(pts)
    ds = [d for d, y in pts if d > 0 and y > 0]
    if not f or not ds:
        return f
    if max(ds) / min(ds) < 1.2 or abs(f[1]) > 4:
        ys = sorted(y for d, y in pts if d > 0 and y > 0)
        return (ys[len(ys) // 2], 0.0, len(ys))       # flat: median, no slope
    return f


def _read_csv():
    try:
        lines = open(COST_CSV).read().strip().splitlines()
    except FileNotFoundError:
        return []
    hdr = lines[0].split(",")
    return [dict(zip(hdr, ln.split(","))) for ln in lines[1:]]


def _f(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def write_summary(st, rows):
    rows = LIVE_ROWS if LIVE_ROWS is not None else rows   # builds pass a snapshot; report live
    try:
        _write_summary(st, rows)
    except Exception as e:  # noqa: BLE001
        detail(f"summary write failed: {e!r}\n{traceback.format_exc()}")


def _write_summary(st, rows):
    recs = _read_csv()
    ver = [r for r in recs if r.get("result") == "VERIFIED"]
    rs = rung_log_stats()
    Y = st["frontier_Y"]
    out = [f"# Erdős #287 — Phase 3/4 run summary", "",
           f"_Auto-generated {ts()} UTC by phase4_orchestrator.py (rewritten at every verified MainN, "
           "skip, or stop)._", "",
           "## Latest kernel-verified bound", "",
           f"- **`Main{st['version']}.erdos287_below`: M ≤ {sci(Y)} ({len(str(Y))} digits)**",
           ("- **Past the 10^1000 target** (a 1001-digit bound); the run continues."
            if len(str(Y)) >= 1001 else
            f"- Target 10^1000: **{1001 - len(str(Y))} digits to go** from here."),
           f"- Verified rungs: **{st['total_rungs']}** (339 Phase 1 + 590 Phase 2 + "
           f"{st['total_rungs'] - 929} Phase 3); Phase 3 batches verified: {len(ver)}",
           f"- Also: `Records{st['version']}.erdos287_n1`, `Records{st['version']}.erdos287_k`, "
           f"`Conditional{st['version']}.erdos287_of_rung` (all in "
           "`~/erdos287-verify/erdos-287-lean/P287/`).",
           "- Rule: counted only after a green full `lake build`, axioms ⊆ [propext, Classical.choice, "
           "Quot.sound], no sorry.", "",
           "Exact bound:", "", "```", str(Y), "```", "",
           "## Search frontier (NOT yet verified unless equal to the above)", "",
           f"- Rungs searched: {339 + len(rows)}; frontier U ≈ {sci(rows[-1][0])} "
           f"({len(str(rows[-1][0]))} digits); searched-but-unverified rungs: {len(rows) - st['exported_rows']}",
           f"- Build skips so far: {st['build_skips']} (consecutive: {st['consecutive_skips']}); "
           f"rows/chunk cap: {st['chunk_rows_cap']}", ""]
    for flag in (STOP_CORRECTNESS, STOP_EXHAUSTED, STOP_MANUAL):
        if os.path.exists(flag):
            out += [f"**STOP FLAG PRESENT: `{flag}`**", "", "```", open(flag).read()[:3000], "```", ""]
    out += ["## Batches (phase3_cost_curve.csv)", "",
            "| Main | result | rungs | digits | search s/rung | rows/chunk×conc | Lean MB/rung | olean MB/rung | "
            "chunk CPU s/rung | build wall s | peak GB (per proc) |", "|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in recs:
        lb, ob = _f(r.get("lean_bytes_per_rung")), _f(r.get("olean_bytes_per_rung"))
        lbs = "" if lb is None else "%.1f" % (lb / 2 ** 20)
        obs = "" if ob is None else "%.1f" % (ob / 2 ** 20)
        out.append("| %s | %s | %s-%s | %s | %s | %s×%s | %s | %s | %s | %s | %s (%s) |" % (
            r.get("main_version"), r.get("result"), r.get("rung_first"), r.get("rung_last"),
            r.get("digits_end"), r.get("search_s_per_rung"), r.get("rows_per_chunk"), r.get("build_conc"),
            lbs, obs, r.get("chunk_build_cpu_s_per_rung"), r.get("build_wall_s"), r.get("peak_mem_gb"),
            r.get("peak_mem_gb_per_proc")))
    out.append("")

    wins = {}
    for n, (d, i, dt) in rs.items():
        if n >= 930:
            wins[i] = wins.get(i, 0) + 1
    out += ["## Search tuning notes", "",
            f"- Winning branch counts since rung 930 (i: count): {dict(sorted(wins.items()))}",
            "- Even i is structurally dead: c=2^i≡1 (mod 3) ⇒ q=c·p+1≡p+1, so q prime needs p≡1 (mod 3) ⇒ "
            "3 | h·2^a ⇒ 3 | h, impossible for prime h>3. Dropped from the search at the v3 switch "
            "(rungs 930–1018 used v2: i=1..8, budget 260 for every rung).",
            "- Odd i have no small-prime obstruction (for r ≥ 5 at most 2 of r−1 residues of h are excluded); "
            "which odd i wins is chance. i=7 becomes feasible only once F exceeds ~830 digits "
            "(needs 3c·(3c)! < F/c).",
            "- v3 used budget 60 first, 260 only if every branch missed; v4 keeps that and no longer "
            "rescans blocks 0–59 in stage 2.",
            f"- **v4 (Phase 4)**: gmpy2 {('ON' if fs.HAVE_GMPY2 else 'OFF')} (19× faster Miller–Rabin, "
            "validated against the whole accepted ladder), (branch, block) tasks over "
            f"{SEARCH_WORKERS} workers instead of 5, builds overlapped with the next batch's search "
            f"(overlap={OVERLAP}), batches of ≥{BATCH_SIZE} rows (cap {MAX_PENDING_ROWS}). "
            "Rows in the table with note `p4` use it; compare `search_s_per_rung` across the switch.", ""]

    # --- fits & projections
    out += ["## Cost curve fit and projected practical limit", ""]
    p4_first, cfg = 10 ** 9, "v3 config"
    try:
        for ln in open(STATUS_LOG, errors="replace"):
            if "orchestrator v4 started" in ln:
                m = re.search(r"searched rungs (\d+)", ln)
                if m:
                    p4_first = min(p4_first, int(m.group(1)) + 1)
    except OSError:
        pass
    sp = [(int(d), dt) for n, (d, i, dt) in rs.items() if n >= p4_first]
    if len(sp) >= 15:
        cfg = f"v4 config: gmpy2 + {SEARCH_WORKERS} workers, rungs {p4_first}+"
    else:                                  # not enough v4 points yet
        sp = [(int(d), dt) for n, (d, i, dt) in rs.items() if 1019 <= n < p4_first]
    fs_ = _fit_guarded(sp)
    fb = _fit([(int(r["digits_end"]), _f(r["chunk_build_cpu_s_per_rung"])) for r in ver
               if _f(r.get("chunk_build_cpu_s_per_rung"))])
    fl = _fit([(int(r["digits_end"]), _f(r["lean_bytes_per_rung"])) for r in recs
               if _f(r.get("lean_bytes_per_rung"))] +
              [(422, 7.9e6)])  # WideExt40-44 measurement at switch time
    fo = [(_f(r["olean_bytes_per_rung"]) or 0) / (_f(r["lean_bytes_per_rung"]) or 1) for r in ver
          if _f(r.get("olean_bytes_per_rung"))]
    olean_ratio = sum(fo) / len(fo) if fo else 0.57  # WideExt39: 65 MB olean / ~114 MB .lean
    gbmb = st["est_gb_per_mb"]
    d0 = len(str(Y))

    def fmt(f, unit):
        if not f:
            return "insufficient data"
        if f[1] == 0.0:
            return (f"{f[0]:.3g} {unit}, flat (median of n={f[2]}; the digit range covered so far is "
                    "too narrow to fit a slope)")
        return f"{f[0]:.3g} · d^{f[1]:.2f} {unit} (n={f[2]})"

    out += [f"- search s/rung ≈ {fmt(fs_, 's')} (per-rung points, {cfg})",
            f"- chunk-build CPU s/rung ≈ {fmt(fb, 's')} (per verified batch; lake per-module times / rows)",
            f"- Lean bytes/rung ≈ {fmt(fl, 'B')}; olean ≈ {olean_ratio:.2f}× Lean bytes",
            f"- build memory model: {BASE_GB_PER_PROC:.0f} GB + {gbmb:.3f} GB per MB of chunk source "
            "(from latest batch peak)", ""]
    if fs_ and fb and len(ver) >= 3:
        dt_lim = d_mem = d_disk = None
        free = shutil.disk_usage(LEAN_DIR).free
        used = 0.0
        d = float(d0)
        while d < 200000 and (dt_lim is None or d_mem is None or d_disk is None):
            s_cost = fs_[0] * d ** fs_[1] + fb[0] * d ** fb[1]
            if dt_lim is None and s_cost > 3600:
                dt_lim = d
            bpr = fl[0] * d ** fl[1] if fl else 7.9e6 * (d / 422) ** 2
            if d_mem is None and BASE_GB_PER_PROC + gbmb * bpr / 2 ** 20 > 110:
                d_mem = d
            used += bpr * (1 + olean_ratio) / 0.398 * 1.0  # ~0.398 digits per rung
            if d_disk is None and used > free * 0.9:
                d_disk = d
            d += 1.0
        out += [f"- Projection from {d0} digits (extrapolation — treat as order-of-magnitude):",
                f"  - one rung costs > 1 h (search + single-process chunk build): ~{dt_lim and int(dt_lim)} digits",
                f"  - a ONE-rung chunk needs > 110 GB RAM to build: ~{d_mem and int(d_mem)} digits",
                f"  - disk (Lean + olean, from now) fills 90% of free space: ~{d_disk and int(d_disk)} digits",
                "  - whichever comes first is the practical 'limit rung'. Memory/chunk-size limits are partly "
                "fixable (1 rung/chunk, a leaner certificate encoding); the per-rung time limit is the real "
                "wall for this certificate scheme.", ""]
    else:
        out += [f"- Not enough verified batches for a projection yet (have {len(ver)}, need 3).", ""]

    fw = _fit([(int(r["digits_end"]), _f(r["build_wall_s_per_rung"])) for r in ver
               if _f(r.get("build_wall_s_per_rung"))])
    if fs_ and fw:
        dpr = []
        for a_, b_ in zip(ver, ver[1:]):
            dd, nn = int(b_["digits_end"]) - int(a_["digits_end"]), int(b_["rows"])
            if nn:
                dpr.append(dd / nn)
        per_rung_digits = sum(dpr[-3:]) / len(dpr[-3:]) if dpr else 0.37
        for label, cost in (("overlapped (v4)", lambda d: max(fs_[0] * d ** fs_[1], fw[0] * d ** fw[1])),
                            ("sequential (v3)", lambda d: fs_[0] * d ** fs_[1] + fw[0] * d ** fw[1])):
            d, secs, n = float(d0), 0.0, 0
            while d < 1000 and n < 500000:
                secs += cost(d)
                d += per_rung_digits
                n += 1
            out += [f"- ETA from {d0} to 1000 digits, {label}: ~{n} more rungs, "
                    f"~{secs / 3600:.0f} h ({secs / 86400:.1f} days) at {per_rung_digits:.3f} digits/rung"]
        out += ["  (fits are extrapolations from measured batches; the v4 search fit needs a few p4 "
                "batches before the overlapped number means much)", ""]

    issues = []
    try:
        for ln in open(STATUS_LOG, errors="replace"):
            if any(k in ln for k in ("SKIPPED", "CORRECTNESS", "attempt 1 failed", "watchdog", "WARNING",
                                     "EXCEPTION", "exited", "STOP", "LIMIT")):
                issues.append(ln.rstrip())
    except FileNotFoundError:
        pass
    out += ["## Issues / restarts during the run", ""] + (["```"] + issues[-40:] + ["```"] if issues else ["- none"])
    out += ["", "## Where things are (GB10)", "",
            "- Orchestrator: `~/p287work/phase4_orchestrator.py` (pid in `~/p287work/phase3.pid`), search "
            "module `~/p287work/fastsearch2.py`, filter check `~/p287work/validate_gmpy2.py`",
            "- Watchdog: `~/p287work/phase3_watchdog.sh` via user crontab (*/10 and @reboot)",
            "- Logs: `phase3_status.log` (milestones), `phase3_detail.log` (every rung / lake call), "
            "`phase3_build_logs/`, `phase3_cost_curve.csv`, `phase3_watchdog.log`",
            "- State: `phase3_state.json`, rungs `rungs_extended.json` (+ `rungs_snapshot_MainN.json`)",
            "- Stop cleanly: `touch ~/p287work/STOP_MANUAL` (takes effect at the next batch boundary)", ""]
    open(SUMMARY + ".tmp", "w").write("\n".join(out) + "\n")
    os.replace(SUMMARY + ".tmp", SUMMARY)


# ------------------------------------------------------------------ builder
class Builder:
    """The single build slot. One build at a time, in a background thread."""

    def __init__(self):
        self.thread = None
        self.result = None
        self.tag = ""
        self.t0 = 0.0

    def busy(self):
        return self.thread is not None and self.thread.is_alive()

    def failed_correctness(self):
        return self.result == "correctness" or os.path.exists(STOP_CORRECTNESS)

    def start(self, st, rows, reason):
        assert not self.busy(), "refusing to start a second build"
        snap, N = list(rows), st["version"] + 1
        self.result, self.t0 = None, time.time()
        self.tag = f"Main{N} ({len(snap) - st['exported_rows']} rows)"

        def run():
            try:
                self.result = build_batch(st, snap, reason)
            except BaseException as e:  # noqa: BLE001
                self.result = "resource"
                try:
                    unwire(N)
                except Exception:  # noqa: BLE001
                    pass
                status(f"build thread for Main{N} crashed ({e!r}); un-wired, rows stay pending")
                detail(traceback.format_exc())

        self.thread = threading.Thread(target=run, name="builder")
        self.thread.start()

    def join(self, why=""):
        if self.thread is None:
            return self.result
        if self.thread.is_alive():
            set_phase(f"waiting for the build of {self.tag} to finish {why}")
            status(f"search is ahead of the build: waiting for {self.tag} "
                   f"({time.time() - self.t0:.0f}s so far) {why}")
        self.thread.join()
        self.thread = None
        return self.result


def wait_for_memory():
    """Never start a build while memory is already high."""
    t0 = time.time()
    warned = False
    while MemSampler.used() > MEM_START_LIMIT_GB and time.time() - t0 < MEM_WAIT_S:
        if not warned:
            status(f"memory at {MemSampler.used():.0f} GB (> {MEM_START_LIMIT_GB:.0f}); "
                   "delaying the start of the build")
            warned = True
        time.sleep(30)
    if warned:
        status(f"memory now {MemSampler.used():.0f} GB after {time.time() - t0:.0f}s; starting the build")


# ------------------------------------------------------------------- main
def main():
    lockf = open(LOCK_PATH, "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("another orchestrator holds the lock; exiting", flush=True)
        return 0
    if os.path.exists(STOP_CORRECTNESS):
        print("STOP_CORRECTNESS present; refusing to start", flush=True)
        return 0
    open(PID_PATH, "w").write(str(os.getpid()))
    if not os.environ.get("P3_NO_PKILL"):
        # a previous orchestrator killed mid-build leaves lake/lean orphans (own session) -- clear them
        subprocess.run(["pkill", "-KILL", "-f", "lake build"], check=False)
        subprocess.run(["pkill", "-KILL", "-f", "bin/lean .*P287/"], check=False)
    rows = load_rows()
    st = load_state(rows)
    save_state(st)
    unwire(st["version"] + 1)   # never leave unverified MainN imports wired after a crash
    global LIVE_ROWS
    LIVE_ROWS = rows
    status(f"orchestrator v4 started pid={os.getpid()}: verified Main{st['version']} "
           f"(M <= {sci(st['frontier_Y'])}, {st['total_rungs']} rungs); searched rungs {339 + len(rows)}; "
           f"pending {len(rows) - st['exported_rows']}; i={I_RANGE} budgets={BUDGET_STAGES} B={SIEVE_B}; "
           f"gmpy2={fs.HAVE_GMPY2} workers={SEARCH_WORKERS} ({SEARCH_WORKERS_BUILDING} during a build) "
           f"batch>={BATCH_SIZE} rows (cap {MAX_PENDING_ROWS}) overlap={OVERLAP}")
    threading.Thread(target=heartbeat_loop, daemon=True).start()
    write_summary(st, rows)

    builder = Builder()
    with mp.Pool(SEARCH_WORKERS, initializer=_worker_init) as pool:
        if len(rows) - st["exported_rows"] >= MIN_BUILD_ROWS_AT_START:
            wait_for_memory()
            if OVERLAP:
                builder.start(st, rows, "pending rows at startup")
            elif build_batch(st, list(rows), "pending rows at startup") == "correctness":
                return 3
        loops = 0
        while True:
            if os.path.exists(STOP_MANUAL):
                builder.join("(STOP_MANUAL)")
                status("STOP_MANUAL present: exiting cleanly at batch boundary")
                write_summary(st, rows)
                return 0
            set_phase(f"searching from rung {339 + len(rows) + 1}")
            outcome = search_one_batch(pool, rows, st, builder)
            if outcome == "BUILD_STOP":
                builder.join("(correctness stop)")
                return 3
            if outcome == "EXCEPTION":
                builder.join("(search failed -- not abandoning a running build)")
                if builder.result == "correctness":
                    return 3
                status("search EXCEPTION (see phase3_detail.log); exiting so the watchdog restarts from state")
                return 1
            if builder.join("(batch boundary)") == "correctness":
                return 3
            if outcome == "GENUINE_STOP":
                r = build_batch(st, list(rows), "search exhausted")
                if r == "correctness":
                    return 3
                open(STOP_EXHAUSTED, "w").write(f"{ts()} UTC: no rung found past U={rows[-1][0]}\n")
                status("STOPPED: full-window search found no further rung; STOP_EXHAUSTED written")
                write_summary(st, rows)
                return 0
            if os.path.exists(STOP_MANUAL):
                continue
            if len(rows) - st["exported_rows"] > 0:
                wait_for_memory()
                if OVERLAP:
                    builder.start(st, rows, "search batch complete (build overlapped with next search)")
                elif build_batch(st, list(rows), "search batch complete") == "correctness":
                    return 3
            loops += 1
            if MAX_LOOPS and loops >= MAX_LOOPS:
                builder.join("(max loops reached)")
                return 0


if __name__ == "__main__":
    sys.exit(main())
