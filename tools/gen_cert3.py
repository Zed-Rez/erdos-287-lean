"""Cheaper Lucas certificates: exponentiate by 2^a FIRST, then by h.

For p = h·2^a + 1 the two Lucas conditions sit at exponents (p−1)/2 = h·2^(a−1)
and (p−1)/h = 2^a. The old emitter ran square-and-multiply on the exponent
h·2^a — bit string bits(h)‖0^a — which hands (p−1)/2 over for free as the
penultimate step, but says nothing about 2^a, so 2^a needed a second full trace of
its own: 2a + 28 steps in all.

Reverse the association. Trace the pure squarings g^(2^j), j = 0..a, ONCE (a
steps). Its last two entries are exactly g^(2^a) = g^((p−1)/h) and g^(2^(a−1)).
Then a single lemma

    pow_mul_step : b^e % n = v → v^f % n = w → b^(e*f) % n = w

lifts each of those to exponent ·h with a short trace of only bits(h) ≈ 27 steps,
giving g^(p−1) and g^((p−1)/2). Total a + 54 rather than 2a + 28 — a 30% cut in
the whole rung at the scales the ladder is heading for.

q = 2^i·p + 1 is left alone: its two conditions are q−1 and (q−1)/2, which ARE
prefix-related, and (q−1)/p = 2^i is three lines. That side is already optimal.
"""
import sys

sys.path.insert(0, "/home/zedgb10/attempts/013-certladder")
from gen_cert import trace, witness, BOILER  # noqa: E402

EXTRA = [
    "theorem pow_mul_step (b e f n v w : ℕ) (h1 : b ^ e % n = v) (h2 : v ^ f % n = w) :",
    "    b ^ (e * f) % n = w := by",
    "  rw [pow_mul, Nat.pow_mod, h1, h2]", ""]


def _split(a, cap=250):
    """Write the exponent a as a sum of pieces of size <= cap.

    `norm_num` refuses to evaluate a power whose exponent exceeds 256 (the same
    threshold that makes `decide` bail out). Writing 2^a as 2^(a1+a2+...) and
    rewriting with `pow_add` first leaves it only powers it will evaluate, and
    `Nat.Prime.dvd_of_dvd_pow` still applies to the un-evaluated 2^(a1+a2+...)
    because that step is symbolic in the exponent.
    """
    parts, rest = [], a
    while rest > cap:
        parts.append(cap)
        rest -= cap
    parts.append(rest)
    return " + ".join(str(x) for x in parts)


def cert3(j, r, L):
    """Lucas certificates for p and q, with the base-changed p side."""
    _U, c, i, h, a, p, q, _tp = r
    gp, gq = witness(p, [2, h]), witness(q, [2, p])
    P = f"r{j}"
    # --- p: one squaring trace, then two short base-changed runs ---
    sN, sV = trace(f"{P}s", gp, 2 ** a, p, L); L.append("")
    assert sN == a + 1
    B, Bh = sV[a + 1], sV[a]                       # g^(2^a), g^(2^(a-1))
    assert B == pow(gp, 2 ** a, p) and Bh == pow(gp, 2 ** (a - 1), p)
    tN, tV = trace(f"{P}t", B, h, p, L); L.append("")
    uN, uV = trace(f"{P}u", Bh, h, p, L); L.append("")
    assert tV[tN] == 1, "witness fails Fermat"
    half = uV[uN]
    assert half == pow(gp, (p - 1) // 2, p) != 1
    assert B != 1                                   # the (p-1)/h condition
    L += [f"theorem {P}pfull : ({gp}:ℕ) ^ {p-1} % {p} = 1 := by",
          f"  have e : ({p-1}:ℕ) = {2**a} * {h} := by norm_num",
          f"  rw [e]",
          f"  exact pow_mul_step {gp} {2**a} {h} {p} {B} 1 {P}s{a+1} {P}t{tN}", "",
          f"theorem {P}phalf : ({gp}:ℕ) ^ {(p-1)//2} % {p} = {half} := by",
          f"  have e : ({(p-1)//2}:ℕ) = {2**(a-1)} * {h} := by norm_num",
          f"  rw [e]",
          f"  exact pow_mul_step {gp} {2**(a-1)} {h} {p} {Bh} {half} {P}s{a} {P}u{uN}", "",
          f"theorem {P}pdiv (d : ℕ) (hd : d.Prime) (hv : d ∣ {p} - 1) : d = 2 ∨ d = {h} := by",
          f"  have hN : ({p}:ℕ) - 1 = {h} * 2^({_split(a)}) := by (try simp only [pow_add]); norm_num",
          "  rw [hN] at hv",
          "  rcases (Nat.Prime.dvd_mul hd).mp hv with hx | hx",
          "  · right; exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp hx",
          "  · left",
          "    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow hx)", "",
          f"theorem {P}p : Nat.Prime {p} := by",
          f"  refine lucas_primality {p} ((({gp}:ℕ) : ZMod {p})) ?_ ?_",
          f"  · have e : ({p}:ℕ) - 1 = {p-1} := by norm_num",
          f"    rw [e]; exact cast_one {P}pfull",
          "  · intro d hd hv",
          f"    rcases {P}pdiv d hd hv with rfl | rfl",
          f"    · have e : (({p}:ℕ) - 1) / 2 = {(p-1)//2} := by norm_num",
          f"      rw [e]; exact cast_ne_one {P}phalf (by norm_num) (by norm_num) (by norm_num)",
          f"    · have e : (({p}:ℕ) - 1) / {h} = {2**a} := by norm_num",
          f"      rw [e]; exact cast_ne_one {P}s{a+1} (by norm_num) (by norm_num) (by norm_num)", ""]
    # --- q: unchanged, the prefix trick is already optimal here ---
    qN, qV = trace(f"{P}qA", gq, q - 1, q, L); L.append("")
    bN, bV = trace(f"{P}qB", gq, 2 ** i, q, L); L.append("")
    assert qV[qN] == 1 and qV[qN - 1] == pow(gq, (q - 1) // 2, q) != 1
    assert bV[bN] == pow(gq, (q - 1) // p, q) != 1
    L += [f"theorem {P}qdiv (d : ℕ) (hd : d.Prime) (hv : d ∣ {q} - 1) : d = 2 ∨ d = {p} := by",
          f"  have hN : ({q}:ℕ) - 1 = {p} * 2^{i} := by norm_num",
          "  rw [hN] at hv",
          "  rcases (Nat.Prime.dvd_mul hd).mp hv with hx | hx",
          f"  · right; exact (Nat.prime_dvd_prime_iff_eq hd {P}p).mp hx",
          "  · left",
          "    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow hx)", "",
          f"theorem {P}q : Nat.Prime {q} := by",
          f"  refine lucas_primality {q} ((({gq}:ℕ) : ZMod {q})) ?_ ?_",
          f"  · have e : ({q}:ℕ) - 1 = {q-1} := by norm_num",
          f"    rw [e]; exact cast_one {P}qA{qN}",
          "  · intro d hd hv",
          f"    rcases {P}qdiv d hd hv with rfl | rfl",
          f"    · have e : (({q}:ℕ) - 1) / 2 = {(q-1)//2} := by norm_num",
          f"      rw [e]; exact cast_ne_one {P}qA{qN-1} (by norm_num) (by norm_num) (by norm_num)",
          f"    · have e : (({q}:ℕ) - 1) / {p} = {2**i} := by norm_num",
          f"      rw [e]; exact cast_ne_one {P}qB{bN} (by norm_num) (by norm_num) (by norm_num)", ""]


def emit3(rungs, ns, path, start):
    hi = rungs[-1][0]
    L = ["/- Certificate rungs with base-changed p certificates (gen_cert3.py). -/",
         "import P287.StepA2", "import Mathlib.NumberTheory.LucasPrimality",
         "import Mathlib.Tactic.NormNum.Prime", "",
         "set_option maxRecDepth 40000", "", f"namespace {ns}", ""] + BOILER + EXTRA
    for j, r in enumerate(rungs):
        cert3(j, r, L)
    L += [f"/-- **#287 for every M in [{start}, {hi}].** -/",
          "theorem chunk_gap {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)",
          "    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)",
          "    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)",
          f"    (hlo : {start} ≤ s ⟨k - 1, by omega⟩)",
          f"    (hhi : s ⟨k - 1, by omega⟩ ≤ {hi}) :",
          "    3 ≤ PCI.max_gap k s := by"]
    for j, (U, c, i, h, a, p, q, tp) in enumerate(rungs):
        L += [f"  by_cases c{j} : s ⟨k - 1, by omega⟩ ≤ {U}",
              f"  · exact StepA2.step_gap (p := {p}) (q := {q}) (n := {c*p}) (a := {c})"
              f" (b := 1) (tp := {tp}) (tq := 2)",
              f"      r{j}p r{j}q (by norm_num) (by norm_num)",
              "      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])",
              "      (by norm_num) (by norm_num) hk s hmono h1 hsum",
              "      (by omega) (by omega) (by omega) (by omega)",
              f"  push_neg at c{j}"]
    L += ["  omega", "", "#print axioms chunk_gap", "", f"end {ns}"]
    open(path, "w").write("\n".join(L) + "\n")
    return start, hi
