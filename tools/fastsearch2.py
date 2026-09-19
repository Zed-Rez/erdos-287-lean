"""Phase 4 rung search: same sieve + same acceptance test as fastsearch.py, but

  * primality is routed through gmpy2 (GMP 6.3.0) when it imports, falling back
    to the pure-Python pock.is_prime_mr otherwise.  gmpy2.is_prime(n, 25) runs
    25 Miller-Rabin rounds after trial division; measured 19x faster than the
    pure-Python path at 600 and 1000 digits, identical answers on the whole
    accepted ladder (see validate_gmpy2.py).  pock.py itself is NOT touched:
    the certificate path (gen_cert*/Lean) still uses the original code, and the
    Lean kernel is what certifies a rung -- this filter only decides which
    candidates are worth emitting.
  * scan() takes an explicit block range [b_first, b_last) so the driver can
    spread one branch's window over many workers.  Block k is the same set of
    candidates the sequential loop would visit on its k-th iteration, so
    "largest h in blocks [0,budget)" is unchanged: each worker returns the
    largest h in its range and the driver takes the first (= largest) hit.
"""
import os
import sys

sys.path.insert(0, "/home/zedgb10/attempts/013-certladder")
from gen_cert import PMAXH  # noqa: E402,F401  (re-exported for the orchestrator)
from gen_cert2 import cover  # noqa: E402,F401
from pock import is_prime_mr as _py_is_prime  # noqa: E402

try:
    from gmpy2 import is_prime as _gmp_is_prime, mpz
    HAVE_GMPY2 = True
except Exception:  # noqa: BLE001
    HAVE_GMPY2 = False

MR_ROUNDS = 25


def _isp(n):
    """Primality filter: gmpy2 when available, else the original pure-Python MR."""
    if HAVE_GMPY2:
        return bool(_gmp_is_prime(mpz(n), MR_ROUNDS))
    return _py_is_prime(n)


B = int(os.environ.get("P4_SIEVE_B", "100000"))
BLOCK = 120000


def _small_primes(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        i += 1
    return [i for i in range(3, n + 1) if sieve[i]]      # odd primes only


SMALL = _small_primes(B)


def set_B(b):
    global B, SMALL
    B, SMALL = b, _small_primes(b)


def scan(hlo, hhi, a, c, side, block=BLOCK, budget=60, b_first=0, b_last=None):
    """Largest h in block range [b_first, b_last) of the window [hlo,hhi] with
    h, p = h*2^a+1 and q = c*p+1 all prime.

    Returns (h, exhausted): h is None if no hit; exhausted is True when the
    range ran past the bottom of the window, so later blocks are empty too.
    Block k covers (top0 - 2*block*k) downwards, exactly as the sequential
    loop in fastsearch.scan does.
    """
    P2 = pow(2, a)
    top0 = hhi if hhi % 2 else hhi - 1
    b_last = budget if b_last is None else min(b_last, budget)
    for k in range(b_first, b_last):
        top = top0 - 2 * block * k
        if top < hlo:
            return None, True
        bot = max(hlo, top - 2 * (block - 1))
        if bot % 2 == 0:
            bot += 1
        n = (top - bot) // 2 + 1
        if n <= 0:
            return None, True
        alive = bytearray([1]) * n
        for r in SMALL:
            inv2 = (r + 1) // 2                      # inverse of 2 mod r
            ip = pow(P2 % r, -1, r) if P2 % r else None
            targets = [0]
            if ip is not None:
                targets.append((-ip) % r)
                icp = pow((c * P2) % r, -1, r) if (c * P2) % r else None
                if icp is not None:
                    targets.append((-(c + 1) * icp) % r)
            for x in targets:
                j = ((x - bot) % r) * inv2 % r
                alive[j::r] = bytearray(len(alive[j::r]))
        for j in range(n - 1, -1, -1):
            if not alive[j]:
                continue
            h = bot + 2 * j
            if not _isp(h):
                continue
            p = h * P2 + 1
            if p <= side or not _isp(p):
                continue
            if _isp(c * p + 1):
                return h, False
        if bot == hlo:
            return None, True
    return None, False
