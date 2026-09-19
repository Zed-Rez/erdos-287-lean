"""Sieved rung search — the grind's bottleneck was h-by-h trial division.

`find_rung2` tested each candidate h with a full trial-division primality check
(~1200 divisions for h ~ 2^27) before it ever reached the cheap big-integer work.
At M ~ 1e80 that cost 16 s per rung, dominating everything.

Here a block of odd h is sieved by every prime r <= B against THREE conditions at
once, each a single arithmetic progression in h:

    r | h                         h ≡ 0                    (mod r)
    r | p = h·2^a + 1             h ≡ -inv(2^a)            (mod r)
    r | q = c·p + 1               h ≡ -(c+1)·inv(c·2^a)    (mod r)

Only survivors — about (0.56/ln B)^3 of the block — reach Miller–Rabin. The final
acceptance test is still the same full `is_prime_mr` on h, p and q, so the sieve
can only ever discard candidates that are provably composite; and the emitted
certificates are kernel-checked regardless.
"""
import sys
from math import factorial

sys.path.insert(0, "/home/zedgb10/attempts/013-certladder")
sys.path.insert(0, "/home/zedgb10/attempts/013-certladder")
from gen_cert import PMAXH  # noqa: E402
from gen_cert2 import cover  # noqa: E402
from pock import is_prime_mr  # noqa: E402

B = 30000


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


def scan(hlo, hhi, a, c, side, block=120000, budget=60):
    """Largest h in [hlo,hhi] with h, p = h·2^a+1 and q = c·p+1 all prime."""
    P2 = pow(2, a)
    top = hhi if hhi % 2 else hhi - 1
    blocks = 0
    while top >= hlo and blocks < budget:
        blocks += 1
        bot = max(hlo, top - 2 * (block - 1))
        if bot % 2 == 0:
            bot += 1
        n = (top - bot) // 2 + 1
        if n <= 0:
            break
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
            if not is_prime_mr(h):
                continue
            p = h * P2 + 1
            if p <= side or not is_prime_mr(p):
                continue
            if is_prime_mr(c * p + 1):
                return h
        top = bot - 2
    return None


def find_rung_fast(F):
    best = None
    for i in (1, 2, 3):
        c, tp = 2 ** i, 3 * 2 ** i
        side = tp * factorial(tp)
        nmax, nmin = F - 2, -(-(2 * F + 20) // 5)
        pmax, pmin = nmax // c, -(-nmin // c)
        pmin = max(pmin, side + 1)
        if pmin > pmax:
            continue
        a = max(2, pmax.bit_length() - 27)
        hlo, hhi = (pmin - 1) // 2 ** a + 1, (pmax - 1) // 2 ** a
        if hhi < 3 or hhi > PMAXH:
            continue
        h = scan(hlo, hhi, a, c, side)
        if h is None:
            continue
        p = h * 2 ** a + 1
        U = cover(c, p)
        if U >= F and (best is None or U > best[0]):
            best = (U, c, i, h, a, p, c * p + 1, tp)
    return best
