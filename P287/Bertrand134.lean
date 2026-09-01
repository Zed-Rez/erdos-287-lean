/- **The last prose step, formalised: `g₁ ≥ 134` with no supplied prime.**

`RoughChain.g1_ge_of_free_prime` gives `t ≤ g₁ + 1` for a free odd prime with `t` consecutive
multiples inside the window, but the passage to a NUMERAL needed two prose steps: exhibit such a
prime, and count its multiples. Both are elementary, and both are done here.

* **Exhibit.** Bertrand at `M/431` gives a prime `p` with `M/431 < p ≤ 2·(M/431)`. The lower bound
  makes `M < 431·p`, which is exactly the hypothesis of `Rough.no_large_prime_factor`, so `p`
  divides no denominator; `p` is odd because it exceeds `M/431 ≥ 2`.
* **Count.** With `a = n₁/p + 1` and `t = (M−1)/p − n₁/p`, the multiples `a·p, …, (a+t−1)·p` lie
  strictly inside the window (`a+t−1 = (M−1)/p` exactly), and `t ≥ 135` because
  `Lower3.lower3` (`2718·n₁ ≤ 1000·M + 2718`) forces `M − 1 − n₁ ≥ 1718·M/2718 − 2`, while
  `p ≤ 2M/431` makes `135·p ≤ 270·M/431`.

The `135` uses the **guaranteed** window width `W/M ≥ 1 − 1/e = 0.6321` — the `R = e` end of
`[e, e²]`, not the `R = e²` end. Quoting the best case here is the error recorded at LEDGER 522.

Result: **`134 ≤ g₁`** for every hypothetical counterexample with `M ≥ 10^189`, against `PowBlock`'s
`g₁ ≥ 2`. Nothing about the record moves — `g₁` is `O(1)` and `M` is astronomical — but the claim is
now kernel-checked end to end rather than prose.
-/
import P287.RoughChain
import P287.Rough
import P287.Lower3
import Mathlib.NumberTheory.Bertrand

namespace Bertrand134

open Finset

variable {k : ℕ}

/-- **`g₁ ≥ 134`, with the prime produced rather than assumed.** -/
theorem g1_ge_134 (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2)
    (hM : 10 ^ 189 ≤ s ⟨k - 1, by omega⟩) :
    134 ≤ GapOne.g1 k s hk := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hMd
  have hMbig : 10 ^ 189 ≤ M := hM
  have hM355 : 355 ≤ M := le_trans (by norm_num) hMbig
  have hMpos : 0 < M / 431 := by omega
  -- (1) Bertrand at `M / 431`.  `M/431 < p` gives `M < 431·p`, which is exactly what
  -- `Rough.no_large_prime_factor` wants.  omega handles division by the LITERAL 431.
  obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (n := M / 431) (by omega)
  have hppos : 0 < p := hp.pos
  have h431 : M < 431 * p := by omega
  -- (2) `p` divides no denominator, and `p` is odd
  have hfree := Rough.no_large_prime_factor hk s hmono h1 hsum hMbig hp h431
  have hp2 : p % 2 = 1 := by
    have hne : p ≠ 2 := by intro h; rw [h] at hplo; omega
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hne)
  -- (3) `135·p ≤ M − 1 − n₁`: the GUARANTEED window width (`Lower3`, the `R = e` end) against
  -- `p ≤ 2·(M/431)`.  Linear in `p`, `n₁`, `M` and a literal division, so omega closes it.
  have hlow := Lower3.lower3 hk s hmono h1 hsum
  have hn1M : n1 ≤ M := by
    obtain ⟨-, hle, -⟩ := StepAB.setup hk s hmono h1 hsum
    exact hle _ (Finset.mem_image_of_mem s (Finset.mem_univ (⟨0, by omega⟩ : Fin k)))
  have h135 : 135 * p ≤ M - 1 - n1 := by omega
  -- (4) a block of exactly 135 consecutive multiples, starting just above `n₁`
  have hloa : n1 < (n1 / p + 1) * p := by
    have hid := Nat.div_add_mod n1 p
    have hlt := Nat.mod_lt n1 hppos
    calc n1 = p * (n1 / p) + n1 % p := hid.symm
      _ < p * (n1 / p) + p := by omega
      _ = (n1 / p + 1) * p := by ring
  have hhia : (n1 / p + 1 + 135 - 1) * p < M := by
    have hle : n1 / p * p ≤ n1 := Nat.div_mul_le_self n1 p
    have hidx : n1 / p + 1 + 135 - 1 = n1 / p + 135 := by
      generalize n1 / p = q
      omega
    calc (n1 / p + 1 + 135 - 1) * p = n1 / p * p + 135 * p := by
          rw [hidx]; ring
      _ ≤ n1 + 135 * p := by omega
      _ < M := by omega
  -- (5) feed it to the free-prime bound
  have hmain := RoughChain.g1_ge_of_free_prime hk s hmono h1 hsum hg hp2
    (by omega : 0 < 135) hfree hloa hhia
  omega

#print axioms g1_ge_134

end Bertrand134
