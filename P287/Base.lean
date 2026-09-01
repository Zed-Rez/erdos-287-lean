/- The base case M ≤ 8, with no exhaustive search.

`StepAB.max_prime_pow` says the largest term is never a prime power, which
disposes of M = 4, 5, 7, 8 outright — including the two values {4, 8} for which no
pair of consecutive interior exclusions exists. M ≥ 4 because 2·n₁ ≤ M and n₁ ≥ 2.
Only M = 6 needs a rung, and it gets the cheapest one there is: 4 = 2² is excluded
by rule B and 5 is excluded by rule A at t = 1.
-/
import P287.StepAB
import Mathlib.Tactic.NormNum.Prime

namespace Base

theorem base_gap {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 8) :
    3 ≤ PCI.max_gap k s := by
  have h2 := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
  by_cases c4 : s ⟨k - 1, by omega⟩ = 4
  · exact (StepAB.max_prime_pow (q := 2) (e := 2) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c4])).elim
  by_cases c5 : s ⟨k - 1, by omega⟩ = 5
  · exact (StepAB.max_prime_pow (q := 5) (e := 1) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c5])).elim
  by_cases c7 : s ⟨k - 1, by omega⟩ = 7
  · exact (StepAB.max_prime_pow (q := 7) (e := 1) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c7])).elim
  by_cases c8 : s ⟨k - 1, by omega⟩ = 8
  · exact (StepAB.max_prime_pow (q := 2) (e := 3) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c8])).elim
  -- only M = 6 survives; 4 and 5 are consecutive exclusions, both interior
  refine StepAB.gap_of_excl (n := 4) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
  · exact StepAB.notTermB (q := 2) (e := 2) (n := 4) (by norm_num) (by norm_num)
      (by norm_num) hk s hmono h1 hsum (by omega)
  · exact StepAB.notTermA (p := 5) (t := 1) (n := 5) (a := 1) (by norm_num)
      (by norm_num) (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum
      (by omega)

#print axioms base_gap

end Base
