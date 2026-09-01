/- One rung of a gaps-≤3 ladder: three consecutive forced-out integers.

The #287 rung needs two consecutive exclusions because gaps ≤ 2 leaves the
complement with no two consecutive. Gaps ≤ 3 lets the complement hold two, so the
rung needs THREE. Nothing else changes: Lemma A′ (`StepAB.notTermA`) and the
interiority bound (`Lower.lower`, which needs only strict monotonicity) are both
independent of the gap bound.

Measured beforehand (`verified/058`): only 205 values of M in [4, 60000] admit no
such triple, the largest being 385.
-/
import P287.Part1G3
import P287.StepAB
import P287.Lower

namespace StepG3

theorem step_gap4 {p q r n a b c tp tq tr : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (htp : 1 ≤ tp) (htq : 1 ≤ tq) (htr : 1 ≤ tr)
    (hpf : tp * Nat.factorial tp < p) (hqf : tq * Nat.factorial tq < q)
    (hrf : tr * Nat.factorial tr < r)
    (hna : n = a * p) (hnb : n + 1 = b * q) (hnc : n + 2 = c * r)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 3 ≤ s ⟨k - 1, by omega⟩)
    (hhip : s ⟨k - 1, by omega⟩ < (tp + 1) * p)
    (hhiq : s ⟨k - 1, by omega⟩ < (tq + 1) * q)
    (hhir : s ⟨k - 1, by omega⟩ < (tr + 1) * r)
    (hint : 2 * s ⟨k - 1, by omega⟩ + 20 ≤ 5 * n) :
    4 ≤ PCI.max_gap k s := by
  have e0 := StepAB.notTermA hp htp hpf hna hk s hmono h1 hsum hhip
  have e1 := StepAB.notTermA hq htq hqf hnb hk s hmono h1 hsum hhiq
  have e2 := StepAB.notTermA hr htr hrf hnc hk s hmono h1 hsum hhir
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

#print axioms step_gap4

end StepG3
