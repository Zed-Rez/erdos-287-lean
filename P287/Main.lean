/- Erdős #287, kernel-verified for every largest term below 3.8·10⁸.

    base_gap    M ≤ 8            StepAB.max_prime_pow, one rung
    low_gap     9 ≤ M ≤ 38       4 rungs, rules A and B
    ladder_gap  39 ≤ M ≤ 3.8e8   24 rungs, rule A only

No exhaustive search anywhere, and nothing rests on Python.
-/
import P287.Base
import P287.LowLadder
import P287.Ladder

namespace Main

/-- **Erdős #287 holds for every representation whose largest term is at most
382 613 443.** -/
theorem erdos287_below {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 382613443) :
    3 ≤ PCI.max_gap k s := by
  by_cases c1 : s ⟨k - 1, by omega⟩ ≤ 8
  · exact Base.base_gap hk s hmono h1 hsum c1
  push_neg at c1
  by_cases c2 : s ⟨k - 1, by omega⟩ ≤ 38
  · exact LowLadder.low_gap hk s hmono h1 hsum (by omega) c2
  push_neg at c2
  exact Ladder.ladder_gap hk s hmono h1 hsum (by omega) hhi

#print axioms erdos287_below

end Main
