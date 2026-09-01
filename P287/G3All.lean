/- **Gaps ≤ 3 are impossible for every largest term `M ∈ [84, 42 359 617]`.**

Three ranges, now contiguous:

    StepG3C.g3_mid      M ∈ [ 84,       374]   three rungs, at 81, 157, 249
    StepG3B.g3_low      M ∈ [340,       451]   the rung at {337, 338, 339}
    LadderG3.g3_gap     M ∈ [386, 42359617]    the 16-rung ladder

`M ≤ 85` is settled separately and exhaustively, in exact integer arithmetic:
`lcm(1..85) = 8.076·10³⁶` fits in a 128-bit integer, so 1 is represented as that
lcm and every partial sum is exact (`attempts/019-m85/byM.c`). The unique
representation there is `{2, 3, 6}`. The two arguments overlap at 84 and 85.

So: **`{2,3,6}` is the only Egyptian representation of 1 with all consecutive gaps
≤ 3 and largest term at most 42 359 617**, with everything from 84 upward
kernel-checked.

Closing the eighteen values `M ∈ [365, 382]` needed `RuleBGen.ruleB_sharp` — rule B
at general `t` — because on the older rules there is no forced-out triple anywhere
in `[2, M]` for those `M`. Reaching down to 84 needed `StepG3C.notTermA_sharp`,
Lemma A′ with `t·lcm(1..t) < p` rather than `t·t! < p`.
-/
import P287.StepG3C
import P287.LadderG3

namespace G3All

/-- **No gaps-≤3 representation of 1 has largest term in `[84, 42 359 617]`.** -/
theorem g3_all {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 84 ≤ s ⟨k - 1, by omega⟩)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 42359617) :
    4 ≤ PCI.max_gap k s := by
  rcases Nat.lt_or_ge (s ⟨k - 1, by omega⟩) 375 with h | h
  · exact StepG3C.g3_mid hk s hmono h1 hsum hlo (by omega)
  rcases Nat.lt_or_ge (s ⟨k - 1, by omega⟩) 386 with h2 | h2
  · exact StepG3B.g3_low hk s hmono h1 hsum (by omega) (by omega)
  · exact LadderG3.g3_gap hk s hmono h1 hsum h2 hhi

#print axioms g3_all

end G3All
