/- Three gaps-≤3 rungs covering `M ∈ [84, 374]`.

Together with `StepG3B.g3_low` ([340, 451]) and `LadderG3.g3_gap` ([386, 42 359 617])
this makes the whole range `84 ≤ M ≤ 4.236·10⁷` kernel-verified, and `M ≤ 85` is
settled exhaustively in exact integer arithmetic (`attempts/019-m85/byM.c`), so the
two meet with 84 and 85 in the overlap.

The rungs need `t = 4`, and `StepAB.notTermA` states Lemma A′ in the FACTORIAL form
`t·t! < p`. That is too weak here: `4·4! = 96` exceeds `p = 83`, while the truth
`4·lcm(1..4) = 48` does not. `lcmUpto t` and `t!` agree up to `t = 3` and first
differ at `t = 4` (12 vs 24), which is exactly where these rungs live — so the first
thing below is `notTermA_sharp`, `notTermA` with `LemAGen.lemA_sharp` in place of
`lemA_gen`. The proof is otherwise unchanged.

    n =  81:  81 = 3⁴ (rule B, narrow) | 82 = 2·41, t=3 | 83 prime, t=4   → M ∈ [84,161]
    n = 157: 157 prime, t=4 | 158 = 2·79, t=4 | 159 = 3·53, t=4           → M ∈ [160,264]
    n = 249: 249 = 3·83, t=4 | 250 = 2·5³ (rule B, general) | 251 prime   → M ∈ [252,374]
-/
import P287.StepG3B
import Mathlib.Tactic.NormNum.Prime

namespace StepG3C

/-- **Lemma A′ in sequence form, sharp.** `notTermA` with `t·lcm(1..t) < p`
instead of `t·t! < p`. -/
theorem notTermA_sharp {p t n : ℕ} (hp : Nat.Prime p) (ht : 1 ≤ t)
    (hpf : t * LemAGen.lcmUpto t < p) {a : ℕ} (hna : n = a * p)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < (t + 1) * p) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := StepAB.setup hk s hmono h1 hsum
  have hno : ¬ ∃ x ∈ Finset.image s Finset.univ, p ∣ x := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    intro hex
    refine LemAGen.lemA_sharp (p := p) (t := t) ht hpf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ t := by
      by_contra hc
      push_neg at hc
      have hmul : p * (t + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
      have e1 : p * (t + 1) = (t + 1) * p := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  intro i hi
  refine hno ⟨n, ?_, ⟨a, by rw [hna]; ring⟩⟩
  rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)

theorem lcm3 : LemAGen.lcmUpto 3 = 6 := by
  first | rfl | decide | (norm_num [LemAGen.lcmUpto, Nat.lcm])
theorem lcm4 : LemAGen.lcmUpto 4 = 12 := by
  first | rfl | decide | (norm_num [LemAGen.lcmUpto, Nat.lcm])

variable {k : ℕ}

/-- Rung at 81: `M ∈ [84, 161]`. -/
theorem rung81 (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 84 ≤ s ⟨k - 1, by omega⟩) (hhi : s ⟨k - 1, by omega⟩ ≤ 161) :
    4 ≤ PCI.max_gap k s := by
  have e0 := StepAB.notTermB (q := 3) (e := 4) (n := 81) (by norm_num) (by norm_num)
    (by norm_num) hk s hmono h1 hsum (by omega)
  have e1 := notTermA_sharp (p := 41) (t := 3) (n := 82) (a := 2)
    (by norm_num) (by norm_num) (by rw [lcm3]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have e2 := notTermA_sharp (p := 83) (t := 4) (n := 83) (a := 1)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have hs0 : s ⟨0, by omega⟩ ≤ 81 := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

/-- Rung at 157: `M ∈ [160, 264]`. -/
theorem rung157 (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 160 ≤ s ⟨k - 1, by omega⟩) (hhi : s ⟨k - 1, by omega⟩ ≤ 264) :
    4 ≤ PCI.max_gap k s := by
  have e0 := notTermA_sharp (p := 157) (t := 4) (n := 157) (a := 1)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have e1 := notTermA_sharp (p := 79) (t := 4) (n := 158) (a := 2)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have e2 := notTermA_sharp (p := 53) (t := 4) (n := 159) (a := 3)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have hs0 : s ⟨0, by omega⟩ ≤ 157 := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

/-- Rung at 249: `M ∈ [252, 374]`. The middle needs general rule B (`250 = 2·5³`). -/
theorem rung249 (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 252 ≤ s ⟨k - 1, by omega⟩) (hhi : s ⟨k - 1, by omega⟩ ≤ 374) :
    4 ≤ PCI.max_gap k s := by
  have hl2 : LemAGen.lcmUpto 2 = 2 := by
    first | rfl | decide | (norm_num [LemAGen.lcmUpto, Nat.lcm])
  have e0 := notTermA_sharp (p := 83) (t := 4) (n := 249) (a := 3)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have e1 := StepG3B.notTermBGen (q := 5) (e := 3) (t := 2) (a := 2) (n := 250)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hl2]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) hk s hmono h1 hsum (by norm_num; omega) (by norm_num; omega)
  have e2 := notTermA_sharp (p := 251) (t := 4) (n := 251) (a := 1)
    (by norm_num) (by norm_num) (by rw [lcm4]; norm_num) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have hs0 : s ⟨0, by omega⟩ ≤ 249 := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

/-- **`M ∈ [84, 374]`**: the three rungs chained. -/
theorem g3_mid (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 84 ≤ s ⟨k - 1, by omega⟩) (hhi : s ⟨k - 1, by omega⟩ ≤ 374) :
    4 ≤ PCI.max_gap k s := by
  rcases Nat.lt_or_ge (s ⟨k - 1, by omega⟩) 160 with h | h
  · exact rung81 hk s hmono h1 hsum hlo (by omega)
  rcases Nat.lt_or_ge (s ⟨k - 1, by omega⟩) 252 with h2 | h2
  · exact rung157 hk s hmono h1 hsum (by omega) (by omega)
  · exact rung249 hk s hmono h1 hsum (by omega) hhi

#print axioms notTermA_sharp
#print axioms g3_mid

end StepG3C
