/- One rung of the DOWNWARD ladder for Erdős #287 — the "factor 2.5" version.

This is `StepA.step_gap` with the interiority hypothesis sharpened from
`M ≤ 2n+1` (factor 2, licensed by the counting bound `2·n₁ ≤ M`,
`PCI.two_mul_first_le_last`) to `2·M + 20 ≤ 5·n` (factor 2.5, licensed by the
sharper `Lower.lower : 5·n₁ ≤ 2·M + 20`). Combining `Lower.lower` with the new
`hint` gives `5·n₁ ≤ 5·n`, i.e. `n₁ ≤ n`, exactly the fact `StepA.step_gap`
extracted from `hint` and `two_mul_first_le_last` directly. Every other step of
the proof is verbatim `StepA.step_gap`.

RECONSTRUCTION NOTE: this file does not exist anywhere in the currently
recovered workspace or in the public `erdos-287-lean` repo as checked out on
GB10 (only `StepA.lean`, with the weaker `hint`, is present) — it was part of
the ~250MB of Lean sources lost with the Monair machine. It is reconstructed
here from `StepA.lean`'s proof plus the already-proved, already-kernel-checked
`Lower.lower`, both present in this repo; no new mathematics is introduced,
only the substitution described above.
-/
import P287.Part1
import P287.LemAGenMod
import P287.Lower

namespace StepA2

open Finset

theorem step_gap {p q n a b tp tq : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (htp : 1 ≤ tp) (htq : 1 ≤ tq)
    (hpf : tp * Nat.factorial tp < p) (hqf : tq * Nat.factorial tq < q)
    (hna : n = a * p) (hnb : n + 1 = b * q)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 2 ≤ s ⟨k - 1, by omega⟩)
    (hhip : s ⟨k - 1, by omega⟩ < (tp + 1) * p)
    (hhiq : s ⟨k - 1, by omega⟩ < (tq + 1) * q)
    (hint : 2 * s ⟨k - 1, by omega⟩ + 20 ≤ 5 * n) :
    3 ≤ PCI.max_gap k s := by
  classical
  set M := s ⟨k - 1, by omega⟩ with hMdef
  set T : Finset ℕ := Finset.image s Finset.univ with hTdef
  have hsumT : ∑ x ∈ T, ((x : ℚ))⁻¹ = 1 := by
    rw [hTdef, Finset.sum_image (hmono.injective.injOn)]; exact hsum
  have hmono_le : ∀ i : Fin k, s ⟨0, by omega⟩ ≤ s i := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hle_last : ∀ i : Fin k, s i ≤ M := by
    intro i
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with h | h
    · have : i = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTpos : ∀ x ∈ T, 0 < x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hmono_le i; omega
  have hTle : ∀ x ∈ T, x ≤ M := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hle_last i; omega
  -- no term is divisible by p: its multiples in the window are j·p with j ≤ tp
  have hnoP : ¬ ∃ x ∈ T, p ∣ x := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    intro hex
    refine LemAGen.lemA_gen (p := p) (t := tp) htp hpf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ tp := by
      by_contra hc
      push_neg at hc
      have hmul : p * (tp + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
      have e1 : p * (tp + 1) = (tp + 1) * p := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  -- likewise for q
  have hnoQ : ¬ ∃ x ∈ T, q ∣ x := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    intro hex
    refine LemAGen.lemA_gen (p := q) (t := tq) htq hqf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ tq := by
      by_contra hc
      push_neg at hc
      have hmul : q * (tq + 1) ≤ q * j := Nat.mul_le_mul_left _ hc
      have e1 : q * (tq + 1) = (tq + 1) * q := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  have hnnot : ∀ i, s i ≠ n := by
    intro i hi
    refine hnoP ⟨n, ?_, ⟨a, by rw [hna]; ring⟩⟩
    rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  have hn1not : ∀ i, s i ≠ n + 1 := by
    intro i hi
    refine hnoQ ⟨n + 1, ?_, ⟨b, by rw [hnb]; ring⟩⟩
    rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  -- sharpened interiority: `Lower.lower` gives `5·n₁ ≤ 2·M + 20 ≤ 5·n`.
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_three_of_two_missing hk s hs0 (by omega) hnnot hn1not

#print axioms step_gap

end StepA2
