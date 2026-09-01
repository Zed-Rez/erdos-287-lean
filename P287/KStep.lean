/- **The complement of a gaps-≤2 set, as an independent Finset with a known reciprocal sum.**

Step (a)-(c) of the improved `k` bound (LEDGER 446-448). The `k` records in `Records*` are derived
from `M ≤ n₁ + 2(k−1)` together with `Lower3`, giving the uniform `M ≤ 3.1644 k`. That takes the
worst case `n₁ = M/e` without noticing that at that `n₁` the reciprocal-sum constraint is severe, so
the true uniform constant is `2/(1 − 1/e²) = 2.3130`.

This file sets up the object the argument needs: `C = Icc n₁ M \ image s`, which is

* **independent** — two consecutive missing interior values would force a gap `≥ 3`
  (`PCI.gap_three_of_two_missing`, used in contrapositive), and
* has **`∑_{x ∈ C} 1/x = H(n₁,M) − 1`** exactly, since the terms sum to `1` and lie in `Icc n₁ M`.

Feeding it to `IndepRank.sum_inv_ge` gives the harmonic inequality that the log step then converts.
-/
import P287.IndepRank
import P287.StepAB
import P287.Part1

namespace KStep

open Finset

variable {k : ℕ}

/-- The complement of the term set inside the window. -/
noncomputable def compl (k : ℕ) (s : Fin k → ℕ) (hk : 2 ≤ k) : Finset ℕ :=
  (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ (Finset.image s Finset.univ)

/-- **The complement is independent**: two consecutive missing interior values force a gap `≥ 3`. -/
theorem compl_indep (hk : 2 ≤ k) (s : Fin k → ℕ) (hg : PCI.max_gap k s ≤ 2) :
    ∀ x ∈ compl k s hk, x + 1 ∉ compl k s hk := by
  classical
  intro x hx hx1
  rw [compl, Finset.mem_sdiff, Finset.mem_Icc] at hx hx1
  obtain ⟨⟨hxlo, hxhi⟩, hxT⟩ := hx
  obtain ⟨⟨h1lo, h1hi⟩, h1T⟩ := hx1
  have e0 : ∀ i, s i ≠ x := by
    intro i hi
    exact hxT (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have e1 : ∀ i, s i ≠ x + 1 := by
    intro i hi
    exact h1T (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have := PCI.gap_three_of_two_missing hk s hxlo h1hi e0 e1
  omega

/-- Every element of the complement is at least `n₁` (hence positive) and at most `M`. -/
theorem compl_mem (hk : 2 ≤ k) (s : Fin k → ℕ) {x : ℕ} (hx : x ∈ compl k s hk) :
    s ⟨0, by omega⟩ ≤ x ∧ x ≤ s ⟨k - 1, by omega⟩ := by
  classical
  rw [compl, Finset.mem_sdiff, Finset.mem_Icc] at hx
  exact hx.1

/-- **The complement's reciprocal sum is `H(n₁,M) − 1`.** -/
theorem compl_sum (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    ∑ x ∈ compl k s hk, ((x : ℚ))⁻¹
      = (∑ n ∈ Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩), ((n : ℚ))⁻¹) - 1 := by
  classical
  obtain ⟨hpos, hle, hsumT⟩ := StepAB.setup hk s hmono h1 hsum
  set T := Finset.image s Finset.univ with hTdef
  -- every term lies in the window
  have hsub : T ⊆ Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩) := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
    refine Finset.mem_Icc.mpr ⟨?_, hi ▸ hle x hx⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have hi0 : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [← hi, hi0]
    · exact hi ▸ le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  -- state the equation explicitly: the named `(f := …)` form left the Finset types as metavariables
  have hsd : (∑ x ∈ (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ T, ((x : ℚ))⁻¹)
      + (∑ x ∈ T, ((x : ℚ))⁻¹)
      = ∑ x ∈ Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩), ((x : ℚ))⁻¹ :=
    Finset.sum_sdiff hsub
  rw [hsumT] at hsd
  rw [compl, ← hTdef]
  linarith [hsd]

/-- **The harmonic inequality.** Feeding the complement to `IndepRank.sum_inv_ge`:
the greedy sum from the top of the window is at most `H(n₁,M) − 1`. -/
theorem greedy_le (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2) :
    ∑ j ∈ Finset.range (compl k s hk).card,
        (((s ⟨k - 1, by omega⟩ - 2 * j : ℕ) : ℚ))⁻¹
      ≤ (∑ n ∈ Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩), ((n : ℚ))⁻¹) - 1 := by
  classical
  have hpos : ∀ y ∈ compl k s hk, 0 < y := by
    intro y hy
    have := (compl_mem hk s hy).1
    omega
  have hb : ∀ y ∈ compl k s hk, y ≤ s ⟨k - 1, by omega⟩ := fun y hy => (compl_mem hk s hy).2
  have := IndepRank.sum_inv_ge hpos hb (compl_indep hk s hg)
  rw [compl_sum hk s hmono h1 hsum] at this
  exact this

#print axioms compl_indep
#print axioms compl_sum
#print axioms greedy_le

end KStep
