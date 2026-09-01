/- Three consecutive missing values force a gap of at least 4.

`PCI.gap_three_of_two_missing` is the gap-2 workhorse: two consecutive values absent
from the term set force max_gap ≥ 3. The same argument with one more absent value
gives max_gap ≥ 4, which is what a gaps-≤3 contradiction needs. The proof below is
`gap_three_of_two_missing` verbatim with the extra hypothesis threaded through — the
maximal index j with s j < m has s(j+1) ∉ {m, m+1, m+2}, hence s(j+1) − s j ≥ 4.

`Part1` is left untouched: everything in the #287 ladder depends on its .olean.
-/
import P287.Part1

namespace PCI

theorem gap_four_of_three_missing {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    {m : ℕ}
    (hlo : s ⟨0, by omega⟩ ≤ m) (hhi : m + 1 ≤ s ⟨k - 1, by omega⟩)
    (hm : ∀ i, s i ≠ m) (hm1 : ∀ i, s i ≠ m + 1) (hm2 : ∀ i, s i ≠ m + 2) :
    4 ≤ max_gap k s := by
  classical
  set I := Finset.univ.filter (fun i : Fin k => s i < m) with hIdef
  have h0mem : (⟨0, by omega⟩ : Fin k) ∈ I := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases lt_or_eq_of_le hlo with h | h
    · exact h
    · exact absurd h (hm _)
  have hIne : I.Nonempty := ⟨_, h0mem⟩
  have hjmem : I.max' hIne ∈ I := I.max'_mem hIne
  have hjlt : s (I.max' hIne) < m := (Finset.mem_filter.mp hjmem).2
  -- the maximiser is not the final index
  have hjlast : ((I.max' hIne : Fin k) : ℕ) + 1 < k := by
    by_contra hcon
    push_neg at hcon
    have hval : ((I.max' hIne : Fin k) : ℕ) = k - 1 := by
      have := (I.max' hIne).isLt; omega
    have heq : (I.max' hIne : Fin k) = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext hval
    rw [heq] at hjlt
    omega
  -- its successor is at least m + 2
  have hj'notmem : (⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ : Fin k) ∉ I := by
    intro hmem
    have hle := Finset.le_max' I _ hmem
    rw [Fin.le_def] at hle
    simp only at hle
    omega
  have hj'ge : m ≤ s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hj'notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
  have hj'ge2 : m + 3 ≤ s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ := by
    have h1 := hm ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    have h2 := hm1 ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    have h3 := hm2 ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    omega
  -- that gap is one of the terms of the sup
  have hidx : ((I.max' hIne : Fin k) : ℕ) < k - 1 := by omega
  have hterm : s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ - s (I.max' hIne)
      ≤ max_gap k s := by
    have := Finset.le_sup (f := fun i : Fin (k - 1) =>
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
      (Finset.mem_univ (⟨((I.max' hIne : Fin k) : ℕ), hidx⟩ : Fin (k - 1)))
    simpa using this
  omega

#print axioms gap_four_of_three_missing

end PCI
