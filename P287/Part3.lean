/- The ℝ-valued form of `prime_conjecture_implies`, matching 287.lean exactly.

Third module: `Part1` has the lemmas, `Part2` the ℚ-valued theorem, and this file
only adds the ℚ→ℝ cast bridge and composes. Kept separate because a single file
containing lemmas + assembly + ℝ peaks over the fast-lane memory budget.
-/
import P287.Part2
import Mathlib.Data.Real.Basic

namespace PCI

open Finset

/-- ℚ → ℝ casts distribute over a finite sum (no `Rat.cast_sum` in this Mathlib). -/
theorem cast_sum_gen {ι : Type*} (T : Finset ι) (f : ι → ℚ) :
    ((∑ i ∈ T, f i : ℚ) : ℝ) = ∑ i ∈ T, ((f i : ℝ)) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Rat.cast_add, ih]

theorem sum_rat_of_sum_real {k : ℕ} (s : Fin k → ℕ)
    (h : ∑ i : Fin k, (1 : ℝ) / (s i : ℝ) = 1) :
    ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1 := by
  have h' : ∑ i : Fin k, ((s i : ℝ))⁻¹ = 1 := by simpa [one_div] using h
  have hmap : ((∑ i : Fin k, ((s i : ℚ))⁻¹ : ℚ) : ℝ)
      = ∑ i : Fin k, ((s i : ℝ))⁻¹ := by
    rw [cast_sum_gen]
    refine Finset.sum_congr rfl ?_
    intro i _
    push_cast
    ring
  rw [h'] at hmap
  exact_mod_cast hmap

/-- **`erdos_287.variants.prime_conjecture_implies`**, in the upstream statement
shape: named ∀-binders as in `∀ᵉ`, ℝ-valued sum, `max_gap` byte-identical. -/
theorem prime_conjecture_implies
    (H : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ P : ℕ, Nat.Prime P ∧ N ≤ P ∧ P ≤ 2 * N ∧ Nat.Prime ((P + 1) / 2)) :
    ∃ (k₀ : ℕ), ∀ (k : ℕ) (hk₀ : k₀ ≤ k) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
      3 ≤ max_gap k s := by
  obtain ⟨k₀, hk₀⟩ := prime_conjecture_implies_rat H
  exact ⟨k₀, fun k h1 h2 s hm hs hsum => hk₀ k h1 h2 s hm hs (sum_rat_of_sum_real s hsum)⟩

#print axioms prime_conjecture_implies

end PCI
