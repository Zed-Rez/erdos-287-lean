/- **The budget criterion: the surviving integers must still afford 1.**

Every attack in this development so far closes a range by exhibiting a RUNG — two consecutive
integers both forced out of the term set. That is a statement about a *pair*, and pair statements
about large prime factors are exactly what sieve methods cannot reach. This file records a
different sufficient condition, which needs no pair at all.

If `E` is any set of integers known not to be terms, then the terms live in `[n₁, M] \ E`, and their
reciprocals sum to `1`. Since reciprocals are positive,

    1  ≤  Σ_{n ∈ [n₁,M] \ E}  1/n.

Contrapositive: **if the integers surviving `E` cannot themselves reach `1`, there is no
representation at all.** No gap hypothesis is used, and `E` never has to contain two consecutive
elements — only enough of them, weighted by `1/n`.

The point is what this asks of number theory. With `E = { n : P(n) > M/431 }` (`Rough.term_smooth`),
the criterion bites as soon as `Σ_{n∈E} 1/n > H − 1`, `H = Σ_{n₁}^{M} 1/n`, and `Σ_{n∈E} 1/n` is
governed by the DENSITY of integers with a large prime factor — Mertens, classical and effective —
rather than by any correlation between neighbours. Measured (`attempts/026-budget`) at `M = 10¹⁹⁰`:
`Σ_E 1/n ≈ 0.0260` at the top of the window and the criterion closes

    M/n₁  <  2.7575,

against the full gap-`≤2` range `[e, e²] = [2.7183, 7.3891]` — a genuine sliver above the `Lower3`
boundary, 1.43% of the log-range, and the Rosser–Schoenfeld error budget is 0.05% of the margin.

It does not close the rest, and the reason is sharp: reaching `M/n₁ = e²` needs a cofactor bound
`A > 8.3·10¹⁷`, while Lemma A′ caps `A ≤ log M − 2 log log M ≈ 425`. So among the three natural
sufficient conditions the ranking is
`rung (A = 431, pair)` ≺ `budget (A > 8.3·10¹⁷, density)` ≺ `cardinality (A > √M)`,
and the rung is the cheapest — the pair barrier is not an artefact of the method chosen.
-/
import P287.StepAB

namespace Budget

open Finset

/-- **The budget criterion.** The integers of `[n₁, M]` outside any set `E` of known non-terms
still have reciprocal sum at least 1. -/
theorem budget {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (E : Finset ℕ) (hE : ∀ n ∈ E, ∀ i, s i ≠ n) :
    1 ≤ ∑ n ∈ (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ E, ((n : ℚ))⁻¹ := by
  classical
  obtain ⟨hpos, hle, hsumT⟩ := StepAB.setup hk s hmono h1 hsum
  set T := Finset.image s Finset.univ with hTdef
  -- every term is at least n₁
  have hge : ∀ x ∈ T, s ⟨0, by omega⟩ ≤ x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [← hi, this]
    · exact hi ▸ le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  -- T sits inside the window with E removed
  have hsub : T ⊆ (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ E := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hge x hx, hle x hx⟩, ?_⟩
    intro hxE
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    exact hE x hxE i hi
  -- reciprocals are nonnegative, so enlarging the index set only increases the sum
  have hnn : ∀ n ∈ (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ E, n ∉ T →
      (0 : ℚ) ≤ ((n : ℚ))⁻¹ := by
    intro n _ _
    positivity
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [hsumT] at this
  exact this

/-- The usable contrapositive: if the survivors cannot reach 1, there is no representation. -/
theorem no_rep_of_budget {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (E : Finset ℕ) (hE : ∀ n ∈ E, ∀ i, s i ≠ n)
    (hlt : ∑ n ∈ (Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)) \ E, ((n : ℚ))⁻¹ < 1) :
    ∑ i : Fin k, ((s i : ℚ))⁻¹ ≠ 1 := by
  intro hsum
  exact absurd (budget hk s hmono h1 hsum E hE) (by linarith)

#print axioms budget
#print axioms no_rep_of_budget

end Budget
