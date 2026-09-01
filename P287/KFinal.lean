/- **Step (e): the improved `k` bound.**

`Records*` derive `k` from `M ≤ n₁ + 2(k−1)` together with `Lower3`, giving the uniform
`1718·M ≤ 5436·k − 2718`, i.e. `M ≤ 3.1644·k`. That uses the worst case `n₁ = M/e` without noticing
that AT that `n₁` the reciprocal-sum constraint is severe. Coupling them through
`KLog.log_ineq` gives

    **6389·M ≤ 14778·(k+1)**,   i.e.   M ≤ 2.31304·(k+1),

a factor `1.368` better. The last step is pure algebra: with `c = |C| = (M+1−n₁) − k` the analytic
input reads `7389(M+2)(n₁−1)² ≤ 1000(2k+2n₁−M)M²`, and the minimisation over `n₁` is the perfect
square `(7389(n₁−1) − 1000M)² ≥ 0` — no case analysis, and `Window4`/`Lower3` are not needed here.
-/
import P287.KLog

namespace KFinal

open Finset

variable {k : ℕ}

/-- **The improved `k` bound**: `6389·M ≤ 14778·(k+1)`, against `Records*`'s `M ≤ 3.1644·k`. -/
theorem kbound (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2) :
    6389 * s ⟨k - 1, by omega⟩ ≤ 14778 * (k + 1) := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  set c := (KStep.compl k s hk).card with hcdef
  -- the term set sits inside the window and has exactly `k` elements
  obtain ⟨hpos0, hle0, -⟩ := StepAB.setup hk s hmono h1 hsum
  have hTsub : Finset.image s Finset.univ ⊆ Finset.Icc n1 M := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
    refine Finset.mem_Icc.mpr ⟨?_, hi ▸ hle0 x hx⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have hi0 : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [← hi, hi0]
    · exact hi ▸ le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTcard : (Finset.image s Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hnM : n1 ≤ M := hle0 n1 (Finset.mem_image_of_mem s (Finset.mem_univ _))
  have hkle : k ≤ M + 1 - n1 := by
    have := Finset.card_le_card hTsub
    rw [hTcard, Nat.card_Icc] at this
    exact this
  -- `c + k = |Icc|` is cleaner than a subtraction identity, and it is the form needed below
  have hccard : c + k = M + 1 - n1 := by
    have hadd := Finset.card_sdiff_add_card_eq_card hTsub
    rw [hTcard, Nat.card_Icc] at hadd
    rw [hcdef, KStep.compl]
    exact hadd
  -- `2c ≤ M`, from independence (or trivially if `C` is empty)
  have hc : 2 * c ≤ M := by
    rcases Finset.eq_empty_or_nonempty (KStep.compl k s hk) with hE | hE
    · rw [hcdef, hE]; simp
    · have := IndepRank.card_le hE (fun y hy => (KStep.compl_mem hk s hy).1)
        (fun y hy => (KStep.compl_mem hk s hy).2) (KStep.compl_indep hk s hg)
      omega
  -- the analytic input, exponentiated
  have hlog := KLog.log_ineq hk s hmono h1 hsum hg hc
  have hBpos : (0:ℝ) < ((M - 2 * c + 2 : ℕ) : ℝ) := by
    have : 0 < M - 2 * c + 2 := by omega
    exact_mod_cast this
  have hMpos : (0:ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hEpos : (0:ℝ) < (n1 : ℝ) - 1 := by
    have : (1:ℝ) < (n1 : ℝ) := by exact_mod_cast h1
    linarith
  have hApos : (0:ℝ) < (M : ℝ) + 2 := by linarith
  have hexp := KLog.exp_step hApos hBpos hMpos hEpos hlog
  have h2 := KLog.exp_two_gt
  -- clear the casts and the exponential
  have hBcast : ((M - 2 * c + 2 : ℕ) : ℝ) = (M : ℝ) - 2 * (c : ℝ) + 2 := by
    push_cast [Nat.cast_sub hc]; ring
  have hccastR : (c : ℝ) = (M : ℝ) + 1 - (n1 : ℝ) - (k : ℝ) := by
    have h' : ((c + k : ℕ) : ℝ) = ((M + 1 - n1 : ℕ) : ℝ) := by exact_mod_cast hccard
    push_cast [Nat.cast_sub (show n1 ≤ M + 1 by omega)] at h'
    linarith
  rw [hBcast, hccastR] at hexp
  -- the perfect square finishes it
  have hsq := sq_nonneg (7389 * ((n1 : ℝ) - 1) - 1000 * (M : ℝ))
  have hpp : (0:ℝ) < ((M : ℝ) + 2) * ((n1 : ℝ) - 1) ^ 2 := by positivity
  -- clear the exponential
  have h3 : (7389:ℝ) * (((M : ℝ) + 2) * ((n1 : ℝ) - 1) ^ 2)
      ≤ 1000 * (((M : ℝ) - 2 * ((M : ℝ) + 1 - (n1 : ℝ) - (k : ℝ)) + 2) * (M : ℝ) ^ 2) := by
    nlinarith [hexp, h2, hpp]
  -- divide by M once, by hand: put it in the shape `X * M ≤ Y * M`
  have hA : ((7389:ℝ) * ((n1 : ℝ) - 1) ^ 2) * (M : ℝ)
      ≤ (1000 * (2 * (k : ℝ) + 2 * (n1 : ℝ) - (M : ℝ)) * (M : ℝ)) * (M : ℝ) := by
    nlinarith [h3, hMpos, sq_nonneg ((n1 : ℝ) - 1)]
  have hdiv := le_of_mul_le_mul_right hA hMpos
  -- and once more, after multiplying the square by M
  have hB : ((6389:ℝ) * (M : ℝ)) * (M : ℝ) ≤ (14778 * ((k : ℝ) + 1)) * (M : ℝ) := by
    nlinarith [hdiv, hsq, hMpos]
  have hgoal : 6389 * (M : ℝ) ≤ 14778 * ((k : ℝ) + 1) := le_of_mul_le_mul_right hB hMpos
  exact_mod_cast hgoal

#print axioms kbound

end KFinal
