/- **The sharp lower bound: `e·(n₁ − 1) ≤ M`, hence `2718·n₁ ≤ 1000·M + 2718`.**

The mirror of `Window4`. `Lower.lower` gives `5n₁ ≤ 2M + 20` (i.e. `n₁ ≤ 0.4M`), `Lower2.lower2`
gives `8n₁ ≤ 3M + 145` (`0.375M`); the truth is `n₁ ≤ M/e + 1 ≈ 0.368M`. Those two block the sum by
index and avoid logarithms, exactly as the `Window` line did, and they stop short for the same
reason.

The analytic argument is one telescoped inequality in the other direction. Strict monotonicity alone
gives `sᵢ ≥ n₁ + i`, so

    1 = Σᵢ 1/sᵢ  ≤  Σ_{i<k} 1/(n₁+i)  ≤  log(n₁+k−1) − log(n₁−1),

using `1/u ≤ log u − log(u−1)`, which is `Real.log_le_sub_one_of_pos` applied to `(u−1)/u`. Hence
`(n₁+k−1)/(n₁−1) ≥ e`, and `M ≥ n₁ + (k−1)` gives `M ≥ e·(n₁−1)`. `e > 2.718` comes from
`Real.exp_one_gt_d9`.

No gap hypothesis is used anywhere — only strict monotonicity — exactly as in `Lower.lower`.

With `Window4` this puts both window constants at their limits: `M ≤ 7.39n₁ − 2` and
`n₁ ≤ M/e + 1`. There is nothing further to sharpen on either axis.
-/
import P287.Lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Lower3

open Finset

/-- One telescoping step, downward: `1/u ≤ log u − log(u−1)` for `u > 1`. -/
theorem log_step {u : ℝ} (hu : 1 < u) : 1 / u ≤ Real.log u - Real.log (u - 1) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hu1 : (0:ℝ) < u - 1 := by linarith
  have hpos : (0:ℝ) < (u - 1) / u := by positivity
  have hb := Real.log_le_sub_one_of_pos hpos
  have hune : u ≠ 0 := ne_of_gt hu0
  have hkey : (u - 1) / u - 1 = -(1 / u) := by field_simp; ring
  rw [hkey] at hb
  rw [Real.log_div (ne_of_gt hu1) (ne_of_gt hu0)] at hb
  linarith

/-- Telescoped: `Σ_{i<J} 1/(n₁+i) ≤ log(n₁+J−1) − log(n₁−1)`. -/
theorem tele (n1 : ℕ) (hn : 1 < n1) : ∀ J : ℕ,
    ∑ i ∈ Finset.range J, (1 / ((n1 : ℝ) + i))
      ≤ Real.log ((n1 : ℝ) + J - 1) - Real.log ((n1 : ℝ) - 1) := by
  have hnR : (1:ℝ) < (n1 : ℝ) := by exact_mod_cast hn
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have hu : (1:ℝ) < (n1 : ℝ) + J := by
        have : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        linarith
      have hstep := log_step hu
      have hc1 : ((n1 : ℝ) + J - 1) = ((n1 : ℝ) + J) - 1 := by ring
      have hc2 : ((n1 : ℝ) + (J + 1) - 1) = (n1 : ℝ) + J := by ring
      rw [Finset.sum_range_succ]
      push_cast
      rw [hc2]
      rw [hc1] at ih
      linarith [ih, hstep]

/-- **The sharp lower bound**, integer form: `2718·n₁ ≤ 1000·M + 2718`, i.e. `n₁ ≤ M/e + 1`.
No gap hypothesis — strict monotonicity suffices. -/
theorem lower3 {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    2718 * s ⟨0, by omega⟩ ≤ 1000 * s ⟨k - 1, by omega⟩ + 2718 := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  have hnR : (1:ℝ) < (n1 : ℝ) := by exact_mod_cast h1
  -- the real-valued sum is 1
  have hsumR : ∑ i : Fin k, (1 / ((s i : ℝ))) = 1 := by
    have hcast : ((∑ i : Fin k, ((s i : ℚ))⁻¹ : ℚ) : ℝ) = ∑ i : Fin k, (1 / ((s i : ℝ))) := by
      push_cast
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [one_div]
    rw [← hcast, hsum]
    norm_num
  -- 1 ≤ Σ_{i<k} 1/(n₁+i)
  have hterm : (1:ℝ) ≤ ∑ i ∈ Finset.range k, (1 / ((n1 : ℝ) + i)) := by
    have hle : ∑ i : Fin k, (1 / ((s i : ℝ)))
        ≤ ∑ i ∈ Finset.range k, (1 / ((n1 : ℝ) + i)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (1 / ((n1 : ℝ) + i))) k]
      refine Finset.sum_le_sum ?_
      intro i _
      have hb := Lower.term_ge s hmono hk i.val i.isLt
      have hfin : (⟨i.val, i.isLt⟩ : Fin k) = i := by apply Fin.ext; rfl
      rw [hfin] at hb
      have hpos : (0:ℝ) < (n1 : ℝ) + (i.val : ℝ) := by
        have : (0:ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
        linarith
      have hcast : ((n1 : ℝ) + (i.val : ℝ)) ≤ ((s i : ℕ) : ℝ) := by exact_mod_cast hb
      exact one_div_le_one_div_of_le hpos hcast
    rw [hsumR] at hle
    exact hle
  -- telescoping gives log((n₁+k−1)/(n₁−1)) ≥ 1
  have htel := tele n1 h1 k
  have hlog : (1:ℝ) ≤ Real.log ((n1 : ℝ) + k - 1) - Real.log ((n1 : ℝ) - 1) := by linarith
  have hd1 : (0:ℝ) < (n1 : ℝ) - 1 := by linarith
  have hdk : (0:ℝ) < (n1 : ℝ) + k - 1 := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hdiv : (1:ℝ) ≤ Real.log (((n1 : ℝ) + k - 1) / ((n1 : ℝ) - 1)) := by
    rw [Real.log_div (ne_of_gt hdk) (ne_of_gt hd1)]
    exact hlog
  have hexp : Real.exp 1 ≤ ((n1 : ℝ) + k - 1) / ((n1 : ℝ) - 1) := by
    have := (Real.le_log_iff_exp_le (by positivity)).mp hdiv
    exact this
  -- M ≥ n₁ + (k−1)
  have hMle : n1 + (k - 1) ≤ M := Lower.term_ge s hmono hk (k - 1) (by omega)
  have hMR : (n1 : ℝ) + (k : ℝ) - 1 ≤ (M : ℝ) := by
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : 1 ≤ k := by omega
      push_cast [Nat.cast_sub this]; ring
    have : ((n1 + (k - 1) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMle
    push_cast [hk1] at this
    linarith
  -- e·(n₁ − 1) ≤ M, then e > 2.718
  have hkey : Real.exp 1 * ((n1 : ℝ) - 1) ≤ (M : ℝ) := by
    have := (le_div_iff₀ hd1).mp hexp
    linarith
  have he : (2.718:ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hfin : (2718:ℝ) * ((n1 : ℝ) - 1) < 1000 * (M : ℝ) := by nlinarith [hkey, he, hd1]
  have : ((2718 * n1 : ℕ) : ℝ) ≤ ((1000 * M + 2718 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

#print axioms lower3

end Lower3
