/- **The sharp window bound: `M + 2 ≤ e²·n₁`, hence `100(M+2) ≤ 739·n₁`.**

`Window.window` gives `M < 15n₁`, `Window2` gives `9.5`, `Window3` gives `7.8`. All three block the
sum by INDEX and avoid logarithms entirely; the scheme converges to `e² ≈ 7.389` and provably never
reaches it, since `J` blocks of `⌊n₁/d⌋` give exactly `1 + 2J/d` and `Σ_{j<J} 1/(d+2j+2) > 1` forces
`d + 2J > d·e²`.

This file reaches the limit by giving up on elementarity — the first and only analytic argument in
the development. Gaps ≤ 2 give `sᵢ ≤ n₁ + 2i`, so

    1 = Σᵢ 1/sᵢ  ≥  Σ_{i<k} 1/(n₁+2i)  ≥  ½·(log(n₁+2k) − log n₁),

the last step by telescoping a one-line inequality: `log(u+2) − log u = log(1 + 2/u) ≤ 2/u`. Hence
`log((n₁+2k)/n₁) ≤ 2`, so `n₁ + 2k ≤ e²·n₁`, and `M ≤ n₁ + 2(k−1)` finishes.

`e² < 7.39` comes from `Real.exp_one_lt_d9`, so the integer form is `100(M+2) ≤ 739·n₁`. That
retires the Window/Window2/Window3 line: there is nothing left to sharpen.
-/
import P287.Kbound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Window4

open Finset

/-- One telescoping step: `log(u+2) − log u ≤ 2/u`. -/
theorem log_step {u : ℝ} (hu : 0 < u) :
    Real.log (u + 2) - Real.log u ≤ 2 / u := by
  have h2 : (0:ℝ) < u + 2 := by linarith
  have hdiv : Real.log (u + 2) - Real.log u = Real.log ((u + 2) / u) := by
    rw [Real.log_div (ne_of_gt h2) (ne_of_gt hu)]
  rw [hdiv]
  have hpos : (0:ℝ) < (u + 2) / u := by positivity
  have hb := Real.log_le_sub_one_of_pos hpos
  have hune : u ≠ 0 := ne_of_gt hu
  have hkey : (u + 2) / u - 1 = 2 / u := by field_simp; ring
  rw [hkey] at hb
  exact hb

/-- Telescoped: `log(n₁+2J) − log n₁ ≤ 2·Σ_{i<J} 1/(n₁+2i)`. -/
theorem tele (n1 : ℕ) (hn : 0 < n1) : ∀ J : ℕ,
    Real.log ((n1 : ℝ) + 2 * J) - Real.log n1
      ≤ 2 * ∑ i ∈ Finset.range J, (1 / ((n1 : ℝ) + 2 * i)) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have hpos : (0:ℝ) < (n1 : ℝ) + 2 * J := by
        have : (0:ℝ) < (n1 : ℝ) := by exact_mod_cast hn
        positivity
      have hstep := log_step hpos
      have hcast : ((n1 : ℝ) + 2 * (J + 1)) = ((n1 : ℝ) + 2 * J) + 2 := by push_cast; ring
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      rw [hcast]
      have h2 : 2 * (1 / ((n1 : ℝ) + 2 * J)) = 2 / ((n1 : ℝ) + 2 * J) := by ring
      linarith [ih, hstep]

/-- **The sharp window bound**, integer form: `100·(M+2) ≤ 739·n₁`. -/
theorem window4 {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2) :
    100 * (s ⟨k - 1, by omega⟩ + 2) ≤ 739 * s ⟨0, by omega⟩ := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  have hnpos : 0 < n1 := by omega
  have hnR : (0:ℝ) < (n1 : ℝ) := by exact_mod_cast hnpos
  -- the real-valued sum is 1
  have hsumR : ∑ i : Fin k, (1 / ((s i : ℝ))) = 1 := by
    have := hsum
    have hcast : ((∑ i : Fin k, ((s i : ℚ))⁻¹ : ℚ) : ℝ) = ∑ i : Fin k, (1 / ((s i : ℝ))) := by
      push_cast
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [one_div]
    rw [← hcast, hsum]
    norm_num
  -- each term dominates 1/(n₁+2i)
  have hterm : ∑ i ∈ Finset.range k, (1 / ((n1 : ℝ) + 2 * i)) ≤ 1 := by
    have hle : ∑ i ∈ Finset.range k, (1 / ((n1 : ℝ) + 2 * i))
        ≤ ∑ i : Fin k, (1 / ((s i : ℝ))) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (1 / ((n1 : ℝ) + 2 * i))) k]
      refine Finset.sum_le_sum ?_
      intro i _
      have hb := Kbound.term_le s hk hg i.val i.isLt
      have hip : (0:ℝ) < (s i : ℝ) := by
        have h0 : s ⟨0, by omega⟩ ≤ s i := by
          rcases Nat.eq_zero_or_pos i.val with hz | hz
          · have he : (⟨0, by omega⟩ : Fin k) = i := by apply Fin.ext; simpa using hz.symm
            rw [he]
          · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
        have : 0 < s i := by omega
        exact_mod_cast this
      have hle2 : ((s i : ℕ) : ℝ) ≤ (n1 : ℝ) + 2 * (i.val : ℝ) := by
        have : (s ⟨i.val, i.isLt⟩ : ℕ) ≤ n1 + 2 * i.val := hb
        have hfin : (⟨i.val, i.isLt⟩ : Fin k) = i := by apply Fin.ext; rfl
        rw [hfin] at this
        exact_mod_cast this
      exact one_div_le_one_div_of_le hip hle2
    rw [hsumR] at hle
    exact hle
  -- telescoping gives log((n₁+2k)/n₁) ≤ 2
  have hlog := tele n1 hnpos k
  have hlog2 : Real.log ((n1 : ℝ) + 2 * k) - Real.log n1 ≤ 2 := by linarith
  have hkpos : (0:ℝ) < (n1 : ℝ) + 2 * k := by positivity
  have hdiv : Real.log (((n1 : ℝ) + 2 * k) / n1) ≤ 2 := by
    rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hnR)]
    exact hlog2
  have hexp : ((n1 : ℝ) + 2 * k) / n1 ≤ Real.exp 2 := by
    have := (Real.log_le_iff_le_exp (by positivity)).mp hdiv
    exact this
  -- e² < 7.39
  have he2 : Real.exp 2 < 7.39 := by
    have h1e := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos (1:ℝ), h1e]
  have hfin : ((n1 : ℝ) + 2 * k) < 7.39 * n1 := by
    have := (div_le_iff₀ hnR).mp hexp
    nlinarith [he2, hnR]
  -- M ≤ n₁ + 2(k−1)
  have hMle : M ≤ n1 + 2 * (k - 1) := Kbound.term_le s hk hg (k - 1) (by omega)
  have hMR : ((M : ℝ) + 2) ≤ (n1 : ℝ) + 2 * k := by
    have : (M : ℝ) ≤ (n1 : ℝ) + 2 * ((k : ℝ) - 1) := by
      have hc : (M : ℕ) ≤ n1 + 2 * (k - 1) := hMle
      have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : 1 ≤ k := by omega
        push_cast [Nat.cast_sub this]
        ring
      calc (M : ℝ) ≤ ((n1 + 2 * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hc
        _ = (n1 : ℝ) + 2 * ((k : ℝ) - 1) := by push_cast [hk1]; ring
    linarith
  have hbig : 100 * ((M : ℝ) + 2) ≤ 739 * (n1 : ℝ) := by nlinarith [hMR, hfin, hnR]
  have : ((100 * (M + 2) : ℕ) : ℝ) ≤ ((739 * n1 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

#print axioms window4

end Window4
