/- `5·n₁ ≤ 2·M + 20`, i.e. `n₁ ≤ (2M+20)/5` — an upper bound on the first term.

`PCI.two_mul_first_le_last` gives only `n₁ ≤ M/2`, and that is what caps every
ladder rung at a factor 2: interiority needs `n ≥ n₁`, and `n ≥ M/2` is the best
`n₁ ≤ M/2` can license. Sharpening the constant from 2 to 2.5 widens every rung
by the same factor, so 1.32× fewer rungs for the same range.

The sharp constant is `e` (`n₁ < M/e + 1`), but that is analytic. This is the
elementary substitute, and — unlike `Window.window` — it needs no gap hypothesis
at all, only strict monotonicity:

    s i ≥ n₁ + i,  so  1 = Σ 1/s i ≤ Σ_{i<k} 1/(n₁ + i).

Block the INDICES into six blocks of `m = ⌊n₁/4⌋`. On block j every term is at
most `1/(n₁ + j·m) ≤ 1/((4+j)·m)` because `4m ≤ n₁`, so the block contributes at
most `1/(4+j)` — and ℕ-division makes `4m ≤ n₁` free, with no floor analysis.

    Σ_{j<6} 1/(4+j) = 1/4+1/5+1/6+1/7+1/8+1/9 = 2509/2520 < 1,

so six blocks already fall short of 1. Hence `k > 6m`, and `M ≥ n₁ + (k−1)` turns
that into the claim. (Seven blocks would give 1/4+…+1/10 = 2509/2520 + 1/10 > 1,
so six is the most this decomposition can use.)
-/
import P287.Part1

namespace Lower

open Finset

/-- Strict monotonicity alone: the `j`-th term is at least `n₁ + j`. -/
theorem term_ge {k : ℕ} (s : Fin k → ℕ) (hmono : StrictMono s) (hk : 2 ≤ k) :
    ∀ j : ℕ, ∀ hj : j < k, s ⟨0, by omega⟩ + j ≤ s ⟨j, hj⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 : s ⟨n, by omega⟩ < s ⟨n + 1, hj⟩ := by
        first
          | exact hmono (Fin.mk_lt_mk.mpr (by omega))
          | exact hmono (by simp [Fin.lt_def]; omega)
      omega

/-- One block of `m` consecutive indices contributes at most `1/(4+j)`. -/
theorem blockU (n1 m j : ℕ) (h4 : 4 * m ≤ n1) (hm : 0 < m) :
    ∑ i ∈ Finset.Ico (j * m) ((j + 1) * m), ((n1 + i : ℕ) : ℚ)⁻¹
      ≤ ((4 + j : ℕ) : ℚ)⁻¹ := by
  have hexp : (j + 1) * m = j * m + m := by ring
  have hcard : (Finset.Ico (j * m) ((j + 1) * m)).card = m := by
    rw [Nat.card_Ico]; omega
  have hb : ∀ i ∈ Finset.Ico (j * m) ((j + 1) * m),
      ((n1 + i : ℕ) : ℚ)⁻¹ ≤ (((4 + j) * m : ℕ) : ℚ)⁻¹ := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hexp2 : (4 + j) * m = 4 * m + j * m := by ring
    have hle : (4 + j) * m ≤ n1 + i := by omega
    have hpos : (0 : ℚ) < (((4 + j) * m : ℕ) : ℚ) := by
      have : 0 < (4 + j) * m := by positivity
      exact_mod_cast this
    have hcast : (((4 + j) * m : ℕ) : ℚ) ≤ ((n1 + i : ℕ) : ℚ) := by exact_mod_cast hle
    first
      | exact inv_anti₀ hpos hcast
      | exact inv_le_inv_of_le hpos hcast
      | exact one_div_le_one_div_of_le hpos hcast
  have hsum := Finset.sum_le_card_nsmul _ _ _ hb
  rw [hcard, nsmul_eq_mul] at hsum
  refine le_trans hsum (le_of_eq ?_)
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

/-- Six blocks of `m` indices contribute at most `Σ_{j<6} 1/(4+j) < 1`. -/
theorem blocksU (n1 m : ℕ) (h4 : 4 * m ≤ n1) (hm : 0 < m) : ∀ J : ℕ,
    (∑ i ∈ Finset.Ico 0 (J * m), ((n1 + i : ℕ) : ℚ)⁻¹)
      ≤ ∑ j ∈ Finset.range J, ((4 + j : ℕ) : ℚ)⁻¹ := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have hsplit : (∑ i ∈ Finset.Ico 0 (J * m), ((n1 + i : ℕ) : ℚ)⁻¹)
          + (∑ i ∈ Finset.Ico (J * m) ((J + 1) * m), ((n1 + i : ℕ) : ℚ)⁻¹)
          = ∑ i ∈ Finset.Ico 0 ((J + 1) * m), ((n1 + i : ℕ) : ℚ)⁻¹ :=
        Finset.sum_Ico_consecutive _ (Nat.zero_le _)
          (Nat.mul_le_mul_right _ (by omega))
      rw [Finset.sum_range_succ, ← hsplit]
      exact add_le_add ih (blockU n1 m J h4 hm)

/-- **`5·n₁ ≤ 2·M + 20`.** No gap hypothesis is used. -/
theorem lower {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    5 * s ⟨0, by omega⟩ ≤ 2 * s ⟨k - 1, by omega⟩ + 20 := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  have hcount := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
  by_cases hsmall : n1 ≤ 9
  · omega
  push_neg at hsmall
  by_contra hc
  push_neg at hc
  set m := n1 / 4 with hmdef
  have h4 : 4 * m ≤ n1 := by omega
  have h4' : n1 ≤ 4 * m + 3 := by omega
  have hmpos : 0 < m := by omega
  have hlast := term_ge s hmono hk (k - 1) (by omega)
  have hk6 : k ≤ 6 * m := by omega
  set F : ℕ → ℚ := fun i => if h : i < k then ((s ⟨i, h⟩ : ℚ))⁻¹ else 0 with hF
  have hFsum : ∑ i ∈ Finset.range k, F i = 1 := by
    rw [← hsum, ← Fin.sum_univ_eq_sum_range F k]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [hF, i.isLt]
  have hFle : ∀ i ∈ Finset.range k, F i ≤ ((n1 + i : ℕ) : ℚ)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hF, dif_pos hi]
    have hb := term_ge s hmono hk i hi
    have hpos : (0 : ℚ) < ((n1 + i : ℕ) : ℚ) := by
      have : 0 < n1 + i := by omega
      exact_mod_cast this
    have hcast : ((n1 + i : ℕ) : ℚ) ≤ ((s ⟨i, hi⟩ : ℕ) : ℚ) := by exact_mod_cast hb
    first
      | exact inv_anti₀ hpos hcast
      | exact inv_le_inv_of_le hpos hcast
      | exact one_div_le_one_div_of_le hpos hcast
  have hstep1 : (1 : ℚ) ≤ ∑ i ∈ Finset.range k, ((n1 + i : ℕ) : ℚ)⁻¹ := by
    rw [← hFsum]
    exact Finset.sum_le_sum hFle
  have hsub : Finset.range k ⊆ Finset.range (6 * m) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hstep2 : ∑ i ∈ Finset.range k, ((n1 + i : ℕ) : ℚ)⁻¹
      ≤ ∑ i ∈ Finset.range (6 * m), ((n1 + i : ℕ) : ℚ)⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _
    positivity
  have hstep3 : (∑ i ∈ Finset.range (6 * m), ((n1 + i : ℕ) : ℚ)⁻¹)
      ≤ ∑ j ∈ Finset.range 6, ((4 + j : ℕ) : ℚ)⁻¹ := by
    rw [Finset.range_eq_Ico]
    exact blocksU n1 m h4 hmpos 6
  have hfin : (1 : ℚ) ≤ ∑ j ∈ Finset.range 6, ((4 + j : ℕ) : ℚ)⁻¹ :=
    le_trans hstep1 (le_trans hstep2 hstep3)
  norm_num [Finset.sum_range_succ] at hfin

#print axioms lower

end Lower
