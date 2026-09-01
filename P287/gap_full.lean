/- KURSCHAK + full plumbing: the REAL-valued `gap_at_least_two`, kernel-clean.

   KURSCHAK'S THEOREM, kernel-clean:
   a sum of reciprocals of two or more CONSECUTIVE integers, starting at >= 2,
   is never equal to 1.

This is exactly the mathematical content of
`erdos_287.variants.gap_at_least_two` in FormalConjectures/ErdosProblems/287.lean,
which is tagged `research solved` upstream but is a bare `sorry`: if every gap of
a solution were 1 the terms would be consecutive, which this rules out.

Two ingredients, both proved here:
  * `unique_max`  -- on an interval the maximal 2-adic valuation is attained at
    exactly ONE point (two maximisers 2^k u < 2^k v with u,v odd would sandwich
    the even 2^k(u+1), whose valuation is larger);
  * `sum_inv_ne_one` -- if one term uniquely dominates the 2-adic valuation then
    by ultrametricity it alone fixes v_2 of the sum, at -v_2(j) < 0, whereas
    v_2(1) = 0.

Narrow imports only; every Mathlib name used was confirmed by a probe build.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat

namespace Kurschak

open Finset

/-- `k + 1 ≤ padicValNat 2 m` follows from `2 ^ (k+1) ∣ m`. -/
theorem le_padicValNat_of_dvd {m k : ℕ} (hm : m ≠ 0) (h : 2 ^ (k + 1) ∣ m) :
    k + 1 ≤ padicValNat 2 m := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have := (Nat.Prime.pow_dvd_iff_le_factorization h2 hm).mp h
  rwa [Nat.factorization_def m h2] at this

/-- `n = 2 ^ v * u` with `u` odd, where `v = padicValNat 2 n`. -/
theorem split_two_adic {n : ℕ} (hn : n ≠ 0) :
    ∃ u, n = 2 ^ padicValNat 2 n * u ∧ ¬ (2 ∣ u) := by
  refine ⟨n / 2 ^ padicValNat 2 n, (Nat.mul_div_cancel' pow_padicValNat_dvd).symm, ?_⟩
  rintro ⟨c, hc⟩
  have hdvd : 2 ^ (padicValNat 2 n + 1) ∣ n := by
    refine ⟨c, ?_⟩
    calc n = 2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n) :=
          (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
      _ = 2 ^ padicValNat 2 n * (2 * c) := by rw [hc]
      _ = 2 ^ (padicValNat 2 n + 1) * c := by ring
  have := le_padicValNat_of_dvd hn hdvd
  omega

private theorem no_two {a b n₁ n₂ : ℕ}
    (h₁ : n₁ ∈ Icc a b) (h₂ : n₂ ∈ Icc a b) (ha : 0 < a)
    (hmax : ∀ m ∈ Icc a b, padicValNat 2 m ≤ padicValNat 2 n₁)
    (heq : padicValNat 2 n₂ = padicValNat 2 n₁) (hlt : n₁ < n₂) : False := by
  have hn₁0 : n₁ ≠ 0 := by have := (mem_Icc.mp h₁).1; omega
  have hn₂0 : n₂ ≠ 0 := by have := (mem_Icc.mp h₂).1; omega
  obtain ⟨u, hu, hudd⟩ := split_two_adic hn₁0
  obtain ⟨v, hv, hvdd⟩ := split_two_adic hn₂0
  rw [heq] at hv
  set k := padicValNat 2 n₁ with hk
  have huv : u < v := by
    by_contra h
    push_neg at h
    have : n₂ ≤ n₁ := by rw [hu, hv]; exact Nat.mul_le_mul_left _ h
    omega
  have heven : 2 ∣ (u + 1) := by
    rcases Nat.even_or_odd u with he | ho
    · exact absurd he.two_dvd hudd
    · exact ho.add_one.two_dvd
  have hm_mem : 2 ^ k * (u + 1) ∈ Icc a b := by
    rw [mem_Icc]
    refine ⟨le_trans (mem_Icc.mp h₁).1 ?_, le_trans ?_ (mem_Icc.mp h₂).2⟩
    · rw [hu]; exact Nat.mul_le_mul_left _ (by omega)
    · rw [hv]; exact Nat.mul_le_mul_left _ (by omega)
  have hm0 : 2 ^ k * (u + 1) ≠ 0 := by positivity
  have hdvd : 2 ^ (k + 1) ∣ 2 ^ k * (u + 1) := by
    obtain ⟨c, hc⟩ := heven
    exact ⟨c, by rw [hc]; ring⟩
  have hval : k + 1 ≤ padicValNat 2 (2 ^ k * (u + 1)) := le_padicValNat_of_dvd hm0 hdvd
  have := hmax _ hm_mem
  omega

/-- The maximal 2-adic valuation on `Icc a b` is attained at only one point. -/
theorem unique_max {a b n₁ n₂ : ℕ} (ha : 0 < a)
    (h₁ : n₁ ∈ Icc a b) (h₂ : n₂ ∈ Icc a b)
    (hmax : ∀ m ∈ Icc a b, padicValNat 2 m ≤ padicValNat 2 n₁)
    (heq : padicValNat 2 n₂ = padicValNat 2 n₁) : n₁ = n₂ := by
  rcases lt_trichotomy n₁ n₂ with hlt | h | hgt
  · exact absurd (no_two h₁ h₂ ha hmax heq hlt) not_false
  · exact h
  · exact absurd (no_two h₂ h₁ ha (fun m hm => heq ▸ hmax m hm) heq.symm hgt) not_false

/-- Positive-everywhere version of `n ↦ 1/n`. -/
noncomputable def G (n : ℕ) : ℚ := if n = 0 then 1 else (n : ℚ)⁻¹

theorem G_pos (n : ℕ) : 0 < G n := by
  unfold G
  split
  · norm_num
  · rename_i h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have hq : (0 : ℚ) < n := by exact_mod_cast hn
    exact inv_pos.mpr hq

theorem G_eq {n : ℕ} (hn : n ≠ 0) : G n = (n : ℚ)⁻¹ := by unfold G; simp [hn]

theorem padicValRat_G {n : ℕ} (hn : n ≠ 0) :
    padicValRat 2 (G n) = -(padicValNat 2 n : ℤ) := by
  rw [G_eq hn, padicValRat.inv, padicValRat.of_nat]

/-- A uniquely dominant term fixes the 2-adic valuation of the whole sum. -/
theorem padicValRat_sum {T : Finset ℕ} (hT : ∀ n ∈ T, n ≠ 0)
    {j : ℕ} (hj : j ∈ T)
    (hmax : ∀ i ∈ T, i ≠ j → padicValNat 2 i < padicValNat 2 j) :
    padicValRat 2 (∑ n ∈ T, G n) = -(padicValNat 2 j : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  rcases eq_or_ne (T.erase j) ∅ with he | he
  · have : ∑ n ∈ T, G n = G j := by
      rw [← Finset.add_sum_erase T G hj, he, Finset.sum_empty, add_zero]
    rw [this, padicValRat_G (hT j hj)]
  · have hne : (T.erase j).Nonempty := Finset.nonempty_of_ne_empty he
    have hlt : ∀ i ∈ T.erase j, padicValRat 2 (G j) < padicValRat 2 (G i) := by
      intro i hi
      have hiT : i ∈ T := Finset.mem_of_mem_erase hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [padicValRat_G (hT j hj), padicValRat_G (hT i hiT)]
      exact neg_lt_neg (by exact_mod_cast hmax i hiT hij)
    have hsum : padicValRat 2 (G j) < padicValRat 2 (∑ i ∈ T.erase j, G i) :=
      padicValRat.lt_sum_of_lt hne hlt G_pos
    have hrest_pos : 0 < ∑ i ∈ T.erase j, G i :=
      Finset.sum_pos (fun i _ => G_pos i) hne
    have hkey : padicValRat 2 (G j + ∑ i ∈ T.erase j, G i)
        = min (padicValRat 2 (G j)) (padicValRat 2 (∑ i ∈ T.erase j, G i)) := by
      refine padicValRat.add_eq_min ?_ (ne_of_gt (G_pos j)) (ne_of_gt hrest_pos)
        (ne_of_lt hsum)
      exact ne_of_gt (add_pos (G_pos j) hrest_pos)
    rw [Finset.add_sum_erase T G hj] at hkey
    rw [hkey, min_eq_left (le_of_lt hsum), padicValRat_G (hT j hj)]

/-- **Kürschák.** For `2 ≤ a < b`, the reciprocals of `a, a+1, …, b` never sum to 1. -/
theorem interval_sum_inv_ne_one {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    ∑ n ∈ Icc a b, G n ≠ 1 := by
  classical
  have hane : (Icc a b).Nonempty := ⟨a, mem_Icc.mpr ⟨le_refl a, le_of_lt hab⟩⟩
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image (Icc a b) (padicValNat 2) hane
  have hT : ∀ n ∈ Icc a b, n ≠ 0 := by
    intro n hn; have := (mem_Icc.mp hn).1; omega
  -- the maximum is attained only at j
  have huniq : ∀ i ∈ Icc a b, i ≠ j → padicValNat 2 i < padicValNat 2 j := by
    intro i hi hij
    rcases lt_or_eq_of_le (hjmax i hi) with h | h
    · exact h
    · exact absurd (unique_max (by omega) hjmem hi hjmax h).symm hij
  -- the interval contains an even number, so the maximum valuation is ≥ 1
  have hpos : 0 < padicValNat 2 j := by
    have hev : ∃ e ∈ Icc a b, 2 ∣ e := by
      rcases Nat.even_or_odd a with he | ho
      · exact ⟨a, mem_Icc.mpr ⟨le_refl a, le_of_lt hab⟩, he.two_dvd⟩
      · exact ⟨a + 1, mem_Icc.mpr ⟨by omega, by omega⟩, ho.add_one.two_dvd⟩
    obtain ⟨e, hemem, hedvd⟩ := hev
    have he0 : e ≠ 0 := hT e hemem
    have : 1 ≤ padicValNat 2 e := by
      refine le_padicValNat_of_dvd he0 ?_
      simpa using hedvd
    exact lt_of_lt_of_le this (hjmax e hemem)
  intro hsum
  have hval := padicValRat_sum hT hjmem huniq
  rw [hsum] at hval
  simp only [padicValRat.one] at hval
  omega


/-! ### Plumbing: from `max_gap ≤ 1` to a consecutive block, then to Kürschák. -/

/-- `max_gap` copied verbatim from FormalConjectures/ErdosProblems/287.lean. -/
def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- If every gap is ≤ 1 and `s` is strictly monotone, the terms are consecutive. -/
theorem terms_consecutive {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (hgap : max_gap k s ≤ 1) :
    ∀ (i : ℕ) (h : i < k), s ⟨i, h⟩ = s ⟨0, by omega⟩ + i := by
  intro i
  induction i with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    have hn : n < k := by omega
    have hnk : n < k - 1 := by omega
    have hle : s ⟨n + 1, h⟩ - s ⟨n, hn⟩ ≤ 1 := by
      refine le_trans ?_ hgap
      exact Finset.le_sup (f := fun i : Fin (k - 1) =>
        s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ ⟨n, hnk⟩)
    have hlt : s ⟨n, hn⟩ < s ⟨n + 1, h⟩ := by
      apply hmono
      simp [Fin.lt_def]
    have hstep : s ⟨n + 1, h⟩ = s ⟨n, hn⟩ + 1 := by omega
    rw [hstep, ih hn]
    omega

/-- **`gap_at_least_two`, rational form.** The ℝ-valued statement in 287.lean follows
from this by injectivity of the cast ℚ → ℝ. -/
theorem gap_at_least_two_rat {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    2 ≤ max_gap k s := by
  by_contra hcon
  push_neg at hcon
  have hgap : max_gap k s ≤ 1 := by omega
  have hterm := terms_consecutive hk s hmono hgap
  set a := s ⟨0, by omega⟩ with ha
  -- the sum over Fin k is the sum over the block [a, a+k-1]
  have hrw : ∑ i : Fin k, ((s i : ℚ))⁻¹ = ∑ i ∈ Finset.range k, ((a + i : ℕ) : ℚ)⁻¹ := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => ((a + n : ℕ) : ℚ)⁻¹) k]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hterm i.val i.isLt]
  have hIcc : ∑ n ∈ Finset.Icc a (a + k - 1), G n
      = ∑ i ∈ Finset.range k, ((a + i : ℕ) : ℚ)⁻¹ := by
    have hIcoIcc : Finset.Icc a (a + k - 1) = Finset.Ico a (a + k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcoIcc, Finset.sum_Ico_eq_sum_range]
    have : a + k - a = k := by omega
    rw [this]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact G_eq (by omega)
  have hne := interval_sum_inv_ne_one (a := a) (b := a + k - 1) (by omega) (by omega)
  rw [hIcc, ← hrw, hsum] at hne
  exact hne rfl


/-! ### The ℝ → ℚ bridge, giving the statement shape used in 287.lean. -/

/-- ℚ → ℝ casts distribute over a finite sum. Proved by induction so it depends only
on `Rat.cast_add`; this Mathlib has neither `Rat.cast_sum` nor `Rat.castHom`, and
push_cast / simp / norm_cast all stall on this goal. -/
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

/-- **`erdos_287.variants.gap_at_least_two`** — the statement shape of the upstream
declaration, which is tagged `research solved` but ships as a bare `sorry`. -/
theorem gap_at_least_two {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, 1 / (s i : ℝ) = 1) :
    2 ≤ max_gap k s :=
  gap_at_least_two_rat hk s hmono h1 (sum_rat_of_sum_real s hsum)

/-- The upstream binder shape, verbatim from 287.lean (∀-form, anonymous `2 ≤ k`
hypothesis), so the match is exact rather than merely logically equivalent. -/
theorem gap_at_least_two_upstream_shape :
    ∀ (k : ℕ) (_ : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s :=
  fun _ hk s hm h1 hs => gap_at_least_two hk s hm h1 hs

#print axioms interval_sum_inv_ne_one
#print axioms gap_at_least_two_rat
#print axioms gap_at_least_two
#print axioms gap_at_least_two_upstream_shape

end Kurschak
