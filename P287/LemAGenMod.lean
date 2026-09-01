/- LEMMA A′ IN GENERAL: any multiplier window {p, 2p, …, tp}.

`lemA_two` and `lemA_four` were the windows t = 2 and t = 4, each proved by its own
case analysis.  This subsumes both, for every t at once, with no case analysis at
all — the denominator-clearing argument never needed the window to be fixed.

Setup: p prime, T a finite set of positive integers whose p-divisible elements all
have the form m·p with 1 ≤ m ≤ t, at least one of them present.  Put
L = t! (any common multiple of 1..t works; t! keeps the Lean trivial — the sharp
choice lcm(1,…,t) ≈ e^t would give the tighter threshold t ≲ ln p rather than
t ≲ ln p / ln ln p).  For n = m·p in the p-part, L·p/n = L/m is an INTEGER (m ∣ L), so
the p-part equals k/(L·p) with

        k = Σ L/m,      0 < k ≤ |A|·L ≤ t·L.

Hence if p > t·L, then p divides neither k nor L, the p-part has valuation −1, and
by ultrametricity the whole sum has valuation −1 ≠ 0 = v_p(1).

Side condition p > t·t!.  With lcm(1,…,t) in place of t! this is exactly the
A(M) ≈ ln M threshold measured in attempts/008-conditional/window.py.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Factorial.Basic

namespace LemAGen

open Finset

variable {p : ℕ}

theorem val_add_of_neg [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hx : padicValRat p x < 0) (hy : 0 ≤ padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

theorem val_sum_nonneg [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ}
    (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    0 ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, 0 ≤ padicValRat p (f n) := fun n hn =>
        hval n (mem_insert_of_mem hn)
      have hsum := ih hpos' hval'
      rw [Finset.sum_insert ha]
      rcases Finset.eq_empty_or_nonempty B with rfl | hB
      · simpa using hval a (mem_insert_self a _)
      · have hBpos : 0 < ∑ n ∈ B, f n := Finset.sum_pos hpos' hB
        have htot : f a + ∑ n ∈ B, f n ≠ 0 :=
          ne_of_gt (add_pos (hpos a (mem_insert_self a _)) hBpos)
        exact le_trans (le_min (hval a (mem_insert_self a _)) hsum)
          (padicValRat.min_le_padicValRat_add htot)

theorem sum_ne_one_of_val_neg [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n) (hA : A.Nonempty)
    (hAval : padicValRat p (∑ n ∈ A, f n) < 0)
    (hBval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    (∑ n ∈ A, f n) + (∑ n ∈ B, f n) ≠ 1 := by
  classical
  have hApos' : 0 < ∑ n ∈ A, f n := Finset.sum_pos hApos hA
  rcases Finset.eq_empty_or_nonempty B with rfl | hB
  · simp only [Finset.sum_empty, add_zero]
    intro h
    rw [h] at hAval
    simp only [padicValRat.one] at hAval
    omega
  · have hBpos' : 0 < ∑ n ∈ B, f n := Finset.sum_pos hBpos hB
    have hval := val_add_of_neg (p := p) (ne_of_gt hApos') (ne_of_gt hBpos')
      (ne_of_gt (add_pos hApos' hBpos')) hAval (val_sum_nonneg hBpos hBval)
    intro h
    rw [h] at hval
    simp only [padicValRat.one] at hval
    omega

theorem val_frac [Fact (Nat.Prime p)] {a b : ℕ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hap : ¬ p ∣ a) (hbp : ¬ p ∣ b) :
    padicValRat p ((a : ℚ) / ((b : ℚ) * (p : ℚ))) = -1 := by
  have hpp : (0:ℚ) < p := by positivity
  have hane : (a : ℚ) ≠ 0 := by positivity
  have hbne : (b : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div hane (by positivity), padicValRat.mul hbne (ne_of_gt hpp),
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hap, padicValNat.eq_zero_of_not_dvd hbp,
      padicValNat.self hp]
  simp

/-- **Lemma A′, general window.** -/
theorem lemA_gen {t : ℕ} [Fact (Nat.Prime p)] (ht : 1 ≤ t)
    (hp : t * (Nat.factorial t) < p)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  set L := Nat.factorial t with hLdef
  have hLpos : 0 < L := Nat.factorial_pos t
  have hp1 : 1 < p := by
    have : 1 ≤ t * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hppos : 0 < p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast hppos
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAcases : ∀ n ∈ A, ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p := by
    intro n hn
    obtain ⟨hnT, hnd⟩ := Finset.mem_filter.mp hn
    exact hdvd n hnT hnd
  -- every element of A lies in the image of {1,…,t} under (· * p)
  have hAsub : A ⊆ (Finset.Icc 1 t).image (fun m => m * p) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmt⟩, rfl⟩
  have hcard : A.card ≤ t := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    simp [Nat.card_Icc]
  -- the cleared weight of each element
  have hw : ∀ n ∈ A, 0 < L * p / n ∧ L * p / n ≤ L
      ∧ ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    have hmL : m ∣ L := Nat.dvd_factorial hm1 hmt
    have hmpos : 0 < m := hm1
    have hdiv : L * p / (m * p) = L / m := by
      rw [Nat.mul_div_mul_right _ _ hppos]
    have hLm : L / m * m = L := Nat.div_mul_cancel hmL
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiv]; exact Nat.div_pos (Nat.le_of_dvd hLpos hmL) hmpos
    · rw [hdiv]; exact Nat.div_le_self _ _
    · rw [hdiv]
      have hmQ : (0:ℚ) < m := by exact_mod_cast hmpos
      have hcast : ((L / m : ℕ) : ℚ) = (L:ℚ) / (m:ℚ) := by
        rw [eq_div_iff (ne_of_gt hmQ)]
        exact_mod_cast hLm
      rw [hcast]
      have hLQ : (0:ℚ) < L := by exact_mod_cast hLpos
      push_cast
      field_simp
  have hterm : ∀ n ∈ A, ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) :=
    fun n hn => (hw n hn).2.2
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (L * p / n) : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  set k := ∑ n ∈ A, (L * p / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos (fun n hn => (hw n hn).1) hAne
  have hkle : k ≤ t * L := by
    calc k ≤ A.card * L := Finset.sum_le_card_nsmul A _ L (fun n hn => (hw n hn).2.1)
      _ ≤ t * L := Nat.mul_le_mul_right _ hcard
  have hpk : ¬ p ∣ k := by
    intro h; have := Nat.le_of_dvd hkpos h; omega
  have hpL : ¬ p ∣ L := by
    intro h
    have := Nat.le_of_dvd hLpos h
    have : 1 * L ≤ t * L := Nat.mul_le_mul_right _ ht
    omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    rw [hsumA, val_frac hp1 hkpos hLpos hpk hpL]
    norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval


end LemAGen
