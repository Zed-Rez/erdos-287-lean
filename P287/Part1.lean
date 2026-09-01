/- ASSEMBLY: `erdos_287.variants.prime_conjecture_implies`, kernel-clean.

Given the prime conjecture (for all large N there is a prime P in [N,2N] with
(P+1)/2 prime), every Egyptian fraction representation of 1 with enough terms has
a gap of at least 3.

Proof.  Let M = s(k-1) and N = M/2.  The hypothesis gives a prime P in [N,2N]
with Q = (P+1)/2 prime.
  * P >= M/2 gives 3P > M, so the multiples of P that are <= M are exactly P and
    2P: `lemA_two` then says NO element is divisible by P, in particular P is not
    a term.
  * Q >= M/4 gives 5Q > M, so the multiples of Q that are <= M lie in
    {Q,2Q,3Q,4Q}: `lemA_four` says no element is divisible by Q, and 2Q = P+1, so
    P+1 is not a term either.
  * n_1 <= M/2 <= P by the counting bound, and P < M because M itself IS a term
    while P is not.  So P and P+1 both lie strictly inside the range.
  * `gap_three_of_two_missing` turns two consecutive missing values into a gap >= 3.

No analysis anywhere: the only inequalities used are counting and divisibility.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr

namespace PCI

open Finset
variable {p : ℕ}


open Finset

variable {p : ℕ}

/-- A term of negative valuation dominates one of non-negative valuation. -/
theorem val_add_of_neg [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hx : padicValRat p x < 0) (hy : 0 ≤ padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

/-- A finite sum of positive rationals of non-negative valuation has non-negative
valuation. -/
theorem val_sum_nonneg [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ}
    (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    0 ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, 0 ≤ padicValRat p (f n) := fun n hn => hval n (mem_insert_of_mem hn)
      have hsum := ih hpos' hval'
      rw [Finset.sum_insert ha]
      rcases Finset.eq_empty_or_nonempty B with rfl | hB
      · simpa using hval a (mem_insert_self a _)
      · have hBpos : 0 < ∑ n ∈ B, f n := Finset.sum_pos hpos' hB
        have hane : f a ≠ 0 := ne_of_gt (hpos a (mem_insert_self a _))
        have hbne : (∑ n ∈ B, f n) ≠ 0 := ne_of_gt hBpos
        have htot : f a + ∑ n ∈ B, f n ≠ 0 :=
          ne_of_gt (add_pos (hpos a (mem_insert_self a _)) hBpos)
        exact le_trans (le_min (hval a (mem_insert_self a _)) hsum)
          (padicValRat.min_le_padicValRat_add htot)

/-- **Lemma A′, split form.** If the p-divisible part of the sum has valuation −1
and the rest has valuation ≥ 0, the whole sum has valuation −1, hence is not 1. -/
theorem sum_ne_one_of_val_neg [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n)
    (hA : A.Nonempty)
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


/-- ν_p(a / (b·p)) = −1 when p divides neither a nor b. -/
theorem val_frac [Fact (Nat.Prime p)] {a b : ℕ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hap : ¬ p ∣ a) (hbp : ¬ p ∣ b) :
    padicValRat p ((a : ℚ) / ((b : ℚ) * (p : ℚ))) = -1 := by
  have hpp : (0:ℚ) < p := by positivity
  have hane : (a : ℚ) ≠ 0 := by positivity
  have hbne : (b : ℚ) ≠ 0 := by positivity
  have hpne : (p : ℚ) ≠ 0 := ne_of_gt hpp
  rw [padicValRat.div hane (by positivity), padicValRat.mul hbne hpne,
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hap, padicValNat.eq_zero_of_not_dvd hbp,
      padicValNat.self hp]
  simp

/-- **Lemma A′ for the window {p, 2p}.** If p > 3 and every element of `T`
divisible by p is p or 2p, and at least one such element is present, then the
reciprocals of `T` do not sum to 1.

This is exactly the instance `prime_conjecture_implies` needs for the prime
p ∈ (M/3, M], whose only multiples in the window are p and 2p. -/
theorem lemA_two [Fact (Nat.Prime p)] (hp : 3 < p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → n = p ∨ n = 2 * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hp1 : 1 < p := by omega
  have hppos : 0 < p := by omega
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  -- positivity on both parts
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
  -- B has non-negative valuation termwise
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  -- A is nonempty and contained in {p, 2p}
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAsub : A ⊆ ({p, 2 * p} : Finset ℕ) := by
    intro x hx
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hx
    rcases hdvd x hxT hxd with rfl | rfl <;> simp
  -- evaluate the p-part: it is 1/p, 1/(2p) or 3/(2p), all of valuation −1
  have hne2 : p ≠ 2 * p := by omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    have hcases : A = {p} ∨ A = {2 * p} ∨ A = {p, 2 * p} := by
      by_cases h1 : p ∈ A <;> by_cases h2 : 2 * p ∈ A
      · exact Or.inr (Or.inr (Finset.Subset.antisymm hAsub (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)))
      · refine Or.inl (Finset.Subset.antisymm ?_ (by simpa using h1))
        intro x hx
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl
        · rfl
        · exact absurd hx h2
      · refine Or.inr (Or.inl (Finset.Subset.antisymm ?_ (by simpa using h2)))
        intro x hx
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl
        · exact absurd hx h1
        · rfl
      · obtain ⟨x, hx⟩ := hAne
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · exact absurd hx h1
        · exact absurd hx h2
    have hpd : ¬ p ∣ 1 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    have hpd2 : ¬ p ∣ 2 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    have hpd3 : ¬ p ∣ 3 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    rcases hcases with h | h | h
    · rw [h, Finset.sum_singleton]
      have : ((p : ℚ))⁻¹ = ((1 : ℕ) : ℚ) / (((1 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast; ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd hpd]
      norm_num
    · rw [h, Finset.sum_singleton]
      have hpq : (0:ℚ) < p := by positivity
      have : ((((2 * p : ℕ)) : ℚ))⁻¹ = ((1 : ℕ) : ℚ) / (((2 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast; ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd hpd2]
      norm_num
    · rw [h, Finset.sum_pair hne2]
      have hpq : (0:ℚ) < p := by positivity
      have : ((p : ℚ))⁻¹ + ((((2 * p : ℕ)) : ℚ))⁻¹
          = ((3 : ℕ) : ℚ) / (((2 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast
        field_simp
        ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd3 hpd2]
      norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval


/-- **Lemma A′ for the window {p,2p,3p,4p}** — the instance needed for
q = (P+1)/2 in `prime_conjecture_implies`.

The 16 subsets are never enumerated. Clearing denominators by 12p turns each term
into an integer 12/m ∈ {12,6,4,3}, so the p-part equals k/(12p) with k a positive
integer; k ≤ 4·12 = 48 < p because |A| ≤ 4 and every weight is ≤ 12. Then
`val_frac` gives valuation −1. -/
theorem lemA_four [Fact (Nat.Prime p)] (hp : 48 < p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → n = p ∨ n = 2 * p ∨ n = 3 * p ∨ n = 4 * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hp1 : 1 < p := by omega
  have hppos : 0 < p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast hppos
  have hpne : (p:ℚ) ≠ 0 := ne_of_gt hpQ
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
  have hAsub : A ⊆ ({p, 2 * p, 3 * p, 4 * p} : Finset ℕ) := by
    intro x hx
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hx
    rcases hdvd x hxT hxd with rfl | rfl | rfl | rfl <;> simp
  -- membership in A pins n to one of four values
  have hAcases : ∀ n ∈ A, n = p ∨ n = 2*p ∨ n = 3*p ∨ n = 4*p := by
    intro n hn
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hn
    exact hdvd n hxT hxd
  -- weights after clearing denominators by 12p; `rw [h]` not `rfl`, so that the
  -- substitution cannot rename the prime `p` itself
  have hw : ∀ x ∈ A, 12 * p / x = 12 ∨ 12 * p / x = 6 ∨ 12 * p / x = 4
      ∨ 12 * p / x = 3 := by
    intro x hx
    rcases hAcases x hx with h | h | h | h
    · exact Or.inl (by rw [h]; exact Nat.mul_div_cancel _ hppos)
    · exact Or.inr (Or.inl (by
        rw [h, show 12 * p = 6 * (2 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)))
    · exact Or.inr (Or.inr (Or.inl (by
        rw [h, show 12 * p = 4 * (3 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega))))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [h, show 12 * p = 3 * (4 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega))))
  have hterm : ∀ x ∈ A, ((x : ℚ))⁻¹ = ((12 * p / x : ℕ) : ℚ) / (12 * (p:ℚ)) := by
    intro x hx
    have hxpos : 0 < x := hTpos x (Finset.mem_of_mem_filter x hx)
    have hxQ : (0:ℚ) < x := by exact_mod_cast hxpos
    rcases hAcases x hx with h | h | h | h
    · rw [h, show (12 * p / p : ℕ) = 12 from Nat.mul_div_cancel _ hppos]
      push_cast; field_simp
    · rw [h, show (12 * p / (2 * p) : ℕ) = 6 from by
        rw [show 12 * p = 6 * (2 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
    · rw [h, show (12 * p / (3 * p) : ℕ) = 4 from by
        rw [show 12 * p = 4 * (3 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
    · rw [h, show (12 * p / (4 * p) : ℕ) = 3 from by
        rw [show 12 * p = 3 * (4 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (12 * p / n) : ℕ) : ℚ) / (12 * (p:ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  have hwpos : ∀ x ∈ A, 0 < 12 * p / x := by
    intro x hx; rcases hw x hx with h | h | h | h <;> omega
  have hwle : ∀ x ∈ A, 12 * p / x ≤ 12 := by
    intro x hx; rcases hw x hx with h | h | h | h <;> omega
  set k := ∑ n ∈ A, (12 * p / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos hwpos hAne
  have hcard : A.card ≤ 4 := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by
      refine Nat.succ_le_succ ?_
      exact le_trans (Finset.card_insert_le _ _) (by
        refine Nat.succ_le_succ ?_
        exact le_trans (Finset.card_insert_le _ _) (by simp)))
  have hkle : k ≤ 48 := by
    calc k ≤ A.card * 12 := Finset.sum_le_card_nsmul A _ 12 hwle
      _ ≤ 4 * 12 := by exact Nat.mul_le_mul_right _ hcard
      _ = 48 := by norm_num
  have hpk : ¬ p ∣ k := by
    intro h
    have := Nat.le_of_dvd hkpos h
    omega
  have hp12 : ¬ p ∣ 12 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    rw [hsumA]
    have : ((k:ℕ) : ℚ) / (12 * (p:ℚ)) = ((k:ℕ) : ℚ) / (((12:ℕ):ℚ) * (p:ℚ)) := by
      push_cast; ring
    rw [this, val_frac hp1 hkpos (by norm_num) hpk hp12]
    norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval



/-- `max_gap` byte-identical to FormalConjectures/ErdosProblems/287.lean. -/
def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

theorem gap_three_of_two_missing {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    {m : ℕ}
    (hlo : s ⟨0, by omega⟩ ≤ m) (hhi : m + 1 ≤ s ⟨k - 1, by omega⟩)
    (hm : ∀ i, s i ≠ m) (hm1 : ∀ i, s i ≠ m + 1) :
    3 ≤ max_gap k s := by
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
  have hj'ge2 : m + 2 ≤ s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ := by
    have h1 := hm ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    have h2 := hm1 ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
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

/-- **n₁ ≤ M/2, by counting — no analysis.**
1 = Σ 1/sᵢ < k/s₀ strictly (every later term is smaller, and k ≥ 2), so s₀ < k;
and strict monotonicity gives s(k-1) ≥ s₀ + (k-1). Hence 2·s₀ ≤ s(k-1). -/
theorem two_mul_first_le_last {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (hpos : 0 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    2 * s ⟨0, by omega⟩ ≤ s ⟨k - 1, by omega⟩ := by
  classical
  have h0 : (0:ℚ) < (s ⟨0, by omega⟩ : ℚ) := by exact_mod_cast hpos
  -- strict monotonicity forces linear growth
  have hgrow : ∀ (i : ℕ) (h : i < k), s ⟨0, by omega⟩ + i ≤ s ⟨i, h⟩ := by
    intro i
    induction i with
    | zero => intro h; simp
    | succ n ih =>
        intro h
        have hn : n < k := by omega
        have hstep : s ⟨n, hn⟩ < s ⟨n + 1, h⟩ := by
          apply hmono; simp [Fin.lt_def]
        have := ih hn
        omega
  -- every term is ≤ 1/s₀, and the term at index 1 is strictly smaller
  have hle : ∀ i ∈ Finset.univ, ((s i : ℚ))⁻¹ ≤ ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    intro i _
    have hmono' : s ⟨0, by omega⟩ ≤ s i := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
        rw [this]
      · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
    have h1 : (0:ℚ) < (s i : ℚ) := by
      have : 0 < s i := lt_of_lt_of_le hpos hmono'
      exact_mod_cast this
    have : (s ⟨0, by omega⟩ : ℚ) ≤ (s i : ℚ) := by exact_mod_cast hmono'
    gcongr
  have hone : ∃ i ∈ Finset.univ, ((s i : ℚ))⁻¹ < ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    refine ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
    have hlt : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := by
      apply hmono; simp [Fin.lt_def]
    have h1 : (0:ℚ) < (s ⟨1, by omega⟩ : ℚ) := by
      have : 0 < s ⟨1, by omega⟩ := lt_trans hpos hlt
      exact_mod_cast this
    have : (s ⟨0, by omega⟩ : ℚ) < (s ⟨1, by omega⟩ : ℚ) := by exact_mod_cast hlt
    gcongr
  have hsumlt : (1:ℚ) < (k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    rw [← hsum]
    calc ∑ i : Fin k, ((s i : ℚ))⁻¹
        < ∑ _i : Fin k, ((s ⟨0, by omega⟩ : ℚ))⁻¹ := Finset.sum_lt_sum hle hone
      _ = (k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- hence s₀ < k
  have hs0k : s ⟨0, by omega⟩ < k := by
    have hkey : (s ⟨0, by omega⟩ : ℚ) < (k : ℚ) := by
      have h1 : (1:ℚ) * (s ⟨0, by omega⟩ : ℚ)
          < ((k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹) * (s ⟨0, by omega⟩ : ℚ) :=
        by exact mul_lt_mul_of_pos_right hsumlt h0
      rw [one_mul, inv_mul_cancel_right₀ (ne_of_gt h0)] at h1
      exact h1
    exact_mod_cast hkey
  have hlast := hgrow (k - 1) (by omega)
  omega


/-! ### helpers -/

/-- Strict monotonicity forces linear growth from the first term. -/
theorem growth {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s) :
    ∀ (i : ℕ) (h : i < k), s ⟨0, by omega⟩ + i ≤ s ⟨i, h⟩ := by
  intro i
  induction i with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      have hn : n < k := by omega
      have hstep : s ⟨n, hn⟩ < s ⟨n + 1, h⟩ := by apply hmono; simp [Fin.lt_def]
      have := ih hn
      omega


end PCI
