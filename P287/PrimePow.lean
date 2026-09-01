/- **No denominator has a large prime-power part.**

Three theorems about EVERY representation of `1` as a sum of distinct unit fractions — no gap
hypothesis, so they constrain the general Egyptian-fraction problem, not just #287.

The engine is a one-line consequence of `QLaw.qlaw` that had not been extracted:

* **`level_card_ne_one` — no `q`-adic level is a SINGLETON.** If exactly one denominator `n` has
  `v_q(n) = e` (with `e` bounding every valuation), the law reads `u⁻¹ = 0` in `ZMod q` for
  `u = n/q^e`. But `q ∤ u`, so `u` is a unit and `u⁻¹ ≠ 0`. Contradiction. Hence every level has
  size `0` or `≥ 2`; at the MAXIMAL level, which is nonempty by definition, the size is `≥ 2`.

  This is the exact general form of the classical "the largest power of 2 must be matched": at
  `q = 2` it is `MaxVal.maxlevel_card_even` weakened from parity to `≠ 1`, but unlike parity it
  holds verbatim at every prime, where the top level really can have ODD size.

Two consequences, each a statement about SPECIFIC integers:

* **`primePow_le_half` — `2·q^e ≤ M` whenever `q^e` divides a denominator.** So no denominator has
  a prime-power part in `(M/2, M]`. In particular no denominator IS a prime power `> M/2`, which
  strictly extends `Egyptian`'s "the largest denominator is never a prime power" from `M` to every
  denominator and every prime-power divisor.

* **`primePow_le_third` — `3·q^e ≤ M`, for every prime `q ≠ 3`.** Here the level has two
  candidates `{q^E, 2q^E}`; size `≠ 1` and size `≤ 2` force it to be EXACTLY the pair, and then the
  law says `1 + 2⁻¹ = 0`, i.e. `q ∣ 3`.

  **The exception at `q = 3` is real, not an artefact**: `1 = 1/2 + 1/3 + 1/6` has `M = 6` and
  `3 > M/3`, and it is precisely the configuration `Q3.q3_dichotomy` describes (`3^b` is a term iff
  `2·3^b` is). So the constant 3 cannot be raised without excluding `q = 3`, and the pair of
  theorems is sharp as stated.

At `e = 1` and large `q` these are far weaker than `Rough.term_smooth` (`P(n) ≤ M/431`); their
content is at `e ≥ 2`, where the mod-`q` law cannot see the size of `q^e` at all, and where `Rough`
says nothing.
-/
import P287.QLaw
import Mathlib.Tactic.LinearCombination

namespace PrimePow

open Finset

variable {q e : ℕ} [Fact (Nat.Prime q)]

/-- **No `q`-adic level is a singleton.** With `e` bounding every valuation, the set of terms at
level `e` has size `0` or `≥ 2` — never exactly one. -/
theorem level_card_ne_one (he : 1 ≤ e) {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e) :
    (T.filter (fun n => padicValNat q n = e)).card ≠ 1 := by
  classical
  intro hcard
  have hp : Nat.Prime q := Fact.out
  haveI : Fact (1 < q) := ⟨hp.one_lt⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hq := QLaw.qlaw (q := q) (e := e) he hTpos hsum hmax
  rw [ha, Finset.sum_singleton] at hq
  have haF : a ∈ T.filter (fun n => padicValNat q n = e) := by
    rw [ha]; exact Finset.mem_singleton_self a
  have haT : a ∈ T := Finset.mem_of_mem_filter a haF
  have hav : padicValNat q a = e := (Finset.mem_filter.mp haF).2
  obtain ⟨-, hnd⟩ := QLaw.cof_spec (q := q) (e := e) (hTpos a haT) hav
  have hcop : Nat.Coprime (QLaw.cof q e a) q :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  have hcm := ZMod.coe_mul_inv_eq_one (n := q) (QLaw.cof q e a) hcop
  rw [hq, mul_zero] at hcm
  exact zero_ne_one hcm

omit [Fact (Nat.Prime q)] in
/-- The maximal `q`-adic level of a nonempty finite set: an upper bound that is attained. -/
theorem exists_top_level {T : Finset ℕ} {n : ℕ} (hn : n ∈ T) :
    ∃ E, (∀ m ∈ T, padicValNat q m ≤ E) ∧ (∃ m ∈ T, padicValNat q m = E) ∧
      padicValNat q n ≤ E := by
  classical
  have hne : (T.image (fun m => padicValNat q m)).Nonempty :=
    ⟨padicValNat q n, Finset.mem_image_of_mem _ hn⟩
  refine ⟨(T.image (fun m => padicValNat q m)).max' hne, ?_, ?_, ?_⟩
  · intro m hm; exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hm)
  · obtain ⟨m, hm, hme⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    exact ⟨m, hm, hme⟩
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hn)

/-- **No denominator has a prime-power part exceeding `M/2`.** -/
theorem primePow_le_half {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    {M : ℕ} (hM : ∀ n ∈ T, n ≤ M)
    {n : ℕ} (hn : n ∈ T) (he : 1 ≤ e) (hdvd : q ^ e ∣ n) :
    2 * q ^ e ≤ M := by
  classical
  have hp : Nat.Prime q := Fact.out
  by_contra hcon
  push_neg at hcon
  obtain ⟨E, hmax, ⟨m₀, hm₀, hm₀E⟩, hnE⟩ := exists_top_level (q := q) hn
  have hn0 : n ≠ 0 := by have := hTpos n hn; omega
  have hen : e ≤ padicValNat q n := (padicValNat_dvd_iff_le hn0).mp hdvd
  have heE : e ≤ E := le_trans hen hnE
  have hpow : q ^ e ≤ q ^ E := Nat.pow_le_pow_right hp.pos heE
  have hlone : ∀ m ∈ T, padicValNat q m = E → m = q ^ E := by
    intro m hm hv
    obtain ⟨hmul, -⟩ := QLaw.cof_spec (q := q) (e := E) (hTpos m hm) hv
    have hmpos := hTpos m hm
    have hc1 : 1 ≤ QLaw.cof q E m := by
      rcases Nat.eq_zero_or_pos (QLaw.cof q E m) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    have hle := hM m hm
    have hc2 : QLaw.cof q E m < 2 := by
      by_contra hbig
      push_neg at hbig
      have hstep : 2 * q ^ E ≤ QLaw.cof q E m * q ^ E := Nat.mul_le_mul_right _ hbig
      rw [hmul] at hstep
      omega
    have hc : QLaw.cof q E m = 1 := by omega
    rw [hc, one_mul] at hmul
    omega
  have hE1 : 1 ≤ E := le_trans he heE
  exact QLaw.level_empty_of_lone (q := q) (e := E) hE1 hTpos hsum hmax hlone m₀ hm₀ hm₀E

/-- **No denominator has a prime-power part exceeding `M/3`, at any prime other than 3.**
The exception at `q = 3` is genuine: `1 = 1/2 + 1/3 + 1/6`. -/
theorem primePow_le_third {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    {M : ℕ} (hM : ∀ n ∈ T, n ≤ M) (hq3 : q ≠ 3)
    {n : ℕ} (hn : n ∈ T) (he : 1 ≤ e) (hdvd : q ^ e ∣ n) :
    3 * q ^ e ≤ M := by
  classical
  have hp : Nat.Prime q := Fact.out
  haveI : Fact (1 < q) := ⟨hp.one_lt⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨E, hmax, ⟨m₀, hm₀, hm₀E⟩, hnE⟩ := exists_top_level (q := q) hn
  have hn0 : n ≠ 0 := by have := hTpos n hn; omega
  have hen : e ≤ padicValNat q n := (padicValNat_dvd_iff_le hn0).mp hdvd
  have heE : e ≤ E := le_trans hen hnE
  have hpow : q ^ e ≤ q ^ E := Nat.pow_le_pow_right hp.pos heE
  have hE1 : 1 ≤ E := le_trans he heE
  have hqE : 0 < q ^ E := pow_pos hp.pos E
  -- every level-E term is `c · q^E` with `1 ≤ c ≤ 2` and `q ∤ c`
  have hcof : ∀ m ∈ T, padicValNat q m = E →
      QLaw.cof q E m * q ^ E = m ∧ ¬ q ∣ QLaw.cof q E m ∧
        1 ≤ QLaw.cof q E m ∧ QLaw.cof q E m < 3 := by
    intro m hm hv
    obtain ⟨hmul, hnd⟩ := QLaw.cof_spec (q := q) (e := E) (hTpos m hm) hv
    have hmpos := hTpos m hm
    have hc1 : 1 ≤ QLaw.cof q E m := by
      rcases Nat.eq_zero_or_pos (QLaw.cof q E m) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    have hle := hM m hm
    have hc3 : QLaw.cof q E m < 3 := by
      by_contra hbig
      push_neg at hbig
      have hstep : 3 * q ^ E ≤ QLaw.cof q E m * q ^ E := Nat.mul_le_mul_right _ hbig
      rw [hmul] at hstep
      omega
    exact ⟨hmul, hnd, hc1, hc3⟩
  -- q = 2: the cofactor is odd and < 3, hence 1, so the level is lone and therefore empty
  rcases eq_or_ne q 2 with hq2 | hq2
  · subst hq2
    refine QLaw.level_empty_of_lone (q := 2) (e := E) hE1 hTpos hsum hmax ?_ m₀ hm₀ hm₀E
    intro m hm hv
    obtain ⟨hmul, hnd, hc1, hc3⟩ := hcof m hm hv
    have hc : QLaw.cof 2 E m = 1 := by omega
    rw [hc, one_mul] at hmul
    omega
  -- q ≥ 5: the level is exactly {q^E, 2q^E}, and the law then forces q ∣ 3
  · set A := T.filter (fun m => padicValNat q m = E) with hAdef
    have hm₀A : m₀ ∈ A := Finset.mem_filter.mpr ⟨hm₀, hm₀E⟩
    have hsub : A ⊆ ({q ^ E, 2 * q ^ E} : Finset ℕ) := by
      intro m hm
      have hmT : m ∈ T := Finset.mem_of_mem_filter m hm
      have hmv : padicValNat q m = E := (Finset.mem_filter.mp hm).2
      obtain ⟨hmul, -, hc1, hc3⟩ := hcof m hmT hmv
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (by omega : QLaw.cof q E m = 1 ∨ QLaw.cof q E m = 2) with h | h <;>
        rw [h] at hmul
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hne : (q : ℕ) ^ E ≠ 2 * q ^ E := by omega
    have hpc : ({q ^ E, 2 * q ^ E} : Finset ℕ).card = 2 := Finset.card_pair hne
    have hcle : A.card ≤ 2 := by
      have := Finset.card_le_card hsub; omega
    have hc0 : A.card ≠ 0 := by
      intro h; exact absurd (Finset.card_eq_zero.mp h ▸ hm₀A) (by simp)
    have hc1 : A.card ≠ 1 := level_card_ne_one (q := q) (e := E) hE1 hTpos hsum hmax
    have hAeq : A = ({q ^ E, 2 * q ^ E} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hq := QLaw.qlaw (q := q) (e := E) hE1 hTpos hsum hmax
    rw [← hAdef, hAeq, Finset.sum_pair hne] at hq
    have hcofa : QLaw.cof q E (q ^ E) = 1 := Nat.div_self hqE
    have hcofb : QLaw.cof q E (2 * q ^ E) = 2 := Nat.mul_div_cancel 2 hqE
    rw [hcofa, hcofb] at hq
    -- `1⁻¹ = 1` and `2·2⁻¹ = 1` both come from `coe_mul_inv_eq_one`, so every inverse below
    -- carries the SAME `Inv` instance as the one `qlaw` produced.
    have hcop2 : Nat.Coprime 2 q :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hq2 h.symm)
    have hcop3 : Nat.Coprime 3 q :=
      (Nat.coprime_primes Nat.prime_three hp).mpr (fun h => hq3 h.symm)
    have hone := ZMod.coe_mul_inv_eq_one (n := q) 1 (Nat.coprime_one_left q)
    have hcm2 := ZMod.coe_mul_inv_eq_one (n := q) 2 hcop2
    have hcm3 := ZMod.coe_mul_inv_eq_one (n := q) 3 hcop3
    push_cast at hq hone hcm2 hcm3
    -- 1·x = 1, x + y = 0, 2·y = 1  ⟹  3 = 0
    have h3 : (3 : ZMod q) = 0 := by linear_combination (-2 : ZMod q) * hone + 2 * hq - hcm2
    rw [h3, zero_mul] at hcm3
    exact zero_ne_one hcm3

#print axioms level_card_ne_one
#print axioms primePow_le_half
#print axioms primePow_le_third

end PrimePow
