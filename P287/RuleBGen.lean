/- RULE B, GENERAL FORM: no term attains the maximal q-adic valuation `e`,
once the terms that could attain it are few enough.

`RuleB.ruleB` handles only the case where `q^e` is the UNIQUE integer in `[1,M]`
with `v_q = e` (which needs `M < 2q^e`), and concludes only that `q^e` itself is
not a term. That is the `t = 1` case of what is actually true.

In general, if `q^(e+1) > M` then the integers of `[1,M]` with `v_q = e` are
exactly `u·q^e` for `1 ≤ u ≤ t = ⌊M/q^e⌋`, and clearing denominators over the
sub-sum of those terms gives `k/(L·q^e)` with `0 < k ≤ t·L`. So `q > t·L` forces
`q ∤ k`, the sub-sum has valuation exactly `−e`, every other term has valuation
`≥ 1−e`, and the total cannot be the integer 1. NONE of the `u·q^e` is a term.

This is `LemAGen.lemA_param` with the base valuation shifted from 0 to `1−e`; the
shifted ultrametric helpers are already in `RuleB` (`val_add_of_lt`, `val_sum_ge`,
`sum_ne_one_of_val_lt`), which is why only the `A`-side argument is new here.

It is needed: on the two previously-verified rules alone (`lemA_sharp` and the
narrow `notTermB`) the gaps-≤3 argument has forced-out triples for every
`M ∈ [86, 385]` EXCEPT `M ∈ [365, 382]`, and for those 18 values there is no
triple anywhere in `[2,M]`. Every one of them is closed by the single instance
`q = 13`, `e = 2`, `t = 2` — the terms with `v₁₃ = 2` are `169` and `338`, and
`2·lcm(1,2) = 4 < 13`.
-/
import P287.RuleB
import P287.LemAParam

namespace RuleBGen

open Finset

variable {q : ℕ}

/-- `v_q(a / (b·q^e)) = −e` when `q` divides neither `a` nor `b`. -/
theorem val_frac_pow [Fact (Nat.Prime q)] {a b e : ℕ} (hq : 1 < q)
    (ha : 0 < a) (hb : 0 < b) (haq : ¬ q ∣ a) (hbq : ¬ q ∣ b) :
    padicValRat q ((a : ℚ) / ((b : ℚ) * ((q ^ e : ℕ) : ℚ))) = -(e : ℤ) := by
  have hqp : (0:ℚ) < q := by positivity
  have hqe : (0:ℚ) < ((q ^ e : ℕ) : ℚ) := by
    have : 0 < q ^ e := pow_pos (by omega) e
    exact_mod_cast this
  have hane : (a : ℚ) ≠ 0 := by positivity
  have hbne : (b : ℚ) ≠ 0 := by positivity
  have hpow : padicValNat q (q ^ e) = e := by
    first
      | exact padicValNat.prime_pow_self q e
      | exact padicValNat.prime_pow e
      | simp
  rw [padicValRat.div hane (by positivity), padicValRat.mul hbne (ne_of_gt hqe),
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd haq, padicValNat.eq_zero_of_not_dvd hbq, hpow]
  simp

/-- **Rule B, general form.** `L` is any common multiple of `1, …, t`. -/
theorem ruleB_param {t L e : ℕ} [Fact (Nat.Prime q)] (ht : 1 ≤ t) (he : 1 ≤ e)
    (hLpos : 0 < L) (hLdvd : ∀ m, 1 ≤ m → m ≤ t → m ∣ L)
    (hq : t * L < q)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    (hstruct : ∀ n ∈ T, padicValNat q n = e → ∃ u, 1 ≤ u ∧ u ≤ t ∧ n = u * q ^ e)
    (hex : ∃ n ∈ T, padicValNat q n = e) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hq1 : 1 < q := by
    have : 1 ≤ t * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hqepos : 0 < q ^ e := pow_pos (by omega) e
  have hqeQ : (0:ℚ) < ((q ^ e : ℕ) : ℚ) := by exact_mod_cast hqepos
  set A := T.filter (fun n => padicValNat q n = e) with hAdef
  set B := T.filter (fun n => ¬ padicValNat q n = e) with hBdef
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
  -- every non-exceptional term has valuation ≥ 1 − e, strictly above −e
  have hBval : ∀ n ∈ B, -(e : ℤ) < padicValRat q ((n : ℚ))⁻¹ := by
    intro n hn
    obtain ⟨hnT, hne⟩ := Finset.mem_filter.mp hn
    have hle := hmax n hnT
    have : padicValNat q n < e := by omega
    rw [padicValRat.inv, padicValRat.of_nat]
    omega
  obtain ⟨n0, hn0T, hn0v⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0v⟩⟩
  have hAcases : ∀ n ∈ A, ∃ u, 1 ≤ u ∧ u ≤ t ∧ n = u * q ^ e := by
    intro n hn
    obtain ⟨hnT, hnv⟩ := Finset.mem_filter.mp hn
    exact hstruct n hnT hnv
  have hAsub : A ⊆ (Finset.Icc 1 t).image (fun u => u * q ^ e) := by
    intro n hn
    obtain ⟨u, hu1, hut, rfl⟩ := hAcases n hn
    exact Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr ⟨hu1, hut⟩, rfl⟩
  have hcard : A.card ≤ t := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    simp [Nat.card_Icc]
  -- clearing denominators: the weight of `u·q^e` is `L/u ≤ L`
  have hw : ∀ n ∈ A, 0 < L * q ^ e / n ∧ L * q ^ e / n ≤ L
      ∧ ((n : ℚ))⁻¹ = ((L * q ^ e / n : ℕ) : ℚ) / ((L:ℚ) * ((q ^ e : ℕ) : ℚ)) := by
    intro n hn
    obtain ⟨u, hu1, hut, rfl⟩ := hAcases n hn
    have huL : u ∣ L := hLdvd u hu1 hut
    have hupos : 0 < u := hu1
    have hdiv : L * q ^ e / (u * q ^ e) = L / u := by
      rw [Nat.mul_div_mul_right _ _ hqepos]
    have hLu : L / u * u = L := Nat.div_mul_cancel huL
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiv]; exact Nat.div_pos (Nat.le_of_dvd hLpos huL) hupos
    · rw [hdiv]; exact Nat.div_le_self _ _
    · rw [hdiv]
      have huQ : (0:ℚ) < u := by exact_mod_cast hupos
      have hcast : ((L / u : ℕ) : ℚ) = (L:ℚ) / (u:ℚ) := by
        rw [eq_div_iff (ne_of_gt huQ)]
        exact_mod_cast hLu
      rw [hcast]
      have hLQ : (0:ℚ) < L := by exact_mod_cast hLpos
      push_cast
      field_simp
  have hterm : ∀ n ∈ A, ((n : ℚ))⁻¹
      = ((L * q ^ e / n : ℕ) : ℚ) / ((L:ℚ) * ((q ^ e : ℕ) : ℚ)) :=
    fun n hn => (hw n hn).2.2
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (L * q ^ e / n) : ℕ) : ℚ) / ((L:ℚ) * ((q ^ e : ℕ) : ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  set k := ∑ n ∈ A, (L * q ^ e / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos (fun n hn => (hw n hn).1) hAne
  have hkle : k ≤ t * L := by
    calc k ≤ A.card * L := Finset.sum_le_card_nsmul A _ L (fun n hn => (hw n hn).2.1)
      _ ≤ t * L := Nat.mul_le_mul_right _ hcard
  have hqk : ¬ q ∣ k := by
    intro h; have := Nat.le_of_dvd hkpos h; omega
  have hqL : ¬ q ∣ L := by
    intro h
    have h1 := Nat.le_of_dvd hLpos h
    have h2 : 1 * L ≤ t * L := Nat.mul_le_mul_right _ ht
    omega
  have hAval : padicValRat q (∑ n ∈ A, ((n : ℚ))⁻¹) = -(e : ℤ) := by
    rw [hsumA]
    exact val_frac_pow hq1 hkpos hLpos hqk hqL
  rw [← hsplit]
  exact RuleB.sum_ne_one_of_val_lt hApos hBpos hAne hAval (by omega) hBval

/-- **Rule B, sharp form**: `L = lcm(1, …, t)`, the strongest choice. -/
theorem ruleB_sharp {t e : ℕ} [Fact (Nat.Prime q)] (ht : 1 ≤ t) (he : 1 ≤ e)
    (hq : t * LemAGen.lcmUpto t < q)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    (hstruct : ∀ n ∈ T, padicValNat q n = e → ∃ u, 1 ≤ u ∧ u ≤ t ∧ n = u * q ^ e)
    (hex : ∃ n ∈ T, padicValNat q n = e) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 :=
  ruleB_param ht he (LemAGen.lcmUpto_pos t)
    (fun m h1 h2 => LemAGen.dvd_lcmUpto h1 t h2) hq hTpos hmax hstruct hex

#print axioms val_frac_pow
#print axioms ruleB_param
#print axioms ruleB_sharp

end RuleBGen
