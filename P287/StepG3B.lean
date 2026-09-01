/- The gaps-≤3 rung that the two older exclusion rules could not build.

`StepG3.step_gap4` needs THREE consecutive forced-out integers, each excluded by
`StepAB.notTermA` (a large prime factor). On the two previously-verified rules —
`lemA_sharp` and the narrow `notTermB` (`q^e` itself, when `M < 2q^e`) — such a
triple exists for every `M ∈ [86, 385]` EXCEPT the eighteen values `M ∈ [365, 382]`,
and for those there is no triple anywhere in `[2, M]`, so no sharpening of the
interior bound can help.

`RuleBGen.ruleB_sharp` supplies the missing exclusion. Exactly one instance is
needed, `(q, e, t) = (13, 2, 2)`: for `M < 3·169` the integers with `v₁₃ = 2` are
`169` and `338`, and `2·lcm(1,2) = 4 < 13`, so neither is a term. That makes
`{337, 338, 339}` a forced-out triple:

    337 = 1·337   prime, t = 1   (rule A)
    338 = 2·13²                  (rule B, general t — the new ingredient)
    339 = 3·113   t = 3          (rule A)

The binding constraint is `M < (3+1)·113 = 452` from 339, so this single rung
covers `M ∈ [340, 451]` — comfortably containing the [365, 382] hole and
overlapping `LadderG3.g3_gap`'s range, which starts at 386.
-/
import P287.StepG3
import P287.RuleBGen
import Mathlib.Tactic.NormNum.Prime

namespace StepG3B

/-- **Rule B in sequence form.** If `n = a·q^e` with `1 ≤ a ≤ t < q`, `e` is the
largest `q`-adic valuation available below `M`, and `t·lcm(1..t) < q`, then `n` is
not a term. (`a < q` is automatic: `a ≤ t ≤ t·lcm(1..t) < q`.) -/
theorem notTermBGen {q e t a n : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e) (ht : 1 ≤ t)
    (hqt : t * LemAGen.lcmUpto t < q)
    (ha1 : 1 ≤ a) (hat : a ≤ t) (hn : n = a * q ^ e)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < (t + 1) * q ^ e)
    (hhi2 : s ⟨k - 1, by omega⟩ < q ^ (e + 1)) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := StepAB.setup hk s hmono h1 hsum
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  intro i hi
  have hLpos := LemAGen.lcmUpto_pos t
  have haq : a < q := by
    have h2 : t * 1 ≤ t * LemAGen.lcmUpto t := Nat.mul_le_mul_left _ hLpos
    omega
  have hqa : ¬ q ∣ a := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hqepos : 0 < q ^ e := pow_pos hq.pos e
  -- `v_q(n) = e` exactly, since `q ∤ a`
  have hpow : padicValNat q (q ^ e) = e := by
    first
      | exact padicValNat.prime_pow_self q e
      | exact padicValNat.prime_pow e
      | simp
  have hval : padicValNat q n = e := by
    rw [hn, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd hqa, hpow]
    omega
  -- the three hypotheses of `ruleB_sharp`
  have hmax : ∀ m ∈ Finset.image s Finset.univ, padicValNat q m ≤ e := by
    intro m hm
    by_contra hc
    push_neg at hc
    have hdvd : q ^ (e + 1) ∣ m :=
      dvd_trans (pow_dvd_pow q (by omega)) pow_padicValNat_dvd
    have h3 := Nat.le_of_dvd (hTpos m hm) hdvd
    have h4 := hTle m hm
    omega
  have hstruct : ∀ m ∈ Finset.image s Finset.univ, padicValNat q m = e →
      ∃ u, 1 ≤ u ∧ u ≤ t ∧ m = u * q ^ e := by
    intro m hm hv
    have hdvd : q ^ e ∣ m := hv ▸ pow_padicValNat_dvd
    obtain ⟨u, hu⟩ := hdvd
    have hmpos := hTpos m hm
    have hmu : m = u * q ^ e := by rw [hu]; ring
    refine ⟨u, ?_, ?_, hmu⟩
    · rcases Nat.eq_zero_or_pos u with rfl | h
      · rw [hu] at hmpos; simp at hmpos
      · exact h
    · by_contra hc
      push_neg at hc
      have h5 : (t + 1) * q ^ e ≤ u * q ^ e := Nat.mul_le_mul_right _ (by omega)
      have h6 := hTle m hm
      omega
  have hex : ∃ m ∈ Finset.image s Finset.univ, padicValNat q m = e := by
    refine ⟨n, ?_, hval⟩
    rw [← hi]
    exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  exact RuleBGen.ruleB_sharp ht he hqt hTpos hmax hstruct hex hsumT

/-- **The [340, 451] rung**, built on the triple `{337, 338, 339}`. -/
theorem g3_low {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 340 ≤ s ⟨k - 1, by omega⟩) (hhi : s ⟨k - 1, by omega⟩ ≤ 451) :
    4 ≤ PCI.max_gap k s := by
  have hl2 : LemAGen.lcmUpto 2 = 2 := by
    first | rfl | decide | (norm_num [LemAGen.lcmUpto, Nat.lcm]) | (simp [LemAGen.lcmUpto, Nat.lcm])
  have e0 := StepAB.notTermA (p := 337) (t := 1) (n := 337) (a := 1)
    (by norm_num) (by norm_num) (by norm_num [Nat.factorial]) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have e1 := notTermBGen (q := 13) (e := 2) (t := 2) (a := 2) (n := 338)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hl2]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) hk s hmono h1 hsum (by norm_num; omega) (by norm_num; omega)
  have e2 := StepAB.notTermA (p := 113) (t := 3) (n := 339) (a := 3)
    (by norm_num) (by norm_num) (by norm_num [Nat.factorial]) (by norm_num)
    hk s hmono h1 hsum (by omega)
  have hs0 : s ⟨0, by omega⟩ ≤ 337 := by
    have := Lower.lower hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

#print axioms notTermBGen
#print axioms g3_low

end StepG3B
