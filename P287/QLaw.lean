/- **The q-adic counting law: `Σ u⁻¹ ≡ 0 (mod q)` over the cofactors of the top `q`-level.**

`MaxVal.maxlevel_card_even` — the top 2-level has even size — is the case `q = 2` of a law that
holds at every prime. `Master.master` gives `q ∣ Σ L·q^e/n` over the level-`e` terms, but only
relative to a multiplier `L` the caller must supply, and the statement's content is invisible while
`L` is in it. Writing `n = u·q^e`, the summand is `L/u`, so the congruence is `L·Σ 1/u ≡ 0`; since
`q ∤ L`, `L` is a unit mod `q` and cancels:

    Σ_{u ∈ I} u⁻¹ = 0   in   ZMod q,        I = { n/q^e : n ∈ T, v_q(n) = e }.

No multiplier appears, and nothing has to be chosen. At `q = 2` every `u` is odd, so `u⁻¹ = 1` and
the law reads `#I ≡ 0 (mod 2)` — exactly the parity law. At odd `q` it is strictly more than a count:
the top level can and does have odd size (both occur in the exhaustive test set).

`e` need only be an UPPER BOUND on the valuations, inherited from `Master.master`, which is what lets
the law fire on a level that is empty.

Checked on two structurally unrelated families before formalising (`verified/080`): 10491/10491 on
the split-grown corpus, and 5465/5465 on the 199 exhaustive representations of 1 with denominators
`≤ 30`. Non-vacuous — deleting one cofactor from `I` breaks the congruence in 1515 of 1515 tested
cases — and the naive variant with `u` in place of `u⁻¹` fails in 26 cases of the exhaustive family.
-/
import P287.Master
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.BigOperators

namespace QLaw

open Finset

variable {q e : ℕ} [Fact (Nat.Prime q)]

/-- The cofactor of a level-`e` term. -/
def cof (q e n : ℕ) : ℕ := n / q ^ e

/-- A level-`e` term is `cof · q^e`, and `q` does not divide the cofactor. -/
theorem cof_spec {n : ℕ} (hn : 0 < n) (hv : padicValNat q n = e) :
    cof q e n * q ^ e = n ∧ ¬ q ∣ cof q e n := by
  have hp : Nat.Prime q := Fact.out
  have hdvd : q ^ e ∣ n := hv ▸ pow_padicValNat_dvd
  have hmul : cof q e n * q ^ e = n := Nat.div_mul_cancel hdvd
  refine ⟨hmul, ?_⟩
  intro hc
  obtain ⟨d, hd⟩ := hc
  have hbig : q ^ (e + 1) ∣ n := ⟨d, by rw [← hmul, hd]; ring⟩
  have hn0 : n ≠ 0 := by omega
  have hle : e + 1 ≤ padicValNat q n := by
    haveI : Fact (Nat.Prime q) := ⟨hp⟩
    exact (padicValNat_dvd_iff_le hn0).mp hbig
  omega

/-- **The q-adic counting law.** -/
theorem qlaw (he : 1 ≤ e) {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e) :
    ∑ n ∈ T.filter (fun n => padicValNat q n = e), ((cof q e n : ZMod q))⁻¹ = 0 := by
  classical
  have hp : Nat.Prime q := Fact.out
  set A := T.filter (fun n => padicValNat q n = e) with hAdef
  have hAT : ∀ n ∈ A, n ∈ T := fun n hn => Finset.mem_of_mem_filter n hn
  have hAv : ∀ n ∈ A, padicValNat q n = e := fun n hn => (Finset.mem_filter.mp hn).2
  have hspec : ∀ n ∈ A, cof q e n * q ^ e = n ∧ ¬ q ∣ cof q e n :=
    fun n hn => cof_spec (hTpos n (hAT n hn)) (hAv n hn)
  have hcop : ∀ n ∈ A, Nat.Coprime q (cof q e n) :=
    fun n hn => (Nat.Prime.coprime_iff_not_dvd hp).mpr (hspec n hn).2
  -- P, the product of the cofactors, is coprime to q
  set P := ∏ n ∈ A, cof q e n with hPdef
  have hcopP : Nat.Coprime q P := Nat.Coprime.prod_right (fun n hn => hcop n hn)
  have hqP : ¬ q ∣ P := (Nat.Prime.coprime_iff_not_dvd hp).mp hcopP
  have hPpos : 0 < P := Nat.pos_of_ne_zero (fun h => hqP (h ▸ dvd_zero q))
  -- every level-e term divides P * q^e
  have hdvd : ∀ n ∈ T, padicValNat q n = e → n ∣ P * q ^ e := by
    intro n hn hv
    have hnA : n ∈ A := Finset.mem_filter.mpr ⟨hn, hv⟩
    have h1 : cof q e n ∣ P := Finset.dvd_prod_of_mem _ hnA
    have h2 := mul_dvd_mul h1 (dvd_refl (q ^ e))
    rwa [(hspec n hnA).1] at h2
  have hmaster := Master.master he hPpos hqP hTpos hsum hmax hdvd
  have hcast : ((∑ n ∈ A, (P * q ^ e / n) : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hmaster
  rw [Nat.cast_sum] at hcast
  -- each summand is P · (cofactor)⁻¹
  have hterm : ∀ n ∈ A, ((P * q ^ e / n : ℕ) : ZMod q)
      = (P : ZMod q) * ((cof q e n : ZMod q))⁻¹ := by
    intro n hn
    have hnpos := hTpos n (hAT n hn)
    have hc := (hspec n hn).1
    have hdc : cof q e n ∣ P := Finset.dvd_prod_of_mem _ hn
    have hdiv : P * q ^ e / n = P / cof q e n := by
      set u := cof q e n with hu
      have hcan : P / u * u = P := Nat.div_mul_cancel hdc
      refine Nat.div_eq_of_eq_mul_left hnpos ?_
      calc P * q ^ e = (P / u * u) * q ^ e := by rw [hcan]
        _ = P / u * (u * q ^ e) := by ring
        _ = P / u * n := by rw [hc]
    have hmulZ : ((P / cof q e n : ℕ) : ZMod q) * ((cof q e n : ℕ) : ZMod q) = (P : ZMod q) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdc]
    have hcm := ZMod.coe_mul_inv_eq_one (n := q) (cof q e n) (hcop n hn).symm
    rw [hdiv]
    calc ((P / cof q e n : ℕ) : ZMod q)
        = ((P / cof q e n : ℕ) : ZMod q) * ((cof q e n : ZMod q) * ((cof q e n : ZMod q))⁻¹) := by
          rw [hcm, mul_one]
      _ = (((P / cof q e n : ℕ) : ZMod q) * (cof q e n : ZMod q)) * ((cof q e n : ZMod q))⁻¹ := by
          ring
      _ = (P : ZMod q) * ((cof q e n : ZMod q))⁻¹ := by rw [hmulZ]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hcast
  -- cancel the unit P
  have hPinv := ZMod.coe_mul_inv_eq_one (n := q) P hcopP.symm
  have hrw : (∑ n ∈ A, ((cof q e n : ZMod q))⁻¹)
      = ((P : ZMod q))⁻¹ * ((P : ZMod q) * (∑ n ∈ A, ((cof q e n : ZMod q))⁻¹)) := by
    rw [← mul_assoc, mul_comm ((P : ZMod q))⁻¹ (P : ZMod q), hPinv, one_mul]
  rw [hrw, hcast, mul_zero]

/-- **At `q = 2` the law IS the parity law**, so `qlaw` strictly generalizes
`MaxVal.maxlevel_card_even`: every cofactor is odd, hence `1` in `ZMod 2`, and the sum counts. -/
theorem card_even_of_two {e : ℕ} (he : 1 ≤ e) {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat 2 n ≤ e) :
    Even (T.filter (fun n => padicValNat 2 n = e)).card := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := qlaw (q := 2) he hTpos hsum hmax
  have hone : ∀ n ∈ T.filter (fun n => padicValNat 2 n = e),
      ((cof 2 e n : ZMod 2))⁻¹ = 1 := by
    intro n hn
    have hnT : n ∈ T := Finset.mem_of_mem_filter n hn
    have hnd := (cof_spec (hTpos n hnT) ((Finset.mem_filter.mp hn).2)).2
    have hmod : cof 2 e n % 2 = 1 := by omega
    have hcast : (cof 2 e n : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, hmod, Nat.cast_one]
    rw [hcast]
    decide
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hdvd : (2:ℕ) ∣ (T.filter (fun n => padicValNat 2 n = e)).card :=
    (ZMod.natCast_eq_zero_iff _ _).mp h
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by omega⟩

/-- **The general exclusion theorem.** If the cofactors of the level-`e` terms are confined to a set
`U`, and NO nonempty subset of `U` has vanishing inverse-sum mod `q`, then the level is EMPTY.

This is the single statement behind every exclusion in this development. `RuleB` is the case
`U = {1}` (see `level_empty_of_lone` below); `RuleBGen.ruleB_sharp` is `U = {1,…,t}` with the size
condition `t·lcm(1..t) < q`, which is exactly the crude sufficient condition for the hypothesis here;
and the dichotomies at `q = 2, 3` are the cases where `U` has two elements and a nonempty subset DOES
qualify, so the level is not empty but is pinned. -/
theorem level_empty (he : 1 ≤ e) {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    {U : Finset ℕ} (hU : ∀ n ∈ T, padicValNat q n = e → cof q e n ∈ U)
    (hno : ∀ I ⊆ U, I.Nonempty → ∑ u ∈ I, ((u : ZMod q))⁻¹ ≠ 0) :
    ∀ n ∈ T, padicValNat q n ≠ e := by
  classical
  intro n hn hv
  have hq := qlaw he hTpos hsum hmax
  set A := T.filter (fun n => padicValNat q n = e) with hAdef
  have hnA : n ∈ A := Finset.mem_filter.mpr ⟨hn, hv⟩
  -- the cofactor map is injective on the level, since n = cof · q^e recovers n
  have hinj : ∀ x ∈ A, ∀ y ∈ A, cof q e x = cof q e y → x = y := by
    intro x hx y hy hxy
    have hx' := (cof_spec (hTpos x (Finset.mem_of_mem_filter x hx))
      ((Finset.mem_filter.mp hx).2)).1
    have hy' := (cof_spec (hTpos y (Finset.mem_of_mem_filter y hy))
      ((Finset.mem_filter.mp hy).2)).1
    rw [← hx', ← hy', hxy]
  have himg : ∑ u ∈ A.image (cof q e), ((u : ZMod q))⁻¹
      = ∑ x ∈ A, ((cof q e x : ZMod q))⁻¹ := Finset.sum_image hinj
  have hsubU : A.image (cof q e) ⊆ U := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    exact hxu ▸ hU x (Finset.mem_of_mem_filter x hx) (Finset.mem_filter.mp hx).2
  have hne : (A.image (cof q e)).Nonempty := ⟨cof q e n, Finset.mem_image_of_mem _ hnA⟩
  exact hno _ hsubU hne (by rw [himg]; exact hq)

/-- **Rule B, recovered.** If every level-`e` term equals `q^e` itself, the level is empty —
the `U = {1}` case of `level_empty`, since the only nonempty subset gives `1⁻¹ = 1 ≠ 0`. -/
theorem level_empty_of_lone (he : 1 ≤ e) {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    (hlone : ∀ n ∈ T, padicValNat q n = e → n = q ^ e) :
    ∀ n ∈ T, padicValNat q n ≠ e := by
  classical
  have hp : Nat.Prime q := Fact.out
  refine level_empty he hTpos hsum hmax (U := {1}) ?_ ?_
  · intro n hn hv
    have hqe : 0 < q ^ e := pow_pos hp.pos e
    rw [Finset.mem_singleton]
    show n / q ^ e = 1
    rw [hlone n hn hv]
    exact Nat.div_self hqe
  · intro I hI hne
    have hI1 : I = {1} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hne, fun x hx => Finset.mem_singleton.mp (hI hx)⟩
    haveI : Fact (1 < q) := ⟨hp.one_lt⟩
    rw [hI1, Finset.sum_singleton, Nat.cast_one]
    intro hzero
    have hcm : (1 : ZMod q) * (1 : ZMod q)⁻¹ = 1 := by
      have h := ZMod.coe_mul_inv_eq_one (n := q) 1 (Nat.coprime_one_left q)
      simpa using h
    rw [hzero, mul_zero] at hcm
    exact zero_ne_one hcm

#print axioms qlaw
#print axioms card_even_of_two
#print axioms level_empty
#print axioms level_empty_of_lone

end QLaw
