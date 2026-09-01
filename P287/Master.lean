/- **The master congruence.** One statement behind every exclusion rule in this development.

Let `T` be finite with all `n > 0` and `Σ_{n ∈ T} 1/n = 1`. Fix a prime `q`, an `e ≥ 1`
bounding the `q`-adic valuations on `T`, and an `L > 0` with `q ∤ L` such that every term of
valuation exactly `e` divides `L·q^e`. Then

    q  ∣  Σ_{n : v_q(n) = e}  L·q^e / n.

That is the whole content of the p-adic method here. Everything else is a way of making the
right-hand side small enough, or structured enough, to read something off it:

* **Lemma A′** (`LemAGen.lemA_param`, `lemA_sharp`) — the weights are `L/u` for `u ≤ t`, so the
  sum is at most `t·L`; if `t·L < q` the only multiple of `q` available is 0, so the level is
  empty. `e = 1` there.
* **Rule B, narrow** (`RuleB.ruleB`) — the same at `t = 1`: one candidate, weight `L`, and
  `q ∤ L`, so the level is empty. This is where `M < 2q^e` comes from.
* **Rule B, general** (`RuleBGen.ruleB_param`, `ruleB_sharp`) — Lemma A′'s size argument run at
  arbitrary `e` rather than `e = 1`.
* **The parity law at 2** (`MaxVal.maxlevel_card_even`) — at `q = 2` the size argument is
  hopeless, because `t·L < 2` forces `t = 1`. But every weight is ODD there (`L` odd, and each
  cofactor divides `L`), so the sum is `≡ #A (mod 2)` and the congruence says `#A` is EVEN. No
  size hypothesis at all.

So the size-based rules and the parity law are not two methods; they are two ways of exploiting
one congruence, and `q = 2` is exactly where the size route dies and the parity route survives.

The proof is the shared skeleton with the size step deleted: if `q` did not divide the sum, the
level-`e` block would have `q`-adic valuation exactly `−e`, strictly below every other term's,
so the total would have valuation `−e < 0` and could not be the integer 1.

No nonemptiness hypothesis is needed: over an empty level the sum is 0, and `q ∣ 0`.
-/
import P287.RuleBGen

namespace Master

open Finset

/-- **The master congruence.** -/
theorem master {q e L : ℕ} [Fact (Nat.Prime q)] (he : 1 ≤ e)
    (hLpos : 0 < L) (hqL : ¬ q ∣ L)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    (hdvd : ∀ n ∈ T, padicValNat q n = e → n ∣ L * q ^ e) :
    q ∣ ∑ n ∈ T.filter (fun n => padicValNat q n = e), (L * q ^ e / n) := by
  classical
  by_contra hk
  have hq : Nat.Prime q := Fact.out
  have hq1 : 1 < q := hq.one_lt
  have hqepos : 0 < q ^ e := pow_pos hq.pos e
  have hDpos : 0 < L * q ^ e := Nat.mul_pos hLpos hqepos
  set A := T.filter (fun n => padicValNat q n = e) with hAdef
  set B := T.filter (fun n => ¬ padicValNat q n = e) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  have hAT : ∀ n ∈ A, n ∈ T := fun n hn => Finset.mem_of_mem_filter n hn
  have hAv : ∀ n ∈ A, padicValNat q n = e := fun n hn => (Finset.mem_filter.mp hn).2
  -- an empty level would make the sum 0, which q does divide
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with h | h
    · exact absurd (by rw [h]; simp) hk
    · exact h
  -- the weights are positive integers
  have hw : ∀ n ∈ A, (L * q ^ e / n) * n = L * q ^ e ∧ 0 < L * q ^ e / n := by
    intro n hn
    have hnd : n ∣ L * q ^ e := hdvd n (hAT n hn) (hAv n hn)
    have hmul : (L * q ^ e / n) * n = L * q ^ e := Nat.div_mul_cancel hnd
    refine ⟨hmul, ?_⟩
    exact Nat.div_pos (Nat.le_of_dvd hDpos hnd) (hTpos n (hAT n hn))
  have hterm : ∀ n ∈ A, ((n : ℚ))⁻¹
      = ((L * q ^ e / n : ℕ) : ℚ) / ((L : ℚ) * ((q ^ e : ℕ) : ℚ)) := by
    intro n hn
    have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hTpos n (hAT n hn)
    have hLQ : (0 : ℚ) < (L : ℚ) := by exact_mod_cast hLpos
    have hqQ : (0 : ℚ) < ((q ^ e : ℕ) : ℚ) := by exact_mod_cast hqepos
    have hden : (0 : ℚ) < (L : ℚ) * ((q ^ e : ℕ) : ℚ) := by positivity
    rw [eq_div_iff (ne_of_gt hden), inv_mul_eq_div, div_eq_iff (ne_of_gt hnpos)]
    have := (hw n hn).1
    push_cast
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) this.symm
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (L * q ^ e / n) : ℕ) : ℚ) / ((L : ℚ) * ((q ^ e : ℕ) : ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  have hkpos : 0 < ∑ n ∈ A, (L * q ^ e / n) :=
    Finset.sum_pos (fun n hn => (hw n hn).2) hAne
  -- the level-e block would sit strictly below everything else
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have : (0:ℚ) < (n:ℚ) := by exact_mod_cast hTpos n (hAT n hn)
    exact inv_pos.mpr this
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have : (0:ℚ) < (n:ℚ) := by
      exact_mod_cast hTpos n (Finset.mem_of_mem_filter n hn)
    exact inv_pos.mpr this
  have hBval : ∀ n ∈ B, -(e : ℤ) < padicValRat q ((n : ℚ))⁻¹ := by
    intro n hn
    obtain ⟨hnT, hne⟩ := Finset.mem_filter.mp hn
    have hle := hmax n hnT
    have hlt : padicValNat q n < e := by omega
    rw [padicValRat.inv, padicValRat.of_nat]
    omega
  have hAval : padicValRat q (∑ n ∈ A, ((n : ℚ))⁻¹) = -(e : ℤ) := by
    rw [hsumA]
    exact RuleBGen.val_frac_pow hq1 hkpos hLpos hk hqL
  exact RuleB.sum_ne_one_of_val_lt hApos hBpos hAne hAval (by omega) hBval
    (by rw [hsplit]; exact hsum)

/-- **The size route.** If the weights cannot reach `q`, the level is empty — this is the shape
`lemA_param`, `ruleB_param` and the narrow rule B all use. -/
theorem level_empty_of_small {q e L S : ℕ} [Fact (Nat.Prime q)] (he : 1 ≤ e)
    (hLpos : 0 < L) (hqL : ¬ q ∣ L)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    (hmax : ∀ n ∈ T, padicValNat q n ≤ e)
    (hdvd : ∀ n ∈ T, padicValNat q n = e → n ∣ L * q ^ e)
    (hbound : ∑ n ∈ T.filter (fun n => padicValNat q n = e), (L * q ^ e / n) ≤ S)
    (hSq : S < q) :
    ∀ n ∈ T, padicValNat q n ≠ e := by
  classical
  have hdiv := master he hLpos hqL hTpos hsum hmax hdvd
  have hzero : ∑ n ∈ T.filter (fun n => padicValNat q n = e), (L * q ^ e / n) = 0 := by
    rcases Nat.eq_zero_or_pos
      (∑ n ∈ T.filter (fun n => padicValNat q n = e), (L * q ^ e / n)) with h | h
    · exact h
    · have := Nat.le_of_dvd h hdiv
      omega
  intro n hnT hnv
  have hmem : n ∈ T.filter (fun n => padicValNat q n = e) :=
    Finset.mem_filter.mpr ⟨hnT, hnv⟩
  have hqepos : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have hnd : n ∣ L * q ^ e := hdvd n hnT hnv
  have hwpos : 0 < L * q ^ e / n :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hLpos hqepos) hnd) (hTpos n hnT)
  have hle : L * q ^ e / n
      ≤ ∑ m ∈ T.filter (fun m => padicValNat q m = e), (L * q ^ e / m) :=
    Finset.single_le_sum (fun m _ => Nat.zero_le _) hmem
  omega

#print axioms master
#print axioms level_empty_of_small

end Master
