/- RULE B: the unique q-adic maximiser is not a term.

If `q^e ≤ M < 2·q^e` then `q^e` is the ONLY element of `[1, M]` whose q-adic
valuation reaches `e`: anything else divisible by `q^e` is at least `2q^e > M`.
Clearing denominators therefore leaves exactly one term coprime to `q` while the
total, `1`, is not — so `q^e` cannot be a term.

At `e = 1` this is Lemma A′ at `t = 1`; only `e ≥ 2` is new, and that is exactly
what the small-M end of the ladder needs (the prime powers 8, 16, 25, 32). Rule A
alone leaves the residue {9,10,11,21,22,23,33,…,38} uncovered.

The three helper lemmas here generalise `LemAGen.val_add_of_neg`,
`val_sum_nonneg` and `sum_ne_one_of_val_neg`, which all assume the non-exceptional
terms have valuation ≥ 0. Here they have valuation ≥ 1 - e, which is negative once
e ≥ 2, so the comparison has to be against the exceptional term's own valuation
rather than against zero.
-/
import P287.LemAGenMod

namespace RuleB

open Finset

variable {p : ℕ}

/-- Ultrametricity: a strictly smallest valuation wins, with no reference to 0. -/
theorem val_add_of_lt [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : padicValRat p x < padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

/-- A sum of positive terms all of valuation ≥ c has valuation ≥ c, for c ≤ 0. -/
theorem val_sum_ge [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ} {c : ℤ}
    (hc : c ≤ 0) (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, c ≤ padicValRat p (f n)) :
    c ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simpa using hc
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, c ≤ padicValRat p (f n) := fun n hn =>
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

/-- If one block has valuation `c < 0` and every other term beats it strictly,
the total cannot be `1`. -/
theorem sum_ne_one_of_val_lt [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ} {c : ℤ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n) (hA : A.Nonempty)
    (hAval : padicValRat p (∑ n ∈ A, f n) = c) (hc : c < 0)
    (hBval : ∀ n ∈ B, c < padicValRat p (f n)) :
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
    have hBge : c + 1 ≤ padicValRat p (∑ n ∈ B, f n) :=
      val_sum_ge (by omega) hBpos (fun n hn => by have := hBval n hn; omega)
    have hlt : padicValRat p (∑ n ∈ A, f n) < padicValRat p (∑ n ∈ B, f n) := by
      omega
    have hval := val_add_of_lt (p := p) (ne_of_gt hApos') (ne_of_gt hBpos')
      (ne_of_gt (add_pos hApos' hBpos')) hlt
    intro h
    rw [h] at hval
    simp only [padicValRat.one] at hval
    omega

/-- **Rule B.** `q^e` is the unique element of `[1,M]` of maximal `q`-adic
valuation as soon as `M < 2·q^e`, and therefore is not a term. -/
theorem ruleB {q e M : ℕ} [Fact (Nat.Prime q)] (he : 1 ≤ e)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (hhi : M < 2 * q ^ e)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    q ^ e ∉ T := by
  classical
  intro hx
  have hq : Nat.Prime q := Fact.out
  have hq1 : 1 < q := hq.one_lt
  have hxpos : 0 < q ^ e := pow_pos (by omega) e
  -- the valuation of the exceptional term
  have hpvx : padicValNat q (q ^ e) = e := by
    first
    | exact padicValNat.prime_pow_self q e
    | exact padicValNat.prime_pow e
    | simp
  -- every other term has strictly smaller q-adic valuation
  have hother : ∀ n ∈ T.erase (q ^ e), padicValNat q n < e := by
    intro n hn
    obtain ⟨hne, hnT⟩ := Finset.mem_erase.mp hn
    by_contra hc
    push_neg at hc
    have hdvd : q ^ e ∣ n :=
      dvd_trans (pow_dvd_pow q hc) (pow_padicValNat_dvd)
    obtain ⟨j, hj⟩ := hdvd
    have hnpos := hTpos n hnT
    have hnle := hTle n hnT
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j <;> simp_all <;> omega
      · exact h
    have : q ^ e * 2 ≤ q ^ e * j := Nat.mul_le_mul_left _ hj2
    omega
  -- split off the exceptional term and compare valuations
  have hsplit : ((q ^ e : ℕ) : ℚ)⁻¹ + ∑ n ∈ T.erase (q ^ e), ((n : ℚ))⁻¹
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := by
    first
    | exact Finset.add_sum_erase T _ hx
    | exact Finset.add_sum_erase _ _ hx
    | simp [Finset.add_sum_erase, hx]
  refine sum_ne_one_of_val_lt (p := q) (A := ({q ^ e} : Finset ℕ))
    (B := T.erase (q ^ e)) (f := fun n => ((n : ℚ))⁻¹) (c := -(e : ℤ))
    ?_ ?_ ⟨q ^ e, Finset.mem_singleton_self _⟩ ?_ (by omega) ?_ ?_
  · intro n hn
    rw [Finset.mem_singleton] at hn
    subst hn
    have : (0:ℚ) < ((q ^ e : ℕ) : ℚ) := by exact_mod_cast hxpos
    exact inv_pos.mpr this
  · intro n hn
    have := hTpos n (Finset.mem_of_mem_erase hn)
    have h2 : (0:ℚ) < (n : ℚ) := by exact_mod_cast this
    exact inv_pos.mpr h2
  · rw [Finset.sum_singleton, padicValRat.inv, padicValRat.of_nat, hpvx]
  · intro n hn
    have hlt := hother n hn
    have hnpos := hTpos n (Finset.mem_of_mem_erase hn)
    have h2 : (0:ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    rw [padicValRat.inv, padicValRat.of_nat]
    omega
  · rw [Finset.sum_singleton, hsplit]
    exact hsum

#print axioms ruleB

end RuleB
