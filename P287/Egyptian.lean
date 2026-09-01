/- General facts about Egyptian fraction representations of 1.

Everything here is about an arbitrary finite set `T` of positive integers with
`Σ_{n ∈ T} 1/n = 1`. **No gap hypothesis appears anywhere** — these are not facts
about Erdős #287, they are facts about Egyptian fractions, and #287 only ever used
them as a tool. They fall out of two lemmas already proved for that purpose:
`LemAGen.lemA_gen` (Lemma A′) and `RuleB.ruleB` (the unique q-adic maximiser).

Writing `M` for the largest denominator:

* `largest_not_prime`        — M is never prime;
* `largest_not_prime_power`  — M is never a prime power;
* `cofactor_bound`           — if `M = a·p` with `p` prime then `p ≤ a·a!`.

The last is the quantitative one. Applied to `p = P(M)`, the largest prime factor,
with `a = M/P(M)`, it says `P(M) ≤ a·a!` and hence `M ≤ a²·a!`, i.e.

    M / P(M)  ≥  (1 + o(1)) · log M / log log M.

So the largest denominator is forced to be quite smooth: it is never `p`, never
`p^e`, never `2p`, never `3p` for `p ≥ 19`, never `4p` for `p ≥ 97`, and so on.
-/
import P287.LemAGenMod
import P287.RuleB

namespace Egyptian

/-- **Lemma A′ in bounded form.** If every denominator is at most `M`, and a prime
`p` is large compared with `t = ⌊M/p⌋`, then no denominator is divisible by `p`. -/
theorem not_dvd_of_large {p M : ℕ} (hp : Nat.Prime p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (ht : 1 ≤ M / p) (hbig : (M / p) * Nat.factorial (M / p) < p)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    ∀ n ∈ T, ¬ p ∣ n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro n hn hdvd
  refine LemAGen.lemA_gen (p := p) (t := M / p) ht hbig hTpos ?_ ⟨n, hn, hdvd⟩ hsum
  intro x hx hd
  obtain ⟨j, hj⟩ := hd
  have hxle := hTle x hx
  have hxpos := hTpos x hx
  have hj' : j * p = x := by rw [hj]; ring
  refine ⟨j, ?_, ?_, by rw [hj]; ring⟩
  · rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at hj; omega
    · exact h
  · rw [Nat.le_div_iff_mul_le hp.pos]
    omega

/-- **The largest denominator is never prime.** -/
theorem largest_not_prime {M : ℕ} {T : Finset ℕ} (hM : M ∈ T)
    (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    ¬ Nat.Prime M := by
  intro hp
  have hdiv : M / M = 1 := Nat.div_self hp.pos
  refine not_dvd_of_large hp hTpos hTle (by omega) ?_ hsum M hM dvd_rfl
  rw [hdiv]
  simpa [Nat.factorial] using hp.one_lt

/-- **The largest denominator is never a prime power.** -/
theorem largest_not_prime_power {q e M : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e)
    {T : Finset ℕ} (hM : M ∈ T)
    (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    M ≠ q ^ e := by
  intro hMq
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hpos : 0 < q ^ e := pow_pos hq.pos e
  exact RuleB.ruleB (q := q) (e := e) (M := M) he hTpos hTle (by omega) hsum (hMq ▸ hM)

/-- **Smoothness of the largest denominator.** If `M = a·p` with `p` prime then
`p ≤ a·a!`; equivalently `M ≤ a²·a!`, so `a = M/p` grows at least like
`log M / log log M`. -/
theorem cofactor_bound {a p M : ℕ} (hp : Nat.Prime p) (ha : 1 ≤ a) (hMa : M = a * p)
    {T : Finset ℕ} (hM : M ∈ T)
    (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    p ≤ a * Nat.factorial a := by
  by_contra hc
  push_neg at hc
  have hdiv : M / p = a := by rw [hMa]; exact Nat.mul_div_cancel _ hp.pos
  refine not_dvd_of_large hp hTpos hTle (by rw [hdiv]; exact ha) ?_ hsum M hM ⟨a, by rw [hMa]; ring⟩
  rw [hdiv]; exact hc

#print axioms largest_not_prime
#print axioms largest_not_prime_power
#print axioms cofactor_bound

end Egyptian
