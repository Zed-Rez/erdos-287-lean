/- **Every term of a counterexample has largest prime factor at most M/431.**

`Smooth55` bounds the COFACTOR: no term is `a·q` with `q` prime and `a ≤ 55`. That constant is the
worst case over the window — it is forced by a term sitting at the very bottom, near `n₁ = M/7.8`,
where `t = ⌊M/q⌋` is largest. Bounding the PRIME FACTOR directly is cleaner, uniform across the
window, and stronger where it matters:

    a prime `p` with `M < 431·p` has `t = ⌊M/p⌋ ≤ 430`, and
    `430 · lcm(1..430) ≈ 7.4·10¹⁸⁵ < M/431`,
    so Lemma A′ removes EVERY multiple of `p`.

Hence no term has a prime factor exceeding `M/431`. Note this uses no window bound at all — only
`n ≤ M` — where the cofactor version needs `Window3`. At the top of the window it is about 7.7×
stronger than `Smooth55` (which gives only `P(M) < M/56` there); at the bottom the two agree.

`T = 430` is maximal for the current range: `T·(T+1)·lcm(1..T) ≈ 3.20·10¹⁸⁸ < M`, while `T = 431`
gives `1.39·10¹⁹¹ > M`.
-/
import P287.StepAB
import P287.LemAParam
import Mathlib.Tactic.NormNum.GCD

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Rough

open LemAGen

/-- `lcmUpto` is monotone: each step multiplies in a new factor. -/
theorem lcmUpto_dvd_mono : ∀ {m n : ℕ}, m ≤ n → lcmUpto m ∣ lcmUpto n := by
  intro m n h
  induction n with
  | zero => simp_all
  | succ j ih =>
      rcases Nat.lt_or_ge m (j + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (by
          show lcmUpto j ∣ Nat.lcm (j + 1) (lcmUpto j)
          exact Nat.dvd_lcm_right _ _)
      · have : m = j + 1 := by omega
        rw [this]

theorem lcmUpto_mono {m n : ℕ} (h : m ≤ n) : lcmUpto m ≤ lcmUpto n :=
  Nat.le_of_dvd (lcmUpto_pos n) (lcmUpto_dvd_mono h)

/-- **Lemma A′, sharp, in "no multiple of `p`" form.** `Egyptian.not_dvd_of_large` with
`lemA_sharp` in place of `lemA_gen`. -/
theorem not_dvd_of_large_sharp {p M : ℕ} (hp : Nat.Prime p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (ht : 1 ≤ M / p) (hbig : (M / p) * lcmUpto (M / p) < p)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    ∀ n ∈ T, ¬ p ∣ n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro n hn hdvd
  refine lemA_sharp (p := p) (t := M / p) ht hbig hTpos ?_ ⟨n, hn, hdvd⟩ hsum
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

/-- **No term is divisible by a prime exceeding `M/431`.** -/
theorem no_large_prime_factor {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hM : 10 ^ 189 ≤ s ⟨k - 1, by omega⟩)
    {p : ℕ} (hp : Nat.Prime p) (hlo : s ⟨k - 1, by omega⟩ < 431 * p) :
    ∀ i, ¬ p ∣ s i := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := StepAB.setup hk s hmono h1 hsum
  set M := s ⟨k - 1, by omega⟩ with hMdef
  have hpow : (10 : ℕ) ^ 189 = 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by norm_num
  rw [hpow] at hM
  have hL430 : lcmUpto 430 = 1726254535626991402141837030862017565327892043446089940314981195457969400079232433011388333892793982922217655863129953971168508558438239788035734077158184050253388128711313736844768000 := by
    norm_num [lcmUpto, Nat.lcm]
  -- t = M / p is at most 430, so t * lcmUpto t <= 430 * lcmUpto 430 < M/431 < p
  intro i hdvd
  have hmem : s i ∈ Finset.image s Finset.univ := Finset.mem_image_of_mem s (Finset.mem_univ i)
  have hsile := hTle (s i) hmem
  have hsipos := hTpos (s i) hmem
  by_cases hple : p ≤ M
  · have ht : 1 ≤ M / p := (Nat.one_le_div_iff hp.pos).mpr hple
    have htle : M / p ≤ 430 := by
      by_contra hc
      push_neg at hc
      have h431 : 431 * p ≤ (M / p) * p := Nat.mul_le_mul_right p (by omega)
      have hdm : (M / p) * p ≤ M := Nat.div_mul_le_self M p
      omega
    have hbig : (M / p) * lcmUpto (M / p) < p := by
      have h1' : lcmUpto (M / p) ≤ lcmUpto 430 := lcmUpto_mono htle
      have h2' : (M / p) * lcmUpto (M / p) ≤ 430 * lcmUpto 430 := Nat.mul_le_mul htle h1'
      rw [hL430] at h2'
      omega
    exact not_dvd_of_large_sharp (M := M) hp hTpos hTle ht hbig hsumT (s i) hmem hdvd
  · -- p exceeds M, so it cannot divide a term
    push_neg at hple
    have := Nat.le_of_dvd hsipos hdvd
    omega

/-- **Uniform smoothness.** Every term's prime factors are at most `M/431`. -/
theorem term_smooth {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hM : 10 ^ 189 ≤ s ⟨k - 1, by omega⟩)
    (i : Fin k) {p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ s i) :
    431 * p ≤ s ⟨k - 1, by omega⟩ := by
  by_contra hc
  push_neg at hc
  exact no_large_prime_factor hk s hmono h1 hsum hM hp hc i hdvd

#print axioms lcmUpto_mono
#print axioms no_large_prime_factor
#print axioms term_smooth

/-- **The barrier, in the right variable.** If two consecutive integers in the window both carry
a prime factor larger than `M/431`, then some gap is at least 3 — i.e. #287 holds for that
representation. No `max_gap ≤ 2` hypothesis is needed: this CONCLUDES the gap bound.

Closing #287 by this method means exhibiting such a pair for every `M` above the unconditionally
verified range: primes `p, q` and `n` in the interior with `p ∣ n`, `q ∣ n+1`, both exceeding
`M/431`. Written as an exponent that asks for `P(n), P(n+1) ≥ M^0.986`, for a CONSECUTIVE PAIR, in
EVERY window — against `p^0.679` for a single shifted prime and only infinitely often, which is the
unconditional record (`verified/072`). -/
theorem gap_three_of_rough_pair {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hM : 10 ^ 189 ≤ s ⟨k - 1, by omega⟩)
    {n : ℕ} (hlo : s ⟨0, by omega⟩ ≤ n) (hhi : n + 1 ≤ s ⟨k - 1, by omega⟩)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpn : p ∣ n) (hqn : q ∣ (n + 1))
    (hpbig : s ⟨k - 1, by omega⟩ < 431 * p)
    (hqbig : s ⟨k - 1, by omega⟩ < 431 * q) :
    3 ≤ PCI.max_gap k s := by
  have e0 : ∀ i, s i ≠ n := by
    intro i hi
    exact no_large_prime_factor hk s hmono h1 hsum hM hp hpbig i (hi ▸ hpn)
  have e1 : ∀ i, s i ≠ n + 1 := by
    intro i hi
    exact no_large_prime_factor hk s hmono h1 hsum hM hq hqbig i (hi ▸ hqn)
  exact PCI.gap_three_of_two_missing hk s hlo hhi e0 e1

#print axioms gap_three_of_rough_pair

end Rough
