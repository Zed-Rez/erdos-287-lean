/- **Erdős #287 follows from the published sufficient condition.**

The remark on erdosproblems.com/287 says #287 holds if for all large `N` there is a
prime `p ∈ [N, 2N]` with `(p+1)/2` also prime. `Conditional.lean` observes that this
is the special case `a = 1, b = 2` of a rung — but only in prose. This file proves it,
so the development formally subsumes the published criterion.

Given `M`, apply the hypothesis at `N = M/2 − 1`. The prime `p` it returns lies in
`[M/2 − 1, M − 2]`, and `a = 1, b = 2, tp = 2, tq = 5` discharges every rung condition:

    n + 2 = p + 2 ≤ M              since p ≤ 2N ≤ M − 2
    M < (tp+1)·p = 3p              since p ≥ M/2 − 1
    M < (tq+1)·q = 6q = 3p + 3     from the line above
    2M + 20 ≤ 5n = 5p              since p ≥ M/2 − 1 and M ≥ 50
    tp·tp! = 4 < p,  tq·tq! = 600 < q

No property of `p` beyond primality of `p` and of `(p+1)/2` is used, and the
side conditions are slack by a factor of order `M` — which is why a rung is a
much weaker demand than the Sophie-Germain shape.
-/
import P287.Conditional
import P287.Part3

namespace SGCond

/-- The published sufficient condition: from `N0` on, every `[N, 2N]` holds a prime
`p` with `(p+1)/2` prime. Stated as `p + 1 = 2q` to avoid a division. -/
def SG (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + 1 = 2 * q ∧ N ≤ p ∧ p ≤ 2 * N

/-- A Sophie-Germain pair in `[M/2 − 1, M − 2]` is a rung for `M`. -/
theorem rung_of_SG {N0 M : ℕ} (h : SG N0) (hM : 2 * N0 + 100 ≤ M) (hM2 : 10000 ≤ M) :
    Conditional.rung M := by
  obtain ⟨p, q, hp, hq, hpq, hlo, hhi⟩ := h (M / 2 - 1) (by omega)
  have f2 : Nat.factorial 2 = 2 := by norm_num [Nat.factorial]
  have f5 : Nat.factorial 5 = 120 := by norm_num [Nat.factorial]
  refine ⟨p, q, p, 1, 2, 2, 5, hp, hq, by norm_num, by norm_num, ?_, ?_, by ring,
    hpq, ?_, ?_, ?_, ?_⟩
  · rw [f2]; omega
  · rw [f5]; omega
  · omega
  · omega
  · omega
  · omega

/-- **The published criterion implies #287 in full.** `N0` is only required to lie
below the unconditionally verified range, which is what "for all large `N`" means
here. -/
theorem erdos287_of_SG {N0 : ℕ} (h : SG N0)
    (hN0 : 2 * N0 + 100 ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    3 ≤ PCI.max_gap k s := by
  refine Conditional.erdos287_of_rung (fun M hM => ?_) hk s hmono h1 hsum
  exact rung_of_SG h (by omega) (by omega)

#print axioms rung_of_SG
#print axioms erdos287_of_SG

/-- The far weaker demand a rung actually makes: `n` and `n+1` each need only SOME
prime factor of small cofactor. No Sophie-Germain shape, no relation between the two
primes. -/
def Cofactor (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N → ∃ n p q a b : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ n = a * p ∧ n + 1 = b * q ∧
    1 ≤ a ∧ a ≤ 10 ∧ 1 ≤ b ∧ b ≤ 10 ∧ N ≤ n ∧ n ≤ 2 * N

/-- Such a pair in `[M/2 − 1, M − 2]` is a rung for `M`, with `tp = tq = 20`. -/
theorem rung_of_Cofactor {N0 M : ℕ} (h : Cofactor N0)
    (hM : 2 * N0 + 100 ≤ M) (hM2 : 10000000000000000000000 ≤ M) : Conditional.rung M := by
  obtain ⟨n, p, q, a, b, hp, hq, hna, hnb, ha1, ha, hb1, hb, hlo, hhi⟩ := h (M / 2 - 1) (by omega)
  have f20 : Nat.factorial 20 = 2432902008176640000 := by norm_num [Nat.factorial]
  have hpos := hp.two_le
  have hqos := hq.two_le
  -- a ≤ 10 and n ≥ M/2 − 1 force 20·p > M; likewise for q
  have hpbig : n ≤ 10 * p := by rw [hna]; exact Nat.mul_le_mul_right p ha
  have hqbig : n + 1 ≤ 10 * q := by rw [hnb]; exact Nat.mul_le_mul_right q hb
  refine ⟨p, q, n, a, b, 20, 20, hp, hq, by norm_num, by norm_num, ?_, ?_, hna, hnb,
    ?_, ?_, ?_, ?_⟩
  · rw [f20]; omega
  · rw [f20]; omega
  · omega
  · omega
  · omega
  · omega

/-- **#287 from the cofactor condition.** Strictly weaker hypothesis than `SG`,
same conclusion. -/
theorem erdos287_of_Cofactor {N0 : ℕ} (h : Cofactor N0)
    (hN0 : 2 * N0 + 100 ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    3 ≤ PCI.max_gap k s := by
  refine Conditional.erdos287_of_rung (fun M hM => ?_) hk s hmono h1 hsum
  exact rung_of_Cofactor h (by omega) (by omega)

#print axioms rung_of_Cofactor
#print axioms erdos287_of_Cofactor

/-! ### Upstream shape, with the exceptional set removed

`erdos_287.variants.prime_conjecture_implies` (upstream, and the erdosproblems.com remark)
concludes only `∃ k₀, ∀ k ≥ k₀, …` — #287 for all but at most finitely many exceptions, with
`k₀` unspecified. `verified/015` discharged exactly that shape.

The same hypothesis in fact gives the conclusion for **every** `k ≥ 2`, with no exceptional
set at all: `Conditional.erdos287_of_rung` needs a rung only for `M` above the range that
`Main3.erdos287_below` already settles unconditionally, and that range (≈ 3.81·10¹⁵⁸) swallows
every would-be exception. Stated below in upstream's real-valued sum shape.
-/

/-- Upstream's hypothesis implies `SG`: `p ≥ N ≥ N0 ≥ 3` and `p` prime force `p` odd, so
`(p+1)/2` is exact. -/
theorem SG_of_primeConjecture {N0 : ℕ} (h3 : 3 ≤ N0)
    (H : ∀ N : ℕ, N0 ≤ N →
      ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N ∧ Nat.Prime ((p + 1) / 2)) :
    SG N0 := by
  intro N hN
  obtain ⟨p, hp, hlo, hhi, hq⟩ := H N hN
  refine ⟨p, (p + 1) / 2, hp, hq, ?_, hlo, hhi⟩
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  omega

/-- **The prime conjecture implies #287 with NO exceptional set** — upstream's shape, but
`∀ k ≥ 2` in place of `∃ k₀, ∀ k ≥ k₀`. -/
theorem primeConjecture_implies_all {N0 : ℕ} (h3 : 3 ≤ N0)
    (H : ∀ N : ℕ, N0 ≤ N →
      ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N ∧ Nat.Prime ((p + 1) / 2))
    (hN0 : 2 * N0 + 100 ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, (1 : ℝ) / (s i : ℝ) = 1) :
    3 ≤ PCI.max_gap k s :=
  erdos287_of_SG (SG_of_primeConjecture h3 H) hN0 hk s hmono h1
    (PCI.sum_rat_of_sum_real s hsum)

#print axioms SG_of_primeConjecture
#print axioms primeConjecture_implies_all

end SGCond
