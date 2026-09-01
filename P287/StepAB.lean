/- Rungs that may use EITHER exclusion rule on either side.

`StepA.step_gap` fixes both exclusions to be rule A (Lemma A′ at a prime factor).
That is enough for every M ≥ 39, but the residue {9,10,11,21,22,23,33,…,38} needs
rule B (`RuleB.ruleB`, the unique q-adic maximiser) at the prime powers 8, 16, 25,
32. So the rung is split into three reusable pieces:

  `setup`        — the Finset of terms, with positivity, the bound by M, and the sum;
  `notTermA` / `notTermB` — one exclusion each, in the form `∀ i, s i ≠ n`;
  `gap_of_excl`  — the glue: two consecutive excluded interior values give a gap ≥ 3.

Interiority still uses only the counting bound `2·n₁ ≤ M`.
-/
import P287.Part1
import P287.LemAGenMod
import P287.RuleB

namespace StepAB

open Finset

theorem setup {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    (∀ x ∈ Finset.image s Finset.univ, 0 < x) ∧
    (∀ x ∈ Finset.image s Finset.univ, x ≤ s ⟨k - 1, by omega⟩) ∧
    (∑ x ∈ Finset.image s Finset.univ, ((x : ℚ))⁻¹ = 1) := by
  classical
  have hmono_le : ∀ i : Fin k, s ⟨0, by omega⟩ ≤ s i := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hle_last : ∀ i : Fin k, s i ≤ s ⟨k - 1, by omega⟩ := by
    intro i
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with h | h
    · have : i = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hmono_le i; omega
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hle_last i; omega
  · rw [Finset.sum_image (hmono.injective.injOn)]; exact hsum

/-- Rule A: `n` is not a term, because some prime `p ∣ n` satisfies Lemma A′. -/
theorem notTermA {p t n : ℕ} (hp : Nat.Prime p) (ht : 1 ≤ t)
    (hpf : t * Nat.factorial t < p) {a : ℕ} (hna : n = a * p)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < (t + 1) * p) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := setup hk s hmono h1 hsum
  have hno : ¬ ∃ x ∈ Finset.image s Finset.univ, p ∣ x := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    intro hex
    refine LemAGen.lemA_gen (p := p) (t := t) ht hpf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ t := by
      by_contra hc
      push_neg at hc
      have hmul : p * (t + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
      have e1 : p * (t + 1) = (t + 1) * p := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  intro i hi
  refine hno ⟨n, ?_, ⟨a, by rw [hna]; ring⟩⟩
  rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)

/-- Rule B: `n = q^e` is not a term, because it is the unique element of the
window of maximal `q`-adic valuation. -/
theorem notTermB {q e n : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e) (hn : n = q ^ e)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < 2 * n) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := setup hk s hmono h1 hsum
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  rw [hn] at hhi
  have hno := RuleB.ruleB (q := q) (e := e) (M := s ⟨k - 1, by omega⟩) he
    hTpos hTle hhi hsumT
  intro i hi
  refine hno ?_
  rw [← hn, ← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)

/-- The glue: two consecutive excluded values, both interior, give a gap ≥ 3. -/
theorem gap_of_excl {n k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 2 ≤ s ⟨k - 1, by omega⟩)
    (hint : s ⟨k - 1, by omega⟩ ≤ 2 * n + 1)
    (hexn : ∀ i, s i ≠ n) (hexn1 : ∀ i, s i ≠ n + 1) :
    3 ≤ PCI.max_gap k s := by
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
    omega
  exact PCI.gap_three_of_two_missing hk s hs0 (by omega) hexn hexn1

/-- **The largest term is never a prime power.** Rule B excludes `q^e` whenever
`M < 2q^e`, and `M = q^e` satisfies that trivially — but `M` is a term. This kills
the two M values ({4, 8}) for which no pair of consecutive interior exclusions
exists, and it is why the base case needs no exhaustive search at all. -/
theorem max_prime_pow {q e : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hM : s ⟨k - 1, by omega⟩ = q ^ e) : False := by
  have hpos : 0 < q ^ e := pow_pos hq.pos e
  have hno := notTermB (q := q) (e := e) (n := q ^ e) hq he rfl hk s hmono h1 hsum
    (by omega)
  exact hno ⟨k - 1, by omega⟩ hM

#print axioms max_prime_pow
#print axioms notTermA
#print axioms notTermB
#print axioms gap_of_excl

end StepAB
