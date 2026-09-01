/- Assembly of `prime_conjecture_implies`, importing the lemmas from `Part1`.
   Split into two modules so each compile stays inside the fast-lane budget. -/
import P287.Part1

namespace PCI

open Finset

/-! ### The implication -/

/-- **`erdos_287.variants.prime_conjecture_implies`.**  The hypothesis is the
right-hand side of `prime_conjecture`; upstream it arrives as `True ↔ this`, from
which it is extracted by `.mp trivial` (checked separately in verified/012).
Stated over ℚ with the upstream ∀-binder shape and `max_gap` byte-identical. The
ℝ-valued form follows by the cast bridge `sum_rat_of_sum_real`, itself kernel-
verified in verified/010 — but composing the two in ONE file peaks at 2278 MB,
over the 1638 MB fast-lane silo, so that last compose step is budget-blocked and
is NOT claimed here. -/
theorem prime_conjecture_implies_rat
    (H : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ P : ℕ, Nat.Prime P ∧ N ≤ P ∧ P ≤ 2 * N ∧ Nat.Prime ((P + 1) / 2)) :
    ∃ (k₀ : ℕ), ∀ (k : ℕ) (hk₀ : k₀ ≤ k) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1 →
      3 ≤ max_gap k s := by
  classical
  obtain ⟨N₀, hN₀⟩ := H
  refine ⟨2 * N₀ + 1000, ?_⟩
  intro k hk₀ hk s hmono h1 hsum
  have hgrow := growth hk s hmono
  set M := s ⟨k - 1, by omega⟩ with hMdef
  have hMk : s ⟨0, by omega⟩ + (k - 1) ≤ M := hgrow (k - 1) (by omega)
  have hMlarge : 2 * N₀ + 1000 ≤ M := by omega
  -- the term set
  set T : Finset ℕ := Finset.image s Finset.univ with hTdef
  have hsumT : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1 := by
    rw [hTdef, Finset.sum_image (hmono.injective.injOn)]; exact hsum
  have hmono_le : ∀ i : Fin k, s ⟨0, by omega⟩ ≤ s i := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hle_last : ∀ i : Fin k, s i ≤ M := by
    intro i
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with h | h
    · have : i = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTpos : ∀ n ∈ T, 0 < n := by
    intro n hn
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hn
    have := hmono_le i
    omega
  have hTle : ∀ n ∈ T, n ≤ M := by
    intro n hn
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hn
    have := hle_last i
    omega
  -- get the prime
  obtain ⟨P, hPprime, hPlo, hPhi, hQprime⟩ := hN₀ (M / 2) (by omega)
  have hPbig : 500 ≤ P := by omega
  have hP2 : P ≠ 2 := by omega
  have hPodd : P % 2 = 1 := by
    rcases Nat.even_or_odd P with he | ho
    · exfalso
      obtain ⟨c, hc⟩ := he
      have hdvd : (2 : ℕ) ∣ P := ⟨c, by omega⟩
      rcases Nat.Prime.eq_one_or_self_of_dvd hPprime 2 hdvd with h | h <;> omega
    · obtain ⟨m, hm⟩ := ho
      omega
  set Q := (P + 1) / 2 with hQdef
  have h2Q : 2 * Q = P + 1 := by omega
  have hQbig : 48 < Q := by omega
  -- no term is divisible by P
  have hnoP : ¬ ∃ n ∈ T, P ∣ n := by
    haveI : Fact (Nat.Prime P) := ⟨hPprime⟩
    intro hex
    refine lemA_two (p := P) (by omega) hTpos ?_ hex hsumT
    intro n hn hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hnle := hTle n hn
    have hnpos := hTpos n hn
    have hm3 : m < 3 := by
      by_contra hcon
      push_neg at hcon
      have : P * 3 ≤ P * m := Nat.mul_le_mul_left _ hcon
      omega
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hm; omega
      · exact h
    interval_cases m
    · left; omega
    · right; omega
  -- no term is divisible by Q
  have hnoQ : ¬ ∃ n ∈ T, Q ∣ n := by
    haveI : Fact (Nat.Prime Q) := ⟨hQprime⟩
    intro hex
    refine lemA_four (p := Q) hQbig hTpos ?_ hex hsumT
    intro n hn hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hnle := hTle n hn
    have hnpos := hTpos n hn
    have hm5 : m < 5 := by
      by_contra hcon
      push_neg at hcon
      have : Q * 5 ≤ Q * m := Nat.mul_le_mul_left _ hcon
      omega
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hm; omega
      · exact h
    interval_cases m
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  -- so P and P+1 are not terms
  have hPnotin : ∀ i, s i ≠ P := by
    intro i hi
    exact hnoP ⟨P, by rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i),
      dvd_refl P⟩
  have hP1notin : ∀ i, s i ≠ P + 1 := by
    intro i hi
    refine hnoQ ⟨P + 1, ?_, ⟨2, by omega⟩⟩
    rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  -- both lie strictly inside the range
  have hs0P : s ⟨0, by omega⟩ ≤ P := by
    have := two_mul_first_le_last hk s hmono (by omega) hsum
    omega
  have hPM : P < M := by
    have := hPnotin ⟨k - 1, by omega⟩
    omega
  exact gap_three_of_two_missing hk s hs0P (by omega) hPnotin hP1notin

#print axioms lemA_two
#print axioms lemA_four
#print axioms gap_three_of_two_missing
#print axioms two_mul_first_le_last
#print axioms prime_conjecture_implies_rat

end PCI
