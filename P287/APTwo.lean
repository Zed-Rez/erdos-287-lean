/- **No representation of 1 has all consecutive gaps equal to 2.**

Equivalently: a counterexample to #287 must contain two consecutive integers.

This is the extremal configuration for the window bound — `M/n₁ → e²` forces the complement
towards the maximum independent set, i.e. towards `T` being an arithmetic progression of
difference 2 — so it is worth knowing it is impossible outright. (For even first term this is
Kürschák's theorem after halving; the general statement is classical, Erdős–Nagell. The proof
below is neither, and needs nothing beyond Bertrand and Lemma A′.)

`T = {a, a+2, …, M}` is *every* integer of `[a, M]` congruent to `a` mod 2. That is a very rigid
set: it must contain whatever Bertrand's postulate puts in the right range, and Lemma A′ then
removes it.

    2a ≤ M                                    always, by `PCI.two_mul_first_le_last`
    a odd :  a prime p ∈ (M/2, M] lies in T,   and ⌊M/p⌋ = 1, so Lemma A′ (1·1! < p) kills it
    a even:  a prime p ∈ (M/4, M/2] gives 2p ∈ T; the terms divisible by p are m·p with m ≤ 3,
             and m must be even, so 2p is the only one — Lemma A′ (3·3! = 18 < p) kills it

The even case is where the "all gaps 2" hypothesis really bites: it is what forces the multiples
of `p` inside the window to be even, hence to be `2p` alone.
-/
import P287.StepAB
import Mathlib.NumberTheory.Bertrand

namespace APTwo

variable {k : ℕ}

/-- **An arithmetic progression of difference 2 never has reciprocal sum 1.** -/
theorem no_ap2 (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hbig : 200 ≤ s ⟨0, by omega⟩)
    (hap : ∀ i : Fin k, s i = s ⟨0, by omega⟩ + 2 * i.val) :
    False := by
  set a := s ⟨0, by omega⟩ with ha
  set M := s ⟨k - 1, by omega⟩ with hM
  have hMval : M = a + 2 * (k - 1) := by
    rw [hM, hap ⟨k - 1, by omega⟩]
  have h2a : 2 * a ≤ M := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
  -- membership: every integer of [a, M] with the parity of a is a term
  have hmem : ∀ n : ℕ, a ≤ n → n ≤ M → (n - a) % 2 = 0 → ∃ i : Fin k, s i = n := by
    intro n hlo hhi hpar
    refine ⟨⟨(n - a) / 2, by omega⟩, ?_⟩
    rw [hap ⟨(n - a) / 2, by omega⟩]
    simp only [Fin.val_mk]
    omega
  rcases Nat.even_or_odd a with hev | hod
  · -- a even: use 2p with p a prime in (M/4, M/2]
    have hev' : a % 2 = 0 := Nat.even_iff.mp hev
    obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (M / 4) (by omega)
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hfac : Nat.factorial 3 = 6 := by norm_num [Nat.factorial]
    have hno := StepAB.notTermA (p := p) (t := 3) (n := 2 * p) (a := 2)
      hp (by norm_num) (by rw [hfac]; omega) (by ring)
      hk s hmono h1 hsum (by omega)
    obtain ⟨i, hi⟩ := hmem (2 * p) (by omega) (by omega) (by omega)
    exact hno i hi
  · -- a odd: use a prime in (M/2, M] directly
    have hod' : a % 2 = 1 := Nat.odd_iff.mp hod
    obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (M / 2) (by omega)
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hfac : Nat.factorial 1 = 1 := by norm_num [Nat.factorial]
    have hno := StepAB.notTermA (p := p) (t := 1) (n := p) (a := 1)
      hp (by norm_num) (by rw [hfac]; omega) (by ring)
      hk s hmono h1 hsum (by omega)
    obtain ⟨i, hi⟩ := hmem p (by omega) (by omega) (by omega)
    exact hno i hi

/-- **A counterexample to #287 must contain two consecutive integers**: not every gap can be 2. -/
theorem not_all_gaps_two (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hbig : 200 ≤ s ⟨0, by omega⟩)
    (hall : ∀ (j : ℕ) (h : j + 1 < k), s ⟨j + 1, h⟩ = s ⟨j, by omega⟩ + 2) :
    False := by
  refine no_ap2 hk s hmono h1 hsum hbig ?_
  have hAP : ∀ (j : ℕ) (hj : j < k), s ⟨j, hj⟩ = s ⟨0, by omega⟩ + 2 * j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ n ih =>
        intro hj
        have hprev := ih (by omega)
        have hstep := hall n (by omega)
        omega
  intro i
  have := hAP i.val i.isLt
  simpa using this

#print axioms not_all_gaps_two

#print axioms no_ap2

end APTwo
