/- **Cashing in the parity lever: a free prime forces many adjacent term-pairs.**

`AltChain.card_le_of_alt_chain'` says an alternating-parity chain of length `t` in the complement
costs `t − 1` units of window, i.e. `g₁ ≥ t − 1` where `g₁ = W − 1 − 2|C|` counts the gap-1 steps.
Producing a long chain looked like it needed rough numbers of both parities interleaved — a
primes-in-short-intervals statement. It does not, because of one observation:

> If an **odd** prime `p` divides no denominator, then every multiple of `p` in the window is a
> non-term, and **consecutive multiples differ by `p`, which is odd — so they alternate in parity.**

So the multiples of a single free prime are an alternating chain *for free*. `Rough.term_smooth`
gives `P(n) ≤ M/431` for every denominator, so every prime `p > M/431` is free, and such a `p` has
`t ≈ W/p` multiples in the window. Since `W/M = 1 − 1/R` with `R ∈ [e, e²]`, the GUARANTEED `t` uses
`R = e` (`W ≥ 0.6321·M`): Bertrand (`p ≤ 2M/431`) gives `t ≥ 135`, and a prime just above `M/431`
would give `t ≥ 272`. The best-case (`R = e²`) figures are `186` and `373`.

> **`compl_card_of_free_prime`.** `p` an odd prime dividing no denominator, with `t` consecutive
> multiples `a·p, …, (a+t−1)·p` inside the window ⟹ `n₁ + 2|C| + t ≤ M + 1`, i.e. **`g₁ ≥ t − 1`**.

That is `g₁ ≥ 134` from Bertrand alone, against the previous `g₁ ≥ 2` from `PowBlock` — about
sixty-five times better, and the first end-to-end use of the parity machinery.

**It does not move `Window4`.** The bracket gives `R ≤ e²(1 − g₁/M)`, and `t` is `O(1)` while `M` is
astronomical, so the gain is `O(1/M)`. A positive *fraction* still needs the interleaving of the
whole rough set. What this settles is that the lever is real and instantiable, not merely abstract.
-/
import P287.AltChain
import P287.KStep
import P287.GapOne

namespace RoughChain

open Finset

variable {k : ℕ}

/-- **The complement is squeezed by the multiples of a free odd prime.** -/
theorem compl_card_of_free_prime (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2)
    {p a t : ℕ} (hp2 : p % 2 = 1) (ht : 0 < t)
    (hfree : ∀ i : Fin k, ¬ p ∣ s i)
    (hlo : s ⟨0, by omega⟩ < a * p)
    (hhi : (a + t - 1) * p < s ⟨k - 1, by omega⟩) :
    s ⟨0, by omega⟩ + 2 * (KStep.compl k s hk).card + t ≤ s ⟨k - 1, by omega⟩ + 1 := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  set C := KStep.compl k s hk with hC
  have hppos : 0 < p := by omega
  -- the chain: `x i = (a + i) * p`
  set x : ℕ → ℕ := fun i => (a + i) * p with hx
  have hxmem : ∀ i, i < t → x i ∈ C := by
    intro i hi
    simp only [hx]
    have hup : (a + i) * p ≤ (a + t - 1) * p := Nat.mul_le_mul_right p (by omega)
    have hdn : a * p ≤ (a + i) * p := Nat.mul_le_mul_right p (by omega)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · intro hmem
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      exact hfree j ⟨a + i, by rw [hj]; ring⟩
  have hne : C.Nonempty := ⟨x 0, hxmem 0 ht⟩
  -- `C` lies strictly inside the window: the endpoints are denominators
  have hend0 : n1 ∈ Finset.image s Finset.univ :=
    Finset.mem_image_of_mem s (Finset.mem_univ (⟨0, by omega⟩ : Fin k))
  have hendM : M ∈ Finset.image s Finset.univ :=
    Finset.mem_image_of_mem s (Finset.mem_univ (⟨k - 1, by omega⟩ : Fin k))
  have hlo' : ∀ z ∈ C, n1 + 1 ≤ z := by
    intro z hz
    have h1' := (KStep.compl_mem hk s hz).1
    rcases Nat.eq_or_lt_of_le h1' with h | h
    · exact absurd (h ▸ hend0) (Finset.mem_sdiff.mp hz).2
    · omega
  have hhi' : ∀ z ∈ C, z ≤ M - 1 := by
    intro z hz
    have h2' := (KStep.compl_mem hk s hz).2
    rcases Nat.eq_or_lt_of_le h2' with h | h
    · exact absurd (h ▸ hendM) (Finset.mem_sdiff.mp hz).2
    · omega
  -- consecutive multiples differ by the ODD number `p`, so they alternate in parity
  have hxmono : ∀ i, i + 1 < t → x i < x (i + 1) := by
    intro i _
    simp only [hx]
    first
      | exact Nat.mul_lt_mul_of_pos_right (by omega) hppos
      | exact mul_lt_mul_of_pos_right (by omega) hppos
      | exact Nat.mul_lt_mul_right hppos |>.mpr (by omega)
  have halt : ∀ i, i + 1 < t → x i % 2 ≠ x (i + 1) % 2 := by
    intro i _
    simp only [hx]
    have hstep : (a + (i + 1)) * p = (a + i) * p + p := by ring
    rw [hstep]
    omega
  have hmain := AltChain.card_le_of_alt_chain' hne hlo' hhi'
    (KStep.compl_indep hk s hg) x ht hxmem hxmono halt
  -- `n1 ≥ 2` and `M ≥ n1 + 1`, so the ℕ-subtraction in `M - 1` is safe
  -- name these: a second anonymous `have` SHADOWS the first, so `hhi' _ this` was being fed
  -- the inequality rather than the membership (LEDGER 362's trap, in its `this` form)
  have hnM : n1 < M := by
    have hm0 := hxmem 0 ht
    have hb1 := hlo' _ hm0
    have hb2 := hhi' _ hm0
    omega
  omega

/-- **The statement in its natural form: `g₁ ≥ t − 1`.** Combines the `|C|` bound above with
`GapOne.g1_add_compl_card` (`g₁ + |C| + 1 = k`) and `GapOne.window_count` (`n₁ + |C| + k = M + 1`).
This is the claim quoted in RESULT.md; it was prose until now. -/
theorem g1_ge_of_free_prime (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2)
    {p a t : ℕ} (hp2 : p % 2 = 1) (ht : 0 < t)
    (hfree : ∀ i : Fin k, ¬ p ∣ s i)
    (hlo : s ⟨0, by omega⟩ < a * p)
    (hhi : (a + t - 1) * p < s ⟨k - 1, by omega⟩) :
    t ≤ GapOne.g1 k s hk + 1 := by
  have hC := compl_card_of_free_prime hk s hmono h1 hsum hg hp2 ht hfree hlo hhi
  have hid := GapOne.g1_add_compl_card hk s hmono h1 hsum hg
  have hwin := GapOne.window_count hk s hmono h1 hsum
  omega

#print axioms g1_ge_of_free_prime
#print axioms compl_card_of_free_prime

end RoughChain
