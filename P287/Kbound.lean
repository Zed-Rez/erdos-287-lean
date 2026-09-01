/- A lower bound on the NUMBER OF TERMS, from the verified range.

The published record for #287 is quoted as n₁ > 3.994·10¹⁹ and k ≥ 6.863·10¹⁹.
`Main2.erdos287_below` bounds the largest term M, and converting that into a bound
on k needs no analysis at all — only two facts, both already available:

  * `PCI.two_mul_first_le_last` : 2·n₁ ≤ M   (counting, already kernel-clean)
  * gaps ≤ 2 telescoped        : M ≤ n₁ + 2(k−1)

Together 2M ≤ 2n₁ + 4(k−1) ≤ M + 4(k−1), so **M ≤ 4(k−1)**. A counterexample with
few terms therefore has a small largest term, and lands inside the verified range.

(The analogous bound on n₁ would need an UPPER bound M < C·n₁, which is nowhere in
this development — the counting bound points the other way. See NOTES.md plan 0
for the elementary five-block proof of M < 32·n₁ that would supply it.)
-/
import P287.Main2

namespace Kbound

/-- Each consecutive gap is at most `max_gap`. -/
theorem step_le {k : ℕ} (s : Fin k → ℕ) (hg : PCI.max_gap k s ≤ 2)
    (i : ℕ) (hi : i + 1 < k) :
    s ⟨i + 1, hi⟩ ≤ s ⟨i, by omega⟩ + 2 := by
  have h : s ⟨i + 1, hi⟩ - s ⟨i, by omega⟩ ≤ PCI.max_gap k s := by
    first
    | exact Finset.le_sup (f := fun j : Fin (k - 1) =>
        s ⟨j.val + 1, by omega⟩ - s ⟨j.val, by omega⟩)
        (Finset.mem_univ (⟨i, by omega⟩ : Fin (k - 1)))
    | · simp only [PCI.max_gap]
        exact Finset.le_sup (Finset.mem_univ (⟨i, by omega⟩ : Fin (k - 1)))
  omega

/-- Telescoping: with all gaps ≤ 2 the `j`-th term is at most `n₁ + 2j`. -/
theorem term_le {k : ℕ} (s : Fin k → ℕ) (hk : 2 ≤ k) (hg : PCI.max_gap k s ≤ 2) :
    ∀ j : ℕ, ∀ hj : j < k, s ⟨j, hj⟩ ≤ s ⟨0, by omega⟩ + 2 * j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := step_le s hg n hj
      omega

/-- **Every counterexample to #287 has more than 2.1474·10²³ terms.**

Stated in the contrapositive: a representation with at most 214 747 052 809 949 179 543 554
terms has a gap of at least 3. The published record is k ≥ 6.863·10¹⁹, so this is
larger by a factor of about 3129 — and it is kernel-checked. -/
theorem erdos287_k {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hkle : k ≤ 214747052809949179543554) :
    3 ≤ PCI.max_gap k s := by
  by_contra hc
  push_neg at hc
  have hg : PCI.max_gap k s ≤ 2 := by omega
  have h2 := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
  have h3 := term_le s hk hg (k - 1) (by omega)
  have hM : s ⟨k - 1, by omega⟩ ≤ 858988211239796718174213 := by omega
  have := Main2.erdos287_below hk s hmono h1 hsum hM
  omega

#print axioms term_le
#print axioms erdos287_k

end Kbound
