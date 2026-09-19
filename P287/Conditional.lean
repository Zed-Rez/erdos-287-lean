/- Erdos #287 in full, from a hypothesis that is only about LARGE M.

`Main3.erdos287_below` settles every M up to 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435
unconditionally. Above that, one *rung* per M suffices. -/
import P287.Main3
import P287.StepA2

namespace Conditional

/-- A *rung* for `M`. -/
def rung (M : ℕ) : Prop :=
  ∃ p q n a b tp tq : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ 1 ≤ tp ∧ 1 ≤ tq ∧
    tp * Nat.factorial tp < p ∧ tq * Nat.factorial tq < q ∧
    n = a * p ∧ n + 1 = b * q ∧
    n + 2 ≤ M ∧ M < (tp + 1) * p ∧ M < (tq + 1) * q ∧ 2 * M + 20 ≤ 5 * n

/-- **Erdos #287, conditional only above the verified range.** -/
theorem erdos287_of_rung
    (H : ∀ M : ℕ, 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435 < M → rung M)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    3 ≤ PCI.max_gap k s := by
  by_cases hM : s ⟨k - 1, by omega⟩ ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435
  · exact Main3.erdos287_below hk s hmono h1 hsum hM
  push_neg at hM
  obtain ⟨p, q, n, a, b, tp, tq, hp, hq, htp, htq, hpf, hqf, hna, hnb,
    hlo, hhip, hhiq, hint⟩ := H _ hM
  exact StepA2.step_gap hp hq htp htq hpf hqf hna hnb hk s hmono h1 hsum
    hlo hhip hhiq hint

#print axioms erdos287_of_rung

end Conditional
