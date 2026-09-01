/- **The gaps-≤3 rung, with both sharp tools.**

`StepG3.step_gap4` was written before two sharper lemmas existed and still uses the crude form of
each:

* Lemma A′ as `t·t! < p`, where `StepG3C.notTermA_sharp` gives `t·lcm(1..t) < p`. The two agree up
  to `t = 3` and first differ at `t = 4`, where `4·4! = 96` becomes `4·lcm(1..4) = 48`; by `t = 8`
  it is `8·8! = 322560` against `8·lcm(1..8) = 6720`, a factor of 48.
* interiority from `Lower.lower` (`5n₁ ≤ 2M + 20`, the factor-2.5 bound), where `Lower3.lower3`
  (`2718·n₁ ≤ 1000M + 2718`) is sharp at `e = 2.71828`.

Both feed the same place: a rung at `n` covers `M` up to `min((t+1)p, …)` from Lemma A′ and up to
the interiority cap from below. Measured on the existing ladder, **interiority is what binds** — its
rungs sit at `ln 0.9139` per rung against the 2.5 cap's `0.9163` — so raising the cap from `2.5n` to
`e(n−1)` is worth `ln 1.0` per rung, and the sharper Lemma A′ widens the admissible `(t, p)` on top
of that.

Unlike the same change on the gaps-≤2 ladder, this is not a treadmill: `g = 3` is a COMPLETE
CLASSIFICATION — `{2,3,6}` is the only gaps-≤3 representation of 1 with `M ≤ X` — so raising `X`
sharpens a finished statement rather than inflating a bound.
-/
import P287.StepG3C
import P287.Lower3

namespace StepG3S

/-- One rung of the gaps-≤3 ladder: three consecutive forced-out interior integers, with the
sharp Lemma A′ and the sharp interiority bound. -/
theorem step_gap4_sharp {p q r n a b c tp tq tr : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (htp : 1 ≤ tp) (htq : 1 ≤ tq) (htr : 1 ≤ tr)
    (hpf : tp * LemAGen.lcmUpto tp < p) (hqf : tq * LemAGen.lcmUpto tq < q)
    (hrf : tr * LemAGen.lcmUpto tr < r)
    (hna : n = a * p) (hnb : n + 1 = b * q) (hnc : n + 2 = c * r)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 3 ≤ s ⟨k - 1, by omega⟩)
    (hhip : s ⟨k - 1, by omega⟩ < (tp + 1) * p)
    (hhiq : s ⟨k - 1, by omega⟩ < (tq + 1) * q)
    (hhir : s ⟨k - 1, by omega⟩ < (tr + 1) * r)
    (hint : 1000 * s ⟨k - 1, by omega⟩ + 2718 ≤ 2718 * n) :
    4 ≤ PCI.max_gap k s := by
  have e0 := StepG3C.notTermA_sharp hp htp hpf hna hk s hmono h1 hsum hhip
  have e1 := StepG3C.notTermA_sharp hq htq hqf hnb hk s hmono h1 hsum hhiq
  have e2 := StepG3C.notTermA_sharp hr htr hrf hnc hk s hmono h1 hsum hhir
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := Lower3.lower3 hk s hmono h1 hsum
    omega
  exact PCI.gap_four_of_three_missing hk s hs0 (by omega) e0 e1 e2

#print axioms step_gap4_sharp

end StepG3S
