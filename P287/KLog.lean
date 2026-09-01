/- **Step (d): converting the harmonic inequality of `KStep.greedy_le` into an algebraic one.**

`KStep.greedy_le` gives `∑_{j<c} 1/(M−2j) ≤ H(n₁,M) − 1` with `c = |C|`. Two telescoping lemmas
that already exist turn that into a polynomial relation:

* **`Window4.tele`** bounds a stride-2 sum BELOW by a log. Reindexing `j ↦ c−1−j` turns
  `∑_{j<c} 1/(M−2j)` into the stride-2 sum `∑_{i<c} 1/((M−2c+2) + 2i)`, so
  `log(M+2) − log(M−2c+2) ≤ 2·∑_{j<c} 1/(M−2j)`.
* **`Lower3.tele`** bounds `H(n₁,M)` ABOVE by `log M − log(n₁−1)`.

Together: `log(M+2) + 2log(n₁−1) + 2 ≤ log(M−2c+2) + 2log M`, and exponentiating with
`e² > 7.389` gives `7389·(M+2)·(n₁−1)² ≤ 1000·(M−2c+2)·M²`.

**Only the reindexing step is proved here.** The cast-and-exponentiate step is written up in
`verified/104/README.md` and follows `Lower3.lower3`'s pattern (`push_cast` + `Finset.sum_congr`
to cross ℚ→ℝ, then `Real.le_log_iff_exp_le`); it is deliberately NOT stubbed — this workspace
does not admit `sorry`.

The pairing shortcut does NOT work here: pairing the terms bounds the greedy sum ABOVE, and
`greedy_le` already supplies an upper bound — a LOWER bound is what is needed, which is exactly
what `Window4.tele` provides.
-/
import P287.KStep
import P287.Window4
import P287.Lower3

namespace KLog

open Finset

variable {k : ℕ}

/-- The greedy sum, reindexed as a stride-2 sum running upward from `M − 2c + 2`. -/
theorem greedy_reindex (M c : ℕ) (hc : 2 * c ≤ M) :
    ∑ j ∈ Finset.range c, (((M - 2 * j : ℕ) : ℚ))⁻¹
      = ∑ i ∈ Finset.range c, (((M - 2 * c + 2 + 2 * i : ℕ) : ℚ))⁻¹ :=
  -- `rw [Finset.sum_congr …]` fails on a beta-reduction mismatch; a `calc` sidesteps it.
  calc ∑ j ∈ Finset.range c, (((M - 2 * j : ℕ) : ℚ))⁻¹
      = ∑ j ∈ Finset.range c, (((M - 2 * c + 2 + 2 * (c - 1 - j) : ℕ) : ℚ))⁻¹ :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          have h : M - 2 * j = M - 2 * c + 2 + 2 * (c - 1 - j) := by omega
          rw [h])
    _ = ∑ i ∈ Finset.range c, (((M - 2 * c + 2 + 2 * i : ℕ) : ℚ))⁻¹ :=
        Finset.sum_range_reflect (fun i => (((M - 2 * c + 2 + 2 * i : ℕ) : ℚ))⁻¹) c

/-- **The exponentiation step.** Turns the log inequality into a polynomial one. Self-contained
real analysis: `log A + 2log E + 2 ≤ log B + 2log D` exponentiates to `e²·A·E² ≤ B·D²`. -/
theorem exp_step {A B D E : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hE : 0 < E)
    (h : Real.log A - Real.log B ≤ 2 * (Real.log D - Real.log E) - 2) :
    Real.exp 2 * (A * E ^ 2) ≤ B * D ^ 2 := by
  have h1 : Real.log (A * E ^ 2) + 2 ≤ Real.log (B * D ^ 2) := by
    rw [Real.log_mul (ne_of_gt hA) (by positivity), Real.log_mul (ne_of_gt hB) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_add, Real.exp_log (by positivity : (0:ℝ) < A * E ^ 2),
      Real.exp_log (by positivity : (0:ℝ) < B * D ^ 2)] at h2
  linarith [h2]

/-- `e² > 7.389`, in the rational form the integer statement needs. -/
theorem exp_two_gt : (7389 : ℝ) / 1000 < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [h, Real.exp_pos 1]

/-- **Step (d), assembled.** `KStep.greedy_le` cast to ℝ, then `Window4.tele` (a log LOWER bound on
the stride-2 sum) and `Lower3.tele` (a log UPPER bound on `H(n₁,M)`). -/
theorem log_ineq (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2)
    (hc : 2 * (KStep.compl k s hk).card ≤ s ⟨k - 1, by omega⟩) :
    Real.log ((s ⟨k - 1, by omega⟩ : ℝ) + 2)
        - Real.log (((s ⟨k - 1, by omega⟩ - 2 * (KStep.compl k s hk).card + 2 : ℕ) : ℝ))
      ≤ 2 * (Real.log ((s ⟨k - 1, by omega⟩ : ℝ)) - Real.log ((s ⟨0, by omega⟩ : ℝ) - 1)) - 2 := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  set c := (KStep.compl k s hk).card with hcdef
  set B := M - 2 * c + 2 with hBdef
  have hBpos : 0 < B := by omega
  have hnM : n1 ≤ M := by
    obtain ⟨-, hle, -⟩ := StepAB.setup hk s hmono h1 hsum
    exact hle n1 (Finset.mem_image_of_mem s (Finset.mem_univ _))
  -- (1) the greedy sum in ℚ, reindexed
  have hq := KStep.greedy_le hk s hmono h1 hsum hg
  rw [greedy_reindex M c hc] at hq
  -- (2) cross to ℝ.  `push_cast` normalises every cast into `↑M - 2↑c` form; do NOT try to
  -- rewrite with a hand-written cast lemma afterwards, the pattern is already gone.
  have hcle : 2 * c ≤ M := hc
  have hqR := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast [Nat.cast_sub hcle] at hqR
  -- (3) Window4.tele on the stride-2 sum
  have htelW := Window4.tele B hBpos c
  rw [hBdef] at htelW
  push_cast [Nat.cast_sub hcle] at htelW
  have hBc : ((M : ℝ) - 2 * (c : ℝ)) + 2 + 2 * (c : ℝ) = (M : ℝ) + 2 := by ring
  rw [hBc] at htelW
  -- (4) Lower3.tele on H(n₁,M), after shifting Icc to range
  have hshift : (∑ n ∈ Finset.Icc n1 M, ((n : ℝ))⁻¹)
      = ∑ i ∈ Finset.range (M + 1 - n1), ((n1 : ℝ) + (i : ℝ))⁻¹ := by
    rw [show Finset.Icc n1 M = Finset.Ico n1 (M + 1) by
          ext x; simp [Finset.mem_Icc, Finset.mem_Ico]]
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring_nf)
  have htelL := Lower3.tele n1 h1 (M + 1 - n1)
  simp only [one_div] at htelL
  have hMc : ((n1 : ℝ) + ((M + 1 - n1 : ℕ) : ℝ) - 1) = (M : ℝ) := by
    push_cast [Nat.cast_sub (show n1 ≤ M + 1 by omega)]
    ring
  rw [hMc] at htelL
  rw [hshift] at hqR
  -- linarith treats `1/y` and `y⁻¹` as DIFFERENT atoms, and the goal still carries the ℕ-cast
  simp only [one_div] at htelW
  -- the goal still carries `↑B` (a `set` definition, opaque to push_cast) — unfold it first
  rw [hBdef]
  push_cast [Nat.cast_sub hcle]
  linarith [htelW, htelL, hqR]

#print axioms log_ineq
#print axioms greedy_reindex
#print axioms exp_step
#print axioms exp_two_gt

end KLog
