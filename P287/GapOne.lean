/- **The counting identity behind every `g₁` statement.**

`g₁` — the number of gap-1 steps, i.e. of integers `m` with both `m` and `m+1` denominators — is the
quantity the parity lever bounds (`AltChain`, `RoughChain`) and the quantity `Window4` would improve
through `R ≤ e²(1 − g₁/M)`. But every Lean statement so far concludes about `|C|`, and the passage to
`g₁` was prose. This file closes that gap:

> **`g1_add_compl_card`.** `g₁ + |C| + 1 = k`.

Equivalently `g₁ = k − 1 − |C|`, and combined with `|C| + k = M + 1 − n₁` (`KStep`) it is the form
used in the prose, `g₁ = W − 1 − 2|C|`.

**The proof is a three-way classification of `m ∈ [n₁, M)`.** Independence of `C` rules out `m ∉ T`
and `m+1 ∉ T` simultaneously, so each such `m` is one of

* both `m, m+1` denominators — counted by `g₁`;
* `m` a denominator, `m+1` not — these biject with `C` under `m ↦ m+1`;
* `m` not a denominator — these are exactly `C`, but this case is not needed separately: the split
  `g₁ + #{m ∈ T : m+1 ∉ T} = #{m ∈ T ∩ [n₁,M)} = k − 1` already finishes it.

The bijection is realised concretely as `A.image (· + 1) = C`, which avoids the argument-order
fragility of `Finset.card_bij'` and needs only `Finset.card_image_of_injective`.
-/
import P287.KStep

namespace GapOne

open Finset

variable {k : ℕ}

/-- **`g₁`**: the number of gap-1 steps — integers `m` in `[n₁, M)` with `m` and `m+1` both
denominators. -/
noncomputable def g1 (k : ℕ) (s : Fin k → ℕ) (hk : 2 ≤ k) : ℕ :=
  ((Finset.Ico (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩)).filter
    (fun m => m ∈ Finset.image s Finset.univ ∧ m + 1 ∈ Finset.image s Finset.univ)).card

/-- **`g₁ + |C| + 1 = k`.** -/
theorem g1_add_compl_card (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hg : PCI.max_gap k s ≤ 2) :
    g1 k s hk + (KStep.compl k s hk).card + 1 = k := by
  classical
  set n1 := s ⟨0, by omega⟩ with hn1
  set M := s ⟨k - 1, by omega⟩ with hM
  set T := Finset.image s Finset.univ with hT
  set C := KStep.compl k s hk with hC
  obtain ⟨hpos, hle, -⟩ := StepAB.setup hk s hmono h1 hsum
  -- `T` sits inside the window and has `k` elements
  have hTsub : T ⊆ Finset.Icc n1 M := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
    refine Finset.mem_Icc.mpr ⟨?_, hi ▸ hle x hx⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have hi0 : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [← hi, hi0]
    · exact hi ▸ le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTcard : T.card = k := by
    rw [hT, Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hMT : M ∈ T := Finset.mem_image_of_mem s (Finset.mem_univ (⟨k - 1, by omega⟩ : Fin k))
  -- `{m ∈ [n₁,M) : m ∈ T}` is `T.erase M`, so it has `k − 1` elements
  have hbase : (Finset.Ico n1 M).filter (fun m => m ∈ T) = T.erase M := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hlt⟩, hmT⟩; exact ⟨by omega, hmT⟩
    · rintro ⟨hne, hmT⟩
      have := Finset.mem_Icc.mp (hTsub hmT)
      exact ⟨⟨this.1, by omega⟩, hmT⟩
  have hbasecard : ((Finset.Ico n1 M).filter (fun m => m ∈ T)).card = k - 1 := by
    rw [hbase, Finset.card_erase_of_mem hMT, hTcard]
  -- the elements of `C` are interior
  have hCmem : ∀ x ∈ C, n1 + 1 ≤ x ∧ x ≤ M := by
    intro x hx
    refine ⟨?_, (KStep.compl_mem hk s hx).2⟩
    have hlo := (KStep.compl_mem hk s hx).1
    rcases Nat.eq_or_lt_of_le hlo with h | h
    · exact absurd (h ▸ (Finset.mem_image_of_mem s (Finset.mem_univ (⟨0, by omega⟩ : Fin k))))
        (Finset.mem_sdiff.mp hx).2
    · omega
  -- **the bijection** `A ↦ A + 1` from `{m ∈ T : m+1 ∉ T}` onto `C`
  -- NO `set` here: `hsplit` is created afterwards, so `set` would not fold into it and the
  -- `←` rewrite finds no pattern (LEDGER 362, in its `set`-scope form).
  have hAimg : (((Finset.Ico n1 M).filter (fun m => m ∈ T)).filter
      (fun m => ¬ (m + 1 ∈ T))).image (fun m => m + 1) = C := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨m, ⟨⟨⟨hml, hmr⟩, -⟩, hm1⟩, rfl⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hm1⟩
    · intro hx
      obtain ⟨hxlo, hxhi⟩ := hCmem x hx
      refine ⟨x - 1, ⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, by omega⟩
      · -- `x − 1` is a denominator: it is in the window and not in `C`
        have hne : x - 1 ∉ C := by
          intro hc
          have := KStep.compl_indep hk s hg _ hc
          rw [show x - 1 + 1 = x by omega] at this
          exact this hx
        have hin : x - 1 ∈ Finset.Icc n1 M := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        rw [hC, KStep.compl, Finset.mem_sdiff] at hne
        push_neg at hne
        exact hne hin
      · rw [show x - 1 + 1 = x by omega]
        exact (Finset.mem_sdiff.mp hx).2
  have hAcard : (((Finset.Ico n1 M).filter (fun m => m ∈ T)).filter
      (fun m => ¬ (m + 1 ∈ T))).card = C.card := by
    rw [← hAimg, Finset.card_image_of_injective _ (add_left_injective 1)]
  -- split `{m ∈ [n₁,M) : m ∈ T}` by whether `m+1` is a denominator
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.Ico n1 M).filter (fun m => m ∈ T)) (p := fun m => m + 1 ∈ T)
  have hg1 : g1 k s hk = (((Finset.Ico n1 M).filter (fun m => m ∈ T)).filter
      (fun m => m + 1 ∈ T)).card := by
    rw [g1]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico]
    tauto
  have hk1 : 1 ≤ k := by omega
  rw [hg1]
  rw [hbasecard] at hsplit
  rw [hAcard] at hsplit
  omega

/-- **The window count**: `n₁ + |C| + k = M + 1`. Needed to pass between `|C|` bounds (what the
parity machinery produces) and `g₁` bounds (what the archimedean bracket consumes). -/
theorem window_count (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    s ⟨0, by omega⟩ + (KStep.compl k s hk).card + k = s ⟨k - 1, by omega⟩ + 1 := by
  classical
  obtain ⟨hpos, hle, -⟩ := StepAB.setup hk s hmono h1 hsum
  have hTsub : Finset.image s Finset.univ ⊆
      Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩) := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
    refine Finset.mem_Icc.mpr ⟨?_, hi ▸ hle x hx⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have hi0 : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [← hi, hi0]
    · exact hi ▸ le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTcard : (Finset.image s Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hadd := Finset.card_sdiff_add_card_eq_card hTsub
  rw [hTcard, Nat.card_Icc] at hadd
  have hnM : s ⟨0, by omega⟩ ≤ s ⟨k - 1, by omega⟩ :=
    hle _ (Finset.mem_image_of_mem s (Finset.mem_univ (⟨0, by omega⟩ : Fin k)))
  rw [KStep.compl]
  omega

#print axioms window_count
#print axioms g1_add_compl_card

end GapOne
