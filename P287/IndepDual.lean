/- **The other half of the bracket: greedy from the BOTTOM maximises the reciprocal sum.**

`IndepRank.sum_inv_ge` says the greedy set `b, b−2, b−4, …` MINIMISES `∑ 1/x` over independent
`C ⊆ [a,b]` at fixed cardinality. Its dual — `a, a+2, a+4, …` MAXIMISES it — is the half of the
archimedean bracket that had never been formalised, even though it is what pins `|C|` from below:

    ∑_{j < |C|} 1/(b − 2j)   ≤   ∑_{x ∈ C} 1/x   ≤   ∑_{j < |C|} 1/(a + 2j)

and with `∑_{x∈C} 1/x = H − 1` exactly (`KStep.compl_sum`) the two together BRACKET `|C|`. That
bracket is what factors as `(R − e²)(R − e)(R + e) ≤ 0`, i.e. it *is* `Lower3` + `Window4`, which is
why no rearrangement of archimedean data can improve either.

**No new induction is needed.** `AltChain.phi_mono` already gives that `φ(z) = z + 2·#{w ∈ C : z < w}`
is non-decreasing on `C`, and `φ(min C) = min C + 2(|C| − 1) ≥ a + 2(|C| − 1)`. Since
`#{y < z} + #{z < y} + 1 = |C|`, that rearranges to exactly the mirrored rank bound

    a + 2·#{y ∈ C : y < z}  ≤  z,

so the mirror of `IndepRank.rank_bound` is a corollary of the machinery built for the parity lever
rather than a second forty-line induction.
-/
import P287.AltChain

namespace IndepDual

open Finset

/-- How many elements of `C` lie strictly below `x`. -/
noncomputable def below (C : Finset ℕ) (x : ℕ) : ℕ := (C.filter (fun y => y < x)).card

/-- The three-way split: below, self, above. -/
theorem below_add_rk {C : Finset ℕ} {x : ℕ} (hx : x ∈ C) :
    below C x + (C.filter (fun y => x < y)).card + 1 = C.card := by
  classical
  have h1 : (C.filter (fun y => y < x)).card + (C.filter (fun y => ¬ y < x)).card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) (p := fun y => y < x)
  have h2 : C.filter (fun y => ¬ y < x) = insert x (C.filter (fun y => x < y)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨hyC, hxy⟩
      rcases eq_or_lt_of_le hxy with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hyC, h⟩
    · rintro (rfl | ⟨hyC, h⟩)
      · exact ⟨hx, le_refl _⟩
      · exact ⟨hyC, le_of_lt h⟩
  have h3 : x ∉ C.filter (fun y => x < y) := by simp
  rw [h2] at h1
  rw [show (insert x (C.filter (fun y => x < y))).card
        = (C.filter (fun y => x < y)).card + 1 from by
        first
          | exact Finset.card_insert_of_notMem h3
          | exact Finset.card_insert_of_not_mem h3] at h1
  simp only [below]
  omega

/-- **The mirrored rank bound**, from `AltChain.phi_mono` rather than a new induction. -/
theorem le_of_below {a : ℕ} {C : Finset ℕ} (hne : C.Nonempty)
    (hlo : ∀ y ∈ C, a ≤ y) (hind : ∀ y ∈ C, y + 1 ∉ C)
    {x : ℕ} (hx : x ∈ C) :
    a + 2 * below C x ≤ x := by
  classical
  have hminC : C.min' hne ∈ C := Finset.min'_mem _ hne
  have hall : C.filter (fun w => C.min' hne < w) = C.erase (C.min' hne) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hwC, hw⟩; exact ⟨by omega, hwC⟩
    · rintro ⟨hwne, hwC⟩
      have := Finset.min'_le _ w hwC
      exact ⟨hwC, by omega⟩
  have hcard : (C.filter (fun w => C.min' hne < w)).card = C.card - 1 := by
    rw [hall, Finset.card_erase_of_mem hminC]
  have hge : AltChain.phi C (C.min' hne) ≤ AltChain.phi C x := by
    rcases eq_or_lt_of_le (Finset.min'_le _ x hx) with h | h
    · rw [h]
    · exact AltChain.phi_mono hind hminC hx h
  have hphimin : AltChain.phi C (C.min' hne) = C.min' hne + 2 * (C.card - 1) := by
    simp only [AltChain.phi]; rw [hcard]
  have hsplit := below_add_rk hx
  have hamin : a ≤ C.min' hne := hlo _ hminC
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr hne
  simp only [AltChain.phi] at hge
  omega

/-- `below` is strictly monotone on `C`, hence injective there. -/
theorem below_inj {C : Finset ℕ} : ∀ x ∈ C, ∀ x' ∈ C, below C x = below C x' → x = x' := by
  classical
  intro x hx x' hx' h
  by_contra hne
  rcases Nat.lt_or_ge x x' with hlt | hge
  · have hsub : C.filter (fun y => y < x) ⊂ C.filter (fun y => y < x') := by
      constructor
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyC, hy'⟩
        exact Finset.mem_filter.mpr ⟨hyC, by omega⟩
      · intro hcon
        have : x ∈ C.filter (fun y => y < x) := hcon (Finset.mem_filter.mpr ⟨hx, hlt⟩)
        exact absurd (Finset.mem_filter.mp this).2 (by omega)
    have := Finset.card_lt_card hsub
    simp only [below] at h; omega
  · have hlt : x' < x := by omega
    have hsub : C.filter (fun y => y < x') ⊂ C.filter (fun y => y < x) := by
      constructor
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyC, hy'⟩
        exact Finset.mem_filter.mpr ⟨hyC, by omega⟩
      · intro hcon
        have : x' ∈ C.filter (fun y => y < x') := hcon (Finset.mem_filter.mpr ⟨hx', hlt⟩)
        exact absurd (Finset.mem_filter.mp this).2 (by omega)
    have := Finset.card_lt_card hsub
    simp only [below] at h; omega

/-- `below` maps `C` onto `range |C|`. -/
theorem below_image {C : Finset ℕ} : C.image (below C) = Finset.range C.card := by
  classical
  have hlt : ∀ x ∈ C, below C x < C.card := by
    intro x hx
    have := below_add_rk hx
    simp only [below] at this ⊢
    omega
  have hsub : C.image (below C) ⊆ Finset.range C.card := by
    intro j hj
    obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hxj ▸ hlt x hx)
  have hcard : (C.image (below C)).card = C.card :=
    Finset.card_image_of_injOn (fun x hx x' hx' h => below_inj x hx x' hx' h)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])

/-- **The dual bound.** Greedy from the bottom maximises the reciprocal sum at fixed cardinality. -/
theorem sum_inv_le {a : ℕ} {C : Finset ℕ} (hne : C.Nonempty) (ha : 1 ≤ a)
    (hlo : ∀ y ∈ C, a ≤ y) (hind : ∀ y ∈ C, y + 1 ∉ C) :
    ∑ x ∈ C, ((x : ℚ))⁻¹ ≤ ∑ j ∈ Finset.range C.card, (((a + 2 * j : ℕ) : ℚ))⁻¹ := by
  classical
  have hkey : ∀ x ∈ C, a + 2 * below C x ≤ x := fun x hx => le_of_below hne hlo hind hx
  calc ∑ x ∈ C, ((x : ℚ))⁻¹
      ≤ ∑ x ∈ C, (((a + 2 * below C x : ℕ) : ℚ))⁻¹ := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have h2 : a + 2 * below C x ≤ x := hkey x hx
        have hapos : (0:ℚ) < ((a + 2 * below C x : ℕ) : ℚ) := by
          have : 0 < a + 2 * below C x := by omega
          exact_mod_cast this
        have hle : ((a + 2 * below C x : ℕ) : ℚ) ≤ (x : ℚ) := by exact_mod_cast h2
        first
          | exact inv_le_inv_of_le hapos hle
          | exact one_div_le_one_div_of_le hapos hle
          | exact (inv_le_inv₀ (lt_of_lt_of_le hapos hle) hapos).mpr hle
    _ = ∑ j ∈ Finset.range C.card, (((a + 2 * j : ℕ) : ℚ))⁻¹ := by
        rw [← below_image, Finset.sum_image (fun x hx x' hx' h => below_inj x hx x' hx' h)]

#print axioms le_of_below
#print axioms below_inj
#print axioms below_image
#print axioms sum_inv_le

end IndepDual
