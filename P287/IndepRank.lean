/- **An independent set is pushed down by everything above it.**

The combinatorial core of the cardinality constraint (`verified/102`). Every archimedean argument in
this development uses the RECIPROCAL SUM of the complement `C` — `Window4` through its maximum,
`Budget` through the rough set's mass. This is about its CARDINALITY, which the gap structure ties
to the number of gap-1 steps by the exact identity `g₁ = W - 1 - 2|C|`.

The statement below is the step that makes the greedy set `b-1, b-3, b-5, …` the minimiser of
`∑_{x∈C} 1/x` over independent `C` of a given size: an element with `m` elements of `C` strictly
above it cannot exceed `b - 2m`, because those `m` elements are pairwise non-adjacent and all at
most `b`, so they occupy a span of at least `2m`.

Verified against brute force over all independent subsets before being formalised
(`verified/102/derive.py`: windows [5,20], [7,25], [10,30], sizes 1..5, greedy == brute force
everywhere).

Independence here is `x ∈ C → x + 1 ∉ C`, which is exactly "no two consecutive", i.e. the complement
of a gaps-`≤2` set.
-/
import P287.PrimePow

namespace IndepRank

open Finset

/-- **The rank bound.** If `C` is an independent set of naturals bounded by `b`, then any `x ∈ C`
with `m` elements of `C` strictly above it satisfies `x + 2m ≤ b`. -/
theorem rank_bound {b : ℕ} {C : Finset ℕ} (hb : ∀ y ∈ C, y ≤ b)
    (hind : ∀ y ∈ C, y + 1 ∉ C) :
    ∀ m : ℕ, ∀ x ∈ C, (C.filter (fun y => x < y)).card = m → x + 2 * m ≤ b := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simpa using hb x hx
    -- some element of `C` lies above `x`; take the least such.
    -- NOT via `set`: `set` does not fold occurrences into hypotheses created after it, so omega
    -- saw the bound variable and the `min'_le` result as two DIFFERENT atoms (NOTES trap).
    have hne : (C.filter (fun y => x < y)).Nonempty := by
      rw [← Finset.card_pos, hm]; exact hpos
    obtain ⟨x', hx'mem, hx'min⟩ :
        ∃ z ∈ C.filter (fun y => x < y), ∀ w ∈ C.filter (fun y => x < y), z ≤ w :=
      ⟨(C.filter (fun y => x < y)).min' hne, Finset.min'_mem _ hne,
       fun w hw => Finset.min'_le _ w hw⟩
    have hx'C : x' ∈ C := (Finset.mem_filter.mp hx'mem).1
    have hxx' : x < x' := (Finset.mem_filter.mp hx'mem).2
    -- independence: `x + 1 ∉ C`, so the least element above `x` is at least `x + 2`
    have hstep : x + 2 ≤ x' := by
      rcases Nat.lt_or_ge (x + 1) x' with h | h
      · omega
      · have hq : x' = x + 1 := by omega
        exact absurd (hq ▸ hx'C) (hind x hx)
    -- the elements above `x'` are exactly those above `x`, minus `x'` itself
    have hsplit : C.filter (fun y => x' < y) = (C.filter (fun y => x < y)).erase x' := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_filter.mp hy with ⟨hyC, hy'⟩
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨hyC, by omega⟩⟩
      · intro hy
        rcases Finset.mem_erase.mp hy with ⟨hyne, hy'⟩
        rcases Finset.mem_filter.mp hy' with ⟨hyC, hy''⟩
        refine Finset.mem_filter.mpr ⟨hyC, ?_⟩
        have hle := hx'min y (Finset.mem_filter.mpr ⟨hyC, hy''⟩)
        omega
    have hcard : (C.filter (fun y => x' < y)).card = m - 1 := by
      rw [hsplit, Finset.card_erase_of_mem hx'mem, hm]
    have hlt : m - 1 < m := by omega
    have := ih (m - 1) hlt x' hx'C hcard
    omega

/-- The same with the count written directly, which is the form the application needs. -/
theorem le_sub_two_mul {b : ℕ} {C : Finset ℕ} (hb : ∀ y ∈ C, y ≤ b)
    (hind : ∀ y ∈ C, y + 1 ∉ C) {x : ℕ} (hx : x ∈ C) :
    x + 2 * (C.filter (fun y => x < y)).card ≤ b :=
  rank_bound hb hind _ x hx rfl

/-- **Cardinality bound.** An independent subset of `[a, b]` has at most `(b - a)/2 + 1` elements —
the minimum element is pushed down by all the others. -/
theorem card_le {a b : ℕ} {C : Finset ℕ} (hne : C.Nonempty)
    (hlo : ∀ y ∈ C, a ≤ y) (hb : ∀ y ∈ C, y ≤ b) (hind : ∀ y ∈ C, y + 1 ∉ C) :
    a + 2 * (C.card - 1) ≤ b := by
  classical
  set x := C.min' hne with hxdef
  have hxC : x ∈ C := Finset.min'_mem _ hne
  have hall : C.filter (fun y => x < y) = C.erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hyC, hy⟩; exact ⟨by omega, hyC⟩
    · rintro ⟨hne', hyC⟩
      have := Finset.min'_le _ y hyC
      exact ⟨hyC, by omega⟩
  have h := le_sub_two_mul hb hind hxC
  rw [hall, Finset.card_erase_of_mem hxC] at h
  have := hlo x hxC
  omega

/-- The rank map: how many elements of `C` lie strictly above `x`. -/
noncomputable def rk (C : Finset ℕ) (x : ℕ) : ℕ := (C.filter (fun y => x < y)).card

/-- `rk` is strictly antitone on `C`, hence injective there. -/
theorem rk_inj {C : Finset ℕ} : ∀ x ∈ C, ∀ x' ∈ C, rk C x = rk C x' → x = x' := by
  classical
  intro x hx x' hx' h
  by_contra hne
  -- WLOG `x < x'`; then `x'` is counted above `x` but not above itself
  rcases Nat.lt_or_ge x x' with hlt | hge
  · have hsub : C.filter (fun y => x' < y) ⊂ C.filter (fun y => x < y) := by
      constructor
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyC, hy'⟩
        exact Finset.mem_filter.mpr ⟨hyC, by omega⟩
      · intro hcon
        have : x' ∈ C.filter (fun y => x' < y) := hcon (Finset.mem_filter.mpr ⟨hx', hlt⟩)
        exact absurd (Finset.mem_filter.mp this).2 (by omega)
    have := Finset.card_lt_card hsub
    simp only [rk] at h; omega
  · have hlt : x' < x := by omega
    have hsub : C.filter (fun y => x < y) ⊂ C.filter (fun y => x' < y) := by
      constructor
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyC, hy'⟩
        exact Finset.mem_filter.mpr ⟨hyC, by omega⟩
      · intro hcon
        have : x ∈ C.filter (fun y => x < y) := hcon (Finset.mem_filter.mpr ⟨hx, hlt⟩)
        exact absurd (Finset.mem_filter.mp this).2 (by omega)
    have := Finset.card_lt_card hsub
    simp only [rk] at h; omega

/-- `rk` maps `C` onto `range C.card`. -/
theorem rk_image {C : Finset ℕ} : C.image (rk C) = Finset.range C.card := by
  classical
  have hlt : ∀ x ∈ C, rk C x < C.card := by
    intro x hx
    have hsub : C.filter (fun y => x < y) ⊂ C := by
      constructor
      · exact Finset.filter_subset _ _
      · intro hcon
        have : x ∈ C.filter (fun y => x < y) := hcon hx
        exact absurd (Finset.mem_filter.mp this).2 (by omega)
    simpa [rk] using Finset.card_lt_card hsub
  have hsub : C.image (rk C) ⊆ Finset.range C.card := by
    intro j hj
    obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hxj ▸ hlt x hx)
  have hcard : (C.image (rk C)).card = C.card := Finset.card_image_of_injOn (fun x hx x' hx' h =>
    rk_inj x hx x' hx' h)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])

/-- **The greedy set minimises the reciprocal sum at fixed cardinality.**
For an independent `C` bounded by `b`, the sum `∑ 1/x` is at least the greedy sum
`∑_{j < |C|} 1/(b - 2j)`. This is the inequality behind the `g₁` bound of `verified/102`. -/
theorem sum_inv_ge {b : ℕ} {C : Finset ℕ} (hpos : ∀ y ∈ C, 0 < y)
    (hb : ∀ y ∈ C, y ≤ b) (hind : ∀ y ∈ C, y + 1 ∉ C) :
    ∑ j ∈ Finset.range C.card, (((b - 2 * j : ℕ) : ℚ))⁻¹ ≤ ∑ x ∈ C, ((x : ℚ))⁻¹ := by
  classical
  have hkey : ∀ x ∈ C, x + 2 * rk C x ≤ b := fun x hx => le_sub_two_mul hb hind hx
  calc ∑ j ∈ Finset.range C.card, (((b - 2 * j : ℕ) : ℚ))⁻¹
      = ∑ x ∈ C, (((b - 2 * rk C x : ℕ) : ℚ))⁻¹ := by
        rw [← rk_image, Finset.sum_image (fun x hx x' hx' h => rk_inj x hx x' hx' h)]
    _ ≤ ∑ x ∈ C, ((x : ℚ))⁻¹ := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have h1 : 0 < x := hpos x hx
        have h2 : x ≤ b - 2 * rk C x := by have := hkey x hx; omega
        have hx0 : (0:ℚ) < (x:ℚ) := by exact_mod_cast h1
        have hle : (x:ℚ) ≤ ((b - 2 * rk C x : ℕ) : ℚ) := by exact_mod_cast h2
        have hpos2 : (0:ℚ) < ((b - 2 * rk C x : ℕ) : ℚ) := lt_of_lt_of_le hx0 hle
        first
          | exact inv_le_inv_of_le hx0 hle
          | exact one_div_le_one_div_of_le hx0 hle
          | exact (inv_le_inv₀ hpos2 hx0).mpr hle

#print axioms rank_bound
#print axioms card_le
#print axioms sum_inv_ge

end IndepRank
