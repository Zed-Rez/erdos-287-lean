/- **Mixed parity in the complement costs window room.**

`IndepRank.card_le` says an independent `C ⊆ [a,b]` satisfies `a + 2(|C| − 1) ≤ b`: the minimum is
pushed down by everything above it. That bound is attained exactly by the greedy set
`a, a+2, a+4, …`, which is **single-parity**. This file is the observation that a `C` containing
both parities cannot be greedy, and pays exactly one unit for it:

> **`card_le_of_mixed_parity`.** If an independent `C ⊆ [a,b]` contains two elements of different
> parity, then `a + 2|C| ≤ b + 1` — one better than `IndepRank.card_le`.

**Why this matters for #287.** With `a = n₁+1`, `b = M−1` and `C` the interior non-terms,
`g₁ = W − 1 − 2|C|` counts the gap-1 steps, so the conclusion is `g₁ ≥ 1`. The general form —
verified exhaustively over 20 722 configurations in `attempts/047-parityswitch/`, with 611 cases
attaining equality — is

    g₁  ≥  #{parity alternations along the sorted complement},

because `ψ(x) = x − 2·#{y ∈ C : y < x}` is non-decreasing, preserves parity, and lands in an
interval of exactly `g₁ + 1` integers, so each alternation costs one unit of range. Every rough
number is a non-term, so `g₁` is bounded below by the alternation count of the ROUGH set. This is
the only known lever on `Window4`, which is otherwise optimal (see `attempts/046-bracket/`).

The proof takes `x` to be the MINIMUM of `C`, which makes the count below `x` zero and avoids
needing a mirrored `rank_bound`; the parity gain enters as `x + 2n ≠ y` when `x` and `y` differ
in parity, upgrading `x + 2n ≤ y` to `x + 2n + 1 ≤ y`.
-/
import P287.IndepRank

namespace ParitySwitch

open Finset

/-- **Mixed parity costs one unit of window.** -/
theorem card_le_of_mixed_parity {a b : ℕ} {C : Finset ℕ} (hne : C.Nonempty)
    (hlo : ∀ z ∈ C, a ≤ z) (hb : ∀ z ∈ C, z ≤ b) (hind : ∀ z ∈ C, z + 1 ∉ C)
    (hmix : ∃ u ∈ C, ∃ v ∈ C, u % 2 ≠ v % 2) :
    a + 2 * C.card ≤ b + 1 := by
  classical
  obtain ⟨u, huC, v, hvC, huv⟩ := hmix
  set x := C.min' hne with hxdef
  have hxC : x ∈ C := Finset.min'_mem _ hne
  -- pick `y ∈ C` of parity different from the minimum
  obtain ⟨y, hyC, hxy⟩ : ∃ y ∈ C, x % 2 ≠ y % 2 := by
    by_cases h : x % 2 = u % 2
    · exact ⟨v, hvC, by omega⟩
    · exact ⟨u, huC, h⟩
  have hxlty : x < y := by
    have := Finset.min'_le _ y hyC
    rcases Nat.lt_or_ge x y with h | h
    · exact h
    · exfalso; have : x = y := by omega
      exact hxy (by rw [this])
  -- the part of `C` at or below `y`, and the part above it
  set Cy := C.filter (fun z => z ≤ y) with hCy
  have hCyb : ∀ z ∈ Cy, z ≤ y := fun z hz => (Finset.mem_filter.mp hz).2
  have hCyind : ∀ z ∈ Cy, z + 1 ∉ Cy := by
    intro z hz hz1
    exact hind z (Finset.mem_of_mem_filter z hz) (Finset.mem_of_mem_filter (z+1) hz1)
  have hxCy : x ∈ Cy := Finset.mem_filter.mpr ⟨hxC, le_of_lt hxlty⟩
  -- (1) the rank bound INSIDE `[x, y]`
  have hmid := IndepRank.le_sub_two_mul hCyb hCyind hxCy
  -- (2) parity upgrades `≤` to `<`
  have hmid' : x + 2 * (Cy.filter (fun z => x < z)).card + 1 ≤ y := by
    rcases Nat.lt_or_ge (x + 2 * (Cy.filter (fun z => x < z)).card) y with h | h
    · omega
    · exfalso
      have heq : x + 2 * (Cy.filter (fun z => x < z)).card = y := by omega
      exact hxy (by omega)
  -- (3) the rank bound ABOVE `y`
  have htop := IndepRank.le_sub_two_mul hb hind hyC
  -- (4) `#above x = #mid + #top`, and `#above x = |C| - 1` because `x` is the minimum
  have hsplit : (Cy.filter (fun z => x < z)).card + (C.filter (fun z => y < z)).card
      = (C.filter (fun z => x < z)).card := by
    rw [hCy]
    rw [← Finset.card_filter_add_card_filter_not
          (s := C.filter (fun z => x < z)) (p := fun z => z ≤ y)]
    congr 1
    · apply Finset.card_nbij id <;> intro z hz <;> simp_all [Finset.mem_filter]
    -- the `omega` here is NOT dead: it discharges `min' hne < z` from `y < z` and `x < y`.
    -- The linter flagged only the FIRST branch's copy as unreachable (LEDGER 481).
    · apply Finset.card_nbij id <;> intro z hz <;> simp_all [Finset.mem_filter] <;> omega
  have hall : C.filter (fun z => x < z) = C.erase x := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hzC, hz⟩; exact ⟨by omega, hzC⟩
    · rintro ⟨hzne, hzC⟩
      have := Finset.min'_le _ z hzC
      exact ⟨hzC, by omega⟩
  have hcard : (C.filter (fun z => x < z)).card = C.card - 1 := by
    rw [hall, Finset.card_erase_of_mem hxC]
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr hne
  have hax : a ≤ x := hlo x hxC
  omega

#print axioms card_le_of_mixed_parity

end ParitySwitch
