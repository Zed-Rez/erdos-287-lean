/- **An alternating-parity chain in the complement costs one window unit per alternation.**

`IndepRank.card_le` gives `a + 2(|C| − 1) ≤ b` for independent `C ⊆ [a,b]`, attained by the greedy
set `a, a+2, a+4, …`, which is single-parity. `ParitySwitch.card_le_of_mixed_parity` improves it by
`1` when `C` contains two elements of different parity. This file is the general statement: **each
further parity alternation costs another unit.**

> **`card_le_of_alt_chain`.** If `C` contains `x₀ < x₁ < … < x_{m−1}` with consecutive elements of
> different parity, and `x₀ = min C`, then `a + 2|C| + (m − 1) ≤ b + 2`.

`m = 1` recovers `IndepRank.card_le`; `m = 2` recovers `ParitySwitch`. In the #287 variables
(`a = n₁+1`, `b = M−1`, `C` the interior non-terms, `g₁ = W − 1 − 2|C|`) it reads **`g₁ ≥ m − 1`**:
the number of gap-1 steps is at least the number of parity alternations among the non-terms. Since
every rough number is a non-term, `g₁` is bounded below by the alternation count of the rough set —
the one lever left on `Window4`, which is otherwise optimal (`attempts/046-bracket/`).

**The mechanism.** Everything runs through

    φ(z)  =  z + 2 · #{w ∈ C : z < w},

which (i) is **non-decreasing** on `C`, (ii) **preserves parity**, and (iii) is **bounded by `b`**
(that is exactly `IndepRank.le_sub_two_mul`). A parity change forces `φ` to increase *strictly*, so an
alternating chain of length `m` needs `m − 1` units of room inside `[φ(min C), b]`, and
`φ(min C) = min C + 2(|C| − 1) ≥ a + 2(|C| − 1)`.

Using `φ` (rank counted from ABOVE, matching `IndepRank`) rather than a displacement counted from
below is what keeps this free of a mirrored `rank_bound`: no lemma below needs the elements under `z`.

The general bound was verified exhaustively before formalising — 20 722 configurations, no
violations, 611 attaining equality (`attempts/047-parityswitch/verify.py`).
-/
import P287.ParitySwitch

namespace AltChain

open Finset

/-- `φ(z) = z + 2·#{w ∈ C : z < w}`. -/
noncomputable def phi (C : Finset ℕ) (z : ℕ) : ℕ := z + 2 * (C.filter (fun w => z < w)).card

/-- `φ` preserves parity: it adds an even number. -/
theorem phi_parity (C : Finset ℕ) (z : ℕ) : phi C z % 2 = z % 2 := by
  simp [phi, Nat.add_mul_mod_self_left, Nat.add_mod, Nat.mul_mod_right]

/-- `φ` is bounded by `b` — this is `IndepRank.le_sub_two_mul`. -/
theorem phi_le {b : ℕ} {C : Finset ℕ} (hb : ∀ z ∈ C, z ≤ b) (hind : ∀ z ∈ C, z + 1 ∉ C)
    {z : ℕ} (hz : z ∈ C) : phi C z ≤ b :=
  IndepRank.le_sub_two_mul hb hind hz

/-- **`φ` is non-decreasing on `C`.** The elements above `y` split into those at most `z` and those
above `z`; the first group is what the rank bound inside `[y, z]` controls. -/
theorem phi_mono {C : Finset ℕ} (hind : ∀ z ∈ C, z + 1 ∉ C)
    {y z : ℕ} (hy : y ∈ C) (hz : z ∈ C) (hyz : y < z) :
    phi C y ≤ phi C z := by
  classical
  set Cz := C.filter (fun w => w ≤ z) with hCz
  have hCzb : ∀ w ∈ Cz, w ≤ z := fun w hw => (Finset.mem_filter.mp hw).2
  have hCzind : ∀ w ∈ Cz, w + 1 ∉ Cz := by
    intro w hw hw1
    exact hind w (Finset.mem_of_mem_filter w hw) (Finset.mem_of_mem_filter (w + 1) hw1)
  have hyCz : y ∈ Cz := Finset.mem_filter.mpr ⟨hy, le_of_lt hyz⟩
  -- the rank bound inside `[y, z]`
  have hin := IndepRank.le_sub_two_mul hCzb hCzind hyCz
  -- `#{w ∈ C : y < w} = #{w ∈ C : y < w ≤ z} + #{w ∈ C : z < w}`
  have hsplit : (Cz.filter (fun w => y < w)).card + (C.filter (fun w => z < w)).card
      = (C.filter (fun w => y < w)).card := by
    rw [hCz]
    rw [← Finset.card_filter_add_card_filter_not
          (s := C.filter (fun w => y < w)) (p := fun w => w ≤ z)]
    congr 1
    · apply Finset.card_nbij id <;> intro w hw <;> simp_all [Finset.mem_filter]
    -- `y < w` and `¬ w ≤ z` collapse to `z < w` because `y < z`
    · apply Finset.card_nbij id <;> intro w hw <;> simp_all [Finset.mem_filter] <;> omega
  simp only [phi]
  omega

/-- A parity change makes `φ` increase strictly. -/
theorem phi_lt {C : Finset ℕ} (hind : ∀ z ∈ C, z + 1 ∉ C)
    {y z : ℕ} (hy : y ∈ C) (hz : z ∈ C) (hyz : y < z) (hpar : y % 2 ≠ z % 2) :
    phi C y < phi C z := by
  have hle := phi_mono hind hy hz hyz
  have hy2 := phi_parity C y
  have hz2 := phi_parity C z
  rcases Nat.lt_or_ge (phi C y) (phi C z) with h | h
  · exact h
  · exfalso; exact hpar (by omega)

/-- **The chain bound**: `m − 1` alternations force `φ` up by `m − 1`. -/
theorem chain_step {C : Finset ℕ} (hind : ∀ z ∈ C, z + 1 ∉ C)
    (x : ℕ → ℕ) {m : ℕ}
    (hxC : ∀ i, i < m → x i ∈ C)
    (hxmono : ∀ i, i + 1 < m → x i < x (i + 1))
    (halt : ∀ i, i + 1 < m → x i % 2 ≠ x (i + 1) % 2) :
    ∀ i, i < m → phi C (x 0) + i ≤ phi C (x i) := by
  intro i
  induction i with
  | zero => intro _; omega
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hstep : phi C (x j) < phi C (x (j + 1)) :=
      phi_lt hind (hxC j hjm) (hxC (j + 1) hj) (hxmono j hj) (halt j hj)
    have := ih hjm
    omega

/-- **Each parity alternation in an independent set costs one unit of window.** -/
theorem card_le_of_alt_chain {a b m : ℕ} {C : Finset ℕ} (hne : C.Nonempty)
    (hlo : ∀ z ∈ C, a ≤ z) (hb : ∀ z ∈ C, z ≤ b) (hind : ∀ z ∈ C, z + 1 ∉ C)
    (x : ℕ → ℕ) (hm : 0 < m)
    (hxC : ∀ i, i < m → x i ∈ C)
    (hxmono : ∀ i, i + 1 < m → x i < x (i + 1))
    (halt : ∀ i, i + 1 < m → x i % 2 ≠ x (i + 1) % 2)
    (hx0 : x 0 = C.min' hne) :
    a + 2 * C.card + (m - 1) ≤ b + 2 := by
  classical
  have hchain := chain_step hind x hxC hxmono halt (m - 1) (by omega)
  have htop : phi C (x (m - 1)) ≤ b := phi_le hb hind (hxC (m - 1) (by omega))
  -- `φ(min C) = min C + 2(|C| − 1)`: everything else in `C` lies above the minimum
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
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr hne
  have hphi0 : phi C (x 0) = C.min' hne + 2 * (C.card - 1) := by
    rw [hx0]; simp only [phi]; rw [hcard]
  have hamin : a ≤ C.min' hne := hlo _ hminC
  omega

/-- **The `x₀ = min C` hypothesis is unnecessary.** `φ` is non-decreasing, so
`φ(x₀) ≥ φ(min C) = min C + 2(|C| − 1) ≥ a + 2(|C| − 1)` whatever `x₀` is. This is the form to
instantiate: any alternating chain anywhere in `C` will do. -/
theorem card_le_of_alt_chain' {a b m : ℕ} {C : Finset ℕ} (hne : C.Nonempty)
    (hlo : ∀ z ∈ C, a ≤ z) (hb : ∀ z ∈ C, z ≤ b) (hind : ∀ z ∈ C, z + 1 ∉ C)
    (x : ℕ → ℕ) (hm : 0 < m)
    (hxC : ∀ i, i < m → x i ∈ C)
    (hxmono : ∀ i, i + 1 < m → x i < x (i + 1))
    (halt : ∀ i, i + 1 < m → x i % 2 ≠ x (i + 1) % 2) :
    a + 2 * C.card + (m - 1) ≤ b + 2 := by
  classical
  have hchain := chain_step hind x hxC hxmono halt (m - 1) (by omega)
  have htop : phi C (x (m - 1)) ≤ b := phi_le hb hind (hxC (m - 1) (by omega))
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
  have hphimin : phi C (C.min' hne) = C.min' hne + 2 * (C.card - 1) := by
    simp only [phi]; rw [hcard]
  -- the only new step: monotonicity from the minimum up to `x 0`
  have hx0C : x 0 ∈ C := hxC 0 hm
  have hge : phi C (C.min' hne) ≤ phi C (x 0) := by
    rcases eq_or_lt_of_le (Finset.min'_le _ (x 0) hx0C) with h | h
    · rw [h]
    · exact phi_mono hind hminC hx0C h
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr hne
  have hamin : a ≤ C.min' hne := hlo _ hminC
  omega

#print axioms card_le_of_alt_chain'
#print axioms phi_mono
#print axioms phi_lt
#print axioms card_le_of_alt_chain

end AltChain
