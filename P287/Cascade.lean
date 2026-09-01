/- **The 2-adic cascade: level `E` determines level `E−1` mod 4.**

`MaxVal.maxlevel_card_even` says the top 2-adic level of a representation of 1 has EVEN size.
That is the mod-2 shadow of a mod-4 statement, which also sees one level further down:

    E = max v₂ over T,  E ≥ 2  ⟹  4 ∣ (Σ_{v₂(n)=E} n/2^E) + 2·#{n : v₂(n) = E−1}.

Reducing mod 2 recovers the old law (each `n/2^E` is odd, so the first sum is `≡ #{v₂ = E}`), so
this is a strict generalisation.

Proof, with no `lcm` and no global unknown. Let `P = ∏_{n∈T} oddPart n`, itself odd, and clear
denominators over `D = 2^E·P`: every `n ∈ T` divides `D`, so `D = Σ_{n∈T} D/n` with
`D/n = 2^(E−v₂ n) · w n`, `w n = P / oddPart n` an ODD integer. Mod 4 the levels `≤ E−2`
contribute nothing, so

    Σ_{v₂=E} w n  +  2·Σ_{v₂=E−1} w n  ≡  0   (mod 4),

and the second sum is `≡ #{v₂ = E−1}` mod 2 since its summands are odd. For the first, `w n ·
oddPart n = P` and `m² ≡ 1 (mod 4)` for odd `m` give `w n ≡ P · oddPart n (mod 4)`; multiplying the
whole congruence by the odd `P` (so `P² ≡ 1`, `2P ≡ 2`) clears `P` and leaves the statement.
-/
import P287.RuleBGen

namespace Cascade

open Finset

/-- **Clearing denominators.** If every term divides `D` and the reciprocals sum to 1, then
`D = Σ D/n` as naturals. -/
theorem clear_denoms {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) {D : ℕ} (hD : 0 < D)
    (hdvd : ∀ n ∈ T, n ∣ D) :
    D = ∑ n ∈ T, D / n := by
  classical
  have hQ : ((D : ℚ)) = ((∑ n ∈ T, D / n : ℕ) : ℚ) := by
    push_cast
    have : ∀ n ∈ T, ((D / n : ℕ) : ℚ) = (D : ℚ) * ((n : ℚ))⁻¹ := by
      intro n hn
      have hnpos := hTpos n hn
      have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      obtain ⟨c, hc⟩ := hdvd n hn
      have hdc : D / n = c := by rw [hc]; exact Nat.mul_div_cancel_left c (by omega)
      rw [hdc, hc]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hsum, mul_one]
  exact_mod_cast hQ

/-- The odd part of `n`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (padicValNat 2 n)

theorem oddPart_mul (n : ℕ) (hn : 0 < n) : oddPart n * 2 ^ (padicValNat 2 n) = n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.div_mul_cancel pow_padicValNat_dvd

theorem oddPart_pos (n : ℕ) (hn : 0 < n) : 0 < oddPart n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.div_pos (Nat.le_of_dvd hn pow_padicValNat_dvd) (pow_pos (by norm_num) _)

theorem oddPart_odd (n : ℕ) (hn : 0 < n) : oddPart n % 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  have hpos := oddPart_pos n hn
  have hmul := oddPart_mul n hn
  set v := padicValNat 2 n with hv
  have h2 : 2 ∣ oddPart n := by omega
  obtain ⟨d, hd⟩ := h2
  have hbig : 2 ^ (v + 1) ∣ n := by
    refine ⟨d, ?_⟩
    rw [← hmul, hd]; ring
  have hn0 : n ≠ 0 := by omega
  have hle : v + 1 ≤ v := by
    rw [hv]
    exact (padicValNat_dvd_iff_le hn0).mp hbig
  omega

/-- An odd square is `1 mod 4`. -/
theorem sq_mod_four {m : ℕ} (hm : m % 2 = 1) : m * m % 4 = 1 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  subst ht
  have h : (2 * t + 1) * (2 * t + 1) = 4 * (t * t + t) + 1 := by ring
  rw [h]
  omega

/-- A factor of an odd number is odd. -/
theorem odd_of_mul_odd {m w P : ℕ} (h : m * w = P) (hP : P % 2 = 1) : w % 2 = 1 := by
  by_contra hc
  have h2 : 2 ∣ w := by omega
  have : 2 ∣ P := h ▸ h2.mul_left m
  omega

/-- **The `L`-cancellation, pointwise**: if `m·w = P` with `m` odd then `w ≡ P·m (mod 4)`. -/
theorem w_mod_four {m w P : ℕ} (h : m * w = P) (hm : m % 2 = 1) : w % 4 = (P * m) % 4 := by
  obtain ⟨s, hs⟩ : ∃ s, m * m = 4 * s + 1 := ⟨m * m / 4, by have := sq_mod_four hm; omega⟩
  have key : P * m = 4 * (w * s) + w := by
    calc P * m = (m * w) * m := by rw [h]
      _ = w * (m * m) := by ring
      _ = w * (4 * s + 1) := by rw [hs]
      _ = 4 * (w * s) + w := by ring
  omega

/-- **The 2-adic cascade.** The top level `E` determines level `E−1` modulo 4. Reducing mod 2
recovers `MaxVal.maxlevel_card_even`, so this is a strict generalisation. -/
theorem cascade {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1)
    {E : ℕ} (hE : 2 ≤ E) (hmax : ∀ n ∈ T, padicValNat 2 n ≤ E) :
    4 ∣ (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
        + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := ∏ n ∈ T, oddPart n with hPdef
  have hPodd : P % 2 = 1 := by
    rw [hPdef, Finset.prod_nat_mod, Finset.prod_congr rfl (fun n hn => oddPart_odd n (hTpos n hn))]
    simp
  have hPpos : 0 < P := by omega
  have hdvdP : ∀ n ∈ T, oddPart n ∣ P := fun n hn => Finset.dvd_prod_of_mem _ hn
  have hwmul : ∀ n ∈ T, oddPart n * (P / oddPart n) = P :=
    fun n hn => Nat.mul_div_cancel' (hdvdP n hn)
  have hwodd : ∀ n ∈ T, (P / oddPart n) % 2 = 1 :=
    fun n hn => odd_of_mul_odd (hwmul n hn) hPodd
  set D := 2 ^ E * P with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]; exact Nat.mul_pos (pow_pos (by norm_num) E) hPpos
  -- every term divides D, so we may clear denominators
  have hndvd : ∀ n ∈ T, n ∣ D := by
    intro n hn
    have h2 : 2 ^ (padicValNat 2 n) ∣ 2 ^ E := pow_dvd_pow 2 (hmax n hn)
    have hmd := mul_dvd_mul h2 (hdvdP n hn)
    have hne : 2 ^ (padicValNat 2 n) * oddPart n = n := by
      rw [mul_comm]; exact oddPart_mul n (hTpos n hn)
    rw [hne] at hmd
    exact hmd
  have hclear := clear_denoms hTpos hsum hDpos hndvd
  -- and each cleared term factors as 2^(E-v) * w
  have hterm : ∀ n ∈ T, D / n = 2 ^ (E - padicValNat 2 n) * (P / oddPart n) := by
    intro n hn
    have hnpos := hTpos n hn
    have hv := hmax n hn
    have hEsplit : 2 ^ (padicValNat 2 n) * 2 ^ (E - padicValNat 2 n) = 2 ^ E := by
      rw [← pow_add]; congr 1; omega
    refine Nat.div_eq_of_eq_mul_left hnpos ?_
    calc D = P * 2 ^ E := by rw [hDdef]; ring
      _ = (oddPart n * (P / oddPart n)) * (2 ^ (padicValNat 2 n) * 2 ^ (E - padicValNat 2 n)) := by
          rw [hwmul n hn, hEsplit]
      _ = (2 ^ (E - padicValNat 2 n) * (P / oddPart n)) * (oddPart n * 2 ^ (padicValNat 2 n)) := by
          ring
      _ = (2 ^ (E - padicValNat 2 n) * (P / oddPart n)) * n := by rw [oddPart_mul n hnpos]
  rw [Finset.sum_congr rfl hterm] at hclear
  -- split T by 2-adic level: E, then E-1, then the rest
  have hs1 := Finset.sum_filter_add_sum_filter_not T (fun n => padicValNat 2 n = E)
      (fun n => 2 ^ (E - padicValNat 2 n) * (P / oddPart n))
  have hs2 := Finset.sum_filter_add_sum_filter_not
      (T.filter (fun n => ¬ padicValNat 2 n = E)) (fun n => padicValNat 2 n = E - 1)
      (fun n => 2 ^ (E - padicValNat 2 n) * (P / oddPart n))
  have hBeq : (T.filter (fun n => ¬ padicValNat 2 n = E)).filter
      (fun n => padicValNat 2 n = E - 1) = T.filter (fun n => padicValNat 2 n = E - 1) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, h⟩; exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, by omega⟩, h⟩
  rw [hBeq] at hs2
  -- level E: the power is 2^0
  have hfA : ∑ n ∈ T.filter (fun n => padicValNat 2 n = E),
      2 ^ (E - padicValNat 2 n) * (P / oddPart n)
      = ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), (P / oddPart n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hv : padicValNat 2 n = E := (Finset.mem_filter.mp hn).2
    rw [hv, Nat.sub_self, pow_zero, one_mul]
  -- level E-1: the power is 2^1
  have hfB : ∑ n ∈ T.filter (fun n => padicValNat 2 n = E - 1),
      2 ^ (E - padicValNat 2 n) * (P / oddPart n)
      = 2 * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E - 1), (P / oddPart n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hv : padicValNat 2 n = E - 1 := (Finset.mem_filter.mp hn).2
    have h1 : E - padicValNat 2 n = 1 := by omega
    rw [h1, pow_one]
  -- everything below level E-1 is divisible by 4
  have hR4 : (4:ℕ) ∣ ∑ n ∈ (T.filter (fun n => ¬ padicValNat 2 n = E)).filter
      (fun n => ¬ padicValNat 2 n = E - 1), 2 ^ (E - padicValNat 2 n) * (P / oddPart n) := by
    refine Finset.dvd_sum ?_
    intro n hn
    have h1 : n ∈ T.filter (fun n => ¬ padicValNat 2 n = E) := Finset.mem_of_mem_filter n hn
    have h2 : ¬ padicValNat 2 n = E - 1 := (Finset.mem_filter.mp hn).2
    have h3 : ¬ padicValNat 2 n = E := (Finset.mem_filter.mp h1).2
    have h5 := hmax n (Finset.mem_of_mem_filter n h1)
    have h6 : 2 ≤ E - padicValNat 2 n := by omega
    have h7 : (2:ℕ) ^ 2 ∣ 2 ^ (E - padicValNat 2 n) := pow_dvd_pow 2 h6
    have h8 : (4:ℕ) ∣ 2 ^ (E - padicValNat 2 n) := by norm_num at h7; exact h7
    exact h8.mul_right _
  have hD4 : (4:ℕ) ∣ D := by
    rw [hDdef]
    have h7 : (2:ℕ) ^ 2 ∣ 2 ^ E := pow_dvd_pow 2 hE
    have h8 : (4:ℕ) ∣ 2 ^ E := by norm_num at h7; exact h7
    exact h8.mul_right P
  rw [hfA] at hs1
  rw [hfB] at hs2
  -- 4 ∣ (Σ_E w) + 2·(Σ_{E-1} w)
  have hkey : (4:ℕ) ∣ (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), (P / oddPart n))
      + 2 * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E - 1), (P / oddPart n) := by
    omega
  -- the two congruences: w ≡ P·oddPart (mod 4), and w odd
  have hA4 : (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), (P / oddPart n)) % 4
      = (P * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), oddPart n) % 4 := by
    rw [Finset.sum_nat_mod]
    rw [Finset.sum_congr rfl (fun n hn => w_mod_four (hwmul n (Finset.mem_of_mem_filter n hn))
      (oddPart_odd n (hTpos n (Finset.mem_of_mem_filter n hn))))]
    rw [← Finset.sum_nat_mod, Finset.mul_sum]
  have hB2 : (∑ n ∈ T.filter (fun n => padicValNat 2 n = E - 1), (P / oddPart n)) % 2
      = (T.filter (fun n => padicValNat 2 n = E - 1)).card % 2 := by
    rw [Finset.sum_nat_mod]
    rw [Finset.sum_congr rfl (fun n hn => hwodd n (Finset.mem_of_mem_filter n hn))]
    simp
  have hmid : (4:ℕ) ∣ (P * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), oddPart n)
      + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card := by omega
  -- multiply through by the odd P to clear it
  obtain ⟨u, hu⟩ : ∃ u, P = 2 * u + 1 := ⟨P / 2, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, P * P = 4 * w + 1 := ⟨P * P / 4, by have := sq_mod_four hPodd; omega⟩
  have hconv : (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), oddPart n)
      = ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hv : padicValNat 2 n = E := (Finset.mem_filter.mp hn).2
    show n / 2 ^ (padicValNat 2 n) = n / 2 ^ E
    rw [hv]
  rw [hconv] at hmid
  have hkey2 : P * ((P * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
        + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card)
      = 4 * (w * (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
        + u * (T.filter (fun n => padicValNat 2 n = E - 1)).card)
        + ((∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
        + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card) := by
    calc P * ((P * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
          + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card)
        = (P * P) * (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
          + 2 * P * (T.filter (fun n => padicValNat 2 n = E - 1)).card := by ring
      _ = (4 * w + 1) * (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
          + 2 * (2 * u + 1) * (T.filter (fun n => padicValNat 2 n = E - 1)).card := by
            rw [hw, hu]
      _ = 4 * (w * (∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
          + u * (T.filter (fun n => padicValNat 2 n = E - 1)).card)
          + ((∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
          + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card) := by ring
  have hlast : (4:ℕ) ∣ P * ((P * ∑ n ∈ T.filter (fun n => padicValNat 2 n = E), n / 2 ^ E)
      + 2 * (T.filter (fun n => padicValNat 2 n = E - 1)).card) := hmid.mul_left P
  rw [hkey2] at hlast
  omega

#print axioms clear_denoms
#print axioms oddPart_odd
#print axioms w_mod_four
#print axioms cascade

end Cascade
