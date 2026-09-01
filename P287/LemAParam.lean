/- Lemma A′ with the multiplier bound left as a PARAMETER, and its sharp instance.

`LemAGen.lemA_gen` fixes L = t! and so demands p > t·t!. The proof never uses
anything about t! beyond `0 < L` and `m ∣ L` for every m ≤ t, so L can be any
common multiple of 1..t — and the smallest is lcm(1..t), which grows like e^t
rather than t!. At t = 20 that is 20·lcm(1..20) = 4.66·10⁹ against 20·20! =
4.87·10¹⁹: ten orders of magnitude weaker a hypothesis, for the same conclusion.

`lemA_gen` itself is left untouched — 38 rung chunks depend on its .olean.
-/
import P287.LemAGenMod

namespace LemAGen

variable {p : ℕ}

theorem lemA_param {t L : ℕ} [Fact (Nat.Prime p)] (ht : 1 ≤ t)
    (hLpos : 0 < L) (hLdvd : ∀ m, 1 ≤ m → m ≤ t → m ∣ L)
    (hp : t * L < p)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hp1 : 1 < p := by
    have : 1 ≤ t * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hppos : 0 < p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast hppos
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAcases : ∀ n ∈ A, ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p := by
    intro n hn
    obtain ⟨hnT, hnd⟩ := Finset.mem_filter.mp hn
    exact hdvd n hnT hnd
  -- every element of A lies in the image of {1,…,t} under (· * p)
  have hAsub : A ⊆ (Finset.Icc 1 t).image (fun m => m * p) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmt⟩, rfl⟩
  have hcard : A.card ≤ t := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    simp [Nat.card_Icc]
  -- the cleared weight of each element
  have hw : ∀ n ∈ A, 0 < L * p / n ∧ L * p / n ≤ L
      ∧ ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    have hmL : m ∣ L := hLdvd m hm1 hmt
    have hmpos : 0 < m := hm1
    have hdiv : L * p / (m * p) = L / m := by
      rw [Nat.mul_div_mul_right _ _ hppos]
    have hLm : L / m * m = L := Nat.div_mul_cancel hmL
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiv]; exact Nat.div_pos (Nat.le_of_dvd hLpos hmL) hmpos
    · rw [hdiv]; exact Nat.div_le_self _ _
    · rw [hdiv]
      have hmQ : (0:ℚ) < m := by exact_mod_cast hmpos
      have hcast : ((L / m : ℕ) : ℚ) = (L:ℚ) / (m:ℚ) := by
        rw [eq_div_iff (ne_of_gt hmQ)]
        exact_mod_cast hLm
      rw [hcast]
      have hLQ : (0:ℚ) < L := by exact_mod_cast hLpos
      push_cast
      field_simp
  have hterm : ∀ n ∈ A, ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) :=
    fun n hn => (hw n hn).2.2
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (L * p / n) : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  set k := ∑ n ∈ A, (L * p / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos (fun n hn => (hw n hn).1) hAne
  have hkle : k ≤ t * L := by
    calc k ≤ A.card * L := Finset.sum_le_card_nsmul A _ L (fun n hn => (hw n hn).2.1)
      _ ≤ t * L := Nat.mul_le_mul_right _ hcard
  have hpk : ¬ p ∣ k := by
    intro h; have := Nat.le_of_dvd hkpos h; omega
  have hpL : ¬ p ∣ L := by
    intro h
    have := Nat.le_of_dvd hLpos h
    have : 1 * L ≤ t * L := Nat.mul_le_mul_right _ ht
    omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    rw [hsumA, val_frac hp1 hkpos hLpos hpk hpL]
    norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval


/-- `lcmUpto t = lcm(1, …, t)`, defined here rather than via `Finset.lcm`, which
lives in a module this development does not otherwise import. -/
def lcmUpto : ℕ → ℕ
  | 0 => 1
  | (n + 1) => Nat.lcm (n + 1) (lcmUpto n)

theorem lcmUpto_pos (t : ℕ) : 0 < lcmUpto t := by
  induction t with
  | zero => simp [lcmUpto]
  | succ n ih =>
      simp only [lcmUpto]
      first
        | exact Nat.lcm_pos (by omega) ih
        | (apply Nat.pos_of_ne_zero
           intro hz
           rw [Nat.lcm_eq_zero_iff] at hz
           omega)
        | positivity

theorem dvd_lcmUpto {m : ℕ} (h1 : 1 ≤ m) : ∀ t : ℕ, m ≤ t → m ∣ lcmUpto t := by
  intro t
  induction t with
  | zero => intro h2; omega
  | succ n ih =>
      intro h2
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · refine dvd_trans (ih (by omega)) ?_
        simp only [lcmUpto]
        exact Nat.dvd_lcm_right _ _
      · have hm : m = n + 1 := by omega
        rw [hm]
        simp only [lcmUpto]
        exact Nat.dvd_lcm_left _ _

/-- **Lemma A′, sharp**: the side condition is `p > t · lcm(1..t)`, not `p > t · t!`. -/
theorem lemA_sharp {t : ℕ} [Fact (Nat.Prime p)] (ht : 1 ≤ t)
    (hp : t * lcmUpto t < p)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 :=
  lemA_param ht (lcmUpto_pos t) (fun m h1 h2 => dvd_lcmUpto h1 t h2) hp hTpos hdvd hex

#print axioms lemA_param
#print axioms lemA_sharp

end LemAGen
