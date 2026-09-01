/- Erdős #287, kernel-verified for every largest term up to 8.5899e23.

   Main.erdos287_below   M <= 382613443      (primality by norm_num)
   Cert0..Cert4          up to 8.5899e23     (51 Lucas-certificate rungs)
-/
import P287.Main
import P287.Cert0
import P287.Cert1
import P287.Cert2
import P287.Cert3
import P287.Cert4

namespace Main2

/-- **Erdős #287 holds for every representation whose largest term is at most
    858988211239796718174213.** -/
theorem erdos287_below {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 858988211239796718174213) :
    3 ≤ PCI.max_gap k s := by
  by_cases b0 : s ⟨k - 1, by omega⟩ ≤ 382613443
  · exact Main.erdos287_below hk s hmono h1 hsum b0
  push_neg at b0
  by_cases b1 : s ⟨k - 1, by omega⟩ ≤ 391621783557
  · exact Cert0.chunk_gap hk s hmono h1 hsum (by omega) b1
  push_neg at b1
  by_cases b2 : s ⟨k - 1, by omega⟩ ≤ 400814598258693
  · exact Cert1.chunk_gap hk s hmono h1 hsum (by omega) b2
  push_neg at b2
  by_cases b3 : s ⟨k - 1, by omega⟩ ≤ 410193742117470225
  · exact Cert2.chunk_gap hk s hmono h1 hsum (by omega) b3
  push_neg at b3
  by_cases b4 : s ⟨k - 1, by omega⟩ ≤ 419791687907295625233
  · exact Cert3.chunk_gap hk s hmono h1 hsum (by omega) b4
  push_neg at b4
  by_cases b5 : s ⟨k - 1, by omega⟩ ≤ 858988211239796718174213
  · exact Cert4.chunk_gap hk s hmono h1 hsum (by omega) b5
  push_neg at b5
  omega

#print axioms erdos287_below

end Main2
