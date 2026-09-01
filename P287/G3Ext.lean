/- **The gaps-≤3 classification, extended to 2.624·10³⁵.**

`{2,3,6}` is the only representation of 1 with all gaps ≤ 3 and largest term ≤ 262366504093531377302242018528024295.
Chains `G3All` (M ≤ 4.236e7), five `norm_num` chunks `LadderG3S0..4` (to 2.5333e12), and
seventeen PRATT-CERTIFIED chunks `LadderG3P0..16` (53 rungs). -/
import P287.G3All
import P287.LadderG3S0
import P287.LadderG3S1
import P287.LadderG3S2
import P287.LadderG3S3
import P287.LadderG3S4
import P287.LadderG3P0
import P287.LadderG3P1
import P287.LadderG3P2
import P287.LadderG3P3
import P287.LadderG3P4
import P287.LadderG3P5
import P287.LadderG3P6
import P287.LadderG3P7
import P287.LadderG3P8
import P287.LadderG3P9
import P287.LadderG3P10
import P287.LadderG3P11
import P287.LadderG3P12
import P287.LadderG3P13
import P287.LadderG3P14
import P287.LadderG3P15
import P287.LadderG3P16

namespace G3Ext

/-- **No gaps-≤3 representation of 1 has largest term in [84, 262366504093531377302242018528024295].** -/
theorem g3_all_ext {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 84 ≤ s ⟨k - 1, by omega⟩)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 262366504093531377302242018528024295) :
    4 ≤ PCI.max_gap k s := by
  by_cases b0 : s ⟨k - 1, by omega⟩ ≤ 42359617
  · exact G3All.g3_all hk s hmono h1 hsum hlo b0
  push_neg at b0
  by_cases b1 : s ⟨k - 1, by omega⟩ ≤ 17078131209
  · exact LadderG3S0.chunk_gap hk s hmono h1 hsum (by omega) b1
  push_neg at b1
  by_cases b2 : s ⟨k - 1, by omega⟩ ≤ 126165067026
  · exact LadderG3S1.chunk_gap hk s hmono h1 hsum (by omega) b2
  push_neg at b2
  by_cases b3 : s ⟨k - 1, by omega⟩ ≤ 342916605345
  · exact LadderG3S2.chunk_gap hk s hmono h1 hsum (by omega) b3
  push_neg at b3
  by_cases b4 : s ⟨k - 1, by omega⟩ ≤ 932047325282
  · exact LadderG3S3.chunk_gap hk s hmono h1 hsum (by omega) b4
  push_neg at b4
  by_cases b5 : s ⟨k - 1, by omega⟩ ≤ 2533304609565
  · exact LadderG3S4.chunk_gap hk s hmono h1 hsum (by omega) b5
  push_neg at b5
  by_cases b6 : s ⟨k - 1, by omega⟩ ≤ 138256392641491
  · exact LadderG3P0.chunk_gap hk s hmono h1 hsum (by omega) b6
  push_neg at b6
  by_cases b7 : s ⟨k - 1, by omega⟩ ≤ 7545413256328266
  · exact LadderG3P1.chunk_gap hk s hmono h1 hsum (by omega) b7
  push_neg at b7
  by_cases b8 : s ⟨k - 1, by omega⟩ ≤ 151506542694013637
  · exact LadderG3P2.chunk_gap hk s hmono h1 hsum (by omega) b8
  push_neg at b8
  by_cases b9 : s ⟨k - 1, by omega⟩ ≤ 1119258220309038849
  · exact LadderG3P3.chunk_gap hk s hmono h1 hsum (by omega) b9
  push_neg at b9
  by_cases b10 : s ⟨k - 1, by omega⟩ ≤ 61084089147069543030
  · exact LadderG3P4.chunk_gap hk s hmono h1 hsum (by omega) b10
  push_neg at b10
  by_cases b11 : s ⟨k - 1, by omega⟩ ≤ 3333695370043443782880
  · exact LadderG3P5.chunk_gap hk s hmono h1 hsum (by omega) b11
  push_neg at b11
  by_cases b12 : s ⟨k - 1, by omega⟩ ≤ 66938236880176944371966
  · exact LadderG3P6.chunk_gap hk s hmono h1 hsum (by omega) b12
  push_neg at b12
  by_cases b13 : s ⟨k - 1, by omega⟩ ≤ 1344072285935439072072395
  · exact LadderG3P7.chunk_gap hk s hmono h1 hsum (by omega) b13
  push_neg at b13
  by_cases b14 : s ⟨k - 1, by omega⟩ ≤ 26988017522085372741791858
  · exact LadderG3P8.chunk_gap hk s hmono h1 hsum (by omega) b14
  push_neg at b14
  by_cases b15 : s ⟨k - 1, by omega⟩ ≤ 541900236612253669163596863
  · exact LadderG3P9.chunk_gap hk s hmono h1 hsum (by omega) b15
  push_neg at b15
  by_cases b16 : s ⟨k - 1, by omega⟩ ≤ 10880972127726913870740634797
  · exact LadderG3P10.chunk_gap hk s hmono h1 hsum (by omega) b16
  push_neg at b16
  by_cases b17 : s ⟨k - 1, by omega⟩ ≤ 218482197358931278048258682201
  · exact LadderG3P11.chunk_gap hk s hmono h1 hsum (by omega) b17
  push_neg at b17
  by_cases b18 : s ⟨k - 1, by omega⟩ ≤ 4386967451295085009273675011101
  · exact LadderG3P12.chunk_gap hk s hmono h1 hsum (by omega) b18
  push_neg at b18
  by_cases b19 : s ⟨k - 1, by omega⟩ ≤ 88087192692891336176318531225639
  · exact LadderG3P13.chunk_gap hk s hmono h1 hsum (by omega) b19
  push_neg at b19
  by_cases b20 : s ⟨k - 1, by omega⟩ ≤ 1768728307802674782322580911172427
  · exact LadderG3P14.chunk_gap hk s hmono h1 hsum (by omega) b20
  push_neg at b20
  by_cases b21 : s ⟨k - 1, by omega⟩ ≤ 35514809033924137140162525161097511
  · exact LadderG3P15.chunk_gap hk s hmono h1 hsum (by omega) b21
  push_neg at b21
  exact LadderG3P16.chunk_gap hk s hmono h1 hsum (by omega) hhi

#print axioms g3_all_ext

end G3Ext
