/-
# generated (s4_asm/layers.py): all b for a = 2; modules: S4B_02_003_003, S4R_02_004_006, S4B_02_007_007, S4R_02_008_010, S4R_02_011_012, S4R_02_013_016, S4R_02_017_018, S4R_02_019_022, S4R_02_023_028, S4R_02_029_036, S4R_02_037_063
-/
import LRSpectrumFull.S4B_02_003_003
import LRSpectrumFull.S4R_02_004_006
import LRSpectrumFull.S4B_02_007_007
import LRSpectrumFull.S4R_02_008_010
import LRSpectrumFull.S4R_02_011_012
import LRSpectrumFull.S4R_02_013_016
import LRSpectrumFull.S4R_02_017_018
import LRSpectrumFull.S4R_02_019_022
import LRSpectrumFull.S4R_02_023_028
import LRSpectrumFull.S4R_02_029_036
import LRSpectrumFull.S4R_02_037_063

namespace LRSpectrumFull
namespace D0

theorem S4A_2 : ∀ b c d : ℕ, 2 < b → b < c → c < d → 2 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 2 b) (Nat.gcd c d) = 1 → S4 ![2, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (3 ≤ b ∧ b < 3 + 1) ∨ (4 ≤ b ∧ b < 4 + 3) ∨ (7 ≤ b ∧ b < 7 + 1) ∨ (8 ≤ b ∧ b < 8 + 3) ∨ (11 ≤ b ∧ b < 11 + 2) ∨ (13 ≤ b ∧ b < 13 + 4) ∨ (17 ≤ b ∧ b < 17 + 2) ∨ (19 ≤ b ∧ b < 19 + 4) ∨ (23 ≤ b ∧ b < 23 + 6) ∨ (29 ≤ b ∧ b < 29 + 8) ∨ (37 ≤ b ∧ b < 37 + 27) := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h
  · exact s4_blk_2_3_3 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_4_6 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_2_7_7 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_8_10 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_11_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_13_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_17_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_19_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_23_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_29_36 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_2_37_63 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_2

end D0
end LRSpectrumFull
