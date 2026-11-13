/-
# generated (s4_asm/layers.py): all b for a = 3; modules: S4B_03_004_004, S4R_03_005_005, S4B_03_006_006, S4R_03_007_007, S4B_03_008_008, S4R_03_009_012, S4R_03_013_016, S4R_03_017_021, S4R_03_022_028, S4R_03_029_038, S4R_03_039_063
-/
import LRSpectrumFull.S4B_03_004_004
import LRSpectrumFull.S4R_03_005_005
import LRSpectrumFull.S4B_03_006_006
import LRSpectrumFull.S4R_03_007_007
import LRSpectrumFull.S4B_03_008_008
import LRSpectrumFull.S4R_03_009_012
import LRSpectrumFull.S4R_03_013_016
import LRSpectrumFull.S4R_03_017_021
import LRSpectrumFull.S4R_03_022_028
import LRSpectrumFull.S4R_03_029_038
import LRSpectrumFull.S4R_03_039_063

namespace LRSpectrumFull
namespace D0

theorem S4A_3 : ∀ b c d : ℕ, 3 < b → b < c → c < d → 3 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 3 b) (Nat.gcd c d) = 1 → S4 ![3, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (4 ≤ b ∧ b < 4 + 1) ∨ (5 ≤ b ∧ b < 5 + 1) ∨ (6 ≤ b ∧ b < 6 + 1) ∨ (7 ≤ b ∧ b < 7 + 1) ∨ (8 ≤ b ∧ b < 8 + 1) ∨ (9 ≤ b ∧ b < 9 + 4) ∨ (13 ≤ b ∧ b < 13 + 4) ∨ (17 ≤ b ∧ b < 17 + 5) ∨ (22 ≤ b ∧ b < 22 + 7) ∨ (29 ≤ b ∧ b < 29 + 10) ∨ (39 ≤ b ∧ b < 39 + 25) := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h
  · exact s4_blk_3_4_4 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_5_5 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_3_6_6 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_7_7 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_3_8_8 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_9_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_13_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_17_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_22_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_29_38 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_3_39_63 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_3

end D0
end LRSpectrumFull
