/-
# generated (s4_asm/layers.py): all b for a = 1; modules: S4B_01_002_002, S4B_01_003_003, S4B_01_004_004, S4R_01_005_005, S4B_01_006_007, S4B_01_008_008, S4B_01_009_009, S4R_01_010_010, S4B_01_011_011, S4B_01_012_012, S4R_01_013_013, S4R_01_014_016, S4R_01_017_017, S4R_01_018_018, S4R_01_019_021, S4R_01_022_022, S4R_01_023_025, S4R_01_026_028, S4R_01_029_031, S4R_01_032_036, S4R_01_037_042, S4R_01_043_063
-/
import LRSpectrumFull.S4B_01_002_002
import LRSpectrumFull.S4B_01_003_003
import LRSpectrumFull.S4B_01_004_004
import LRSpectrumFull.S4R_01_005_005
import LRSpectrumFull.S4B_01_006_007
import LRSpectrumFull.S4B_01_008_008
import LRSpectrumFull.S4B_01_009_009
import LRSpectrumFull.S4R_01_010_010
import LRSpectrumFull.S4B_01_011_011
import LRSpectrumFull.S4B_01_012_012
import LRSpectrumFull.S4R_01_013_013
import LRSpectrumFull.S4R_01_014_016
import LRSpectrumFull.S4R_01_017_017
import LRSpectrumFull.S4R_01_018_018
import LRSpectrumFull.S4R_01_019_021
import LRSpectrumFull.S4R_01_022_022
import LRSpectrumFull.S4R_01_023_025
import LRSpectrumFull.S4R_01_026_028
import LRSpectrumFull.S4R_01_029_031
import LRSpectrumFull.S4R_01_032_036
import LRSpectrumFull.S4R_01_037_042
import LRSpectrumFull.S4R_01_043_063

namespace LRSpectrumFull
namespace D0

theorem S4A_1 : ∀ b c d : ℕ, 1 < b → b < c → c < d → 1 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 1 b) (Nat.gcd c d) = 1 → S4 ![1, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (2 ≤ b ∧ b < 2 + 1) ∨ (3 ≤ b ∧ b < 3 + 1) ∨ (4 ≤ b ∧ b < 4 + 1) ∨ (5 ≤ b ∧ b < 5 + 1) ∨ (6 ≤ b ∧ b < 6 + 2) ∨ (8 ≤ b ∧ b < 8 + 1) ∨ (9 ≤ b ∧ b < 9 + 1) ∨ (10 ≤ b ∧ b < 10 + 1) ∨ (11 ≤ b ∧ b < 11 + 1) ∨ (12 ≤ b ∧ b < 12 + 1) ∨ (13 ≤ b ∧ b < 13 + 1) ∨ (14 ≤ b ∧ b < 14 + 3) ∨ (17 ≤ b ∧ b < 17 + 1) ∨ (18 ≤ b ∧ b < 18 + 1) ∨ (19 ≤ b ∧ b < 19 + 3) ∨ (22 ≤ b ∧ b < 22 + 1) ∨ (23 ≤ b ∧ b < 23 + 3) ∨ (26 ≤ b ∧ b < 26 + 3) ∨ (29 ≤ b ∧ b < 29 + 3) ∨ (32 ≤ b ∧ b < 32 + 5) ∨ (37 ≤ b ∧ b < 37 + 6) ∨ (43 ≤ b ∧ b < 43 + 21) := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact s4_blk_1_2_2 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_3_3 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_4_4 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_5_5 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_6_7 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_8_8 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_9_9 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_10_10 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_11_11 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_1_12_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_13_13 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_14_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_17_17 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_18_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_19_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_22_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_23_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_26_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_29_31 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_32_36 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_37_42 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_1_43_63 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_1

end D0
end LRSpectrumFull
