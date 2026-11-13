/-
# generated (s4_asm/layers.py): all b for a = 4; modules: S4R_04_005_006, S4B_04_007_008, S4R_04_009_009, S4R_04_010_010, S4R_04_011_011, S4R_04_012_012, S4R_04_013_013, S4R_04_014_015, S4R_04_016_016, S4R_04_017_018, S4R_04_019_020, S4R_04_021_023, S4R_04_024_026, S4R_04_027_030, S4R_04_031_036, S4R_04_037_046, S4R_04_047_062
-/
import LRSpectrumFull.S4R_04_005_006
import LRSpectrumFull.S4B_04_007_008
import LRSpectrumFull.S4R_04_009_009
import LRSpectrumFull.S4R_04_010_010
import LRSpectrumFull.S4R_04_011_011
import LRSpectrumFull.S4R_04_012_012
import LRSpectrumFull.S4R_04_013_013
import LRSpectrumFull.S4R_04_014_015
import LRSpectrumFull.S4R_04_016_016
import LRSpectrumFull.S4R_04_017_018
import LRSpectrumFull.S4R_04_019_020
import LRSpectrumFull.S4R_04_021_023
import LRSpectrumFull.S4R_04_024_026
import LRSpectrumFull.S4R_04_027_030
import LRSpectrumFull.S4R_04_031_036
import LRSpectrumFull.S4R_04_037_046
import LRSpectrumFull.S4R_04_047_062

namespace LRSpectrumFull
namespace D0

theorem S4A_4 : ∀ b c d : ℕ, 4 < b → b < c → c < d → 4 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 4 b) (Nat.gcd c d) = 1 → S4 ![4, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (5 ≤ b ∧ b < 5 + 2) ∨ (7 ≤ b ∧ b < 7 + 2) ∨ (9 ≤ b ∧ b < 9 + 1) ∨ (10 ≤ b ∧ b < 10 + 1) ∨ (11 ≤ b ∧ b < 11 + 1) ∨ (12 ≤ b ∧ b < 12 + 1) ∨ (13 ≤ b ∧ b < 13 + 1) ∨ (14 ≤ b ∧ b < 14 + 2) ∨ (16 ≤ b ∧ b < 16 + 1) ∨ (17 ≤ b ∧ b < 17 + 2) ∨ (19 ≤ b ∧ b < 19 + 2) ∨ (21 ≤ b ∧ b < 21 + 3) ∨ (24 ≤ b ∧ b < 24 + 3) ∨ (27 ≤ b ∧ b < 27 + 4) ∨ (31 ≤ b ∧ b < 31 + 6) ∨ (37 ≤ b ∧ b < 37 + 10) ∨ (47 ≤ b ∧ b < 47 + 16) := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact s4_range_4_5_6 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_blk_4_7_8 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_9_9 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_10_10 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_11_11 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_12_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_13_13 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_14_15 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_16_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_17_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_19_20 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_21_23 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_24_26 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_27_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_31_36 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_37_46 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_4_47_62 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_4

end D0
end LRSpectrumFull
