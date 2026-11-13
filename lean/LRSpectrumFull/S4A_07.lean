/-
# generated (s4_asm/layers.py): all b for a = 7; modules: S4R_07_008_008, S4R_07_009_010, S4R_07_011_012, S4R_07_013_014, S4R_07_015_015, S4R_07_016_017, S4R_07_018_019, S4R_07_020_022, S4R_07_023_025, S4R_07_026_028, S4R_07_029_061
-/
import LRSpectrumFull.S4R_07_008_008
import LRSpectrumFull.S4R_07_009_010
import LRSpectrumFull.S4R_07_011_012
import LRSpectrumFull.S4R_07_013_014
import LRSpectrumFull.S4R_07_015_015
import LRSpectrumFull.S4R_07_016_017
import LRSpectrumFull.S4R_07_018_019
import LRSpectrumFull.S4R_07_020_022
import LRSpectrumFull.S4R_07_023_025
import LRSpectrumFull.S4R_07_026_028
import LRSpectrumFull.S4R_07_029_061

namespace LRSpectrumFull
namespace D0

theorem S4A_7 : ∀ b c d : ℕ, 7 < b → b < c → c < d → 7 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 7 b) (Nat.gcd c d) = 1 → S4 ![7, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (8 ≤ b ∧ b < 8 + 1) ∨ (9 ≤ b ∧ b < 9 + 2) ∨ (11 ≤ b ∧ b < 11 + 2) ∨ (13 ≤ b ∧ b < 13 + 2) ∨ (15 ≤ b ∧ b < 15 + 1) ∨ (16 ≤ b ∧ b < 16 + 2) ∨ (18 ≤ b ∧ b < 18 + 2) ∨ (20 ≤ b ∧ b < 20 + 3) ∨ (23 ≤ b ∧ b < 23 + 3) ∨ (26 ≤ b ∧ b < 26 + 3) ∨ (29 ≤ b ∧ b < 29 + 33) := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h
  · exact s4_range_7_8_8 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_9_10 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_11_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_13_14 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_15_15 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_16_17 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_18_19 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_20_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_23_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_26_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_7_29_61 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_7

end D0
end LRSpectrumFull
