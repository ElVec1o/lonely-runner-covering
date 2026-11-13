/-
# generated (s4_asm/layers.py): all b for a = 6; modules: S4R_06_007_008, S4R_06_009_010, S4R_06_011_011, S4R_06_012_012, S4R_06_013_013, S4R_06_014_014, S4R_06_015_025, S4R_06_026_062
-/
import LRSpectrumFull.S4R_06_007_008
import LRSpectrumFull.S4R_06_009_010
import LRSpectrumFull.S4R_06_011_011
import LRSpectrumFull.S4R_06_012_012
import LRSpectrumFull.S4R_06_013_013
import LRSpectrumFull.S4R_06_014_014
import LRSpectrumFull.S4R_06_015_025
import LRSpectrumFull.S4R_06_026_062

namespace LRSpectrumFull
namespace D0

theorem S4A_6 : ∀ b c d : ℕ, 6 < b → b < c → c < d → 6 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 6 b) (Nat.gcd c d) = 1 → S4 ![6, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (7 ≤ b ∧ b < 7 + 2) ∨ (9 ≤ b ∧ b < 9 + 2) ∨ (11 ≤ b ∧ b < 11 + 1) ∨ (12 ≤ b ∧ b < 12 + 1) ∨ (13 ≤ b ∧ b < 13 + 1) ∨ (14 ≤ b ∧ b < 14 + 1) ∨ (15 ≤ b ∧ b < 15 + 11) ∨ (26 ≤ b ∧ b < 26 + 37) := by omega
  rcases hcase with h | h | h | h | h | h | h | h
  · exact s4_range_6_7_8 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_9_10 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_11_11 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_12_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_13_13 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_14_14 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_15_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_6_26_62 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_6

end D0
end LRSpectrumFull
