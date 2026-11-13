/-
# generated (s4_asm/layers.py): all b for a = 10; modules: S4R_10_011_012, S4R_10_013_015, S4R_10_016_018, S4R_10_019_022, S4R_10_023_027, S4R_10_028_034, S4R_10_035_060
-/
import LRSpectrumFull.S4R_10_011_012
import LRSpectrumFull.S4R_10_013_015
import LRSpectrumFull.S4R_10_016_018
import LRSpectrumFull.S4R_10_019_022
import LRSpectrumFull.S4R_10_023_027
import LRSpectrumFull.S4R_10_028_034
import LRSpectrumFull.S4R_10_035_060

namespace LRSpectrumFull
namespace D0

theorem S4A_10 : ∀ b c d : ℕ, 10 < b → b < c → c < d → 10 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 10 b) (Nat.gcd c d) = 1 → S4 ![10, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (11 ≤ b ∧ b < 11 + 2) ∨ (13 ≤ b ∧ b < 13 + 3) ∨ (16 ≤ b ∧ b < 16 + 3) ∨ (19 ≤ b ∧ b < 19 + 4) ∨ (23 ≤ b ∧ b < 23 + 5) ∨ (28 ≤ b ∧ b < 28 + 7) ∨ (35 ≤ b ∧ b < 35 + 26) := by omega
  rcases hcase with h | h | h | h | h | h | h
  · exact s4_range_10_11_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_13_15 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_16_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_19_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_23_27 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_28_34 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_10_35_60 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_10

end D0
end LRSpectrumFull
