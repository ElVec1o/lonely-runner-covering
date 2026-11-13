/-
# generated (s4_asm/layers.py): all b for a = 12; modules: S4R_12_013_014, S4R_12_015_016, S4R_12_017_018, S4R_12_019_021, S4R_12_022_024, S4R_12_025_060
-/
import LRSpectrumFull.S4R_12_013_014
import LRSpectrumFull.S4R_12_015_016
import LRSpectrumFull.S4R_12_017_018
import LRSpectrumFull.S4R_12_019_021
import LRSpectrumFull.S4R_12_022_024
import LRSpectrumFull.S4R_12_025_060

namespace LRSpectrumFull
namespace D0

theorem S4A_12 : ∀ b c d : ℕ, 12 < b → b < c → c < d → 12 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 12 b) (Nat.gcd c d) = 1 → S4 ![12, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (13 ≤ b ∧ b < 13 + 2) ∨ (15 ≤ b ∧ b < 15 + 2) ∨ (17 ≤ b ∧ b < 17 + 2) ∨ (19 ≤ b ∧ b < 19 + 3) ∨ (22 ≤ b ∧ b < 22 + 3) ∨ (25 ≤ b ∧ b < 25 + 36) := by omega
  rcases hcase with h | h | h | h | h | h
  · exact s4_range_12_13_14 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_12_15_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_12_17_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_12_19_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_12_22_24 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_12_25_60 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_12

end D0
end LRSpectrumFull
