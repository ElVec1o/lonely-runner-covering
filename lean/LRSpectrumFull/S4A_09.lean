/-
# generated (s4_asm/layers.py): all b for a = 9; modules: S4R_09_010_012, S4R_09_013_016, S4R_09_017_021, S4R_09_022_028, S4R_09_029_042, S4R_09_043_061
-/
import LRSpectrumFull.S4R_09_010_012
import LRSpectrumFull.S4R_09_013_016
import LRSpectrumFull.S4R_09_017_021
import LRSpectrumFull.S4R_09_022_028
import LRSpectrumFull.S4R_09_029_042
import LRSpectrumFull.S4R_09_043_061

namespace LRSpectrumFull
namespace D0

theorem S4A_9 : ∀ b c d : ℕ, 9 < b → b < c → c < d → 9 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 9 b) (Nat.gcd c d) = 1 → S4 ![9, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (10 ≤ b ∧ b < 10 + 3) ∨ (13 ≤ b ∧ b < 13 + 4) ∨ (17 ≤ b ∧ b < 17 + 5) ∨ (22 ≤ b ∧ b < 22 + 7) ∨ (29 ≤ b ∧ b < 29 + 14) ∨ (43 ≤ b ∧ b < 43 + 19) := by omega
  rcases hcase with h | h | h | h | h | h
  · exact s4_range_9_10_12 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_9_13_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_9_17_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_9_22_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_9_29_42 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_9_43_61 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_9

end D0
end LRSpectrumFull
