/-
# generated (s4_asm/layers.py): all b for a = 13; modules: S4R_13_014_016, S4R_13_017_018, S4R_13_019_022, S4R_13_023_028, S4R_13_029_033, S4R_13_034_052, S4R_13_053_059
-/
import LRSpectrumFull.S4R_13_014_016
import LRSpectrumFull.S4R_13_017_018
import LRSpectrumFull.S4R_13_019_022
import LRSpectrumFull.S4R_13_023_028
import LRSpectrumFull.S4R_13_029_033
import LRSpectrumFull.S4R_13_034_052
import LRSpectrumFull.S4R_13_053_059

namespace LRSpectrumFull
namespace D0

theorem S4A_13 : ∀ b c d : ℕ, 13 < b → b < c → c < d → 13 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 13 b) (Nat.gcd c d) = 1 → S4 ![13, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (14 ≤ b ∧ b < 14 + 3) ∨ (17 ≤ b ∧ b < 17 + 2) ∨ (19 ≤ b ∧ b < 19 + 4) ∨ (23 ≤ b ∧ b < 23 + 6) ∨ (29 ≤ b ∧ b < 29 + 5) ∨ (34 ≤ b ∧ b < 34 + 19) ∨ (53 ≤ b ∧ b < 53 + 7) := by omega
  rcases hcase with h | h | h | h | h | h | h
  · exact s4_range_13_14_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_17_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_19_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_23_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_29_33 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_34_52 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_13_53_59 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_13

end D0
end LRSpectrumFull
