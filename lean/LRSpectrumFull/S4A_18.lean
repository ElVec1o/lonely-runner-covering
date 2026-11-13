/-
# generated (s4_asm/layers.py): all b for a = 18; modules: S4R_18_019_021, S4R_18_022_025, S4R_18_026_030, S4R_18_031_040, S4R_18_041_042, S4R_18_043_058
-/
import LRSpectrumFull.S4R_18_019_021
import LRSpectrumFull.S4R_18_022_025
import LRSpectrumFull.S4R_18_026_030
import LRSpectrumFull.S4R_18_031_040
import LRSpectrumFull.S4R_18_041_042
import LRSpectrumFull.S4R_18_043_058

namespace LRSpectrumFull
namespace D0

theorem S4A_18 : ∀ b c d : ℕ, 18 < b → b < c → c < d → 18 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 18 b) (Nat.gcd c d) = 1 → S4 ![18, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (19 ≤ b ∧ b < 19 + 3) ∨ (22 ≤ b ∧ b < 22 + 4) ∨ (26 ≤ b ∧ b < 26 + 5) ∨ (31 ≤ b ∧ b < 31 + 10) ∨ (41 ≤ b ∧ b < 41 + 2) ∨ (43 ≤ b ∧ b < 43 + 16) := by omega
  rcases hcase with h | h | h | h | h | h
  · exact s4_range_18_19_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_18_22_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_18_26_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_18_31_40 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_18_41_42 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_18_43_58 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_18

end D0
end LRSpectrumFull
