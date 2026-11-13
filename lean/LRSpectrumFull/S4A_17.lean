/-
# generated (s4_asm/layers.py): all b for a = 17; modules: S4R_17_018_021, S4R_17_022_025, S4R_17_026_030, S4R_17_031_040, S4R_17_041_058
-/
import LRSpectrumFull.S4R_17_018_021
import LRSpectrumFull.S4R_17_022_025
import LRSpectrumFull.S4R_17_026_030
import LRSpectrumFull.S4R_17_031_040
import LRSpectrumFull.S4R_17_041_058

namespace LRSpectrumFull
namespace D0

theorem S4A_17 : ∀ b c d : ℕ, 17 < b → b < c → c < d → 17 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 17 b) (Nat.gcd c d) = 1 → S4 ![17, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (18 ≤ b ∧ b < 18 + 4) ∨ (22 ≤ b ∧ b < 22 + 4) ∨ (26 ≤ b ∧ b < 26 + 5) ∨ (31 ≤ b ∧ b < 31 + 10) ∨ (41 ≤ b ∧ b < 41 + 18) := by omega
  rcases hcase with h | h | h | h | h
  · exact s4_range_17_18_21 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_17_22_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_17_26_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_17_31_40 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_17_41_58 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_17

end D0
end LRSpectrumFull
