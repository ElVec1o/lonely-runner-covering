/-
# generated (s4_asm/layers.py): all b for a = 14; modules: S4R_14_015_017, S4R_14_018_020, S4R_14_021_024, S4R_14_025_029, S4R_14_030_059
-/
import LRSpectrumFull.S4R_14_015_017
import LRSpectrumFull.S4R_14_018_020
import LRSpectrumFull.S4R_14_021_024
import LRSpectrumFull.S4R_14_025_029
import LRSpectrumFull.S4R_14_030_059

namespace LRSpectrumFull
namespace D0

theorem S4A_14 : ∀ b c d : ℕ, 14 < b → b < c → c < d → 14 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 14 b) (Nat.gcd c d) = 1 → S4 ![14, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (15 ≤ b ∧ b < 15 + 3) ∨ (18 ≤ b ∧ b < 18 + 3) ∨ (21 ≤ b ∧ b < 21 + 4) ∨ (25 ≤ b ∧ b < 25 + 5) ∨ (30 ≤ b ∧ b < 30 + 30) := by omega
  rcases hcase with h | h | h | h | h
  · exact s4_range_14_15_17 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_14_18_20 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_14_21_24 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_14_25_29 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_14_30_59 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_14

end D0
end LRSpectrumFull
