/-
# generated (s4_asm/layers.py): all b for a = 11; modules: S4Range11b12n3, S4R_11_015_017, S4R_11_018_022, S4R_11_023_026, S4R_11_027_031, S4R_11_032_042, S4R_11_043_060
-/
import LRSpectrumFull.S4Range11b12n3
import LRSpectrumFull.S4R_11_015_017
import LRSpectrumFull.S4R_11_018_022
import LRSpectrumFull.S4R_11_023_026
import LRSpectrumFull.S4R_11_027_031
import LRSpectrumFull.S4R_11_032_042
import LRSpectrumFull.S4R_11_043_060

namespace LRSpectrumFull
namespace D0

theorem S4A_11 : ∀ b c d : ℕ, 11 < b → b < c → c < d → 11 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 11 b) (Nat.gcd c d) = 1 → S4 ![11, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (12 ≤ b ∧ b < 12 + 3) ∨ (15 ≤ b ∧ b < 15 + 3) ∨ (18 ≤ b ∧ b < 18 + 5) ∨ (23 ≤ b ∧ b < 23 + 4) ∨ (27 ≤ b ∧ b < 27 + 5) ∨ (32 ≤ b ∧ b < 32 + 11) ∨ (43 ≤ b ∧ b < 43 + 18) := by omega
  rcases hcase with h | h | h | h | h | h | h
  · exact S4_a11_12_3 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_15_17 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_18_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_23_26 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_27_31 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_32_42 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_11_43_60 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_11

end D0
end LRSpectrumFull
