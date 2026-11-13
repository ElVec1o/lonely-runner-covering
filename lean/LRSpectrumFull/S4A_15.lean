/-
# generated (s4_asm/layers.py): all b for a = 15; modules: S4R_15_016_018, S4R_15_019_022, S4R_15_023_027, S4R_15_028_035, S4R_15_036_059
-/
import LRSpectrumFull.S4R_15_016_018
import LRSpectrumFull.S4R_15_019_022
import LRSpectrumFull.S4R_15_023_027
import LRSpectrumFull.S4R_15_028_035
import LRSpectrumFull.S4R_15_036_059

namespace LRSpectrumFull
namespace D0

theorem S4A_15 : ∀ b c d : ℕ, 15 < b → b < c → c < d → 15 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 15 b) (Nat.gcd c d) = 1 → S4 ![15, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (16 ≤ b ∧ b < 16 + 3) ∨ (19 ≤ b ∧ b < 19 + 4) ∨ (23 ≤ b ∧ b < 23 + 5) ∨ (28 ≤ b ∧ b < 28 + 8) ∨ (36 ≤ b ∧ b < 36 + 24) := by omega
  rcases hcase with h | h | h | h | h
  · exact s4_range_15_16_18 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_15_19_22 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_15_23_27 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_15_28_35 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_15_36_59 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_15

end D0
end LRSpectrumFull
