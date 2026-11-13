/-
# generated (s4_asm/layers.py): all b for a = 16; modules: S4R_16_017_030, S4R_16_031_058
-/
import LRSpectrumFull.S4R_16_017_030
import LRSpectrumFull.S4R_16_031_058

namespace LRSpectrumFull
namespace D0

theorem S4A_16 : ∀ b c d : ℕ, 16 < b → b < c → c < d → 16 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 16 b) (Nat.gcd c d) = 1 → S4 ![16, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (17 ≤ b ∧ b < 17 + 14) ∨ (31 ≤ b ∧ b < 31 + 28) := by omega
  rcases hcase with h | h
  · exact s4_range_16_17_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_16_31_58 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_16

end D0
end LRSpectrumFull
