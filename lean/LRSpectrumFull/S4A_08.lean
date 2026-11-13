/-
# generated (s4_asm/layers.py): all b for a = 8; modules: S4R_08_009_016, S4R_08_017_028, S4R_08_029_061
-/
import LRSpectrumFull.S4R_08_009_016
import LRSpectrumFull.S4R_08_017_028
import LRSpectrumFull.S4R_08_029_061

namespace LRSpectrumFull
namespace D0

theorem S4A_8 : ∀ b c d : ℕ, 8 < b → b < c → c < d → 8 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 8 b) (Nat.gcd c d) = 1 → S4 ![8, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (9 ≤ b ∧ b < 9 + 8) ∨ (17 ≤ b ∧ b < 17 + 12) ∨ (29 ≤ b ∧ b < 29 + 33) := by omega
  rcases hcase with h | h | h
  · exact s4_range_8_9_16 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_8_17_28 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_8_29_61 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_8

end D0
end LRSpectrumFull
