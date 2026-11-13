/-
# generated (s4_asm/layers.py): all b for a = 29; modules: S4R_29_030_048, S4R_29_049_054
-/
import LRSpectrumFull.S4R_29_030_048
import LRSpectrumFull.S4R_29_049_054

namespace LRSpectrumFull
namespace D0

theorem S4A_29 : ∀ b c d : ℕ, 29 < b → b < c → c < d → 29 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 29 b) (Nat.gcd c d) = 1 → S4 ![29, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (30 ≤ b ∧ b < 30 + 19) ∨ (49 ≤ b ∧ b < 49 + 6) := by omega
  rcases hcase with h | h
  · exact s4_range_29_30_48 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_29_49_54 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_29

end D0
end LRSpectrumFull
