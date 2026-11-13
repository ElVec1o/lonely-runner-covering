/-
# generated (s4_asm/layers.py): all b for a = 43; modules: S4R_43_044_049
-/
import LRSpectrumFull.S4R_43_044_049

namespace LRSpectrumFull
namespace D0

theorem S4A_43 : ∀ b c d : ℕ, 43 < b → b < c → c < d → 43 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 43 b) (Nat.gcd c d) = 1 → S4 ![43, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (44 ≤ b ∧ b < 44 + 6) := by omega
  have h := hcase
  · exact s4_range_43_44_49 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_43

end D0
end LRSpectrumFull
