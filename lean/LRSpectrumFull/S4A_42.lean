/-
# generated (s4_asm/layers.py): all b for a = 42; modules: S4R_42_043_050
-/
import LRSpectrumFull.S4R_42_043_050

namespace LRSpectrumFull
namespace D0

theorem S4A_42 : ∀ b c d : ℕ, 42 < b → b < c → c < d → 42 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 42 b) (Nat.gcd c d) = 1 → S4 ![42, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (43 ≤ b ∧ b < 43 + 8) := by omega
  have h := hcase
  · exact s4_range_42_43_50 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_42

end D0
end LRSpectrumFull
