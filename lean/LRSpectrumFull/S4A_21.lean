/-
# generated (s4_asm/layers.py): all b for a = 21; modules: S4R_21_022_057
-/
import LRSpectrumFull.S4R_21_022_057

namespace LRSpectrumFull
namespace D0

theorem S4A_21 : ∀ b c d : ℕ, 21 < b → b < c → c < d → 21 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 21 b) (Nat.gcd c d) = 1 → S4 ![21, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (22 ≤ b ∧ b < 22 + 36) := by omega
  have h := hcase
  · exact s4_range_21_22_57 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_21

end D0
end LRSpectrumFull
