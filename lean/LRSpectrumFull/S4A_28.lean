/-
# generated (s4_asm/layers.py): all b for a = 28; modules: S4Range28
-/
import LRSpectrumFull.S4Range28

namespace LRSpectrumFull
namespace D0

theorem S4A_28 : ∀ b c d : ℕ, 28 < b → b < c → c < d → 28 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 28 b) (Nat.gcd c d) = 1 → S4 ![28, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (29 ≤ b ∧ b < 29 + 26) := by omega
  have h := hcase
  · exact S4_a28 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_28

end D0
end LRSpectrumFull
