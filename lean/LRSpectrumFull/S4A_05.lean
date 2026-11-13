/-
# generated (s4_asm/layers.py): all b for a = 5; modules: S4Range5
-/
import LRSpectrumFull.S4Range5

namespace LRSpectrumFull
namespace D0

theorem S4A_5 : ∀ b c d : ℕ, 5 < b → b < c → c < d → 5 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 5 b) (Nat.gcd c d) = 1 → S4 ![5, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (6 ≤ b ∧ b < 6 + 57) := by omega
  have h := hcase
  · exact S4_a5 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_5

end D0
end LRSpectrumFull
