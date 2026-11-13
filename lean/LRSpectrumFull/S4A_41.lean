/-
# generated (s4_asm/layers.py): all b for a = 41; modules: S4Range41
-/
import LRSpectrumFull.S4Range41

namespace LRSpectrumFull
namespace D0

theorem S4A_41 : ∀ b c d : ℕ, 41 < b → b < c → c < d → 41 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 41 b) (Nat.gcd c d) = 1 → S4 ![41, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (42 ≤ b ∧ b < 42 + 9) := by omega
  have h := hcase
  · exact S4_a41 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_41

end D0
end LRSpectrumFull
