/-
# generated (s4_asm/layers.py): all b for a = 22; modules: S4Range22
-/
import LRSpectrumFull.S4Range22

namespace LRSpectrumFull
namespace D0

theorem S4A_22 : ∀ b c d : ℕ, 22 < b → b < c → c < d → 22 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 22 b) (Nat.gcd c d) = 1 → S4 ![22, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (23 ≤ b ∧ b < 23 + 34) := by omega
  have h := hcase
  · exact S4_a22 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_22

end D0
end LRSpectrumFull
