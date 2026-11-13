/-
# generated (s4_asm/layers.py): all b for a = 24; modules: S4R_24_025_056
-/
import LRSpectrumFull.S4R_24_025_056

namespace LRSpectrumFull
namespace D0

theorem S4A_24 : ∀ b c d : ℕ, 24 < b → b < c → c < d → 24 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 24 b) (Nat.gcd c d) = 1 → S4 ![24, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (25 ≤ b ∧ b < 25 + 32) := by omega
  have h := hcase
  · exact s4_range_24_25_56 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_24

end D0
end LRSpectrumFull
