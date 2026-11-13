/-
# generated (s4_asm/layers.py): all b for a = 47; modules: S4R_47_048_048
-/
import LRSpectrumFull.S4R_47_048_048

namespace LRSpectrumFull
namespace D0

theorem S4A_47 : ∀ b c d : ℕ, 47 < b → b < c → c < d → 47 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 47 b) (Nat.gcd c d) = 1 → S4 ![47, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (48 ≤ b ∧ b < 48 + 1) := by omega
  have h := hcase
  · exact s4_range_47_48_48 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_47

end D0
end LRSpectrumFull
