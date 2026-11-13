/-
# generated (s4_asm/layers.py): all b for a = 20; modules: S4R_20_021_057
-/
import LRSpectrumFull.S4R_20_021_057

namespace LRSpectrumFull
namespace D0

theorem S4A_20 : ∀ b c d : ℕ, 20 < b → b < c → c < d → 20 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 20 b) (Nat.gcd c d) = 1 → S4 ![20, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (21 ≤ b ∧ b < 21 + 37) := by omega
  have h := hcase
  · exact s4_range_20_21_57 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_20

end D0
end LRSpectrumFull
