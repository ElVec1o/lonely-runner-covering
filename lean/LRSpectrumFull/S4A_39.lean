/-
# generated (s4_asm/layers.py): all b for a = 39; modules: S4R_39_040_051
-/
import LRSpectrumFull.S4R_39_040_051

namespace LRSpectrumFull
namespace D0

theorem S4A_39 : ∀ b c d : ℕ, 39 < b → b < c → c < d → 39 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 39 b) (Nat.gcd c d) = 1 → S4 ![39, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (40 ≤ b ∧ b < 40 + 12) := by omega
  have h := hcase
  · exact s4_range_39_40_51 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_39

end D0
end LRSpectrumFull
