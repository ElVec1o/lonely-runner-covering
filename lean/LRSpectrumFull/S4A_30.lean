/-
# generated (s4_asm/layers.py): all b for a = 30; modules: S4R_30_031_054
-/
import LRSpectrumFull.S4R_30_031_054

namespace LRSpectrumFull
namespace D0

theorem S4A_30 : ∀ b c d : ℕ, 30 < b → b < c → c < d → 30 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 30 b) (Nat.gcd c d) = 1 → S4 ![30, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (31 ≤ b ∧ b < 31 + 24) := by omega
  have h := hcase
  · exact s4_range_30_31_54 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_30

end D0
end LRSpectrumFull
