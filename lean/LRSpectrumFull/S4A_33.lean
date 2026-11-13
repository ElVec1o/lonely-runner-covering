/-
# generated (s4_asm/layers.py): all b for a = 33; modules: S4R_33_034_053
-/
import LRSpectrumFull.S4R_33_034_053

namespace LRSpectrumFull
namespace D0

theorem S4A_33 : ∀ b c d : ℕ, 33 < b → b < c → c < d → 33 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 33 b) (Nat.gcd c d) = 1 → S4 ![33, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (34 ≤ b ∧ b < 34 + 20) := by omega
  have h := hcase
  · exact s4_range_33_34_53 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_33

end D0
end LRSpectrumFull
