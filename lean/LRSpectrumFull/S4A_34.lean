/-
# generated (s4_asm/layers.py): all b for a = 34; modules: S4R_34_035_052
-/
import LRSpectrumFull.S4R_34_035_052

namespace LRSpectrumFull
namespace D0

theorem S4A_34 : ∀ b c d : ℕ, 34 < b → b < c → c < d → 34 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 34 b) (Nat.gcd c d) = 1 → S4 ![34, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (35 ≤ b ∧ b < 35 + 18) := by omega
  have h := hcase
  · exact s4_range_34_35_52 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_34

end D0
end LRSpectrumFull
