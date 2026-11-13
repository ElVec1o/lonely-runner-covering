/-
# generated (s4_asm/layers.py): all b for a = 36; modules: S4R_36_037_052
-/
import LRSpectrumFull.S4R_36_037_052

namespace LRSpectrumFull
namespace D0

theorem S4A_36 : ∀ b c d : ℕ, 36 < b → b < c → c < d → 36 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 36 b) (Nat.gcd c d) = 1 → S4 ![36, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (37 ≤ b ∧ b < 37 + 16) := by omega
  have h := hcase
  · exact s4_range_36_37_52 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_36

end D0
end LRSpectrumFull
