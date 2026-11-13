/-
# generated (s4_asm/layers.py): all b for a = 37; modules: S4R_37_038_051
-/
import LRSpectrumFull.S4R_37_038_051

namespace LRSpectrumFull
namespace D0

theorem S4A_37 : ∀ b c d : ℕ, 37 < b → b < c → c < d → 37 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 37 b) (Nat.gcd c d) = 1 → S4 ![37, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (38 ≤ b ∧ b < 38 + 14) := by omega
  have h := hcase
  · exact s4_range_37_38_51 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_37

end D0
end LRSpectrumFull
