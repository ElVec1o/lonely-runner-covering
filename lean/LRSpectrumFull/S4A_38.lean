/-
# generated (s4_asm/layers.py): all b for a = 38; modules: S4R_38_039_051
-/
import LRSpectrumFull.S4R_38_039_051

namespace LRSpectrumFull
namespace D0

theorem S4A_38 : ∀ b c d : ℕ, 38 < b → b < c → c < d → 38 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 38 b) (Nat.gcd c d) = 1 → S4 ![38, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (39 ≤ b ∧ b < 39 + 13) := by omega
  have h := hcase
  · exact s4_range_38_39_51 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_38

end D0
end LRSpectrumFull
