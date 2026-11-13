/-
# generated (s4_asm/layers.py): all b for a = 44; modules: S4R_44_045_049
-/
import LRSpectrumFull.S4R_44_045_049

namespace LRSpectrumFull
namespace D0

theorem S4A_44 : ∀ b c d : ℕ, 44 < b → b < c → c < d → 44 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 44 b) (Nat.gcd c d) = 1 → S4 ![44, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (45 ≤ b ∧ b < 45 + 5) := by omega
  have h := hcase
  · exact s4_range_44_45_49 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_44

end D0
end LRSpectrumFull
