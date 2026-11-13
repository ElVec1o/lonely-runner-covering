/-
# generated (s4_asm/layers.py): all b for a = 45; modules: S4R_45_046_049
-/
import LRSpectrumFull.S4R_45_046_049

namespace LRSpectrumFull
namespace D0

theorem S4A_45 : ∀ b c d : ℕ, 45 < b → b < c → c < d → 45 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 45 b) (Nat.gcd c d) = 1 → S4 ![45, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (46 ≤ b ∧ b < 46 + 4) := by omega
  have h := hcase
  · exact s4_range_45_46_49 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_45

end D0
end LRSpectrumFull
