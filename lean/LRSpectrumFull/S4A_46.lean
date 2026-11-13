/-
# generated (s4_asm/layers.py): all b for a = 46; modules: S4R_46_047_048
-/
import LRSpectrumFull.S4R_46_047_048

namespace LRSpectrumFull
namespace D0

theorem S4A_46 : ∀ b c d : ℕ, 46 < b → b < c → c < d → 46 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 46 b) (Nat.gcd c d) = 1 → S4 ![46, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (47 ≤ b ∧ b < 47 + 2) := by omega
  have h := hcase
  · exact s4_range_46_47_48 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_46

end D0
end LRSpectrumFull
