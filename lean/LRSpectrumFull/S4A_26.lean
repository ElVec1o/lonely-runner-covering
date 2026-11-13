/-
# generated (s4_asm/layers.py): all b for a = 26; modules: S4R_26_027_055
-/
import LRSpectrumFull.S4R_26_027_055

namespace LRSpectrumFull
namespace D0

theorem S4A_26 : ∀ b c d : ℕ, 26 < b → b < c → c < d → 26 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 26 b) (Nat.gcd c d) = 1 → S4 ![26, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (27 ≤ b ∧ b < 27 + 29) := by omega
  have h := hcase
  · exact s4_range_26_27_55 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_26

end D0
end LRSpectrumFull
