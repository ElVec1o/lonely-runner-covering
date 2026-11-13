/-
# generated (s4_asm/layers.py): all b for a = 27; modules: S4R_27_028_055
-/
import LRSpectrumFull.S4R_27_028_055

namespace LRSpectrumFull
namespace D0

theorem S4A_27 : ∀ b c d : ℕ, 27 < b → b < c → c < d → 27 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 27 b) (Nat.gcd c d) = 1 → S4 ![27, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (28 ≤ b ∧ b < 28 + 28) := by omega
  have h := hcase
  · exact s4_range_27_28_55 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_27

end D0
end LRSpectrumFull
