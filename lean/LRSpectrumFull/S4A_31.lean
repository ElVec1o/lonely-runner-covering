/-
# generated (s4_asm/layers.py): all b for a = 31; modules: S4R_31_032_053
-/
import LRSpectrumFull.S4R_31_032_053

namespace LRSpectrumFull
namespace D0

theorem S4A_31 : ∀ b c d : ℕ, 31 < b → b < c → c < d → 31 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 31 b) (Nat.gcd c d) = 1 → S4 ![31, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (32 ≤ b ∧ b < 32 + 22) := by omega
  have h := hcase
  · exact s4_range_31_32_53 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_31

end D0
end LRSpectrumFull
