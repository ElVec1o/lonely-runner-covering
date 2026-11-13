/-
# generated (s4_asm/layers.py): all b for a = 32; modules: S4R_32_033_053
-/
import LRSpectrumFull.S4R_32_033_053

namespace LRSpectrumFull
namespace D0

theorem S4A_32 : ∀ b c d : ℕ, 32 < b → b < c → c < d → 32 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 32 b) (Nat.gcd c d) = 1 → S4 ![32, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (33 ≤ b ∧ b < 33 + 21) := by omega
  have h := hcase
  · exact s4_range_32_33_53 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_32

end D0
end LRSpectrumFull
