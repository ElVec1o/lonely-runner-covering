/-
# generated (s4_asm/layers.py): all b for a = 40; modules: S4R_40_041_050
-/
import LRSpectrumFull.S4R_40_041_050

namespace LRSpectrumFull
namespace D0

theorem S4A_40 : ∀ b c d : ℕ, 40 < b → b < c → c < d → 40 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 40 b) (Nat.gcd c d) = 1 → S4 ![40, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (41 ≤ b ∧ b < 41 + 10) := by omega
  have h := hcase
  · exact s4_range_40_41_50 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_40

end D0
end LRSpectrumFull
