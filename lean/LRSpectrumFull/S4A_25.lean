/-
# generated (s4_asm/layers.py): all b for a = 25; modules: S4R_25_026_055
-/
import LRSpectrumFull.S4R_25_026_055

namespace LRSpectrumFull
namespace D0

theorem S4A_25 : ∀ b c d : ℕ, 25 < b → b < c → c < d → 25 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 25 b) (Nat.gcd c d) = 1 → S4 ![25, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (26 ≤ b ∧ b < 26 + 30) := by omega
  have h := hcase
  · exact s4_range_25_26_55 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_25

end D0
end LRSpectrumFull
