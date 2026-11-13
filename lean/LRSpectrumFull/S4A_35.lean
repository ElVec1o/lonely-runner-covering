/-
# generated (s4_asm/layers.py): all b for a = 35; modules: S4R_35_036_052
-/
import LRSpectrumFull.S4R_35_036_052

namespace LRSpectrumFull
namespace D0

theorem S4A_35 : ∀ b c d : ℕ, 35 < b → b < c → c < d → 35 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 35 b) (Nat.gcd c d) = 1 → S4 ![35, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (36 ≤ b ∧ b < 36 + 17) := by omega
  have h := hcase
  · exact s4_range_35_36_52 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_35

end D0
end LRSpectrumFull
