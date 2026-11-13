/-
# generated (s4_asm/layers.py): all b for a = 19; modules: S4R_19_020_025, S4R_19_026_030, S4R_19_031_040, S4R_19_041_057
-/
import LRSpectrumFull.S4R_19_020_025
import LRSpectrumFull.S4R_19_026_030
import LRSpectrumFull.S4R_19_031_040
import LRSpectrumFull.S4R_19_041_057

namespace LRSpectrumFull
namespace D0

theorem S4A_19 : ∀ b c d : ℕ, 19 < b → b < c → c < d → 19 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 19 b) (Nat.gcd c d) = 1 → S4 ![19, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (20 ≤ b ∧ b < 20 + 6) ∨ (26 ≤ b ∧ b < 26 + 5) ∨ (31 ≤ b ∧ b < 31 + 10) ∨ (41 ≤ b ∧ b < 41 + 17) := by omega
  rcases hcase with h | h | h | h
  · exact s4_range_19_20_25 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_19_26_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_19_31_40 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_19_41_57 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_19

end D0
end LRSpectrumFull
