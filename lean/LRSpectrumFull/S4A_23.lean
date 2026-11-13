/-
# generated (s4_asm/layers.py): all b for a = 23; modules: S4R_23_024_030, S4R_23_031_040, S4R_23_041_056
-/
import LRSpectrumFull.S4R_23_024_030
import LRSpectrumFull.S4R_23_031_040
import LRSpectrumFull.S4R_23_041_056

namespace LRSpectrumFull
namespace D0

theorem S4A_23 : ∀ b c d : ℕ, 23 < b → b < c → c < d → 23 + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd 23 b) (Nat.gcd c d) = 1 → S4 ![23, b, c, d] := by
  intro b c d hb hbc hcd hs hg
  have hcase : (24 ≤ b ∧ b < 24 + 7) ∨ (31 ≤ b ∧ b < 31 + 10) ∨ (41 ≤ b ∧ b < 41 + 16) := by omega
  rcases hcase with h | h | h
  · exact s4_range_23_24_30 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_23_31_40 b c d h.1 h.2 hbc hcd hs hg
  · exact s4_range_23_41_56 b c d h.1 h.2 hbc hcd hs hg

#print axioms S4A_23

end D0
end LRSpectrumFull
