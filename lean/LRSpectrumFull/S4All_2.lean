/-
# generated (s4_asm/layers.py): all b, a in [11, 20]
-/
import LRSpectrumFull.S4A_11
import LRSpectrumFull.S4A_12
import LRSpectrumFull.S4A_13
import LRSpectrumFull.S4A_14
import LRSpectrumFull.S4A_15
import LRSpectrumFull.S4A_16
import LRSpectrumFull.S4A_17
import LRSpectrumFull.S4A_18
import LRSpectrumFull.S4A_19
import LRSpectrumFull.S4A_20

namespace LRSpectrumFull
namespace D0

theorem S4All_2 : ∀ a b c d : ℕ, 11 ≤ a → a ≤ 20 → a < b → b < c → c < d → a + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro a b c d h1 h2 hb hbc hcd hs hg
  have hcase : a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 ∨ a = 20 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S4A_11 b c d hb hbc hcd hs hg
  · exact S4A_12 b c d hb hbc hcd hs hg
  · exact S4A_13 b c d hb hbc hcd hs hg
  · exact S4A_14 b c d hb hbc hcd hs hg
  · exact S4A_15 b c d hb hbc hcd hs hg
  · exact S4A_16 b c d hb hbc hcd hs hg
  · exact S4A_17 b c d hb hbc hcd hs hg
  · exact S4A_18 b c d hb hbc hcd hs hg
  · exact S4A_19 b c d hb hbc hcd hs hg
  · exact S4A_20 b c d hb hbc hcd hs hg

#print axioms S4All_2

end D0
end LRSpectrumFull
