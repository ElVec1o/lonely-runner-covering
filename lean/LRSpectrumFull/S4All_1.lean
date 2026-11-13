/-
# generated (s4_asm/layers.py): all b, a in [1, 10]
-/
import LRSpectrumFull.S4A_01
import LRSpectrumFull.S4A_02
import LRSpectrumFull.S4A_03
import LRSpectrumFull.S4A_04
import LRSpectrumFull.S4A_05
import LRSpectrumFull.S4A_06
import LRSpectrumFull.S4A_07
import LRSpectrumFull.S4A_08
import LRSpectrumFull.S4A_09
import LRSpectrumFull.S4A_10

namespace LRSpectrumFull
namespace D0

theorem S4All_1 : ∀ a b c d : ℕ, 1 ≤ a → a ≤ 10 → a < b → b < c → c < d → a + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro a b c d h1 h2 hb hbc hcd hs hg
  have hcase : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S4A_1 b c d hb hbc hcd hs hg
  · exact S4A_2 b c d hb hbc hcd hs hg
  · exact S4A_3 b c d hb hbc hcd hs hg
  · exact S4A_4 b c d hb hbc hcd hs hg
  · exact S4A_5 b c d hb hbc hcd hs hg
  · exact S4A_6 b c d hb hbc hcd hs hg
  · exact S4A_7 b c d hb hbc hcd hs hg
  · exact S4A_8 b c d hb hbc hcd hs hg
  · exact S4A_9 b c d hb hbc hcd hs hg
  · exact S4A_10 b c d hb hbc hcd hs hg

#print axioms S4All_1

end D0
end LRSpectrumFull
