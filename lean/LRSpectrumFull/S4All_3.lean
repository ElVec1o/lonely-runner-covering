/-
# generated (s4_asm/layers.py): all b, a in [21, 30]
-/
import LRSpectrumFull.S4A_21
import LRSpectrumFull.S4A_22
import LRSpectrumFull.S4A_23
import LRSpectrumFull.S4A_24
import LRSpectrumFull.S4A_25
import LRSpectrumFull.S4A_26
import LRSpectrumFull.S4A_27
import LRSpectrumFull.S4A_28
import LRSpectrumFull.S4A_29
import LRSpectrumFull.S4A_30

namespace LRSpectrumFull
namespace D0

theorem S4All_3 : ∀ a b c d : ℕ, 21 ≤ a → a ≤ 30 → a < b → b < c → c < d → a + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro a b c d h1 h2 hb hbc hcd hs hg
  have hcase : a = 21 ∨ a = 22 ∨ a = 23 ∨ a = 24 ∨ a = 25 ∨ a = 26 ∨ a = 27 ∨ a = 28 ∨ a = 29 ∨ a = 30 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S4A_21 b c d hb hbc hcd hs hg
  · exact S4A_22 b c d hb hbc hcd hs hg
  · exact S4A_23 b c d hb hbc hcd hs hg
  · exact S4A_24 b c d hb hbc hcd hs hg
  · exact S4A_25 b c d hb hbc hcd hs hg
  · exact S4A_26 b c d hb hbc hcd hs hg
  · exact S4A_27 b c d hb hbc hcd hs hg
  · exact S4A_28 b c d hb hbc hcd hs hg
  · exact S4A_29 b c d hb hbc hcd hs hg
  · exact S4A_30 b c d hb hbc hcd hs hg

#print axioms S4All_3

end D0
end LRSpectrumFull
