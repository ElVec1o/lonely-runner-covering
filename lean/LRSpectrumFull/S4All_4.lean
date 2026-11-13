/-
# generated (s4_asm/layers.py): all b, a in [31, 40]
-/
import LRSpectrumFull.S4A_31
import LRSpectrumFull.S4A_32
import LRSpectrumFull.S4A_33
import LRSpectrumFull.S4A_34
import LRSpectrumFull.S4A_35
import LRSpectrumFull.S4A_36
import LRSpectrumFull.S4A_37
import LRSpectrumFull.S4A_38
import LRSpectrumFull.S4A_39
import LRSpectrumFull.S4A_40

namespace LRSpectrumFull
namespace D0

theorem S4All_4 : ∀ a b c d : ℕ, 31 ≤ a → a ≤ 40 → a < b → b < c → c < d → a + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro a b c d h1 h2 hb hbc hcd hs hg
  have hcase : a = 31 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 35 ∨ a = 36 ∨ a = 37 ∨ a = 38 ∨ a = 39 ∨ a = 40 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S4A_31 b c d hb hbc hcd hs hg
  · exact S4A_32 b c d hb hbc hcd hs hg
  · exact S4A_33 b c d hb hbc hcd hs hg
  · exact S4A_34 b c d hb hbc hcd hs hg
  · exact S4A_35 b c d hb hbc hcd hs hg
  · exact S4A_36 b c d hb hbc hcd hs hg
  · exact S4A_37 b c d hb hbc hcd hs hg
  · exact S4A_38 b c d hb hbc hcd hs hg
  · exact S4A_39 b c d hb hbc hcd hs hg
  · exact S4A_40 b c d hb hbc hcd hs hg

#print axioms S4All_4

end D0
end LRSpectrumFull
