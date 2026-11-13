/-
# generated (s4_asm/layers.py): all b, a in [41, 47]
-/
import LRSpectrumFull.S4A_41
import LRSpectrumFull.S4A_42
import LRSpectrumFull.S4A_43
import LRSpectrumFull.S4A_44
import LRSpectrumFull.S4A_45
import LRSpectrumFull.S4A_46
import LRSpectrumFull.S4A_47

namespace LRSpectrumFull
namespace D0

theorem S4All_5 : ∀ a b c d : ℕ, 41 ≤ a → a ≤ 47 → a < b → b < c → c < d → a + b + c + d ≤ 195 →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro a b c d h1 h2 hb hbc hcd hs hg
  have hcase : a = 41 ∨ a = 42 ∨ a = 43 ∨ a = 44 ∨ a = 45 ∨ a = 46 ∨ a = 47 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact S4A_41 b c d hb hbc hcd hs hg
  · exact S4A_42 b c d hb hbc hcd hs hg
  · exact S4A_43 b c d hb hbc hcd hs hg
  · exact S4A_44 b c d hb hbc hcd hs hg
  · exact S4A_45 b c d hb hbc hcd hs hg
  · exact S4A_46 b c d hb hbc hcd hs hg
  · exact S4A_47 b c d hb hbc hcd hs hg

#print axioms S4All_5

end D0
end LRSpectrumFull
