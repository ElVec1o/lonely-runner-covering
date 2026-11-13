/-
# `PreOK` is closed under list append (used when the time covers of a blocked range are split over several
`TCP_*` modules, each proving `PreOK` of its own list).
-/
import LRSpectrumFull.S4Loop2

namespace LRSpectrumFull
namespace D0

theorem preOK_append {L1 L2 : List (ℕ × ℕ × ℕ × ℕ)} (h1 : PreOK L1) (h2 : PreOK L2) :
    PreOK (L1 ++ L2) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

end D0
end LRSpectrumFull
