/-
# Rank-1 sign-flip invariance of `D` (building block toward the kernel bound)

`D` (the 1-dimensional view-obstruction value of a runner tuple) is unchanged by
negating any single runner — `nearestIntDist` is even. This is the rank-1 analog
of `mD_sign_flip`, and a normalization tool: to apply `coord_bound` to a triple
`(a,b,c)`, one first reduces to non-negative coordinates via this lemma. No `sorry`.
-/
import LRSpectrumFull.DValue

namespace LRSpectrumFull

variable {k : ℕ}

/-- Negating runner `i` leaves the rank-1 gap unchanged. -/
theorem gap_sign_flip (v : Fin (k + 1) → ℤ) (i : Fin (k + 1)) (t : ℝ) :
    gap (Function.update v i (-(v i))) t = gap v t := by
  unfold gap
  congr 1
  funext j
  rcases eq_or_ne j i with h | h
  · subst h
    rw [Function.update_self]
    rw [show ((-(v j) : ℤ) : ℝ) * t = -(((v j : ℤ) : ℝ) * t) by push_cast; ring,
      nearestIntDist_neg]
  · rw [Function.update_of_ne h]

/-- **Sign-flip invariance of `D`.** Negating any single runner leaves the
1-dimensional view-obstruction value unchanged. -/
theorem D_sign_flip (v : Fin (k + 1) → ℤ) (i : Fin (k + 1)) :
    D (Function.update v i (-(v i))) = D v := by
  unfold D ML
  rw [funext (gap_sign_flip v i)]

end LRSpectrumFull
