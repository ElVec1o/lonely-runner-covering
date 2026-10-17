/-
# Milestone 14: the rank-r framework extends the rank-1 D-value faithfully

The rank-`r` tower (`mgap`/`mML`/`mD`, Milestone 12) is a genuine
generalization of the original vector tower (`gap`/`ML`/`D`): at `r = 1`
they coincide. Concretely, viewing a speed vector `v1 : Fin (k+1) → ℤ`
as the one-column matrix `fun i => ![v1 i]`,

    mgap (col v1) t = gap v1 (t 0),   mML (col v1) = ML v1,   mD (col v1) = D v1.

This is the coherence theorem that justifies calling the rank-2 object
`δ₂` "the 2-dimensional threshold": its `r = 1` shadow is exactly the
two-runner theory proved in Milestones 1–10. No `sorry`.
-/

import LRSpectrumFull.Subtorus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace LRSpectrumFull

variable {k : ℕ}

/-- The one-column matrix of a speed vector. -/
def col (v1 : Fin (k + 1) → ℤ) : Fin (k + 1) → Fin 1 → ℤ := fun i => ![v1 i]

/-- At `r = 1` the rank-`r` gap is the rank-1 gap at the single
parameter `t 0`. -/
theorem mgap_col (v1 : Fin (k + 1) → ℤ) (t : Fin 1 → ℝ) :
    mgap (col v1) t = gap v1 (t 0) := by
  unfold mgap gap col
  congr 1
  funext i
  congr 1
  rw [Fin.sum_univ_one]
  simp

theorem mML_col (v1 : Fin (k + 1) → ℤ) : mML (col v1) = ML v1 := by
  unfold mML ML
  congr 1
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t 0, (mgap_col v1 t).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ => s, by rw [mgap_col]⟩

/-- **Coherence:** the rank-`r` D-value of the one-column matrix is the
two-runner D-value of the vector. The `r = 1` framework is the original. -/
theorem mD_col (v1 : Fin (k + 1) → ℤ) : mD (col v1) = D v1 := by
  unfold mD D
  rw [mML_col]

end LRSpectrumFull
