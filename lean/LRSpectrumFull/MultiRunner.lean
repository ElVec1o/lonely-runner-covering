/-
# Milestone 11: multi-runner monotonicity (foundation for the n-runner spectra)

The `gap`/`ML`/`D` tower is already defined for an arbitrary number of
runners `v : Fin (k+1) → ℤ`. This file records the structural fact that
ties the spectra at different `n` together:

**Adding runners can only increase the D-value** (equivalently, only
decreases maximum loneliness). Formally, for any reindexing
`ι : Fin (k+1) → Fin (m+1)` (selecting a sub-collection of the runners
of `v`):

    gap v t ≤ gap (v ∘ ι) t,    ML v ≤ ML (v ∘ ι),    D (v ∘ ι) ≤ D v.

This is the monotonicity behind the Lonely Runner Conjecture's structure:
a larger runner system is "more crowded", so its loneliness gap is
smaller. It is the entry point to the higher-`n` view-obstruction
spectra `S₁(n)` and the `δ₂(n)` thresholds studied in the papers.
No `sorry`.
-/

import LRSpectrumFull.DValue

namespace LRSpectrumFull

variable {k m : ℕ}

/-- The gap of the full system is at most the gap of any sub-collection
(more runners ⇒ smaller minimum). -/
theorem gap_comp_le (v : Fin (m + 1) → ℤ) (ι : Fin (k + 1) → Fin (m + 1)) (t : ℝ) :
    gap v t ≤ gap (v ∘ ι) t := by
  apply le_gap
  intro i
  exact gap_le v t (ι i)

/-- Maximum loneliness is antitone under adding runners:
`ML v ≤ ML (v ∘ ι)`. -/
theorem ML_comp_le (v : Fin (m + 1) → ℤ) (ι : Fin (k + 1) → Fin (m + 1)) :
    ML v ≤ ML (v ∘ ι) := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v))
  rintro y ⟨t, rfl⟩
  exact le_trans (gap_comp_le v ι t) (le_csSup (bddAbove_range_gap (v ∘ ι)) ⟨t, rfl⟩)

/-- The D-value is monotone under adding runners: a sub-collection has a
D-value at most that of the full system, `D (v ∘ ι) ≤ D v`. -/
theorem D_comp_le (v : Fin (m + 1) → ℤ) (ι : Fin (k + 1) → Fin (m + 1)) :
    D (v ∘ ι) ≤ D v := by
  have := ML_comp_le v ι
  simp only [D]; linarith

end LRSpectrumFull
