/-
# Milestone 3: maximum loneliness as a conditional supremum

Building on the nearest-integer-distance atom `‖·‖` of
`NearestInteger.lean`, we define, for a vector of integer speeds
`v : Fin (k+1) → ℤ` (the `+1` guarantees at least one runner):

* `gap v t = min over runners of ‖v_i · t‖` — the instantaneous
  loneliness at time `t` (a `Finset.inf'` over `Fin (k+1)`);
* `ML v = sSup_t gap v t` — the **maximum loneliness**, as a
  conditional supremum over all `t : ℝ`.

`ML` is the quantity from which the D-value `D(v) = 1/2 − ML(v)` of the
view-obstruction spectrum is defined. We prove the two facts that make
`ML` well-defined as a `sSup`:

* `gap` is bounded in `[0, 1/2]` (so the range is bounded above), and
* `ML v ∈ [0, 1/2]`.

The supremum is genuinely conditional (ℝ is only a conditionally
complete lattice), so boundedness is what makes `sSup` meaningful — this
is exactly what is established here. No `sorry`.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import LRSpectrumFull.NearestInteger

namespace LRSpectrumFull

variable {k : ℕ}

/-- Instantaneous loneliness at time `t`: the minimum over the `k+1`
runners of the nearest-integer distance `‖v_i · t‖`. -/
noncomputable def gap (v : Fin (k + 1) → ℤ) (t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => nearestIntDist ((v i : ℝ) * t))

/-- `gap` is nonnegative: a minimum of nonnegative terms. -/
theorem gap_nonneg (v : Fin (k + 1) → ℤ) (t : ℝ) : 0 ≤ gap v t := by
  simp only [gap, Finset.le_inf'_iff]
  intro i _
  exact nearestIntDist_nonneg _

/-- `gap ≤ 1/2`: the minimum is at most any single runner's distance,
which is `≤ 1/2`. -/
theorem gap_le_half (v : Fin (k + 1) → ℤ) (t : ℝ) : gap v t ≤ 1 / 2 := by
  simp only [gap, Finset.inf'_le_iff]
  exact ⟨0, Finset.mem_univ _, nearestIntDist_le_half _⟩

/-- The gap is at most any single runner's nearest-integer distance. -/
theorem gap_le (v : Fin (k + 1) → ℤ) (t : ℝ) (i : Fin (k + 1)) :
    gap v t ≤ nearestIntDist ((v i : ℝ) * t) := by
  simp only [gap]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- A common lower bound for every runner's distance is a lower bound for
the gap (since the gap is their minimum). The dual of `gap_le_half`. -/
theorem le_gap (v : Fin (k + 1) → ℤ) (t : ℝ) (c : ℝ)
    (h : ∀ i, c ≤ nearestIntDist ((v i : ℝ) * t)) : c ≤ gap v t := by
  simp only [gap, Finset.le_inf'_iff]
  intro i _
  exact h i

/-- **Maximum loneliness** of the speed vector `v`: the supremum over all
`t : ℝ` of the instantaneous loneliness. A conditional supremum in ℝ. -/
noncomputable def ML (v : Fin (k + 1) → ℤ) : ℝ :=
  sSup (Set.range (gap v))

/-- The range of `gap v` is bounded above by `1/2`; this is what makes
the conditional supremum `ML v` well-defined. -/
theorem bddAbove_range_gap (v : Fin (k + 1) → ℤ) :
    BddAbove (Set.range (gap v)) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨t, rfl⟩
  exact gap_le_half v t

/-- `ML v ≤ 1/2`. -/
theorem ML_le_half (v : Fin (k + 1) → ℤ) : ML v ≤ 1 / 2 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v))
  rintro y ⟨t, rfl⟩
  exact gap_le_half v t

/-- `0 ≤ ML v`: witnessed by `gap v 0 ≥ 0` sitting inside the range. -/
theorem ML_nonneg (v : Fin (k + 1) → ℤ) : 0 ≤ ML v := by
  unfold ML
  exact (gap_nonneg v 0).trans (le_csSup (bddAbove_range_gap v) ⟨0, rfl⟩)

/-- `ML v ∈ [0, 1/2]`, recorded as a paired bound. -/
theorem ML_bounds (v : Fin (k + 1) → ℤ) : 0 ≤ ML v ∧ ML v ≤ 1 / 2 :=
  ⟨ML_nonneg v, ML_le_half v⟩

end LRSpectrumFull
