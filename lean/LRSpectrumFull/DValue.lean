/-
# Milestone 4: the D-value and the sampling principle

The view-obstruction **D-value** of a speed vector is
`D(v) = 1/2 − ML(v)`, where `ML` is the maximum loneliness from
`MaxLoneliness.lean`. The Lonely-Runner / view-obstruction *spectrum*
`S₁(n)` is precisely the set of D-values realized by `n`-runner systems,
so `D` is the central quantity of the whole project.

This file:

* defines `D` and derives `D v ∈ [0, 1/2]` directly from `ML_bounds`;
* proves the **sampling principle** `D v ≤ 1/2 − gap v t` for every
  single time `t` — i.e. evaluating the instantaneous gap at any one
  time certifies an *upper* bound on the D-value.

The sampling principle is the formal heart of the computer-assisted
spectrum verifications in the papers: the Rust/Python sweeps evaluate
`gap` on a fine grid of times and speeds to certify that no D-value
lands in a forbidden interval. Here that logic is mechanized: a single
gap evaluation is a sound upper bound on `D`. No `sorry`.
-/

import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull

variable {k : ℕ}

/-- The view-obstruction D-value `D(v) = 1/2 − ML(v)`. -/
noncomputable def D (v : Fin (k + 1) → ℤ) : ℝ := 1 / 2 - ML v

/-- `0 ≤ D v`, since `ML v ≤ 1/2`. -/
theorem D_nonneg (v : Fin (k + 1) → ℤ) : 0 ≤ D v := by
  have := ML_le_half v
  simp only [D]; linarith

/-- `D v ≤ 1/2`, since `0 ≤ ML v`. -/
theorem D_le_half (v : Fin (k + 1) → ℤ) : D v ≤ 1 / 2 := by
  have := ML_nonneg v
  simp only [D]; linarith

/-- `D v ∈ [0, 1/2]`. -/
theorem D_bounds (v : Fin (k + 1) → ℤ) : 0 ≤ D v ∧ D v ≤ 1 / 2 :=
  ⟨D_nonneg v, D_le_half v⟩

/-- The instantaneous gap at any time `t` is a lower bound for the
maximum loneliness `ML v` (it lies in the range whose `sSup` is `ML`). -/
theorem gap_le_ML (v : Fin (k + 1) → ℤ) (t : ℝ) : gap v t ≤ ML v :=
  le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩

/-- **Sampling principle.** Evaluating the instantaneous gap at any
single time `t` certifies the upper bound `D v ≤ 1/2 − gap v t`.

This is the formal core of the sweep-based spectrum verification: a
single gap evaluation soundly bounds the D-value from above. -/
theorem D_le_of_gap (v : Fin (k + 1) → ℤ) (t : ℝ) : D v ≤ 1 / 2 - gap v t := by
  have := gap_le_ML v t
  simp only [D]; linarith

end LRSpectrumFull
