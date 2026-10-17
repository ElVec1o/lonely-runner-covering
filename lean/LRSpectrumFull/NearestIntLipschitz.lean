/-
# Toward Piece A: `nearestIntDist` is 1-Lipschitz

The coordinate bound `D(p,q,r) ≥ 3/14 ⟹ max ≤ 6` rests on a continuity
argument: the gap is Lipschitz in the parameter, so a high peak persists on
an interval. The base case is that `nearestIntDist` itself is 1-Lipschitz.
This file proves it (and the helper that the distance is realized by an
integer). No `sorry`.
-/

import LRSpectrumFull.NearestInteger

namespace LRSpectrumFull

/-- `nearestIntDist y` is realized by an actual integer: `‖y‖ = |y - n|`. -/
theorem nearestIntDist_eq_abs (y : ℝ) : ∃ n : ℤ, nearestIntDist y = |y - n| := by
  unfold nearestIntDist
  rcases le_total (Int.fract y) (1 - Int.fract y) with h | h
  · refine ⟨⌊y⌋, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by have := Int.fract_nonneg y; rw [Int.fract] at this; linarith)]
    rw [Int.fract]
  · refine ⟨⌊y⌋ + 1, ?_⟩
    rw [min_eq_right h]
    have hlt : Int.fract y < 1 := Int.fract_lt_one y
    rw [abs_of_nonpos (by rw [Int.fract] at hlt; push_cast; linarith)]
    rw [Int.fract]; push_cast; ring

/-- **`nearestIntDist` is 1-Lipschitz.** `| ‖x‖ − ‖y‖ | ≤ |x − y|`. The
foundational continuity brick for the n=3 coordinate bound. -/
theorem nearestIntDist_lipschitz (x y : ℝ) :
    |nearestIntDist x - nearestIntDist y| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨n, hn⟩ := nearestIntDist_eq_abs y
    have h1 : nearestIntDist x ≤ |x - n| := nearestIntDist_le_dist x n
    have h2 : |x - (n : ℝ)| ≤ |x - y| + |y - n| := abs_sub_le x y (n : ℝ)
    rw [← hn] at h2
    linarith
  · obtain ⟨n, hn⟩ := nearestIntDist_eq_abs x
    have h1 : nearestIntDist y ≤ |y - n| := nearestIntDist_le_dist y n
    have h2 : |y - (n : ℝ)| ≤ |y - x| + |x - n| := abs_sub_le y x (n : ℝ)
    rw [← hn] at h2
    rw [abs_sub_comm y x] at h2
    linarith

end LRSpectrumFull
