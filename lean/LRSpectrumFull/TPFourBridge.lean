/-
# TP'(4), module M0: the runner predicate and the decomposition `t = (j + x) / 5`

`Good v s t` says that the runner of speed `v` and phase `s / 5` is at distance `≥ 1/5` from an integer at time `t`.
This is exactly the per-runner clause of `TPp 4` (threshold `1/(4+1)`).

* `tpDist_add_int`   : `tpDist` is invariant under integer shifts.
* `exists_near_of_not_good` : a bad runner has an integer within `1/5`.
* `good_mul5`        : Lemma 1(a) of the hand proof (HANDPROOF_v2 Sec. 1): a runner of speed `5 w` seen at
  time `(j + x) / 5` behaves as the runner of speed `w` at time `x`, for every natural `j`.
-/
import LRSpectrumFull.TPPrime

namespace LRSpectrumFull

/-- The runner of speed `v` and phase `s / 5` is good at time `t`. -/
def Good (v : ℕ) (s : ℤ) (t : ℝ) : Prop :=
  1 / 5 ≤ tpDist ((v : ℝ) * t + (s : ℝ) / 5)

lemma tpDist_add_int (x : ℝ) (k : ℤ) : tpDist (x + k) = tpDist x := by
  unfold tpDist
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

lemma exists_near_of_not_good {y : ℝ} (h : ¬ (1 / 5 : ℝ) ≤ tpDist y) :
    ∃ n : ℤ, |y - n| < 1 / 5 :=
  ⟨round y, by unfold tpDist at h; exact not_le.mp h⟩

/-- Lemma 1(a): a speed divisible by 5 sees only the offset `x`. -/
lemma good_mul5 (w : ℕ) (s : ℤ) (j : ℕ) (x : ℝ) :
    Good (5 * w) s (((j : ℝ) + x) / 5) ↔ Good w s x := by
  unfold Good
  have h : ((5 * w : ℕ) : ℝ) * (((j : ℝ) + x) / 5) + (s : ℝ) / 5
      = ((w : ℝ) * x + (s : ℝ) / 5) + ((w * j : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, tpDist_add_int]

end LRSpectrumFull
