/-
# Milestone 2: distance to the nearest integer

The atom of the entire Lonely-Runner / view-obstruction theory is the
function `‖x‖ = dist(x, ℤ)`, the distance from a real `x` to the nearest
integer. Maximum loneliness `ML(v) = sup_t min_i ‖v_i t‖` and the
D-value `D(v) = 1/2 − ML(v)` are both built directly on it.

We define `nearestIntDist x := min (Int.fract x) (1 - Int.fract x)`
(equivalently `min over n∈ℤ of |x − n|`, using that the fractional part
already reduces to `[0,1)`), and prove its three defining properties:

* `nearestIntDist_nonneg`  — `0 ≤ ‖x‖`
* `nearestIntDist_le_half` — `‖x‖ ≤ 1/2`   (the global maximum)
* `nearestIntDist_intCast` — `‖(n : ℝ)‖ = 0` for integer `n`

These are fully proven (no `sorry`) and form the base layer for the
future formalization of `ML` and the D-value.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

namespace LRSpectrumFull

open Int

/-- Distance from `x : ℝ` to the nearest integer, `‖x‖ ∈ [0, 1/2]`. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- `‖x‖ ≥ 0`. -/
theorem nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := by
  unfold nearestIntDist
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  exact le_min h0 (by linarith)

/-- `‖x‖ ≤ 1/2`: the nearest-integer distance never exceeds one half. -/
theorem nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  unfold nearestIntDist
  rcases le_total (Int.fract x) (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- The nearest-integer distance of an integer is `0`. -/
theorem nearestIntDist_intCast (n : ℤ) : nearestIntDist (n : ℝ) = 0 := by
  have h : Int.fract ((n : ℤ) : ℝ) = 0 := Int.fract_intCast n
  unfold nearestIntDist
  rw [h, sub_zero]
  exact min_eq_left zero_le_one

/-- Consequently `‖x‖ ∈ [0, 1/2]` always; recorded as a paired bound
(without the `Set.Icc` wrapper, to keep imports minimal). -/
theorem nearestIntDist_bounds (x : ℝ) :
    0 ≤ nearestIntDist x ∧ nearestIntDist x ≤ 1 / 2 :=
  ⟨nearestIntDist_nonneg x, nearestIntDist_le_half x⟩

/-- Evaluation lower bound: for `x ∈ [0, 1)` (so that `fract x = x`),
a value `c ≤ x` and `c ≤ 1 − x` is a lower bound for `‖x‖`. The
computational tool for certifying concrete D-value bounds. -/
theorem nearestIntDist_ge {x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (h0 : c ≤ x) (h1 : c ≤ 1 - x) : c ≤ nearestIntDist x := by
  have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0, hx1⟩
  simp only [nearestIntDist, hf]
  exact le_min h0 h1

/-- `‖·‖` is invariant under integer shifts (it depends only on `fract`). -/
theorem nearestIntDist_add_int (x : ℝ) (k : ℤ) :
    nearestIntDist (x + k) = nearestIntDist x := by
  simp only [nearestIntDist, Int.fract_add_intCast]

/-- `‖·‖` is even: `‖-x‖ = ‖x‖`. -/
theorem nearestIntDist_neg (x : ℝ) : nearestIntDist (-x) = nearestIntDist x := by
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · have hx : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have h2 := Int.floor_add_fract x; rw [h, add_zero] at h2; exact h2.symm
    rw [hx, show -((⌊x⌋ : ℤ) : ℝ) = (((-⌊x⌋ : ℤ)) : ℝ) by push_cast; ring,
      nearestIntDist_intCast, nearestIntDist_intCast]
  · simp only [nearestIntDist, Int.fract_neg h]
    rw [show (1 : ℝ) - (1 - Int.fract x) = Int.fract x by ring, min_comm]

/-- `‖x‖` is at most the distance from `x` to **any** integer `n`
(it is the distance to the *nearest* one). The structural tool behind
the general two-runner bound. -/
theorem nearestIntDist_le_dist (x : ℝ) (n : ℤ) : nearestIntDist x ≤ |x - n| := by
  have hx : x - (n : ℝ) = Int.fract x - ((n - ⌊x⌋ : ℤ) : ℝ) := by
    push_cast; linarith [Int.floor_add_fract x]
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  simp only [nearestIntDist]
  rw [hx]
  rcases le_or_gt (n - ⌊x⌋) 0 with hkle | hkgt
  · have hk : ((n - ⌊x⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hkle
    rw [abs_of_nonneg (by linarith)]
    calc min (Int.fract x) (1 - Int.fract x) ≤ Int.fract x := min_le_left _ _
      _ ≤ Int.fract x - ((n - ⌊x⌋ : ℤ) : ℝ) := by linarith
  · have hk : (1 : ℝ) ≤ ((n - ⌊x⌋ : ℤ) : ℝ) := by
      have h1' : (1 : ℤ) ≤ n - ⌊x⌋ := by omega
      exact_mod_cast h1'
    rw [abs_of_nonpos (by linarith)]
    calc min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
      _ ≤ -(Int.fract x - ((n - ⌊x⌋ : ℤ) : ℝ)) := by linarith

/-- **Bad-set characterization** (Bedert §4, sub-lemma B connect).  At the grid point `a/Q`,
being within `δ` of an integer is a modular condition: the residue `a mod Q` lies within `δQ` of
`0` or of `Q`.  This turns each bad set `{j : ‖v_i j/Q‖ < δ}` into a residue interval — the first
step in reindexing its Fourier coefficient (via the coprime bijection `j ↦ v_i j mod Q`) to a
partial exponential sum, where `exp_partial_sum_bound` applies. -/
theorem nearestIntDist_div_lt_iff (a : ℤ) (Q : ℕ) (hQ : 0 < Q) (δ : ℝ) :
    nearestIntDist ((a : ℝ) / Q) < δ
      ↔ min ((a % Q : ℤ) : ℝ) ((Q : ℝ) - ((a % Q : ℤ) : ℝ)) < δ * Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hfract : Int.fract ((a : ℝ) / Q) = ((a % Q : ℤ) : ℝ) / Q :=
    Int.fract_div_intCast_eq_div_intCast_mod
  unfold nearestIntDist
  rw [hfract, show (1 : ℝ) - ((a % Q : ℤ) : ℝ) / Q = ((Q : ℝ) - ((a % Q : ℤ) : ℝ)) / Q by
    field_simp, min_lt_iff, min_lt_iff, div_lt_iff₀ hQR, div_lt_iff₀ hQR]

end LRSpectrumFull

#print axioms LRSpectrumFull.nearestIntDist_div_lt_iff
