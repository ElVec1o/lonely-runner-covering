/-
# The far-indicator square wave and its exact antiperiodicity

The elementary proof of the odd-relation bound rests on a `±1` square wave
`sq x = +1` iff runner `x` is far (`fract x ∈ [1/4, 3/4)`). The half-open
interval makes the antiperiodic identity **exact** (no a.e.):

    sq (x + 1/2) = − sq x ,      sq (x + 1) = sq x .

These drive the shift `t ↦ t + 1/(2 g_S)` that forces the correlation integrals
`I_S` to vanish. We use the clean characterization `far x ⟺ ⌊2x − 1/2⌋ even`,
under which `x ↦ x + 1/2` bumps the floor by exactly `1` (parity flips) and
`x ↦ x + 1` bumps it by `2` (parity preserved). `sq_far` connects farness to the
loneliness lower bound `‖x‖ ≥ 1/4`. No `sorry`.
-/
import LRSpectrumFull.NearestInteger
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

namespace LRSpectrumFull

/-- The `±1` far-indicator square wave: `+1` when `⌊2x − 1/2⌋` is even
(equivalently `fract x ∈ [1/4, 3/4)`, i.e. runner `x` is far), `−1` otherwise. -/
noncomputable def sq (x : ℝ) : ℝ := if Even ⌊2 * x - 1 / 2⌋ then 1 else -1

/-- **Exact antiperiodicity:** shifting by `1/2` flips the sign. (`⌊2(x+½)−½⌋ =
⌊2x−½⌋ + 1`, so the parity flips.) -/
theorem sq_add_half (x : ℝ) : sq (x + 1 / 2) = - sq x := by
  unfold sq
  rw [show 2 * (x + 1 / 2) - 1 / 2 = (2 * x - 1 / 2) + 1 by ring, Int.floor_add_one]
  by_cases h : Even ⌊2 * x - 1 / 2⌋
  · have h1 : ¬ Even (⌊2 * x - 1 / 2⌋ + 1) := by rw [Int.even_add_one]; exact not_not.mpr h
    rw [if_neg h1, if_pos h]
  · have h1 : Even (⌊2 * x - 1 / 2⌋ + 1) := by rw [Int.even_add_one]; exact h
    rw [if_pos h1, if_neg h]; norm_num

/-- **Period 1:** `sq` depends only on `x` mod `1`. (`⌊2(x+1)−½⌋ = ⌊2x−½⌋ + 2`,
parity preserved.) -/
theorem sq_periodic : Function.Periodic sq 1 := by
  intro x
  unfold sq
  rw [show 2 * (x + 1) - 1 / 2 = (2 * x - 1 / 2) + ((2 : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast]
  by_cases h : Even ⌊2 * x - 1 / 2⌋
  · rw [if_pos h, if_pos (h.add even_two)]
  · rw [if_neg h, if_neg (fun hc => h (by simpa using hc.sub even_two))]

/-- **Farness ⟹ loneliness bound.** If `sq x = 1` then `‖x‖ ≥ 1/4`. -/
theorem sq_far {x : ℝ} (h : sq x = 1) : (1 : ℝ) / 4 ≤ nearestIntDist x := by
  have he : Even ⌊2 * x - 1 / 2⌋ := by
    by_contra hc; unfold sq at h; rw [if_neg hc] at h; norm_num at h
  -- decompose the floor over the integer part of x
  have hdecomp : ⌊2 * x - 1 / 2⌋ = ⌊2 * Int.fract x - 1 / 2⌋ + 2 * ⌊x⌋ := by
    rw [show 2 * x - 1 / 2 = (2 * Int.fract x - 1 / 2) + ((2 * ⌊x⌋ : ℤ) : ℝ) by
      rw [Int.fract]; push_cast; ring, Int.floor_add_intCast]
  -- the local floor ⌊2·fract−1/2⌋ lies in {−1,0,1}; even ⟹ 0
  have hb1 : (-1 : ℤ) ≤ ⌊2 * Int.fract x - 1 / 2⌋ := by
    apply Int.le_floor.mpr; push_cast; have := Int.fract_nonneg x; linarith
  have hb2 : ⌊2 * Int.fract x - 1 / 2⌋ < 2 := by
    apply Int.floor_lt.mpr; push_cast; have := Int.fract_lt_one x; linarith
  have hev2 : ⌊2 * Int.fract x - 1 / 2⌋ % 2 = 0 := by
    have := Int.even_iff.mp he; rw [hdecomp] at this; omega
  have hz : ⌊2 * Int.fract x - 1 / 2⌋ = 0 := by omega
  rw [Int.floor_eq_zero_iff, Set.mem_Ico] at hz
  unfold nearestIntDist
  obtain ⟨hlo, hhi⟩ := hz
  refine le_min ?_ ?_
  · linarith [hlo, hhi]
  · linarith [hlo, hhi]

end LRSpectrumFull
