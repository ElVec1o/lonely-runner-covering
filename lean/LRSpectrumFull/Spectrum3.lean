/-
# Milestone 32: the n=3 spectrum, started — `D((1,2,3)) = 1/4`

The `L₃` classification (paper_DELTA2 Prop 2.2) that the cascade feeds into
needs the *n=3* view-obstruction D-values. Unlike `n=2` (closed form
`1/(2(p+q))`), these have no simple formula and need the same
sup-attainment technique as the two-runner upper bounds (M22).

We begin at the **top of `S₁(3)`**: the triple `(1,2,3)` has the maximal
D-value `1/4`. We prove `ML((1,2,3)) ≤ 1/4` (every time, at least one of
`t, 2t, 3t` is within `1/4` of an integer) by fractional-part case
analysis using only `nearestIntDist_le_dist`, and combine with the
witness `t = 1/4` to get `D((1,2,3)) = 1/4` exactly. No `sorry`.
-/

import LRSpectrumFull.DValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- The speed vector `(1, 2, 3)` as `Fin 3 → ℤ`. -/
def v123 : Fin 3 → ℤ := ![1, 2, 3]

@[simp] theorem v123_2 : v123 2 = 3 := by decide

/-- **Core 3-runner fact:** for `a ∈ [0,1)`, if `‖a‖ > 1/4` and
`‖2a‖ > 1/4` then `‖3a‖ ≤ 1/4`. -/
theorem core123 (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (h1 : 1 / 4 < nearestIntDist a) (h2 : 1 / 4 < nearestIntDist (2 * a)) :
    nearestIntDist (3 * a) ≤ 1 / 4 := by
  have hfa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha0, ha1⟩
  simp only [nearestIntDist, hfa, lt_min_iff] at h1
  obtain ⟨ha14, ha34⟩ := h1
  have hb2 : 1 / 4 < |2 * a - ((1 : ℤ) : ℝ)| :=
    lt_of_lt_of_le h2 (nearestIntDist_le_dist (2 * a) 1)
  push_cast at hb2
  rcases lt_abs.mp hb2 with hgt | hlt
  · -- 2a - 1 > 1/4 ⟹ a > 5/8 ; then 3a within 1/4 of 2
    refine le_trans (nearestIntDist_le_dist (3 * a) 2) ?_
    have h2c : ((2 : ℤ) : ℝ) = 2 := by norm_num
    rw [h2c, abs_le]
    constructor <;> linarith
  · -- 1 - 2a > 1/4 ⟹ a < 3/8 ; then 3a within 1/4 of 1
    refine le_trans (nearestIntDist_le_dist (3 * a) 1) ?_
    have h1c : ((1 : ℤ) : ℝ) = 1 := by norm_num
    rw [h1c, abs_le]
    constructor <;> linarith

/-- Reduce `‖c·t‖` to `‖c·fract t‖` for a real coefficient `c` arising as
a small literal. -/
private theorem nid_lit_fract (c : ℝ) (m : ℤ) (hc : c = (m : ℝ)) (t : ℝ) :
    nearestIntDist (c * t) = nearestIntDist (c * Int.fract t) := by
  subst hc
  conv_lhs => rw [← Int.fract_add_floor t]
  rw [show (m : ℝ) * (Int.fract t + (⌊t⌋ : ℝ)) = (m : ℝ) * Int.fract t + ((m * ⌊t⌋ : ℤ) : ℝ) by
      push_cast; ring, nearestIntDist_add_int]

/-- Witness: `gap (1,2,3) (1/4) ≥ 1/4` (so `ML ≥ 1/4`). -/
theorem gap_v123_ge : (1 / 4 : ℝ) ≤ gap v123 (1 / 4) := by
  apply le_gap
  intro i
  fin_cases i
  · show (1 / 4 : ℝ) ≤ nearestIntDist ((v123 0 : ℝ) * (1 / 4))
    have e : ((v123 0 : ℝ)) * (1 / 4) = 1 / 4 := by norm_num [v123]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (1 / 4 : ℝ) ≤ nearestIntDist ((v123 1 : ℝ) * (1 / 4))
    have e : ((v123 1 : ℝ)) * (1 / 4) = 1 / 2 := by norm_num [v123]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (1 / 4 : ℝ) ≤ nearestIntDist ((v123 2 : ℝ) * (1 / 4))
    have e : ((v123 2 : ℝ)) * (1 / 4) = 3 / 4 := by rw [v123_2]; norm_num
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Hard direction:** `ML((1,2,3)) ≤ 1/4`. -/
theorem ML_v123_le : ML v123 ≤ 1 / 4 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v123))
  rintro y ⟨t, rfl⟩
  by_contra hcon
  rw [not_le] at hcon
  have hr0 : nearestIntDist ((v123 0 : ℝ) * t) = nearestIntDist (Int.fract t) := by
    have hv : (v123 0 : ℝ) = 1 := by norm_num [v123]
    rw [hv, one_mul]
    conv_lhs => rw [← Int.fract_add_floor t]
    rw [nearestIntDist_add_int]
  have hr1 : nearestIntDist ((v123 1 : ℝ) * t) = nearestIntDist (2 * Int.fract t) :=
    nid_lit_fract _ 2 (by norm_num [v123]) t
  have hr2 : nearestIntDist ((v123 2 : ℝ) * t) = nearestIntDist (3 * Int.fract t) :=
    nid_lit_fract _ 3 (by rw [v123_2]) t
  have h0 : 1 / 4 < nearestIntDist (Int.fract t) := by
    rw [← hr0]; exact lt_of_lt_of_le hcon (gap_le v123 t 0)
  have h1 : 1 / 4 < nearestIntDist (2 * Int.fract t) := by
    rw [← hr1]; exact lt_of_lt_of_le hcon (gap_le v123 t 1)
  have h3 : 1 / 4 < nearestIntDist (3 * Int.fract t) := by
    rw [← hr2]; exact lt_of_lt_of_le hcon (gap_le v123 t 2)
  exact absurd (core123 (Int.fract t) (Int.fract_nonneg t) (Int.fract_lt_one t) h0 h1)
    (not_le.mpr h3)

/-- **`D((1,2,3)) = 1/4`** — the maximum of `S₁(3)`. -/
theorem D_v123_eq : D v123 = 1 / 4 := by
  have hle : D v123 ≤ 1 / 4 := by
    have := le_trans gap_v123_ge (gap_le_ML v123 (1 / 4)); simp only [D]; linarith
  have hge : (1 / 4 : ℝ) ≤ D v123 := by
    have := ML_v123_le; simp only [D]; linarith
  linarith

/-! ### The first `3/14` value: `D((1,2,6)) = 3/14`

`ML = 2/7`, attained at `t = 2/7`. Same two-subinterval structure as
`(1,2,3)`: `‖a‖ > 2/7` pins `a ∈ (2/7, 5/7)`, then `‖2a‖ > 2/7` splits it,
and in each piece `‖6a‖ ≤ 2/7` (with `6a` near `2` resp. `4`). -/

/-- The speed vector `(1, 2, 6)` as `Fin 3 → ℤ`. -/
def v126 : Fin 3 → ℤ := ![1, 2, 6]

@[simp] theorem v126_2 : v126 2 = 6 := by decide

/-- **Core fact for `(1,2,6)`:** for `a ∈ [0,1)`, if `‖a‖ > 2/7` and
`‖2a‖ > 2/7` then `‖6a‖ ≤ 2/7`. -/
theorem core126 (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (h1 : 2 / 7 < nearestIntDist a) (h2 : 2 / 7 < nearestIntDist (2 * a)) :
    nearestIntDist (6 * a) ≤ 2 / 7 := by
  have hfa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha0, ha1⟩
  simp only [nearestIntDist, hfa, lt_min_iff] at h1
  obtain ⟨ha27, ha57⟩ := h1
  have hb2 : 2 / 7 < |2 * a - ((1 : ℤ) : ℝ)| :=
    lt_of_lt_of_le h2 (nearestIntDist_le_dist (2 * a) 1)
  push_cast at hb2
  rcases lt_abs.mp hb2 with hgt | hlt
  · -- 2a - 1 > 2/7 ⟹ a > 9/14 ; then 6a within 2/7 of 4
    refine le_trans (nearestIntDist_le_dist (6 * a) 4) ?_
    have hc : ((4 : ℤ) : ℝ) = 4 := by norm_num
    rw [hc, abs_le]; constructor <;> linarith
  · -- 1 - 2a > 2/7 ⟹ a < 5/14 ; then 6a within 2/7 of 2
    refine le_trans (nearestIntDist_le_dist (6 * a) 2) ?_
    have hc : ((2 : ℤ) : ℝ) = 2 := by norm_num
    rw [hc, abs_le]; constructor <;> linarith

/-- Witness: `gap (1,2,6) (2/7) ≥ 2/7` (so `ML ≥ 2/7`). -/
theorem gap_v126_ge : (2 / 7 : ℝ) ≤ gap v126 (2 / 7) := by
  apply le_gap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v126 0 : ℝ) * (2 / 7))
    have e : ((v126 0 : ℝ)) * (2 / 7) = 2 / 7 := by norm_num [v126]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v126 1 : ℝ) * (2 / 7))
    have e : ((v126 1 : ℝ)) * (2 / 7) = 4 / 7 := by norm_num [v126]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v126 2 : ℝ) * (2 / 7))
    have e : ((v126 2 : ℝ)) * (2 / 7) = 5 / 7 + ((1 : ℤ) : ℝ) := by rw [v126_2]; norm_num
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Hard direction:** `ML((1,2,6)) ≤ 2/7`. -/
theorem ML_v126_le : ML v126 ≤ 2 / 7 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v126))
  rintro y ⟨t, rfl⟩
  by_contra hcon
  rw [not_le] at hcon
  have hr0 : nearestIntDist ((v126 0 : ℝ) * t) = nearestIntDist (Int.fract t) := by
    have hv : (v126 0 : ℝ) = 1 := by norm_num [v126]
    rw [hv, one_mul]
    conv_lhs => rw [← Int.fract_add_floor t]
    rw [nearestIntDist_add_int]
  have hr1 : nearestIntDist ((v126 1 : ℝ) * t) = nearestIntDist (2 * Int.fract t) :=
    nid_lit_fract _ 2 (by norm_num [v126]) t
  have hr2 : nearestIntDist ((v126 2 : ℝ) * t) = nearestIntDist (6 * Int.fract t) :=
    nid_lit_fract _ 6 (by rw [v126_2]) t
  have h0 : 2 / 7 < nearestIntDist (Int.fract t) := by
    rw [← hr0]; exact lt_of_lt_of_le hcon (gap_le v126 t 0)
  have h1 : 2 / 7 < nearestIntDist (2 * Int.fract t) := by
    rw [← hr1]; exact lt_of_lt_of_le hcon (gap_le v126 t 1)
  have h6 : 2 / 7 < nearestIntDist (6 * Int.fract t) := by
    rw [← hr2]; exact lt_of_lt_of_le hcon (gap_le v126 t 2)
  exact absurd (core126 (Int.fract t) (Int.fract_nonneg t) (Int.fract_lt_one t) h0 h1)
    (not_le.mpr h6)

/-- **`D((1,2,6)) = 3/14`** — the threshold value of the `δ₂(4)` band,
realized in `S₁(3)`. -/
theorem D_v126_eq : D v126 = 3 / 14 := by
  have hle : D v126 ≤ 3 / 14 := by
    have := le_trans gap_v126_ge (gap_le_ML v126 (2 / 7)); simp only [D]; linarith
  have hge : (3 / 14 : ℝ) ≤ D v126 := by
    have := ML_v126_le; simp only [D]; linarith
  linarith

/-! ### `D((1,3,4)) = 3/14`

No clean two-subinterval split: `‖3a‖` and `‖4a‖` each cross two nearest
integers over `a ∈ (2/7, 5/7)`. We instead partition `(2/7, 5/7)` into
three pieces and exhibit, in each, one runner within `2/7` of an integer:

* `a ∈ (2/7, 3/7]`  ⟹  `‖3a‖ ≤ 2/7` (`3a` near `1`)
* `a ∈ (3/7, 4/7]`  ⟹  `‖4a‖ ≤ 2/7` (`4a` near `2`)
* `a ∈ (4/7, 5/7]`  ⟹  `‖3a‖ ≤ 2/7` (`3a` near `2`)

with the complementary region `‖a‖ ≤ 2/7` for `a ∉ (2/7, 5/7)`. Witness
`t = 3/7`. -/

/-- The speed vector `(1, 3, 4)` as `Fin 3 → ℤ`. -/
def v134 : Fin 3 → ℤ := ![1, 3, 4]

@[simp] theorem v134_2 : v134 2 = 4 := by decide

/-- Witness: `gap (1,3,4) (3/7) ≥ 2/7`. -/
theorem gap_v134_ge : (2 / 7 : ℝ) ≤ gap v134 (3 / 7) := by
  apply le_gap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v134 0 : ℝ) * (3 / 7))
    have e : ((v134 0 : ℝ)) * (3 / 7) = 3 / 7 := by norm_num [v134]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v134 1 : ℝ) * (3 / 7))
    have e : ((v134 1 : ℝ)) * (3 / 7) = 2 / 7 + ((1 : ℤ) : ℝ) := by norm_num [v134]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v134 2 : ℝ) * (3 / 7))
    have e : ((v134 2 : ℝ)) * (3 / 7) = 5 / 7 + ((1 : ℤ) : ℝ) := by rw [v134_2]; norm_num
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Hard direction:** `ML((1,3,4)) ≤ 2/7`. -/
theorem ML_v134_le : ML v134 ≤ 2 / 7 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v134))
  rintro y ⟨t, rfl⟩
  have ha0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have ha1 : Int.fract t < 1 := Int.fract_lt_one t
  have R0 : gap v134 t ≤ nearestIntDist (Int.fract t) := by
    have key : nearestIntDist ((v134 0 : ℝ) * t) = nearestIntDist (Int.fract t) := by
      have hv : (v134 0 : ℝ) = 1 := by norm_num [v134]
      rw [hv, one_mul]
      conv_lhs => rw [← Int.fract_add_floor t]
      rw [nearestIntDist_add_int]
    rw [← key]; exact gap_le v134 t 0
  have R1 : gap v134 t ≤ nearestIntDist (3 * Int.fract t) := by
    have key : nearestIntDist ((v134 1 : ℝ) * t) = nearestIntDist (3 * Int.fract t) := by
      have hv : (v134 1 : ℝ) = 3 := by norm_num [v134]
      rw [hv]; exact nid_lit_fract 3 3 (by norm_num) t
    rw [← key]; exact gap_le v134 t 1
  have R2 : gap v134 t ≤ nearestIntDist (4 * Int.fract t) := by
    have key : nearestIntDist ((v134 2 : ℝ) * t) = nearestIntDist (4 * Int.fract t) := by
      have hv : (v134 2 : ℝ) = 4 := by rw [v134_2]; norm_num
      rw [hv]; exact nid_lit_fract 4 4 (by norm_num) t
    rw [← key]; exact gap_le v134 t 2
  set a := Int.fract t
  rcases le_or_gt a (2 / 7) with h | h1
  · exact le_trans R0 (by
      have hd := nearestIntDist_le_dist a 0
      rw [Int.cast_zero, sub_zero, abs_of_nonneg ha0] at hd; linarith)
  rcases le_or_gt a (5 / 7) with hmid | hhi
  · rcases le_or_gt a (3 / 7) with hA | hA'
    · refine le_trans R1 ?_
      have hd := nearestIntDist_le_dist (3 * a) 1
      rw [Int.cast_one] at hd
      have hb : |3 * a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
      linarith
    · rcases le_or_gt a (4 / 7) with hB | hB'
      · refine le_trans R2 ?_
        have hd := nearestIntDist_le_dist (4 * a) 2
        rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
        have hb : |4 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
        linarith
      · refine le_trans R1 ?_
        have hd := nearestIntDist_le_dist (3 * a) 2
        rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
        have hb : |3 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
        linarith
  · exact le_trans R0 (by
      have hd := nearestIntDist_le_dist a 1
      rw [Int.cast_one] at hd
      have hb : |a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
      linarith)

/-- **`D((1,3,4)) = 3/14`**. -/
theorem D_v134_eq : D v134 = 3 / 14 := by
  have hle : D v134 ≤ 3 / 14 := by
    have := le_trans gap_v134_ge (gap_le_ML v134 (3 / 7)); simp only [D]; linarith
  have hge : (3 / 14 : ℝ) ≤ D v134 := by
    have := ML_v134_le; simp only [D]; linarith
  linarith

/-! ### `D((1,5,6)) = 3/14`

Five alternating subintervals across `(2/7, 5/7)`; in each, `‖5a‖` or
`‖6a‖` stays within `2/7` of an integer. Breakpoints `8/21, 16/35, 23/42,
13/21`. Witness `t = 2/7`. -/

/-- The speed vector `(1, 5, 6)` as `Fin 3 → ℤ`. -/
def v156 : Fin 3 → ℤ := ![1, 5, 6]

@[simp] theorem v156_2 : v156 2 = 6 := by decide

/-- Witness: `gap (1,5,6) (2/7) ≥ 2/7`. -/
theorem gap_v156_ge : (2 / 7 : ℝ) ≤ gap v156 (2 / 7) := by
  apply le_gap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v156 0 : ℝ) * (2 / 7))
    have e : ((v156 0 : ℝ)) * (2 / 7) = 2 / 7 := by norm_num [v156]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v156 1 : ℝ) * (2 / 7))
    have e : ((v156 1 : ℝ)) * (2 / 7) = 3 / 7 + ((1 : ℤ) : ℝ) := by norm_num [v156]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v156 2 : ℝ) * (2 / 7))
    have e : ((v156 2 : ℝ)) * (2 / 7) = 5 / 7 + ((1 : ℤ) : ℝ) := by rw [v156_2]; norm_num
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Hard direction:** `ML((1,5,6)) ≤ 2/7`. -/
theorem ML_v156_le : ML v156 ≤ 2 / 7 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v156))
  rintro y ⟨t, rfl⟩
  have ha0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have ha1 : Int.fract t < 1 := Int.fract_lt_one t
  have R0 : gap v156 t ≤ nearestIntDist (Int.fract t) := by
    have key : nearestIntDist ((v156 0 : ℝ) * t) = nearestIntDist (Int.fract t) := by
      have hv : (v156 0 : ℝ) = 1 := by norm_num [v156]
      rw [hv, one_mul]
      conv_lhs => rw [← Int.fract_add_floor t]
      rw [nearestIntDist_add_int]
    rw [← key]; exact gap_le v156 t 0
  have R1 : gap v156 t ≤ nearestIntDist (5 * Int.fract t) := by
    have key : nearestIntDist ((v156 1 : ℝ) * t) = nearestIntDist (5 * Int.fract t) := by
      have hv : (v156 1 : ℝ) = 5 := by norm_num [v156]
      rw [hv]; exact nid_lit_fract 5 5 (by norm_num) t
    rw [← key]; exact gap_le v156 t 1
  have R2 : gap v156 t ≤ nearestIntDist (6 * Int.fract t) := by
    have key : nearestIntDist ((v156 2 : ℝ) * t) = nearestIntDist (6 * Int.fract t) := by
      have hv : (v156 2 : ℝ) = 6 := by rw [v156_2]; norm_num
      rw [hv]; exact nid_lit_fract 6 6 (by norm_num) t
    rw [← key]; exact gap_le v156 t 2
  set a := Int.fract t
  rcases le_or_gt a (2 / 7) with h | h1
  · exact le_trans R0 (by
      have hd := nearestIntDist_le_dist a 0
      rw [Int.cast_zero, sub_zero, abs_of_nonneg ha0] at hd; linarith)
  rcases le_or_gt a (5 / 7) with hmid | hhi
  · rcases le_or_gt a (8 / 21) with h2 | h2'
    · -- ‖6a‖ near 2
      refine le_trans R2 ?_
      have hd := nearestIntDist_le_dist (6 * a) 2
      rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
      have hb : |6 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
      linarith
    · rcases le_or_gt a (16 / 35) with h3 | h3'
      · -- ‖5a‖ near 2
        refine le_trans R1 ?_
        have hd := nearestIntDist_le_dist (5 * a) 2
        rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
        have hb : |5 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
        linarith
      · rcases le_or_gt a (23 / 42) with h4 | h4'
        · -- ‖6a‖ near 3
          refine le_trans R2 ?_
          have hd := nearestIntDist_le_dist (6 * a) 3
          rw [show ((3 : ℤ) : ℝ) = 3 by norm_num] at hd
          have hb : |6 * a - 3| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
          linarith
        · rcases le_or_gt a (13 / 21) with h5 | h5'
          · -- ‖5a‖ near 3
            refine le_trans R1 ?_
            have hd := nearestIntDist_le_dist (5 * a) 3
            rw [show ((3 : ℤ) : ℝ) = 3 by norm_num] at hd
            have hb : |5 * a - 3| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
            linarith
          · -- ‖6a‖ near 4
            refine le_trans R2 ?_
            have hd := nearestIntDist_le_dist (6 * a) 4
            rw [show ((4 : ℤ) : ℝ) = 4 by norm_num] at hd
            have hb : |6 * a - 4| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
            linarith
  · exact le_trans R0 (by
      have hd := nearestIntDist_le_dist a 1
      rw [Int.cast_one] at hd
      have hb : |a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
      linarith)

/-- **`D((1,5,6)) = 3/14`**. -/
theorem D_v156_eq : D v156 = 3 / 14 := by
  have hle : D v156 ≤ 3 / 14 := by
    have := le_trans gap_v156_ge (gap_le_ML v156 (2 / 7)); simp only [D]; linarith
  have hge : (3 / 14 : ℝ) ≤ D v156 := by
    have := ML_v156_le; simp only [D]; linarith
  linarith

/-! ### `D((2,3,5)) = 3/14` — the last `L₃` triple

This is the hardest: with no speed-`1` runner there is no `‖a‖` to pin the
fractional part, so we partition *all* of `[0,1)` into nine subintervals
(breakpoints `1/7, 9/35, 3/7, 16/35, 9/14, 23/35, 16/21, 6/7`) and in each
exhibit one of `‖2a‖, ‖3a‖, ‖5a‖` within `2/7` of an integer. Witness
`t = 1/7`. This closes `L₃ ⊆ { D ≥ 3/14 }`. -/

/-- The speed vector `(2, 3, 5)` as `Fin 3 → ℤ`. -/
def v235 : Fin 3 → ℤ := ![2, 3, 5]

@[simp] theorem v235_2 : v235 2 = 5 := by decide

/-- Witness: `gap (2,3,5) (1/7) ≥ 2/7`. -/
theorem gap_v235_ge : (2 / 7 : ℝ) ≤ gap v235 (1 / 7) := by
  apply le_gap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v235 0 : ℝ) * (1 / 7))
    have e : ((v235 0 : ℝ)) * (1 / 7) = 2 / 7 := by norm_num [v235]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v235 1 : ℝ) * (1 / 7))
    have e : ((v235 1 : ℝ)) * (1 / 7) = 3 / 7 := by norm_num [v235]
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((v235 2 : ℝ) * (1 / 7))
    have e : ((v235 2 : ℝ)) * (1 / 7) = 5 / 7 := by rw [v235_2]; norm_num
    rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Hard direction:** `ML((2,3,5)) ≤ 2/7`. -/
theorem ML_v235_le : ML v235 ≤ 2 / 7 := by
  unfold ML
  apply csSup_le (Set.range_nonempty (gap v235))
  rintro y ⟨t, rfl⟩
  have ha0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have ha1 : Int.fract t < 1 := Int.fract_lt_one t
  have R0 : gap v235 t ≤ nearestIntDist (2 * Int.fract t) := by
    have key : nearestIntDist ((v235 0 : ℝ) * t) = nearestIntDist (2 * Int.fract t) := by
      have hv : (v235 0 : ℝ) = 2 := by norm_num [v235]
      rw [hv]; exact nid_lit_fract 2 2 (by norm_num) t
    rw [← key]; exact gap_le v235 t 0
  have R1 : gap v235 t ≤ nearestIntDist (3 * Int.fract t) := by
    have key : nearestIntDist ((v235 1 : ℝ) * t) = nearestIntDist (3 * Int.fract t) := by
      have hv : (v235 1 : ℝ) = 3 := by norm_num [v235]
      rw [hv]; exact nid_lit_fract 3 3 (by norm_num) t
    rw [← key]; exact gap_le v235 t 1
  have R2 : gap v235 t ≤ nearestIntDist (5 * Int.fract t) := by
    have key : nearestIntDist ((v235 2 : ℝ) * t) = nearestIntDist (5 * Int.fract t) := by
      have hv : (v235 2 : ℝ) = 5 := by rw [v235_2]; norm_num
      rw [hv]; exact nid_lit_fract 5 5 (by norm_num) t
    rw [← key]; exact gap_le v235 t 2
  set a := Int.fract t
  rcases le_or_gt a (1 / 7) with c1 | c1
  · -- ‖2a‖ near 0
    refine le_trans R0 ?_
    have hd := nearestIntDist_le_dist (2 * a) 0
    rw [Int.cast_zero, sub_zero, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a)] at hd
    linarith
  rcases le_or_gt a (9 / 35) with c2 | c2
  · -- ‖5a‖ near 1
    refine le_trans R2 ?_
    have hd := nearestIntDist_le_dist (5 * a) 1
    rw [Int.cast_one] at hd
    have hb : |5 * a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (3 / 7) with c3 | c3
  · -- ‖3a‖ near 1
    refine le_trans R1 ?_
    have hd := nearestIntDist_le_dist (3 * a) 1
    rw [Int.cast_one] at hd
    have hb : |3 * a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (16 / 35) with c4 | c4
  · -- ‖5a‖ near 2
    refine le_trans R2 ?_
    have hd := nearestIntDist_le_dist (5 * a) 2
    rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
    have hb : |5 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (9 / 14) with c5 | c5
  · -- ‖2a‖ near 1
    refine le_trans R0 ?_
    have hd := nearestIntDist_le_dist (2 * a) 1
    rw [Int.cast_one] at hd
    have hb : |2 * a - 1| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (23 / 35) with c6 | c6
  · -- ‖5a‖ near 3
    refine le_trans R2 ?_
    have hd := nearestIntDist_le_dist (5 * a) 3
    rw [show ((3 : ℤ) : ℝ) = 3 by norm_num] at hd
    have hb : |5 * a - 3| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (16 / 21) with c7 | c7
  · -- ‖3a‖ near 2
    refine le_trans R1 ?_
    have hd := nearestIntDist_le_dist (3 * a) 2
    rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
    have hb : |3 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  rcases le_or_gt a (6 / 7) with c8 | c8
  · -- ‖5a‖ near 4
    refine le_trans R2 ?_
    have hd := nearestIntDist_le_dist (5 * a) 4
    rw [show ((4 : ℤ) : ℝ) = 4 by norm_num] at hd
    have hb : |5 * a - 4| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  · -- a > 6/7 : ‖2a‖ near 2
    refine le_trans R0 ?_
    have hd := nearestIntDist_le_dist (2 * a) 2
    rw [show ((2 : ℤ) : ℝ) = 2 by norm_num] at hd
    have hb : |2 * a - 2| ≤ 2 / 7 := by rw [abs_le]; constructor <;> linarith
    linarith

/-- **`D((2,3,5)) = 3/14`**. -/
theorem D_v235_eq : D v235 = 3 / 14 := by
  have hle : D v235 ≤ 3 / 14 := by
    have := le_trans gap_v235_ge (gap_le_ML v235 (1 / 7)); simp only [D]; linarith
  have hge : (3 / 14 : ℝ) ≤ D v235 := by
    have := ML_v235_le; simp only [D]; linarith
  linarith

/-! ### Converse direction: a general exclusion via the universal witness `t = 1/3`

The classification's converse asks: which triples have `D < 3/14`? This is
the number-theoretic half. Here is a clean, *fully general* slice: if none
of `p, q, r` is divisible by `3`, then at `t = 1/3` every runner satisfies
`‖(coord)/3‖ = 1/3`, so `ML ≥ 1/3` and `D ≤ 1/6 < 3/14`. This excludes an
entire infinite family at once — and correctly leaves `L₃` members such as
`(1,2,3)`, `(1,2,6)`, `(1,3,4)` (which all contain a multiple of `3`)
inside the band, consistent with M32. -/

/-- The speed vector `(p, q, r)`. -/
def vtriple (p q r : ℤ) : Fin 3 → ℤ := ![p, q, r]

@[simp] theorem vtriple_0 (p q r : ℤ) : vtriple p q r 0 = p := rfl
@[simp] theorem vtriple_1 (p q r : ℤ) : vtriple p q r 1 = q := rfl
@[simp] theorem vtriple_2 (p q r : ℤ) : vtriple p q r 2 = r := by
  simp [vtriple]

/-- For `3 ∤ n`, the speed `n` at `t = 1/3` is `1/3` from the nearest
integer. -/
theorem nearestIntDist_third (n : ℤ) (h : ¬ (3 ∣ n)) :
    nearestIntDist ((n : ℝ) * (1 / 3)) = 1 / 3 := by
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hr : (n : ℝ) = ((n % 3 : ℤ) : ℝ) + 3 * ((n / 3 : ℤ) : ℝ) := by
    have : (n % 3 : ℤ) + 3 * (n / 3 : ℤ) = n := Int.emod_add_mul_ediv n 3
    exact_mod_cast this.symm
  have hdecomp : (n : ℝ) * (1 / 3) = ((n % 3 : ℤ) : ℝ) * (1 / 3) + ((n / 3 : ℤ) : ℝ) := by
    rw [hr]; ring
  rw [hdecomp, nearestIntDist_add_int]
  rcases hmod with h1 | h2
  · rw [h1]
    have e : ((1 : ℤ) : ℝ) * (1 / 3) = 1 / 3 := by norm_num
    rw [e]
    have hf : Int.fract (1 / 3 : ℝ) = 1 / 3 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
    unfold nearestIntDist
    rw [hf, min_eq_left (by norm_num : (1 : ℝ) / 3 ≤ 1 - 1 / 3)]
  · rw [h2]
    have e : ((2 : ℤ) : ℝ) * (1 / 3) = 2 / 3 := by norm_num
    rw [e]
    have hf : Int.fract (2 / 3 : ℝ) = 2 / 3 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
    unfold nearestIntDist
    rw [hf, min_eq_right (by norm_num : (1 : ℝ) - 2 / 3 ≤ 2 / 3)]; norm_num

/-- **General exclusion.** If `3 ∤ p, q, r` then `D((p,q,r)) ≤ 1/6`, hence
`< 3/14`: such triples are never in the `δ₂(4)` band. -/
theorem D_le_sixth_of_not_three (p q r : ℤ)
    (hp : ¬ (3 ∣ p)) (hq : ¬ (3 ∣ q)) (hr : ¬ (3 ∣ r)) :
    D (vtriple p q r) ≤ 1 / 6 := by
  have hge : (1 / 3 : ℝ) ≤ gap (vtriple p q r) (1 / 3) := by
    apply le_gap
    intro i
    fin_cases i
    · show (1 / 3 : ℝ) ≤ nearestIntDist ((vtriple p q r 0 : ℝ) * (1 / 3))
      rw [show (vtriple p q r 0 : ℝ) = (p : ℝ) by simp]
      exact le_of_eq (nearestIntDist_third p hp).symm
    · show (1 / 3 : ℝ) ≤ nearestIntDist ((vtriple p q r 1 : ℝ) * (1 / 3))
      rw [show (vtriple p q r 1 : ℝ) = (q : ℝ) by simp]
      exact le_of_eq (nearestIntDist_third q hq).symm
    · show (1 / 3 : ℝ) ≤ nearestIntDist ((vtriple p q r 2 : ℝ) * (1 / 3))
      rw [show (vtriple p q r 2 : ℝ) = (r : ℝ) by simp]
      exact le_of_eq (nearestIntDist_third r hr).symm
  have := le_trans hge (gap_le_ML (vtriple p q r) (1 / 3))
  simp only [D]; linarith

/-- The exclusion is below the threshold: `3 ∤ p, q, r ⟹ D < 3/14`. -/
theorem D_lt_threshold_of_not_three (p q r : ℤ)
    (hp : ¬ (3 ∣ p)) (hq : ¬ (3 ∣ q)) (hr : ¬ (3 ∣ r)) :
    D (vtriple p q r) < 3 / 14 :=
  lt_of_le_of_lt (D_le_sixth_of_not_three p q r hp hq hr) (by norm_num)

/-! ### Reusable converse infrastructure: the modular-witness method

To chip away at the converse systematically we package the witness
argument. `D_lt_of_witness`: *any* `t` putting every runner past `2/7`
gives `D < 3/14`. `D_lt_of_residues`: the witness `t = 1/m` works whenever
each coordinate's residue mod `m` is "far from `0`" — the integer
condition `2m < 7·(n%m)` and `2m < 7·(m − n%m)` (i.e. `‖n/m‖ > 2/7`). With
this, each new excluded family is a one-line `omega` over residues. -/

variable {k : ℕ}

/-- Strict dual of `le_gap`: a common strict lower bound on every runner is
a strict lower bound on the gap. -/
theorem lt_gap (v : Fin (k + 1) → ℤ) (t : ℝ) (c : ℝ)
    (h : ∀ i, c < nearestIntDist ((v i : ℝ) * t)) : c < gap v t := by
  simp only [gap, Finset.lt_inf'_iff]
  intro i _
  exact h i

/-- **Reusable converse tool.** If some `t` puts every runner more than
`2/7` from an integer, then `D v < 3/14`. -/
theorem D_lt_of_witness (v : Fin (k + 1) → ℤ) (t : ℝ)
    (h : ∀ i, (2 / 7 : ℝ) < nearestIntDist ((v i : ℝ) * t)) : D v < 3 / 14 := by
  have hg : (2 / 7 : ℝ) < gap v t := lt_gap v t (2 / 7) h
  have := lt_of_lt_of_le hg (gap_le_ML v t)
  simp only [D]; linarith

/-- `‖n/m‖ > 2/7` from the residue inequalities `2m < 7(n%m)` and
`2m < 7(m − n%m)`. -/
theorem two_sevenths_lt_nearestIntDist_div (n m : ℤ) (hm : 0 < m)
    (h1 : 2 * m < 7 * (n % m)) (h2 : 2 * m < 7 * (m - n % m)) :
    (2 / 7 : ℝ) < nearestIntDist ((n : ℝ) * (1 / (m : ℝ))) := by
  have hmne : (m : ℤ) ≠ 0 := by omega
  have hs0 : 0 ≤ n % m := Int.emod_nonneg n hmne
  have hs1 : n % m < m := Int.emod_lt_of_pos n hm
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne' : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hdecomp : (n : ℝ) * (1 / (m : ℝ))
      = ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) + ((n / m : ℤ) : ℝ) := by
    have he : (n % m : ℤ) + m * (n / m) = n := Int.emod_add_mul_ediv n m
    have hc : (n : ℝ) = ((n % m : ℤ) : ℝ) + (m : ℝ) * ((n / m : ℤ) : ℝ) := by
      exact_mod_cast he.symm
    have hcast : ((n / m : ℤ) : ℝ) = ((n / m : ℤ) : ℝ) * ((m : ℝ) * (1 / (m : ℝ))) := by
      rw [mul_one_div, div_self hmne', mul_one]
    rw [hcast, hc]; ring
  rw [hdecomp, nearestIntDist_add_int]
  have hx0 : 0 ≤ ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) := by
    have : (0 : ℝ) ≤ ((n % m : ℤ) : ℝ) := by exact_mod_cast hs0
    positivity
  have hx1 : ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one hm']; exact_mod_cast hs1
  have hf : Int.fract (((n % m : ℤ) : ℝ) * (1 / (m : ℝ)))
      = ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) := Int.fract_eq_self.mpr ⟨hx0, hx1⟩
  unfold nearestIntDist
  rw [hf, mul_one_div, lt_min_iff]
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hm']
    have : (2 : ℝ) * m < 7 * ((n % m : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  · have hb : ((n % m : ℤ) : ℝ) / m < 5 / 7 := by
      rw [div_lt_iff₀ hm']
      have : (2 : ℝ) * m < 7 * ((m : ℝ) - ((n % m : ℤ) : ℝ)) := by exact_mod_cast h2
      linarith
    linarith

/-- **The modular-witness exclusion.** If there is a modulus `m` for which
every coordinate's residue is far from `0` (`2m < 7(v i % m)` and
`2m < 7(m − v i % m)`), then `D v < 3/14`. -/
theorem D_lt_of_residues (v : Fin (k + 1) → ℤ) (m : ℤ) (hm : 0 < m)
    (h : ∀ i, 2 * m < 7 * (v i % m) ∧ 2 * m < 7 * (m - v i % m)) : D v < 3 / 14 := by
  apply D_lt_of_witness v (1 / (m : ℝ))
  intro i
  exact two_sevenths_lt_nearestIntDist_div (v i) m hm (h i).1 (h i).2

/-- `3 ∤ p,q,r ⟹ D < 3/14`, re-derived through the modular method (`m=3`). -/
theorem D_lt_three (p q r : ℤ) (hp : ¬ 3 ∣ p) (hq : ¬ 3 ∣ q) (hr : ¬ 3 ∣ r) :
    D (vtriple p q r) < 3 / 14 := by
  apply D_lt_of_residues (vtriple p q r) 3 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 3 < 7 * (p % 3) ∧ 2 * 3 < 7 * (3 - p % 3); omega
  · show 2 * 3 < 7 * (q % 3) ∧ 2 * 3 < 7 * (3 - q % 3); omega
  · show 2 * 3 < 7 * (r % 3) ∧ 2 * 3 < 7 * (3 - r % 3); omega

/-- A family the `m=3` witness *cannot* reach: triples with every
coordinate `≡ 3` or `4 (mod 7)` have `D < 3/14`. For example `(3,4,10)`
(here `3 ≡ 0 mod 3`, so `D_lt_three` does not apply, but `3,4,10 ≡ 3,4,3
mod 7`). -/
theorem D_lt_seven (p q r : ℤ)
    (hp : p % 7 = 3 ∨ p % 7 = 4) (hq : q % 7 = 3 ∨ q % 7 = 4)
    (hr : r % 7 = 3 ∨ r % 7 = 4) : D (vtriple p q r) < 3 / 14 := by
  apply D_lt_of_residues (vtriple p q r) 7 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 7 < 7 * (p % 7) ∧ 2 * 7 < 7 * (7 - p % 7); omega
  · show 2 * 7 < 7 * (q % 7) ∧ 2 * 7 < 7 * (7 - q % 7); omega
  · show 2 * 7 < 7 * (r % 7) ∧ 2 * 7 < 7 * (7 - r % 7); omega

/-- Concrete instance the `mod 3` exclusion misses: `D((3,4,10)) < 3/14`. -/
example : D (vtriple 3 4 10) < 3 / 14 := D_lt_seven 3 4 10 (by omega) (by omega) (by omega)

end LRSpectrumFull
