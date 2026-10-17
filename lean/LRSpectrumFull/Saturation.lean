/-
# Milestone 20: the saturation predicate (toward the paper's δ₂)

The paper's `δ₂(n)` ranges over **saturated** (primitive) rank-2 subtori
of `ℤⁿ`. A rank-2 sublattice spanned by the two columns of
`v : Fin n → Fin 2 → ℤ` is saturated iff it equals its `ℚ`-saturation,
which holds **iff the gcd of all its `2×2` minors is `1`**. We define this
predicate and classify the realizer of Milestone 13 against its
saturation.

* The realizer `⟨(1,1,−2,−6),(1,−1,0,−2)⟩` is **not** saturated — its
  minors have gcd `2` (it is an index-2 sublattice of its saturation).
* Its saturation `⟨(1,0,−1,−4),(1,−1,0,−2)⟩` (with `(1,0,−1,−4) =
  (a+b)/2`) **is** saturated — one of its minors is `−1`.

Both span the same real plane, hence the same subtorus. No `sorry`.
-/

import LRSpectrumFull.Delta2Example
import Mathlib.Algebra.GCDMonoid.Finset

namespace LRSpectrumFull

/-- A rank-2 integer matrix is **saturated** (its column lattice is
primitive) iff the gcd of all its `2×2` minors equals `1`. -/
def Saturated2 {n : ℕ} (v : Fin n → Fin 2 → ℤ) : Prop :=
  Finset.gcd (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 0 * v p.2 1 - v p.1 1 * v p.2 0) = 1

/-- The saturation of the Milestone-13 realizer: the same real plane,
spanned by `(1,0,−1,−4) = (a+b)/2` and `b = (1,−1,0,−2)`. -/
def Lsat : Fin 4 → Fin 2 → ℤ :=
  ![![1, 1], ![0, -1], ![-1, 0], ![-4, -2]]

/-- The realizer `Lrz` is **not** saturated (minor-gcd `= 2`, an index-2
sublattice). -/
theorem Lrz_not_saturated : ¬ Saturated2 Lrz := by
  unfold Saturated2 Lrz
  decide

/-- Its saturation `Lsat` **is** saturated (a minor is `−1`). -/
theorem Lsat_saturated : Saturated2 Lsat := by
  unfold Saturated2 Lsat
  decide

/-! ## The saturated realizer also has `mD ≤ 3/14`

At `(t,s) = (3/7, 2/7)` the four coordinates of `Lsat` are again
`5/7, −2/7, −3/7, −16/7`, so `mgap ≥ 2/7` and `mD ≤ 3/14`. Thus a
*genuinely saturated* rank-2 subtorus realizes `3/14`. -/

/-- The witness `(t, s) = (3/7, 2/7)` for the saturated basis. -/
noncomputable def tsat : Fin 2 → ℝ := ![3 / 7, 2 / 7]

theorem mgap_Lsat_ge : (2 / 7 : ℝ) ≤ mgap Lsat tsat := by
  apply le_mgap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lsat 0 j : ℝ) * tsat j))
    have e : (∑ j : Fin 2, ((Lsat 0 j : ℝ) * tsat j)) = 5 / 7 := by
      norm_num [Lsat, tsat, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [e]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lsat 1 j : ℝ) * tsat j))
    have e : (∑ j : Fin 2, ((Lsat 1 j : ℝ) * tsat j)) = 5 / 7 + ((-1 : ℤ) : ℝ) := by
      norm_num [Lsat, tsat, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lsat 2 j : ℝ) * tsat j))
    have e : (∑ j : Fin 2, ((Lsat 2 j : ℝ) * tsat j)) = 4 / 7 + ((-1 : ℤ) : ℝ) := by
      norm_num [Lsat, tsat, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lsat 3 j : ℝ) * tsat j))
    have e : (∑ j : Fin 2, ((Lsat 3 j : ℝ) * tsat j)) = 5 / 7 + ((-3 : ℤ) : ℝ) := by
      norm_num [Lsat, tsat, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The saturated realizer's rank-2 D-value is at most `3/14`. -/
theorem mD_Lsat_le : mD Lsat ≤ 3 / 14 := by
  have := mD_le_of_mgap Lsat tsat
  have hg := mgap_Lsat_ge
  linarith

/-! ## The correctly-scoped `δ₂` threshold

Following the paper, `δ₂` is the **supremum** of D-values of **saturated**
rank-2 subtori lying in the spectral band below `1/4`. We record its
honest framework bounds — `δ₂ ∈ [0, 1/4]` and `δ₂ ≥ mD(Lsat)` (the
saturated realizer is a member). The sharp `δ₂(4) = 3/14` additionally
needs the *exact* value `mD(Lsat) = 3/14` (a 2-parameter sup-attainment)
and the JK24 classification that nothing in `(3/14, 1/4)` is realized —
both open. -/

/-- The set of D-values of saturated rank-2 subtori on `k+1` coordinates
lying below `1/4`. -/
def satBandSet (k : ℕ) : Set ℝ :=
  {x : ℝ | ∃ v : Fin (k + 1) → Fin 2 → ℤ, Saturated2 v ∧ mD v = x ∧ x < 1 / 4}

theorem satBandSet_bddAbove (k : ℕ) : BddAbove (satBandSet k) :=
  ⟨1 / 4, by rintro x ⟨v, -, -, hlt⟩; exact le_of_lt hlt⟩

/-- `Lsat`'s D-value is a member of the band set (saturated, and `< 1/4`). -/
theorem mD_Lsat_mem : mD Lsat ∈ satBandSet 3 :=
  ⟨Lsat, Lsat_saturated, rfl, by have := mD_Lsat_le; norm_num; linarith⟩

/-- The paper's threshold `δ₂(n)`: supremum of the saturated band set. -/
noncomputable def delta2sat (k : ℕ) : ℝ := sSup (satBandSet k)

/-- `δ₂` is at least the D-value of the saturated realizer `Lsat`. -/
theorem delta2sat_ge_Lsat : mD Lsat ≤ delta2sat 3 :=
  le_csSup (satBandSet_bddAbove 3) mD_Lsat_mem

/-- `0 ≤ δ₂(4)`. -/
theorem delta2sat_nonneg : 0 ≤ delta2sat 3 :=
  le_trans (mD_nonneg Lsat) delta2sat_ge_Lsat

/-- `δ₂(4) ≤ 1/4` — the band bound. -/
theorem delta2sat_le_quarter : delta2sat 3 ≤ 1 / 4 := by
  apply csSup_le ⟨mD Lsat, mD_Lsat_mem⟩
  rintro x ⟨v, -, -, hlt⟩
  exact le_of_lt hlt

end LRSpectrumFull
