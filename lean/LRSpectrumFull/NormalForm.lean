/-
# Milestone 28: the JK24 normal form (definition + Cusick–Pomerance cases)

The `δ₂(4)` classification reduces, via the `W(B₄)` symmetry (`mD_perm`,
`mD_sign_flip`), to subtori in the JK24 **normal form**

    u = (a, a, b, c),   v = (d, −d, e, f)

(the two generators / columns), with the case split A/B/C/D by which of
`b, c, e, f` vanish. We define this form and mechanize a *saturated
representative of each Cusick–Pomerance case* (B: `f=0`, C: `e=0`,
D: `b=0`), each shown to have `mD ≤ 3/14` — outside the forbidden band —
by sampling.

This is the **start** of the normal-form formalization: the structure is
defined and the degenerate-coordinate cases have representatives. The
*general* Cases B/C/D (the inhomogeneous Cusick–Pomerance reduction) and
the Case-A kernel-killer cascade remain the multi-week combinatorial core.
No `sorry`.
-/

import LRSpectrumFull.Saturation
import LRSpectrumFull.TwoRunnerBound
import LRSpectrumFull.SubtorusMono

namespace LRSpectrumFull

/-- The JK24 normal form: generators `u = (a,a,b,c)`, `v = (d,−d,e,f)`,
as a runner matrix `Fin 4 → Fin 2 → ℤ` (runner `i = (uᵢ, vᵢ)`). -/
def jkForm (a b c d e f : ℤ) : Fin 4 → Fin 2 → ℤ :=
  ![![a, d], ![a, -d], ![b, e], ![c, f]]

/-! ## Case B representative (`f = 0`): `⟨(1,1,1,1),(1,−1,2,0)⟩` -/

def caseB : Fin 4 → Fin 2 → ℤ := jkForm 1 1 1 1 2 0

theorem caseB_saturated : Saturated2 caseB := by
  unfold Saturated2 caseB jkForm; decide

theorem mD_caseB_le : mD caseB ≤ 3 / 14 := by
  rw [mD_const_col caseB 0 1 (by norm_num) (by decide)]; norm_num

/-! ## Case C representative (`e = 0`): `⟨(1,1,1,1),(1,−1,0,1)⟩` -/

def caseC : Fin 4 → Fin 2 → ℤ := jkForm 1 1 1 1 0 1

theorem caseC_saturated : Saturated2 caseC := by
  unfold Saturated2 caseC jkForm; decide

theorem mD_caseC_le : mD caseC ≤ 3 / 14 := by
  rw [mD_const_col caseC 0 1 (by norm_num) (by decide)]; norm_num

/-! ## Case D representative (`b = 0`): `⟨(1,1,0,1),(1,−1,1,1)⟩` -/

def caseD : Fin 4 → Fin 2 → ℤ := jkForm 1 0 1 1 1 1

theorem caseD_saturated : Saturated2 caseD := by
  unfold Saturated2 caseD jkForm; decide

theorem mD_caseD_le : mD caseD ≤ 3 / 14 := by
  have hg : (2 / 7 : ℝ) ≤ mgap caseD ![0, 1 / 2] := by
    apply le_mgap
    intro i
    fin_cases i
    · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((caseD 0 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j))
      have e : (∑ j : Fin 2, ((caseD 0 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j)) = 1 / 2 := by
        norm_num [caseD, jkForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((caseD 1 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j))
      have e : (∑ j : Fin 2, ((caseD 1 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j)) = 1 / 2 + ((-1 : ℤ) : ℝ) := by
        norm_num [caseD, jkForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [e, nearestIntDist_add_int]
      exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((caseD 2 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j))
      have e : (∑ j : Fin 2, ((caseD 2 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j)) = 1 / 2 := by
        norm_num [caseD, jkForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((caseD 3 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j))
      have e : (∑ j : Fin 2, ((caseD 3 j : ℝ) * (![0, 1 / 2] : Fin 2 → ℝ) j)) = 1 / 2 := by
        norm_num [caseD, jkForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [e]; exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := mD_le_of_mgap caseD ![0, 1 / 2]; linarith

end LRSpectrumFull
