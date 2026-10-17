/-
# Milestone 13: a worked rank-2 subtorus — `mD(realizer) ≤ 3/14`

We exhibit the explicit non-product rank-2 subtorus of `(ℝ/ℤ)⁴` from the
companion paper,

    L = ⟨ (1, 1, −2, −6), (1, −1, 0, −2) ⟩  ⊂ ℤ⁴,

and prove `mD L ≤ 3/14` from the geometric definition by **sampling at
one point** `(s,u) = (3/14, 1/2)`. This is the concrete computation that
the value `3/14` is realized by an actual rank-2 subtorus (consistent
with `3/14 ∈ S₂(4)` in the paper).

**Honest scope.** This does *not* establish the paper's `δ₂(4) ≤ 3/14`.
That bound is the statement `S₂(4) ∩ (3/14, 1/4) = ∅` over *saturated*
subtori — a supremum/classification result needing the JK24 normal form,
not proved here. (Our `delta2` infimum is degenerate — `= 0`, see
`delta2_eq_zero` — so `delta2_le … mD_Lrz_le` is a true but trivial
upper bound, recorded only for completeness.)

At parameters `(s, u) = (3/14, 1/2)` the four coordinates are
`s+u = 5/7`, `s−u = −2/7`, `−2s = −3/7`, `−6s−2u = −16/7`, whose
nearest-integer distances are `2/7, 2/7, 3/7, 2/7` — all `≥ 2/7`. So the
gap there is `≥ 2/7`, giving `ML ≥ 2/7` and `mD = 1/2 − ML ≤ 3/14`.

(`delta2` here is the infimum over *all* rank-2 subtori, so this is a
sound upper bound; the paper's `δ₂` over *saturated* subtori equals
`3/14`. Proving the matching lower bound — that no subtorus does better —
is the multi-week JK24-normal-form classification.) No `sorry`.
-/

import LRSpectrumFull.Subtorus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- The paper's `3/14` realizer `⟨(1,1,−2,−6),(1,−1,0,−2)⟩` as a runner
matrix `Fin 4 → Fin 2 → ℤ`: runner `i` has speed-pair `(aᵢ, bᵢ)`. -/
def Lrz : Fin 4 → Fin 2 → ℤ :=
  ![![1, 1], ![1, -1], ![-2, 0], ![-6, -2]]

/-- The witness parameters `(s, u) = (3/14, 1/2)`. -/
noncomputable def trz : Fin 2 → ℝ := ![3 / 14, 1 / 2]

/-- At `(3/14, 1/2)` every runner of the realizer is at distance `≥ 2/7`
from the integers, so the gap is `≥ 2/7`. -/
theorem mgap_Lrz_ge : (2 / 7 : ℝ) ≤ mgap Lrz trz := by
  apply le_mgap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lrz 0 j : ℝ) * trz j))
    have e : (∑ j : Fin 2, ((Lrz 0 j : ℝ) * trz j)) = 5 / 7 := by
      -- targeted `norm_num` (not broad `simp`) — the default simp simproc set crashes
      -- (`Lean.Expr.appArg!` PANIC) on these matrix/`Fin` subterms inside `fin_cases`.
      norm_num [Lrz, trz, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
    rw [e]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lrz 1 j : ℝ) * trz j))
    have e : (∑ j : Fin 2, ((Lrz 1 j : ℝ) * trz j)) = 5 / 7 + ((-1 : ℤ) : ℝ) := by
      -- targeted `norm_num` (not broad `simp`) — the default simp simproc set crashes
      -- (`Lean.Expr.appArg!` PANIC) on these matrix/`Fin` subterms inside `fin_cases`.
      norm_num [Lrz, trz, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lrz 2 j : ℝ) * trz j))
    have e : (∑ j : Fin 2, ((Lrz 2 j : ℝ) * trz j)) = 4 / 7 + ((-1 : ℤ) : ℝ) := by
      -- targeted `norm_num` (not broad `simp`) — the default simp simproc set crashes
      -- (`Lean.Expr.appArg!` PANIC) on these matrix/`Fin` subterms inside `fin_cases`.
      norm_num [Lrz, trz, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j : Fin 2, ((Lrz 3 j : ℝ) * trz j))
    have e : (∑ j : Fin 2, ((Lrz 3 j : ℝ) * trz j)) = 5 / 7 + ((-3 : ℤ) : ℝ) := by
      -- targeted `norm_num` (not broad `simp`) — the default simp simproc set crashes
      -- (`Lean.Expr.appArg!` PANIC) on these matrix/`Fin` subterms inside `fin_cases`.
      norm_num [Lrz, trz, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The realizer's rank-2 D-value is at most `3/14`. -/
theorem mD_Lrz_le : mD Lrz ≤ 3 / 14 := by
  have := mD_le_of_mgap Lrz trz
  have hg := mgap_Lrz_ge
  linarith

/-- A true but **trivial** corollary (since `delta2 = 0`): the naive
infimum threshold is `≤ 3/14`. NOT the paper's `δ₂(4) ≤ 3/14`, which is a
supremum/classification statement over saturated subtori (not proved
here). The real content is `mD_Lrz_le`: the value `3/14` is realized. -/
theorem delta2_le_three_fourteenths : delta2 3 ≤ 3 / 14 :=
  le_trans (delta2_le 3 Lrz) mD_Lrz_le

end LRSpectrumFull
