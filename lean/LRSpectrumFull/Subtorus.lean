/-
# Milestone 12: rank-r subtori and the δ₂ threshold (the higher-dim ambient)

So far a runner system was a *vector* `Fin (k+1) → ℤ` — a **rank-1**
object with one time parameter. The paper's results (`δ₂(4) ≤ 3/14`,
`2/7 ∉ S₁(4)`) live one level up, on **rank-r subtori**: a system is a
*matrix* `v : Fin (k+1) → Fin r → ℤ` whose runner `i` moves on the
`r`-parameter family `∑ⱼ vᵢⱼ · tⱼ` as `t` ranges over `ℝʳ`.

We lift the whole tower to this setting:

* `mgap v t = minᵢ ‖∑ⱼ vᵢⱼ·tⱼ‖`  (instantaneous loneliness at `t ∈ ℝʳ`)
* `mML v = sup_{t ∈ ℝʳ} mgap v t`  (maximum loneliness, a conditional sup)
* `mD v = 1/2 − mML v`              (the rank-r D-value)
* `delta2 k = ⨅ over rank-2 subtori, mD`   (the `δ₂` threshold)

and prove the framework bounds `mD v ∈ [0, 1/2]` and `δ₂ ∈ [0, 1/2]`.
The `r = 1` case is the existing `gap`/`ML`/`D`. This is the ambient
object the paper's `δ₂(4) ≤ 3/14` sharpens; that sharp bound needs the
JK24 normal form and is a separate, much larger effort. No `sorry`.
-/

import LRSpectrumFull.DValue
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace LRSpectrumFull

variable {k r : ℕ}

/-- Instantaneous loneliness of a rank-`r` subtorus at parameters
`t : Fin r → ℝ`: the minimum over runners of `‖∑ⱼ vᵢⱼ·tⱼ‖`. -/
noncomputable def mgap (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => nearestIntDist (∑ j, (v i j : ℝ) * t j))

theorem mgap_nonneg (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) : 0 ≤ mgap v t := by
  simp only [mgap, Finset.le_inf'_iff]
  intro i _
  exact nearestIntDist_nonneg _

theorem mgap_le_half (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) : mgap v t ≤ 1 / 2 := by
  simp only [mgap, Finset.inf'_le_iff]
  exact ⟨0, Finset.mem_univ _, nearestIntDist_le_half _⟩

/-- A common lower bound on every runner's distance lower-bounds the gap. -/
theorem le_mgap (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) (c : ℝ)
    (h : ∀ i, c ≤ nearestIntDist (∑ j, (v i j : ℝ) * t j)) : c ≤ mgap v t := by
  simp only [mgap, Finset.le_inf'_iff]
  intro i _
  exact h i

/-- Maximum loneliness of a rank-`r` subtorus: the supremum over all
parameters `t ∈ ℝʳ`. A conditional supremum in ℝ. -/
noncomputable def mML (v : Fin (k + 1) → Fin r → ℤ) : ℝ :=
  sSup (Set.range (mgap v))

theorem bddAbove_range_mgap (v : Fin (k + 1) → Fin r → ℤ) :
    BddAbove (Set.range (mgap v)) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨t, rfl⟩
  exact mgap_le_half v t

theorem mML_le_half (v : Fin (k + 1) → Fin r → ℤ) : mML v ≤ 1 / 2 := by
  unfold mML
  apply csSup_le (Set.range_nonempty (mgap v))
  rintro y ⟨t, rfl⟩
  exact mgap_le_half v t

theorem mML_nonneg (v : Fin (k + 1) → Fin r → ℤ) : 0 ≤ mML v := by
  unfold mML
  exact (mgap_nonneg v 0).trans (le_csSup (bddAbove_range_mgap v) ⟨0, rfl⟩)

/-- The rank-`r` D-value `mD v = 1/2 − mML v`. -/
noncomputable def mD (v : Fin (k + 1) → Fin r → ℤ) : ℝ := 1 / 2 - mML v

theorem mD_nonneg (v : Fin (k + 1) → Fin r → ℤ) : 0 ≤ mD v := by
  have := mML_le_half v; simp only [mD]; linarith

theorem mD_le_half (v : Fin (k + 1) → Fin r → ℤ) : mD v ≤ 1 / 2 := by
  have := mML_nonneg v; simp only [mD]; linarith

/-- Instantaneous loneliness at any `t` lower-bounds `mML`. -/
theorem mgap_le_mML (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) : mgap v t ≤ mML v :=
  le_csSup (bddAbove_range_mgap v) ⟨t, rfl⟩

/-- **Sampling principle (rank-`r`).** Evaluating the gap at any single
parameter `t ∈ ℝʳ` certifies the upper bound `mD v ≤ 1/2 − mgap v t`. -/
theorem mD_le_of_mgap (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) :
    mD v ≤ 1 / 2 - mgap v t := by
  have := mgap_le_mML v t; simp only [mD]; linarith

/-! ## The naive infimum threshold is degenerate

One might define a "δ₂" as the infimum of `mD` over *all* rank-2
subtori. We show this naive object equals `0` — so it is **not** the
paper's spectral threshold. The reason: the rank-2 subtorus with every
runner of speed `(1, 0)` passes through the deep hole `1/2` (at the
parameter `(1/2, 0)`), giving `mML = 1/2`, hence `mD = 0`.

The paper's genuine `δ₂(n)` instead is a **supremum** of D-values over
**saturated** (primitive, rank-exactly-2) subtori within the spectral
band below `1/4` — `δ₂(4) ≤ 3/14` means `S₂(4) ∩ (3/14, 1/4) = ∅`. That
is a strictly harder object (it needs the saturation restriction and the
JK24 normal-form classification) and is **not** proved here. -/

/-- The infimum of `mD` over all rank-2 subtori on `k+1` coordinates.
(NOT the paper's `δ₂` — see `delta2_eq_zero`.) -/
noncomputable def delta2 (k : ℕ) : ℝ := ⨅ v : Fin (k + 1) → Fin 2 → ℤ, mD v

theorem delta2_nonneg (k : ℕ) : 0 ≤ delta2 k :=
  le_ciInf (fun v => mD_nonneg v)

/-- `delta2` is at most the D-value of any specific rank-2 subtorus. -/
theorem delta2_le (k : ℕ) (v : Fin (k + 1) → Fin 2 → ℤ) : delta2 k ≤ mD v :=
  ciInf_le ⟨0, by rintro y ⟨w, rfl⟩; exact mD_nonneg w⟩ v

/-- **The naive infimum threshold is degenerate: `delta2 k = 0`.**
Witnessed by the all-`(1,0)` subtorus reaching the deep hole `1/2`. This
is precisely why the paper's `δ₂` restricts to *saturated* subtori. -/
theorem delta2_eq_zero (k : ℕ) : delta2 k = 0 := by
  refine le_antisymm ?_ (delta2_nonneg k)
  have hge : (1 / 2 : ℝ) ≤ mML (fun (_ : Fin (k + 1)) => ![(1 : ℤ), 0]) := by
    refine le_trans ?_ (mgap_le_mML _ (![1 / 2, 0] : Fin 2 → ℝ))
    apply le_mgap
    intro i
    have e : (∑ j : Fin 2,
        (((fun (_ : Fin (k + 1)) => ![(1 : ℤ), 0]) i j : ℝ)) * (![1 / 2, 0] : Fin 2 → ℝ) j)
        = 1 / 2 := by
      simp [Fin.sum_univ_two]
    rw [e]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hwit : mD (fun (_ : Fin (k + 1)) => ![(1 : ℤ), 0]) = 0 := by
    have hle := mML_le_half (fun (_ : Fin (k + 1)) => ![(1 : ℤ), 0])
    simp only [mD]; linarith
  calc delta2 k ≤ mD (fun (_ : Fin (k + 1)) => ![(1 : ℤ), 0]) := delta2_le k _
    _ = 0 := hwit

end LRSpectrumFull
