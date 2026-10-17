/-
# Milestone 31: the cascade `mD(U) ≤ D(generator)` (paper §3 backbone)

The backbone of the `δ₂(4)` classification (paper_DELTA2 §3, Prop 2.1) is
the **cascade**: a 1-dim subtorus `⟨w⟩ ⊂ U` has `D(⟨w⟩) ≥ D(U)`, i.e.

    mD U ≤ D (column j of U),

obtained by restricting the other parameter(s) to `0`. For Case A the two
generators `u = (a,a,b,c)`, `v = (d,−d,e,f)` have no zero coordinates, so
this transfers directly: `mD U ≥ 3/14` forces `D(⟨u⟩) ≥ 3/14` and
`D(⟨v⟩) ≥ 3/14`, which (by the `L₃` classification) bounds all
coordinates by `6`. This file proves the cascade. No `sorry`.
-/

import LRSpectrumFull.Subtorus

namespace LRSpectrumFull

variable {k r : ℕ}

/-- Setting all parameters except `j0` to `0`, the rank-`r` gap restricts
to the 1-dim gap of column `j0`. -/
theorem gap_eq_mgap_single (M : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r) (s : ℝ) :
    gap (fun i => M i j0) s = mgap M (Function.update (0 : Fin r → ℝ) j0 s) := by
  unfold gap mgap
  congr 1
  funext i
  congr 1
  rw [Finset.sum_eq_single j0
    (fun l _ hl => by rw [Function.update_of_ne hl]; simp)
    (fun h0 => absurd (Finset.mem_univ j0) h0)]
  rw [Function.update_self]

/-- **The cascade.** The rank-2 (rank-`r`) D-value is at most the
1-dim D-value of any generator column. -/
theorem mD_le_col (M : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r) :
    mD M ≤ D (fun i => M i j0) := by
  have hML : ML (fun i => M i j0) ≤ mML M := by
    unfold ML
    apply csSup_le (Set.range_nonempty (gap (fun i => M i j0)))
    rintro y ⟨s, rfl⟩
    rw [gap_eq_mgap_single]
    exact mgap_le_mML M _
  simp only [mD, D]
  linarith

/-- **Cascade exclusion.** If a generator column has 1-dim D-value `≤ c`,
then `mD U ≤ c`. With `c = 3/14`: a subtorus with a "small" generator is
automatically outside the band — so the only candidates for the band have
*both* generators with `D > 3/14`, which (by the `L₃` classification of
`S₁(3)`) is a strong finite constraint. This is the entry point of the
paper's §3 case analysis. -/
theorem mD_le_of_col_le (M : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r) {c : ℝ}
    (h : D (fun i => M i j0) ≤ c) : mD M ≤ c :=
  le_trans (mD_le_col M j0) h

end LRSpectrumFull
