/-
# The four-runner window is closed

`five_runners` (the machine-checked Barajas–Serra Prime Filtering theorem at
`p = 5`) discharges the classical four-runner residuals of the separation
architecture outright: `WindowFour`, `FourMultiResidual`, and — since it needs
no hypothesis whatsoever on the family — every four-runner rung the program
had left as a citation.  The separation reduction accordingly loses its
`WindowFour` hypothesis (`separationSF_of_dense`).
-/
import LRSpectrumFull.Delta2FiveRunners
import LRSpectrumFull.Delta2DisjointTriples

namespace LRSpectrumFull

/-- **Every positive four-runner family is `1/5`-lonely** — the `ML` form of
`five_runners`, with no freeness, distinctness, or relation hypothesis.  The
witness time of the Prime Filtering multiplier is a member of the `gap` range,
and `ML` is its supremum. -/
theorem ML_ge_fifth_four (v : Fin 4 → ℤ) (hv : ∀ i, 0 < v i) : 1 / (5 : ℝ) ≤ ML v := by
  obtain ⟨t, _, ht⟩ := five_runners (fun i => (v i).toNat) (fun i => by
    show 0 < (v i).toNat
    have := hv i
    omega)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℝ) = (v i : ℝ) := by
    intro i
    rw [show (((v i).toNat : ℕ) : ℝ) = ((((v i).toNat : ℕ) : ℤ) : ℝ) from
      (Int.cast_natCast _).symm, Int.toNat_of_nonneg (le_of_lt (hv i))]
  have hgap : (1 : ℝ) / 5 ≤ gap v t := by
    refine le_gap v t _ (fun i => ?_)
    have := ht i
    rwa [hcast i] at this
  exact le_trans hgap (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- **The four-runner window: proved, not cited.** -/
theorem windowFour_holds : WindowFour := fun v hv _ => ML_ge_fifth_four v hv

/-- **The four-runner multi-relation residual: proved.** -/
theorem fourMultiResidual_holds : FourMultiResidual :=
  fun v hv _ _ _ => ML_ge_fifth_four v hv

/-- **Separation from the dense-torsion residual alone.**  The free side of the
all-`N` program no longer carries the classical four-runner window: after the
A-free, single-torsion, and multi-torsion floor theorems and `five_runners`,
the dense torsion shard is the only remaining hypothesis. -/
theorem separationSF_of_dense (h2 : DenseTorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_four_and_dense windowFour_holds h2

end LRSpectrumFull
