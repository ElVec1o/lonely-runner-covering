/-
# The circle-method framework for the four-runner sharpening

The banked odd-relation bound (`exists_far_of_parity`) is a circle-method argument built on the far
indicator `sq` (`sq x = +1` iff `x` is in the middle band `[1/4, 3/4]`, i.e. the runner is far). Its
engine is the far-measure integral `∫₀¹ ∏ᵢ (sq(vᵢt) + 1)`: when it is positive, some time makes every
runner far, so `ML v ≥ 1/4`. The parity hypothesis was used *only* to compute that integral exactly
(`= 1`, all correlations vanish).

This file separates the two halves, giving the general framework:

* `exists_far_of_positive` — far-measure `> 0` ⟹ a far time exists (no parity hypothesis);
* `far_measure_expansion` — the far measure equals `1 + Σ_{∅ ≠ S} ∫₀¹ ∏_{i∈S} sq(vᵢt)` (the correlation
  sum), each odd-relation subset contributing `0` by `sqProd_integral_zero`;
* `ML_ge_quarter_of_correlations` — if the correlation sum exceeds `−1`, then `ML v ≥ 1/4`.

This reduces the four-runner sharpening (`no ±1 relation ⟹ ML ≥ 1/4`) to a concrete estimate: the
sum of the `2ⁿ − 1` sub-correlations is `> −1`. The absence of a `±1` relation is exactly what should
control that sum (the shortest correlations are the `±1` ones). The estimate itself is the remaining
research content; the framework here is its exact reduction.
-/
import LRSpectrumFull.OddRelationBound

namespace LRSpectrumFull

open MeasureTheory intervalIntegral

/-- **Far-measure positivity ⟹ a far time.** If the far-measure integral `∫₀¹ ∏ᵢ (sq(vᵢt) + 1)` is
positive, then some `t` places every runner at nearest-integer distance `≥ 1/4`. The second half of
`exists_far_of_parity`, freed of the parity hypothesis: positivity of a nonnegative integrand forces a
point where it is positive, hence every factor `sq(vᵢt) + 1 > 0`, i.e. every `sq(vᵢt) = 1` (far). -/
theorem exists_far_of_positive {n : ℕ} (v : Fin n → ℤ)
    (hInt : 0 < ∫ t in (0:ℝ)..1, ∏ i, (sq ((v i : ℝ) * t) + 1)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) := by
  have hex : ∃ t ∈ Set.uIcc (0:ℝ) 1, 0 < ∏ i, (sq ((v i : ℝ) * t) + 1) := by
    by_contra hcon
    push_neg at hcon
    have hle : 0 ≤ ∫ t in (0:ℝ)..1, -(∏ i, (sq ((v i : ℝ) * t) + 1)) := by
      refine intervalIntegral.integral_nonneg (by norm_num) (fun u hu => ?_)
      have hmem : u ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hu
      linarith [hcon u hmem]
    rw [intervalIntegral.integral_neg] at hle
    linarith [hInt]
  obtain ⟨t, _, hFt⟩ := hex
  refine ⟨t, fun i => ?_⟩
  have hfac : 0 < sq ((v i : ℝ) * t) + 1 := by
    by_contra hc
    push_neg at hc
    have hz : ∏ j, (sq ((v j : ℝ) * t) + 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i)
        (le_antisymm hc (by unfold sq; split <;> norm_num))
    linarith [hFt]
  have hsq1 : sq ((v i : ℝ) * t) = 1 := by
    have h2 : sq ((v i : ℝ) * t) = 1 ∨ sq ((v i : ℝ) * t) = -1 := by unfold sq; split <;> simp
    rcases h2 with h2 | h2
    · exact h2
    · rw [h2] at hfac; norm_num at hfac
  exact sq_far hsq1

/-- **The far-measure expansion.** `∫₀¹ ∏ᵢ (sq(vᵢt) + 1) = 1 + Σ_{∅ ≠ S ⊆ univ} ∫₀¹ ∏_{i∈S} sq(vᵢt)`:
expand the product over subsets, integrate termwise; the empty subset gives `1`. Each nonempty-subset
term is a sub-correlation, and (by `sqProd_integral_zero`) vanishes whenever that subset's scaled sum is
odd — so only the even-sum subsets survive. -/
theorem far_measure_expansion {n : ℕ} (v : Fin n → ℤ) :
    (∫ t in (0:ℝ)..1, ∏ i, (sq ((v i : ℝ) * t) + 1))
      = 1 + ∑ u ∈ (Finset.univ.powerset).erase ∅,
          (∫ t in (0:ℝ)..1, ∏ i ∈ u, sq ((v i : ℝ) * t)) := by
  have hexp : ∀ t, (∏ i, (sq ((v i : ℝ) * t) + 1))
      = ∑ u ∈ Finset.univ.powerset, ∏ i ∈ u, sq ((v i : ℝ) * t) := by
    intro t; rw [Finset.prod_add]; exact Finset.sum_congr rfl (fun u _ => by simp)
  rw [intervalIntegral.integral_congr (fun t (_ : t ∈ Set.uIcc (0:ℝ) 1) => hexp t),
    intervalIntegral.integral_finsetSum (fun u _ => sqProd_intervalIntegrable v u 0 1),
    ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset (Finset.univ : Finset (Fin n)))]
  have hI0 : (∫ _t in (0:ℝ)..1, ∏ i ∈ (∅ : Finset (Fin n)), sq ((v i : ℝ) * _t)) = 1 := by simp
  rw [hI0]; ring

/-- **Correlation-sum criterion for `ML ≥ 1/4`.** If the sum of all nonempty sub-correlations exceeds
`−1`, then the far measure is positive and `ML v ≥ 1/4`. This is the exact reduction of the four-runner
`±1` sharpening to a Fourier/circle-method estimate on the sub-correlations. -/
theorem ML_ge_quarter_of_correlations {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hcorr : (-1 : ℝ) < ∑ u ∈ (Finset.univ.powerset).erase ∅,
          (∫ t in (0:ℝ)..1, ∏ i ∈ u, sq ((v i : ℝ) * t))) :
    (1 : ℝ) / 4 ≤ ML v := by
  have hpos : 0 < ∫ t in (0:ℝ)..1, ∏ i, (sq ((v i : ℝ) * t) + 1) := by
    rw [far_measure_expansion]; linarith
  obtain ⟨t, ht⟩ := exists_far_of_positive v hpos
  exact (le_gap v t _ ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

-- axiom audit
#print axioms exists_far_of_positive
#print axioms far_measure_expansion
#print axioms ML_ge_quarter_of_correlations

end LRSpectrumFull
