/-
# Attainment of the maximum loneliness, and the exact-boundary pin

Two structural results sharpening the circle-method reduction of the four-runner `±1` sharpening —
both stated and proved for **every** number of runners, so they serve the whole tower program
(the `1/4`-band is the `k = n−2` rung `1/2 − 1/(n+2−k) = 1/4` at every `n`).

* **Attainment.** The instantaneous loneliness `gap v` is continuous (each runner's distance is
  `1`-Lipschitz, `nearestIntDist_lipschitz`) and `1`-periodic, so it attains its supremum `ML v` on
  the compact `[0,1]`. Hence `c ≤ ML v ↔ ∃ t, ∀ i, c ≤ ‖vᵢt‖` (`le_ML_iff_exists_far`): every
  threshold statement about the *supremum* is equivalent to the *existence of a witness time*. The
  sharpening's target `ML v ≥ 1/4` is exactly "the far set is nonempty" — no sup-attainment
  subtleties remain anywhere in the program.

* **Exact-boundary pin.** The far measure `∫₀¹ ∏ᵢ (sq(vᵢt) + 1)` is nonnegative, so the correlation
  sum of `far_measure_expansion` is always `≥ −1`; combined with `ML_ge_quarter_of_correlations`,
  any configuration with `ML v < 1/4` has correlation sum **exactly** `−1` — perfect destructive
  interference. A counterexample to the sharpening cannot merely have small far measure: it must sit
  on the exact null boundary of the circle method with an *empty* far set (by attainment), while
  every measure-zero-far config found numerically (e.g. `(1,2,6,11)`, far set `= {1/4}`) still has a
  far *point* and parks at a small modulus (`boundary_config_parks`).
-/
import LRSpectrumFull.Delta2Circle
import LRSpectrumFull.NearestIntLipschitz

namespace LRSpectrumFull

open MeasureTheory intervalIntegral

/-- Finite `inf'` of continuous real functions is continuous (cons-induction on the index set). -/
private theorem continuous_finset_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun t => s.inf' hs fun i => f i t := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a
  | cons a s h hs ih =>
    refine ((hf a).min ih).congr fun t => ?_
    rw [Finset.inf'_cons]

/-- `nearestIntDist` is continuous (it is `1`-Lipschitz). -/
theorem nearestIntDist_continuous : Continuous nearestIntDist := by
  have hl : LipschitzWith 1 nearestIntDist :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
      exact nearestIntDist_lipschitz x y
  exact hl.continuous

/-- `gap` is invariant under integer time shifts (each `vᵢ·n` is an integer). -/
theorem gap_add_int {k : ℕ} (v : Fin (k + 1) → ℤ) (t : ℝ) (n : ℤ) :
    gap v (t + n) = gap v t := by
  unfold gap
  congr 1
  funext i
  rw [show (v i : ℝ) * (t + (n : ℝ)) = (v i : ℝ) * t + ((v i * n : ℤ) : ℝ) by push_cast; ring,
    nearestIntDist_add_int]

/-- The instantaneous loneliness `gap v` is continuous in the time. -/
theorem gap_continuous {k : ℕ} (v : Fin (k + 1) → ℤ) : Continuous (gap v) := by
  unfold gap
  exact continuous_finset_inf' Finset.univ_nonempty _
    (fun i => nearestIntDist_continuous.comp (continuous_const.mul continuous_id))

/-- **Attainment.** The maximum loneliness is attained: some `t ∈ [0,1]` has `gap v t = ML v`.
Continuity + `1`-periodicity reduce the supremum over `ℝ` to a maximum over the compact `[0,1]`. -/
theorem exists_gap_eq_ML {k : ℕ} (v : Fin (k + 1) → ℤ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, gap v t = ML v := by
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (gap_continuous v).continuousOn
  refine ⟨t₀, ht₀, le_antisymm (le_csSup (bddAbove_range_gap v) ⟨t₀, rfl⟩) ?_⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have hfr : gap v t = gap v (Int.fract t) := by
    conv_lhs => rw [← Int.fract_add_floor t]
    exact gap_add_int v (Int.fract t) ⌊t⌋
  rw [hfr]
  exact hmax ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- **Sup-to-witness bridge.** `c ≤ ML v` iff some single time keeps every runner `≥ c`. The `←`
direction is the usual sampling; the `→` direction is the attainment. Every threshold question about
the loneliness supremum is an existence question about a witness time. -/
theorem le_ML_iff_exists_far {k : ℕ} (v : Fin (k + 1) → ℤ) (c : ℝ) :
    c ≤ ML v ↔ ∃ t : ℝ, ∀ i, c ≤ nearestIntDist ((v i : ℝ) * t) := by
  constructor
  · intro h
    obtain ⟨t, _, ht⟩ := exists_gap_eq_ML v
    have hc : c ≤ gap v t := by rw [ht]; exact h
    exact ⟨t, fun i => hc.trans (gap_le v t i)⟩
  · rintro ⟨t, ht⟩
    exact (le_gap v t c ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- The sharpening's target, in far-set form: `ML v ≥ 1/4` iff the far set is nonempty. -/
theorem ML_ge_quarter_iff_far_nonempty {k : ℕ} (v : Fin (k + 1) → ℤ) :
    (1 : ℝ) / 4 ≤ ML v ↔ ∃ t : ℝ, ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) :=
  le_ML_iff_exists_far v (1 / 4)

/-- **The correlation sum is never below `−1`** (the far measure is nonnegative). -/
theorem correlation_sum_ge_neg_one {n : ℕ} (v : Fin n → ℤ) :
    (-1 : ℝ) ≤ ∑ u ∈ (Finset.univ.powerset).erase ∅,
        (∫ t in (0:ℝ)..1, ∏ i ∈ u, sq ((v i : ℝ) * t)) := by
  have hnn : (0 : ℝ) ≤ ∫ t in (0:ℝ)..1, ∏ i, (sq ((v i : ℝ) * t) + 1) :=
    intervalIntegral.integral_nonneg zero_le_one
      (fun u _ => Finset.prod_nonneg fun i _ => by unfold sq; split <;> norm_num)
  rw [far_measure_expansion v] at hnn
  linarith

/-- **Exact-boundary pin.** A configuration with `ML v < 1/4` has correlation sum exactly `−1`:
its sub-correlations interfere perfectly destructively. Any counterexample to the four-runner
sharpening lives on the precise null boundary of the circle method. -/
theorem correlation_sum_eq_neg_one_of_ML_lt {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : ML v < 1 / 4) :
    (∑ u ∈ (Finset.univ.powerset).erase ∅,
        (∫ t in (0:ℝ)..1, ∏ i ∈ u, sq ((v i : ℝ) * t))) = -1 := by
  refine le_antisymm ?_ (correlation_sum_ge_neg_one v)
  by_contra hgt
  push Not at hgt
  exact absurd (ML_ge_quarter_of_correlations v hgt) (not_le.mpr h)

/-- **The measure-zero boundary config parks.** `(1,2,6,11)` — the unique far-measure-zero no-`±1`
config with speeds `≤ 12`, far set `= {1/4}` — has `ML ≥ 1/4` by the banked mod-`4` parking (all
speeds `≢ 0 (mod 4)`). The circle method's null boundary is covered by small-modulus parkings. -/
theorem boundary_config_parks : (1 : ℝ) / 4 ≤ ML ![1, 2, 6, 11] :=
  ML_ge_quarter_of_no_mul_four _ (by decide)

-- axiom audit
#print axioms exists_gap_eq_ML
#print axioms le_ML_iff_exists_far
#print axioms correlation_sum_ge_neg_one
#print axioms correlation_sum_eq_neg_one_of_ML_lt
#print axioms boundary_config_parks

end LRSpectrumFull
