/-
# The odd-relation loneliness bound: the measure assembly

Assembles the elementary proof of `ML(v) ≥ 1/4` under the subset-parity
hypothesis (equivalent to "no all-odd relation", via `OddRelation.lean`):

    for every nonempty `S`, `∑_{i∈S} vᵢ / gcd_S` is odd  ⟹  `ML(v) ≥ 1/4`.

The far-indicator `F t = ∏ᵢ (1 + sq(vᵢt))` integrates to `1` over a period: the
product expands to `∑_S I_S` with `I_S = ∫ ∏_{i∈S} sq(vᵢt)`, each nonempty `I_S`
killed by the shift `t ↦ t + 1/(2·gcd_S)` (which multiplies `∏_{i∈S} sq(vᵢt)` by
`(−1)^{∑ vᵢ/gcd_S} = −1`). As `F ≥ 0` and `∫F = 1 > 0`, some `t` has `F t > 0`,
i.e. every runner far, i.e. `ML(v) ≥ 1/4`.

This file first banks the shift foundations (no measure theory), then the
integral assembly. No `sorry`.
-/
import LRSpectrumFull.SquareWave
import LRSpectrumFull.OddRelation
import LRSpectrumFull.FarSet
import LRSpectrumFull.MaxLoneliness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

namespace LRSpectrumFull

/-- Integer shifts fix `sq` (`⌊·⌋` bumps by `2m`, parity preserved). -/
theorem sq_add_int (x : ℝ) (m : ℤ) : sq (x + m) = sq x := by
  unfold sq
  rw [show 2 * (x + (m : ℝ)) - 1 / 2 = (2 * x - 1 / 2) + ((2 * m : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast]
  by_cases h : Even ⌊2 * x - 1 / 2⌋
  · rw [if_pos h, if_pos (h.add ⟨m, by ring⟩)]
  · rw [if_neg h, if_neg (fun hc => h (by simpa using hc.sub (⟨m, by ring⟩ : Even (2 * m))))]

/-- Half-integer shift by `k/2` multiplies `sq` by `(−1)^k`. -/
theorem sq_add_half_int (x : ℝ) (k : ℤ) :
    sq (x + (k : ℝ) / 2) = (if Even k then (1 : ℝ) else -1) * sq x := by
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · subst hj
    have harg : x + ((2 * j : ℤ) : ℝ) / 2 = x + ((j : ℤ) : ℝ) := by
      have hc : ((2 * j : ℤ) : ℝ) = 2 * ((j : ℤ) : ℝ) := by push_cast; ring
      rw [hc]; ring
    rw [harg, sq_add_int, if_pos ⟨j, by ring⟩, one_mul]
  · subst hj
    have harg : x + ((2 * j + 1 : ℤ) : ℝ) / 2 = (x + (j : ℤ)) + 1 / 2 := by
      have hc : ((2 * j + 1 : ℤ) : ℝ) = 2 * ((j : ℤ) : ℝ) + 1 := by push_cast; ring
      rw [hc]; ring
    rw [harg, sq_add_half, sq_add_int, if_neg (Int.not_even_iff_odd.mpr ⟨j, rfl⟩)]
    ring

/-- The sign character `signK k = (−1)^k`. -/
def signK (k : ℤ) : ℝ := if Even k then 1 else -1

theorem signK_mul (a b : ℤ) : signK a * signK b = signK (a + b) := by
  unfold signK
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [ha, hb, Int.even_add]

theorem prod_signK {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℤ) :
    ∏ i ∈ s, signK (w i) = signK (∑ i ∈ s, w i) := by
  induction s using Finset.induction with
  | empty => simp [signK]
  | insert a s' ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, signK_mul]

/-- The far-indicator product has period `1` (each `sq(vᵢ·)` does, since `vᵢ ∈ ℤ`). This is
the periodicity used to make the shift `t ↦ t + 1/(2·gcd_S)` a full-period translation. -/
theorem sqProd_periodic {n : ℕ} (v : Fin n → ℤ) (s : Finset (Fin n)) :
    Function.Periodic (fun t => ∏ i ∈ s, sq ((v i : ℝ) * t)) 1 := by
  intro t
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show (v i : ℝ) * (t + 1) = (v i : ℝ) * t + ((v i : ℤ) : ℝ) by ring, sq_add_int]

/-! ### Measure foundations -/

open MeasureTheory intervalIntegral

/-- `sq = (fun n => if Even n then 1 else -1) ∘ ⌊2·−1/2⌋` is measurable: the outer map from the
countable `ℤ` is measurable, the inner floor map is measurable. -/
theorem sq_measurable : Measurable sq :=
  (measurable_of_countable (fun n : ℤ => if Even n then (1 : ℝ) else -1)).comp
    (Int.measurable_floor.comp (by fun_prop))

/-- Finite products `∏_{i∈s} sq(vᵢt)` are measurable. -/
theorem sqProd_measurable {n : ℕ} (v : Fin n → ℤ) (s : Finset (Fin n)) :
    Measurable (fun t : ℝ => ∏ i ∈ s, sq ((v i : ℝ) * t)) :=
  Finset.measurable_prod _ (fun i _ => sq_measurable.comp (by fun_prop))

/-- `|sq y| ≤ 1`. -/
theorem abs_sq_le_one (y : ℝ) : |sq y| ≤ 1 := by unfold sq; split <;> norm_num

/-- The far-indicator products are interval-integrable (measurable, bounded by `1`). -/
theorem sqProd_intervalIntegrable {n : ℕ} (v : Fin n → ℤ) (s : Finset (Fin n)) (a b : ℝ) :
    IntervalIntegrable (fun t => ∏ i ∈ s, sq ((v i : ℝ) * t)) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    (sqProd_measurable v s).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => abs_sq_le_one _)

/-- **The shift kills the correlation.** If a shift `τ` sends each `vᵢ` (`i ∈ s`) to a half-integer
`wᵢ/2`, and `∑_{i∈s} wᵢ` is odd, then `∫₀¹ ∏_{i∈s} sq(vᵢt) = 0`: translating by `τ` multiplies
the product by `signK(∑wᵢ) = −1`, while a full-period translation fixes the integral. -/
theorem sqProd_integral_zero {n : ℕ} (v : Fin n → ℤ) (s : Finset (Fin n))
    (τ : ℝ) (w : Fin n → ℤ) (hfactor : ∀ i ∈ s, (v i : ℝ) * τ = (w i : ℝ) / 2)
    (hodd : Odd (∑ i ∈ s, w i)) :
    ∫ t in (0:ℝ)..1, ∏ i ∈ s, sq ((v i : ℝ) * t) = 0 := by
  set G : ℝ → ℝ := fun t => ∏ i ∈ s, sq ((v i : ℝ) * t) with hG
  have hshift : ∀ t, G (t + τ) = signK (∑ i ∈ s, w i) * G t := by
    intro t
    have hp : (∏ i ∈ s, sq ((v i : ℝ) * (t + τ)))
        = ∏ i ∈ s, signK (w i) * sq ((v i : ℝ) * t) := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      rw [show (v i : ℝ) * (t + τ) = (v i : ℝ) * t + (w i : ℝ) / 2 by rw [mul_add, hfactor i hi],
        sq_add_half_int]
      rfl
    simp only [hG]
    rw [hp, Finset.prod_mul_distrib, prod_signK]
  have hsign : signK (∑ i ∈ s, w i) = -1 := by
    rw [signK, if_neg (by rw [Int.not_even_iff_odd]; exact hodd)]
  have hper : Function.Periodic G 1 := sqProd_periodic v s
  have hint1 : (∫ t in (0:ℝ)..1, G (t + τ)) = ∫ t in (0:ℝ)..1, G t := by
    rw [integral_comp_add_right G τ, zero_add, show (1 : ℝ) + τ = τ + 1 by ring]
    have h := hper.intervalIntegral_add_eq τ 0
    rwa [zero_add] at h
  have hint2 : (∫ t in (0:ℝ)..1, G (t + τ)) = signK (∑ i ∈ s, w i) * ∫ t in (0:ℝ)..1, G t := by
    simp_rw [hshift]
    exact intervalIntegral.integral_const_mul _ _
  rw [hint1, hsign, neg_one_mul] at hint2
  linarith [hint2]

/-- **Finset Bézout over `ℤ`:** the gcd of a finite family is an integer combination of it. -/
theorem gcd_bezout {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    ∃ c : ι → ℤ, ∑ i ∈ s, c i * f i = s.gcd f := by
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul (f a) (s.gcd f)
    refine ⟨Function.update (fun i => y * c i) a x, ?_⟩
    rw [Finset.sum_insert ha, Finset.gcd_insert, Function.update_self]
    have hrest : ∑ i ∈ s, Function.update (fun i => y * c i) a x i * f i
        = ∑ i ∈ s, y * c i * f i :=
      Finset.sum_congr rfl (fun i hi => by
        rw [Function.update_of_ne (show i ≠ a by rintro rfl; exact ha hi)])
    have hy : ∑ i ∈ s, y * c i * f i = y * s.gcd f := by
      rw [← hc, Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hrest, hy, hxy]; ring

/-- **The odd-relation loneliness bound.** If every nonempty subset `u` has `∑_{i∈u} vᵢ/gcd_u`
odd (equivalently: `v` has no all-odd relation, by `OddRelation.lean`), then some time places every
runner `≥ 1/4` from the integers, i.e. `ML(v) ≥ 1/4`. -/
theorem exists_far_of_parity {n : ℕ} (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0)
    (hpar : ∀ u : Finset (Fin n), u.Nonempty → Odd (∑ i ∈ u, v i / u.gcd v)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) := by
  have hInt : (∫ t in (0:ℝ)..1, ∏ i, (sq ((v i : ℝ) * t) + 1)) = 1 := by
    have hexp : ∀ t, (∏ i, (sq ((v i : ℝ) * t) + 1))
        = ∑ u ∈ Finset.univ.powerset, ∏ i ∈ u, sq ((v i : ℝ) * t) := by
      intro t
      rw [Finset.prod_add]
      exact Finset.sum_congr rfl (fun u _ => by simp)
    rw [intervalIntegral.integral_congr (fun t (_ : t ∈ Set.uIcc (0:ℝ) 1) => hexp t),
      intervalIntegral.integral_finsetSum (fun u _ => sqProd_intervalIntegrable v u 0 1),
      ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset (Finset.univ : Finset (Fin n)))]
    have hI0 : (∫ _t in (0:ℝ)..1, ∏ i ∈ (∅ : Finset (Fin n)), sq ((v i : ℝ) * _t)) = 1 := by simp
    have hrest : ∑ u ∈ (Finset.univ.powerset).erase ∅,
        (∫ t in (0:ℝ)..1, ∏ i ∈ u, sq ((v i : ℝ) * t)) = 0 := by
      refine Finset.sum_eq_zero (fun u hu => ?_)
      have hune : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hu).1
      have hg0 : u.gcd v ≠ 0 := by
        rw [Ne, Finset.gcd_eq_zero_iff]; push Not
        obtain ⟨i0, hi0⟩ := hune; exact ⟨i0, hi0, hv i0⟩
      refine sqProd_integral_zero v u (1 / (2 * ((u.gcd v : ℤ) : ℝ))) (fun i => v i / u.gcd v)
        (fun i hi => ?_) (hpar u hune)
      have hdvd : u.gcd v ∣ v i := Finset.gcd_dvd hi
      have hgR : ((u.gcd v : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hg0
      have hvi : (v i : ℝ) = ((u.gcd v : ℤ) : ℝ) * ((v i / u.gcd v : ℤ) : ℝ) := by
        rw [← Int.cast_mul, Int.mul_ediv_cancel' hdvd]
      rw [hvi]; field_simp
    rw [hrest, hI0, zero_add]
  have hFnn : ∀ t, 0 ≤ ∏ i, (sq ((v i : ℝ) * t) + 1) :=
    fun t => Finset.prod_nonneg (fun i _ => by unfold sq; split <;> norm_num)
  have hex : ∃ t ∈ Set.uIcc (0:ℝ) 1, 0 < ∏ i, (sq ((v i : ℝ) * t) + 1) := by
    by_contra hcon; push Not at hcon
    have hle : 0 ≤ ∫ t in (0:ℝ)..1, -(∏ i, (sq ((v i : ℝ) * t) + 1)) := by
      refine intervalIntegral.integral_nonneg (by norm_num) (fun u hu => ?_)
      have : u ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hu
      linarith [hcon u this]
    rw [intervalIntegral.integral_neg] at hle
    linarith [hInt]
  obtain ⟨t, _, hFt⟩ := hex
  refine ⟨t, fun i => ?_⟩
  have hfac : 0 < sq ((v i : ℝ) * t) + 1 := by
    by_contra hc; push Not at hc
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

/-- **The odd-relation loneliness bound, in "no all-odd relation" form.** If `v` (all nonzero) has
no nontrivial integer relation with all entries odd-or-zero, then `∃ t, ∀ i, ‖vᵢt‖ ≥ 1/4`, i.e.
`ML(v) ≥ 1/4`. (The contrapositive `ML(v) < 1/4 ⟹ an all-odd wall exists` is the effective-wall
lemma.) -/
theorem exists_far_of_no_odd_relation {n : ℕ} (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0)
    (hno : ∀ a : Fin n → ℤ, (∀ i, a i ≠ 0 → Odd (a i)) → (∑ i, a i * v i) = 0 → ∀ i, a i = 0) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) := by
  classical
  refine exists_far_of_parity v hv (fun u hune => ?_)
  by_contra hoddneg
  rw [Int.not_odd_iff_even] at hoddneg
  set S : ℤ := ∑ j ∈ u, v j / u.gcd v with hS
  obtain ⟨c, hc⟩ := gcd_bezout u v
  set a : Fin n → ℤ := fun i => if i ∈ u then 1 - S * c i else 0 with ha
  obtain ⟨i0, hi0⟩ := hune
  -- `a` is an all-odd relation supported on `u`, so `hno` forces `a i0 = 0` — but it is odd, hence ≠ 0.
  have haodd : ∀ i, a i ≠ 0 → Odd (a i) := by
    intro i hai
    by_cases hi : i ∈ u
    · rw [ha]; simp only [hi, if_true]
      obtain ⟨r, hr⟩ := hoddneg
      exact ⟨-(r * c i), by rw [hr]; ring⟩
    · exact absurd (by rw [ha]; simp only [hi, if_false]) hai
  have hasum : ∑ i, a i * v i = 0 := by
    have heq : ∑ i, a i * v i = ∑ i ∈ u, (1 - S * c i) * v i := by
      rw [ha]; simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [heq]
    have expand : ∑ i ∈ u, (1 - S * c i) * v i = (∑ i ∈ u, v i) - S * ∑ i ∈ u, c i * v i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hSg : S * u.gcd v = ∑ i ∈ u, v i := by
      rw [hS, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => Int.ediv_mul_cancel (Finset.gcd_dvd hi))
    rw [expand, hc, hSg]; ring
  have hai0odd : Odd (a i0) := by
    rw [ha]; simp only [hi0, if_true]
    obtain ⟨r, hr⟩ := hoddneg
    exact ⟨-(r * c i0), by rw [hr]; ring⟩
  have hai0 : a i0 ≠ 0 := by obtain ⟨m, hm⟩ := hai0odd; rw [hm]; omega
  exact hai0 (hno a haodd hasum i0)

/-- **Lonely Runner bound for relation-free speeds.** If the nonzero speeds `v` carry no all-odd
integer relation, their maximum loneliness satisfies `ML(v) ≥ 1/4`. For `n = k+1 ≥ 3` runners this
meets or exceeds the Lonely Runner value `1/(n+1)`, so the Lonely Runner Conjecture holds for every
such configuration (with room to spare when `n > 3`). -/
theorem ML_ge_quarter_of_no_odd_relation {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0)
    (hno : ∀ a : Fin (k + 1) → ℤ, (∀ i, a i ≠ 0 → Odd (a i)) → (∑ i, a i * v i) = 0 → ∀ i, a i = 0) :
    (1 : ℝ) / 4 ≤ ML v := by
  obtain ⟨t, ht⟩ := exists_far_of_no_odd_relation v hv hno
  exact (le_gap v t _ ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- **Lonely Runner bound for speeds none divisible by `4`:** `ML(v) ≥ 1/4`, via the parking time
`t = 1/4`. Consequently any `ML(v) < 1/4` configuration has a runner `≡ 0 (mod 4)`. -/
theorem ML_ge_quarter_of_no_mul_four {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : ∀ i, ¬ ((4 : ℤ) ∣ v i)) : (1 : ℝ) / 4 ≤ ML v := by
  obtain ⟨t, ht⟩ := exists_far_of_no_mul_four v h
  exact (le_gap v t _ ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- **Lonely Runner bound for speeds none divisible by `3`:** `ML(v) ≥ 1/4`, via `t = 1/3`. So any
`ML(v) < 1/4` configuration has a runner `≡ 0 (mod 3)` (and, by `ML_ge_quarter_of_no_mul_four`, one
`≡ 0 (mod 4)`). -/
theorem ML_ge_quarter_of_no_mul_three {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : ∀ i, ¬ ((3 : ℤ) ∣ v i)) : (1 : ℝ) / 4 ≤ ML v := by
  obtain ⟨t, ht⟩ := exists_far_of_no_mul_three v h
  exact (le_gap v t _ ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- **Scaled parking bound.** If some witness `t = a/m` places every `vᵢ·a mod m` in the middle band
`[m/4, 3m/4]`, then `ML(v) ≥ 1/4`. The `1/4`-band companion of `D_lt_of_scaled_residues`, and the
common engine behind every parking: the four bounds above and the two below are all instances. -/
theorem ML_ge_quarter_of_scaled_residues {k : ℕ} (v : Fin (k + 1) → ℤ) (a m : ℤ) (hm : 0 < m)
    (h : ∀ i, m ≤ 4 * (v i * a % m) ∧ m ≤ 4 * (m - v i * a % m)) :
    (1 : ℝ) / 4 ≤ ML v := by
  obtain ⟨t, ht⟩ := exists_far_of_scaled_residues v a m hm h
  exact (le_gap v t _ ht).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- **Second-tier parking `t = 2/7`.** If every speed is `≢ 0, ±3 (mod 7)` (residue in `{1,2,5,6}`),
then `2vᵢ mod 7 ∈ {2,3,4,5}` — the middle band — so `ML(v) ≥ 1/4`. This catches a large share of the
residual `mul-3 ∧ mul-4` configurations that the two clean parkings `t = 1/3, 1/4` cannot reach. -/
theorem ML_ge_quarter_parking_two_sevenths {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : ∀ i, v i % 7 = 1 ∨ v i % 7 = 2 ∨ v i % 7 = 5 ∨ v i % 7 = 6) :
    (1 : ℝ) / 4 ≤ ML v := by
  refine ML_ge_quarter_of_scaled_residues v 2 7 (by norm_num) (fun i => ?_)
  rcases h i with hi | hi | hi | hi <;> omega

/-- **Second-tier parking `t = 3/8`.** If every speed has residue in `{1,2,4,6,7} (mod 8)`, then
`3vᵢ mod 8 ∈ {2,3,4,5,6}` — the middle band — so `ML(v) ≥ 1/4`. Together with `t = 2/7` these cover
the bulk of the residual class; but the far times are diffuse, so no finite set of parkings covers
all of it. -/
theorem ML_ge_quarter_parking_three_eighths {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : ∀ i, v i % 8 = 1 ∨ v i % 8 = 2 ∨ v i % 8 = 4 ∨ v i % 8 = 6 ∨ v i % 8 = 7) :
    (1 : ℝ) / 4 ≤ ML v := by
  refine ML_ge_quarter_of_scaled_residues v 3 8 (by norm_num) (fun i => ?_)
  rcases h i with hi | hi | hi | hi | hi <;> omega

/-- **Bounded-spread far point (a constructive `t*(v)`).** If all speeds lie in a single factor-`3`
band `[M/2, 3M/2]` — i.e. `M ≤ 2vᵢ ≤ 3M` for every `i` — then the *explicit* time `t = 1/(2M)`
places every runner in the middle band, so `ML(v) ≥ 1/4`. This dissolves the apparent "diffuse tail":
the residual configurations with the largest minimal far-denominators (e.g. `(10,11,12,15)`,
`(13,16,17,18)`) are exactly the bounded-spread ones, and here have the closed-form far time
`1/(2·max)`. They only looked hard because that time is not a small-denominator fraction. -/
theorem ML_ge_quarter_of_bounded_spread {k : ℕ} (v : Fin (k + 1) → ℤ) (M : ℤ) (hM : 0 < M)
    (hlb : ∀ i, M ≤ 2 * v i) (hub : ∀ i, 2 * v i ≤ 3 * M) :
    (1 : ℝ) / 4 ≤ ML v := by
  refine ML_ge_quarter_of_scaled_residues v 1 (2 * M) (by omega) (fun i => ?_)
  have hpos : 0 < v i := by have := hlb i; omega
  have hmod : v i * 1 % (2 * M) = v i := by
    rw [mul_one]
    exact Int.emod_eq_of_lt (le_of_lt hpos) (by have := hub i; omega)
  rw [hmod]
  have h1 := hlb i; have h2 := hub i; omega

/-- **Structural necessary conditions for sub-`1/4` loneliness.** If a configuration of nonzero
speeds is lonelier than `1/4` (`ML(v) < 1/4`), then it must simultaneously
* carry a nontrivial **all-odd** integer relation `∑ aᵢ vᵢ = 0` (every `aᵢ` odd or zero),
* contain a speed divisible by `3`, and
* contain a speed divisible by `4`.

These are the contrapositives of the odd-relation loneliness bound and the two parking bounds
`t = 1/3`, `t = 1/4`. The moduli `3` and `4` are forced: `m` is the *only* kind of modulus for which
`‖v/m‖ < 1/4` singles out the residue `0` alone (this requires `m ≤ 4`), so no third clean parking
exists. For four runners this pins any `ML < 1/4` example to the residual class carrying an all-odd
relation together with a `mul-3` and a `mul-4` runner — e.g. `(3,4,8,9)`, which has the length-four
relation `3 − 4 − 8 + 9 = 0` but no three-term `±1` relation. -/
theorem ML_lt_quarter_structure {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0)
    (h : ML v < 1 / 4) :
    (∃ a : Fin (k + 1) → ℤ, (∀ i, a i ≠ 0 → Odd (a i)) ∧ (∑ i, a i * v i) = 0 ∧ ∃ i, a i ≠ 0)
      ∧ (∃ i, (3 : ℤ) ∣ v i) ∧ (∃ i, (4 : ℤ) ∣ v i) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact absurd (ML_ge_quarter_of_no_odd_relation v hv hc) (not_le.mpr h)
  · by_contra hc
    push_neg at hc
    exact absurd (ML_ge_quarter_of_no_mul_three v hc) (not_le.mpr h)
  · by_contra hc
    push_neg at hc
    exact absurd (ML_ge_quarter_of_no_mul_four v hc) (not_le.mpr h)

/-- **The relation–residue divisibility (the "phase" identity, stated honestly).** For any integer
relation `∑ cᵢ vᵢ = 0` and *any* multiplier `k` and modulus `m`, the residues `k·vᵢ mod m` weighted
by `c` sum to a multiple of `m`. Consequently, evaluating a candidate time `t = k/m`, the weighted
offsets `∑ cᵢ (⟨k·vᵢ mod m⟩/m − 1/2)` always land in `(1/2)·ℤ`, quantized by the parity of `∑ cᵢ`.

The point is the hypothesis: it is `∑ cᵢ vᵢ = 0` alone — there is **no** far-band condition on the
residues. So this quantization is a property of integer relations at an arbitrary rational point, not
a structural feature of far-points, and it places no bound on `m`. (It holds verbatim for `k/m` that
are nowhere near a far time.) -/
theorem relation_residue_dvd {n : ℕ} (c v : Fin n → ℤ) (k m : ℤ)
    (h : ∑ i, c i * v i = 0) : m ∣ ∑ i, c i * (k * v i % m) := by
  have key : ∑ i, c i * (k * v i % m)
      = k * (∑ i, c i * v i) - m * ∑ i, c i * (k * v i / m) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi : k * v i % m = k * v i - m * (k * v i / m) := by
      have := Int.emod_add_ediv (k * v i) m; linarith
    rw [hi]; ring
  rw [key, h, mul_zero, zero_sub, dvd_neg]
  exact dvd_mul_right m _

end LRSpectrumFull
