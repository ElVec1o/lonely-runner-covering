/-
# TP'(4), module M0b: the bridge to `five_runners` (step 5b of the hand proof)

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, step 5b; REVIEW2 section 3 (the reduction is an exact
equivalence, `five_runners` is applied to the four original speeds).

* `tpDist_eq_nearestIntDist` : the two distance functions of the project agree
  (Mathlib `abs_sub_round_eq_min`, Algebra/Order/Round.lean).
* `five_runners_tp`          : `five_runners` (Delta2FiveRunners.lean l.50-51) restated with `tpDist`.
* `shift_five`               : step 5b.  If an integer `τ` makes every `v i * τ + s i` divisible by 5, then all four
  runners `Good (v i) (s i)` at `t = u + τ / 5`, where `u` is the time given by `five_runners`.
-/
import LRSpectrumFull.TPFourBridge
import LRSpectrumFull.Delta2FiveRunners

namespace LRSpectrumFull

lemma tpDist_eq_nearestIntDist (x : ℝ) : tpDist x = nearestIntDist x := by
  unfold tpDist nearestIntDist
  exact abs_sub_round_eq_min x

/-- `five_runners` with `tpDist`: four positive speeds, a common time at distance `≥ 1/5` from an integer. -/
lemma five_runners_tp (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ u : ℝ, ∀ i, 1 / 5 ≤ tpDist ((d i : ℝ) * u) := by
  obtain ⟨t, -, ht⟩ := five_runners d hd
  exact ⟨t, fun i => by rw [tpDist_eq_nearestIntDist]; exact ht i⟩

/-- Step 5b: a phase shift `τ` that makes all `v i * τ + s i` multiples of 5 reduces `TP'(4)` to the unshifted
four-runner theorem. -/
lemma shift_five (v : Fin 4 → ℕ) (s : Fin 4 → ℤ) (hv : ∀ i, 0 < v i) (τ : ℤ)
    (hτ : ∀ i, (5 : ℤ) ∣ (v i : ℤ) * τ + s i) :
    ∃ t : ℝ, ∀ i, Good (v i) (s i) t := by
  obtain ⟨u, hu⟩ := five_runners_tp v hv
  refine ⟨u + (τ : ℝ) / 5, fun i => ?_⟩
  obtain ⟨q, hq⟩ := hτ i
  have h5 : (v i : ℝ) * τ + s i = 5 * q := by exact_mod_cast hq
  unfold Good
  have e : (v i : ℝ) * (u + (τ : ℝ) / 5) + (s i : ℝ) / 5 = (v i : ℝ) * u + (q : ℝ) := by
    rw [show (v i : ℝ) * (u + (τ : ℝ) / 5) + (s i : ℝ) / 5
        = (v i : ℝ) * u + ((v i : ℝ) * τ + s i) / 5 by ring, h5]
    ring
  rw [e, tpDist_add_int]
  exact hu i

end LRSpectrumFull
