/-
# Milestone 41: decidable rational witness certificates

The witness proofs of M35/M36 (`le_mgap` over a sampled rational point) are
verbose `simp`/`norm_num` blocks, one per runner. But for a **rational**
witness `s` and integer matrix `M`, the gap `mgap M s` is a *computable
rational* — so the bound `mD M ≤ 3/14` reduces to a single decidable check
`2/7 ≤ mgapQ M s`, dischargeable by `native_decide`.

This file builds that bridge: a rational `nidQ`/`mgapQ` mirroring the real
`nearestIntDist`/`mgap`, proven equal under the cast, giving

    `mD_le_of_mgapQ : 2/7 ≤ mgapQ M s → mD M ≤ 3/14`.

With it, a whole family of saturated forms can be discharged by *one*
list-quantified `native_decide` (see `CaseAEnumerate`). No `sorry`.
-/

import LRSpectrumFull.Subtorus
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Cast.Order

namespace LRSpectrumFull

/-- Rational nearest-integer distance, mirroring `nearestIntDist` on `ℝ`. -/
def nidQ (q : ℚ) : ℚ := min (Int.fract q) (1 - Int.fract q)

/-- `Int.fract` commutes with the `ℚ → ℝ` cast. -/
theorem fract_ratCast (q : ℚ) : Int.fract (q : ℝ) = ((Int.fract q : ℚ) : ℝ) := by
  unfold Int.fract
  rw [Rat.floor_cast]
  push_cast
  ring

/-- The rational `nidQ` casts to the real `nearestIntDist`. -/
theorem nidQ_bridge (q : ℚ) : ((nidQ q : ℚ) : ℝ) = nearestIntDist (q : ℝ) := by
  unfold nidQ nearestIntDist
  rw [Rat.cast_min, fract_ratCast]
  push_cast
  rw [fract_ratCast]

/-- The `ℚ → ℝ` cast commutes with a finite sum. -/
theorem ratCast_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ((∑ i ∈ s, f i : ℚ) : ℝ) = ∑ i ∈ s, ((f i : ℚ) : ℝ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, Rat.cast_add, ih]

/-- Rational gap at a rational parameter, mirroring `mgap`. Computable, so a
witness bound `2/7 ≤ mgapQ M s` is dischargeable by `native_decide`. -/
def mgapQ {k r : ℕ} (M : Fin (k + 1) → Fin r → ℤ) (s : Fin r → ℚ) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => nidQ (∑ j, (M i j : ℚ) * s j))

/-- **The certificate bridge.** A rational witness `s` with `mgapQ M s ≥ 2/7`
forces `mD M ≤ 3/14`. The hypothesis is a decidable rational inequality. -/
theorem mD_le_of_mgapQ {k r : ℕ} (M : Fin (k + 1) → Fin r → ℤ) (s : Fin r → ℚ)
    (h : (2 : ℚ) / 7 ≤ mgapQ M s) : mD M ≤ 3 / 14 := by
  unfold mgapQ at h
  have hreal : (2 / 7 : ℝ) ≤ mgap M (fun j => (s j : ℝ)) := by
    apply le_mgap
    intro i
    show (2 / 7 : ℝ) ≤ nearestIntDist (∑ j, (M i j : ℝ) * (s j : ℝ))
    have hi : (2 : ℚ) / 7 ≤ nidQ (∑ j, (M i j : ℚ) * s j) :=
      (Finset.le_inf'_iff _ _).mp h i (Finset.mem_univ i)
    have key : nearestIntDist (∑ j, (M i j : ℝ) * (s j : ℝ))
        = ((nidQ (∑ j, (M i j : ℚ) * s j) : ℚ) : ℝ) := by
      rw [nidQ_bridge]; congr 1
      rw [ratCast_sum]
      exact Finset.sum_congr rfl (fun x _ => by push_cast; ring)
    rw [key, show (2 / 7 : ℝ) = ((2 : ℚ) / 7 : ℝ) by norm_num]
    exact_mod_cast hi
  have := mD_le_of_mgap M (fun j => (s j : ℝ))
  linarith

end LRSpectrumFull
