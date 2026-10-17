/-
# The all-odd velocity stratum

`cube_floor_allodd` — a positive family `v : Fin (k+1) → ℤ` (`4 ≤ k ≤ 7`)
all of whose velocities are **odd** meets the floor `1/(k+2)` — with no
strong-freeness hypothesis at all.

The parity is the whole engine.  A `[-3,3]`-vanishing combination `c` of an
all-odd family has `∑_w c_w ≡ ∑_w c_w v_w = 0 (mod 2)` (each `v_w` is odd),
so `∑_w c_w` is even; and inside the box the sign of `cubeWtR(a)` is
`(-1)^a`, so every product `∏_w cubeWtR(c_w)` is nonnegative
(`cubeWtR_prod_nonneg_of_even`).  With all van masses nonnegative, each
one-runner-deleted subfamily mass is a subsum of the family mass, so the
sum of the `k+1` subfamily masses is at most `(2/5)(k+1)` times the family
mass (`subfamily_sum_le_allodd`); since `cubeEps k · (2/5)(k+1) < 1` the
certificate `cube_floor_of_cert` closes.

This is the `Neg = 0` stratum: the odd-parity coset of the vanishing web is
empty exactly when every velocity is odd, so the razor-thin coset
cancellation that governs the general certificate degenerates and the
floor follows by a one-line mass count.  It sits alongside the web-shape
strata (line, pair, triple, parallelogram) as a parity slice of the
four-direction residual.
-/
import LRSpectrumFull.Delta2CubeCert

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- Inside the box, the sign of `cubeWtR a` is the parity of `a`. -/
theorem cubeWtR_eq_sign_mul_abs (a : ℤ) (ha : -3 ≤ a ∧ a ≤ 3) :
    cubeWtR a = (if Even a then (1 : ℝ) else -1) * |cubeWtR a| := by
  obtain ⟨h1, h2⟩ := ha
  interval_cases a <;> norm_num [cubeWtR]

/-- The product of signs is the sign of the sum (parity homomorphism). -/
theorem prod_sign_eq_sign_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    (∏ w ∈ s, (if Even (c w) then (1 : ℝ) else -1))
      = if Even (∑ w ∈ s, c w) then 1 else -1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    by_cases hEa : Even (c a) <;> by_cases hEs : Even (∑ w ∈ s, c w) <;>
      simp [hEa, hEs, Int.even_add, parity_simps]

/-- **Parity nonnegativity.**  A box-valued vector with even coordinate sum
has nonnegative `cubeWtR`-product. -/
theorem cubeWtR_prod_nonneg_of_even {m : ℕ} (c : Fin m → ℤ)
    (hb : ∀ w, -3 ≤ c w ∧ c w ≤ 3) (he : Even (∑ w, c w)) :
    0 ≤ ∏ w, cubeWtR (c w) := by
  have hfac : (∏ w, cubeWtR (c w))
      = (∏ w, (if Even (c w) then (1 : ℝ) else -1)) * ∏ w, |cubeWtR (c w)| := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun w _ => cubeWtR_eq_sign_mul_abs (c w) (hb w))
  rw [hfac, prod_sign_eq_sign_sum, if_pos he, one_mul]
  exact Finset.prod_nonneg (fun w _ => abs_nonneg _)

/-- The van filter set of a family, matching `vanMass`'s definition. -/
def vanFilter (m : ℕ) (v : Fin m → ℤ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
    (fun c => (∑ w, c w * v w) = 0)

theorem vanMass_eq_vanFilter {m : ℕ} (v : Fin m → ℤ) :
    vanMass m v = ∑ c ∈ vanFilter m v, ∏ w, cubeWtR (c w) := rfl

theorem mem_vanFilter {m : ℕ} (v : Fin m → ℤ) (c : Fin m → ℤ) :
    c ∈ vanFilter m v ↔ (∀ w, -3 ≤ c w ∧ c w ≤ 3) ∧ (∑ w, c w * v w) = 0 := by
  unfold vanFilter
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hv⟩; exact ⟨fun w => by have := hb w; omega, hv⟩
  · rintro ⟨hb, hv⟩; exact ⟨fun w => by have := hb w; omega, hv⟩

/-- **The subfamily slice identity.**  For any family, `5/2` times the mass
of the subfamily deleting runner `i` equals the mass carried by the
`c_i = 0` slice of the full vanishing web. -/
theorem vanMass_sub_slice {k : ℕ} (v : Fin (k + 1) → ℤ) (i : Fin (k + 1)) :
    (5 / 2 : ℝ) * vanMass k (fun j' => v (i.succAbove j'))
      = ∑ c ∈ (vanFilter (k + 1) v).filter (fun c => c i = 0), ∏ w, cubeWtR (c w) := by
  classical
  rw [vanMass_eq_vanFilter, Finset.mul_sum]
  refine Finset.sum_nbij'
    (@Fin.insertNth k (fun _ => ℤ) i 0)
    (fun c => fun j' => c (i.succAbove j'))
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into the slice
    intro c' hc'
    rw [mem_vanFilter] at hc'
    obtain ⟨hbx, hvan⟩ := hc'
    rw [Finset.mem_filter, mem_vanFilter]
    refine ⟨⟨fun w => ?_, ?_⟩, ?_⟩
    · rcases Fin.eq_self_or_eq_succAbove i w with rfl | ⟨j', rfl⟩
      · rw [Fin.insertNth_apply_same]; omega
      · rw [Fin.insertNth_apply_succAbove]; exact hbx j'
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, zero_mul, zero_add]
      rw [Finset.sum_congr rfl (fun j' _ => by rw [Fin.insertNth_apply_succAbove])]
      exact hvan
    · rw [Fin.insertNth_apply_same]
  · -- inverse maps into the subfamily van set
    intro c hc
    rw [Finset.mem_filter, mem_vanFilter] at hc
    obtain ⟨⟨hbx, hvan⟩, hci⟩ := hc
    rw [mem_vanFilter]
    refine ⟨fun j' => hbx _, ?_⟩
    have hsplit := Fin.sum_univ_succAbove (fun w => c w * v w) i
    rw [hci, zero_mul, zero_add] at hsplit
    rw [← hsplit, hvan]
  · -- left inverse
    intro c' hc'
    funext j'
    simp only [Fin.insertNth_apply_succAbove]
  · -- right inverse
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨_, hci⟩ := hc
    funext w
    rcases Fin.eq_self_or_eq_succAbove i w with rfl | ⟨j', rfl⟩
    · simp only [Fin.insertNth_apply_same, hci]
    · simp only [Fin.insertNth_apply_succAbove]
  · -- value identity
    intro c' hc'
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [show cubeWtR (0 : ℤ) = 5 / 2 from by norm_num [cubeWtR]]

/-- **The subfamily-sum bound on the all-nonnegative stratum.**  When every
van product is nonnegative, the sum of the `k+1` subfamily masses is at most
`(2/5)(k+1)` times the family mass. -/
theorem subfamily_sum_le_allodd {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hnn : ∀ c ∈ vanFilter (k + 1) v, 0 ≤ ∏ w, cubeWtR (c w)) :
    (∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')))
      ≤ (2 / 5 : ℝ) * ((k : ℝ) + 1) * vanMass (k + 1) v := by
  classical
  have hslice : ∀ i : Fin (k + 1),
      (5 / 2 : ℝ) * vanMass k (fun j' => v (i.succAbove j')) ≤ vanMass (k + 1) v := by
    intro i
    rw [vanMass_sub_slice, vanMass_eq_vanFilter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro c hc _
    exact hnn c hc
  have hsum : (5 / 2 : ℝ) * (∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')))
      ≤ ((k : ℝ) + 1) * vanMass (k + 1) v := by
    rw [Finset.mul_sum]
    calc (∑ i : Fin (k + 1), (5 / 2 : ℝ) * vanMass k (fun j' => v (i.succAbove j')))
        ≤ ∑ _i : Fin (k + 1), vanMass (k + 1) v := Finset.sum_le_sum (fun i _ => hslice i)
      _ = ((k : ℝ) + 1) * vanMass (k + 1) v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  linarith

/-- On the all-nonnegative stratum the family mass is strictly positive
(from the zero vector). -/
theorem vanMass_pos_allodd {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hnn : ∀ c ∈ vanFilter (k + 1) v, 0 ≤ ∏ w, cubeWtR (c w)) :
    0 < vanMass (k + 1) v := by
  classical
  rw [vanMass_eq_vanFilter]
  have h0mem : (0 : Fin (k + 1) → ℤ) ∈ vanFilter (k + 1) v := by
    rw [mem_vanFilter]
    exact ⟨fun w => by simp, by simp⟩
  have hz : (∏ w, cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5 / 2 : ℝ) ^ (k + 1) := by
    have hpt : ∀ w, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = (5 / 2 : ℝ) := fun w => by
      rw [Pi.zero_apply]; norm_num [cubeWtR]
    rw [Finset.prod_congr rfl (fun w _ => hpt w), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hle : (∏ w, cubeWtR ((0 : Fin (k + 1) → ℤ) w))
      ≤ ∑ c ∈ vanFilter (k + 1) v, ∏ w, cubeWtR (c w) :=
    Finset.single_le_sum (fun c hc => hnn c hc) h0mem
  have : (0 : ℝ) < ∏ w, cubeWtR ((0 : Fin (k + 1) → ℤ) w) := by rw [hz]; positivity
  linarith

set_option maxHeartbeats 800000 in
/-- **The all-odd cube floor.**  A positive family of `k+1` runners
(`4 ≤ k ≤ 7`) all of whose velocities are odd meets the floor `1/(k+2)`.
No strong-freeness is needed: parity alone makes every van product
nonnegative, and the subfamily-mass count closes the certificate. -/
theorem cube_floor_allodd {k : ℕ} (hk4 : 4 ≤ k) (hk7 : k ≤ 7)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hodd : ∀ i, Odd (v i)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  have hnn : ∀ c ∈ vanFilter (k + 1) v, 0 ≤ ∏ w, cubeWtR (c w) := by
    intro c hc
    rw [mem_vanFilter] at hc
    obtain ⟨hbox, hvan⟩ := hc
    have hv1 : ∀ w, ((v w : ℤ) : ZMod 2) = 1 := by
      intro w
      obtain ⟨t, ht⟩ := hodd w
      rw [ht]; push_cast
      rw [show (2 : ZMod 2) = 0 from by decide]
      ring
    have key : ((∑ w, c w : ℤ) : ZMod 2) = 0 := by
      have h1 : ((∑ w, c w * v w : ℤ) : ZMod 2) = 0 := by rw [hvan]; simp
      push_cast at h1 ⊢
      rw [← h1]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [hv1 w, mul_one]
    have hpar : Even (∑ w, c w) := by
      obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ w, c w) 2).mp key
      exact ⟨d, by rw [hd]; push_cast; ring⟩
    exact cubeWtR_prod_nonneg_of_even c hbox hpar
  refine cube_floor_of_cert hk4 v hv ?_
  have hbound := subfamily_sum_le_allodd v hnn
  have hpos := vanMass_pos_allodd v hnn
  have hcoef : cubeEps k * ((2 / 5 : ℝ) * ((k : ℝ) + 1)) < 1 := by
    interval_cases k <;> norm_num [cubeEps]
  have heps0 : (0 : ℝ) ≤ cubeEps k := by interval_cases k <;> norm_num [cubeEps]
  calc cubeEps k * (∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')))
      ≤ cubeEps k * ((2 / 5 : ℝ) * ((k : ℝ) + 1) * vanMass (k + 1) v) :=
        mul_le_mul_of_nonneg_left hbound heps0
    _ = (cubeEps k * ((2 / 5 : ℝ) * ((k : ℝ) + 1))) * vanMass (k + 1) v := by ring
    _ < 1 * vanMass (k + 1) v := mul_lt_mul_of_pos_right hcoef hpos
    _ = vanMass (k + 1) v := one_mul _

end LRSpectrumFull
