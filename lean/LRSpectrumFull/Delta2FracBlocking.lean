/-
# Fractional blocking: an LP-duality certificate for the floor

A time `p/q` certifies the floor for every family avoiding its **bad-velocity set**
`BadVel(p,q) = { x : x fails the band at p/q }` (`cube_floor_of_witness`).  So a family with no
witness must *hit every* bad-velocity set — it is a transversal of that hypergraph.  A family has
only `m = k+1` velocities, so if the hypergraph's covering number exceeds `m`, no such family
exists and the floor is unconditional.

By LP duality the covering number is bounded below by the **fractional matching number**, and a
fractional matching is a finite rational certificate: weights `y_j ≥ 0` on times `p_j/q_j` with
every velocity carrying load `≤ 1`, and `∑ y_j > m`.  Then a transversal `V` would give

        ∑ y_j  ≤  ∑_j y_j·|BadVel_j ∩ V|  =  ∑_{x ∈ V} load(x)  ≤  |V| = m,

a contradiction.  Scaling by a common denominator `D` keeps everything in `ℕ`.

This is strictly stronger than exhibiting `m+1` *disjoint* bad sets (the integral matching), which
succeeds exactly when `2m+1` is prime and reproves `dense_floor_of_prime` in one paragraph.  The
fractional version additionally settles composite `2m+1` at `m = 4, 7, 12, 13`.
-/
import LRSpectrumFull.Delta2CubeWitness

namespace LRSpectrumFull

open Finset

/-- `x` clears the band at time `p/q` for target `1/(k+2)`.  Decidable, so certificates check. -/
def goodAt (k x p q : ℕ) : Bool :=
  decide (q ≤ (k + 2) * min (x * p % q) (q - x * p % q))

/-- **The fractional blocking certificate.**  Weights `y j` on times `p j / q j`, scaled by `D`:
if every velocity value in `[1, 2(k+1)]` carries load at most `D`, and the total weight exceeds
`(k+1)·D`, then every positive family of `k+1` velocities bounded by `2(k+1)` meets the floor. -/
theorem floor_of_frac_blocking {k N : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hden : ∀ i, (v i).toNat ≤ 2 * (k + 1))
    (p q y : Fin N → ℕ) (hq : ∀ j, 0 < q j) (D : ℕ)
    (hload : ∀ x : ℕ, 1 ≤ x → x ≤ 2 * (k + 1) →
      ∑ j, (if goodAt k x (p j) (q j) then 0 else y j) ≤ D)
    (hsum : (k + 1) * D < ∑ j, y j) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every time in the certificate is defeated by some velocity
  have hex : ∀ j : Fin N, ∃ i : Fin (k + 1), goodAt k (v i).toNat (p j) (q j) = false := by
    intro j
    by_contra hno
    push_neg at hno
    refine absurd (cube_floor_of_witness v hv (p j) (q j) (hq j) (fun i => ?_)) (not_le.mpr hcon)
    have := hno i
    simpa [goodAt, Bool.not_eq_false] using of_decide_eq_true (by
      simpa [goodAt] using (Bool.not_eq_false _).mp this)
  choose f hf using hex
  -- count the weight twice
  have key : (∑ j, y j) ≤ (k + 1) * D := by
    have step : ∀ i : Fin (k + 1),
        (∑ j, (if f j = i then y j else 0)) ≤ D := by
      intro i
      refine le_trans (Finset.sum_le_sum (fun j _ => ?_))
        (hload (v i).toNat (by have := hv i; omega) (hden i))
      by_cases hfj : f j = i
      · have : goodAt k (v i).toNat (p j) (q j) = false := hfj ▸ hf j
        simp [hfj, this]
      · simp [hfj]
    calc (∑ j, y j) = ∑ j, ∑ i : Fin (k + 1), (if f j = i then y j else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp
      _ = ∑ i : Fin (k + 1), ∑ j, (if f j = i then y j else 0) := Finset.sum_comm
      _ ≤ ∑ _i : Fin (k + 1), D := Finset.sum_le_sum (fun i _ => step i)
      _ = (k + 1) * D := by simp [Finset.sum_const, mul_comm]
  omega

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
/-- **Dense window at m = 4** (`2m+1 = 9`, composite): every 4 positive velocities bounded by 8 meet the
floor `1/5`.  Certificate: 5 times, common denominator 1, total weight
5/1 > 4.  Beyond `dense_floor_of_prime`, which needs `2m+1` prime. -/
theorem dense_floor_m4 (v : Fin 4 → ℤ) (hv : ∀ i, 0 < v i) (hden : ∀ i, (v i).toNat ≤ 8) :
    1 / (5 : ℝ) ≤ ML v := by
  have h := floor_of_frac_blocking (k := 3) v hv (by simpa using hden)
    ![1,1,1,1,4] ![5,10,4,3,9] ![1,1,1,1,1] (by decide) 1
    (by intro x h1 h2; interval_cases x <;> decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **Dense window at m = 7** (`2m+1 = 15`, composite): every 7 positive velocities bounded by 14 meet the
floor `1/8`.  Certificate: 9 times, common denominator 2, total weight
15/2 > 7.  Beyond `dense_floor_of_prime`, which needs `2m+1` prime. -/
theorem dense_floor_m7 (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hden : ∀ i, (v i).toNat ≤ 14) :
    1 / (8 : ℝ) ≤ ML v := by
  have h := floor_of_frac_blocking (k := 6) v hv (by simpa using hden)
    ![1,1,5,1,9,1,4,1,9] ![8,16,16,5,19,7,15,6,20] ![2,2,2,2,1,2,1,2,1] (by decide) 2
    (by intro x h1 h2; interval_cases x <;> decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **Dense window at m = 12** (`2m+1 = 25`, composite): every 12 positive velocities bounded by 24 meet the
floor `1/13`.  Certificate: 15 times, common denominator 2, total weight
25/2 > 12.  Beyond `dense_floor_of_prime`, which needs `2m+1` prime. -/
theorem dense_floor_m12 (v : Fin 12 → ℤ) (hv : ∀ i, 0 < v i) (hden : ∀ i, (v i).toNat ≤ 24) :
    1 / (13 : ℝ) ≤ ML v := by
  have h := floor_of_frac_blocking (k := 11) v hv (by simpa using hden)
    ![1,1,8,5,14,1,11,1,11,3,4,7,6,12,9] ![13,26,25,26,29,10,39,12,25,25,25,26,25,25,23] ![2,2,2,1,1,2,2,2,2,2,2,2,1,1,1] (by decide) 2
    (by intro x h1 h2; interval_cases x <;> decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **Dense window at m = 13** (`2m+1 = 27`, composite): every 13 positive velocities bounded by 26 meet the
floor `1/14`.  Certificate: 21 times, common denominator 11, total weight
145/11 > 13.  Beyond `dense_floor_of_prime`, which needs `2m+1` prime. -/
theorem dense_floor_m13 (v : Fin 13 → ℤ) (hv : ∀ i, 0 < v i) (hden : ∀ i, (v i).toNat ≤ 26) :
    1 / (14 : ℝ) ≤ ML v := by
  have h := floor_of_frac_blocking (k := 12) v hv (by simpa using hden)
    ![1,1,1,11,7,5,13,1,8,9,1,10,1,4,11,13,19,4,5,14,7] ![28,14,13,34,27,27,27,12,27,28,11,27,9,27,27,28,40,25,26,37,26] ![11,11,5,9,11,5,7,11,11,2,1,5,11,11,10,6,4,2,1,6,5] (by decide) 11
    (by intro x h1 h2; interval_cases x <;> decide) (by decide)
  norm_num at h
  exact h


end LRSpectrumFull
