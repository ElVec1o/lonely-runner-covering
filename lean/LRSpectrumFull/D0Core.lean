/-
# D0 certificate: definitions

A "depth-0 certificate" for four positive integer speeds `v` is three integer vectors `k1 k2 k3 : Fin 4 → ℤ`
with `det [v | k1 | k2 | k3] ≠ 0` and, for each of the six pairs `i < j`,
`5 * (|g1| + |g2| + |g3|) ≤ 3 * (v i + v j)`, where `g_l = k_l j * v i - k_l i * v j`.
Source of the certificate: `private/INVENTION_2026_11/ROOMS/CERT_FEASIBILITY_2026_11_13.md`, section 1
(`zono.rs::passes`, which tests the same inequalities in the sign-pattern form).
Everything here is decidable on integers (kernel `decide`).
-/
import LRSpectrumFull.TPSmall

namespace LRSpectrumFull
namespace D0

/-- 3x3 determinant by the rule of Sarrus-free expansion. -/
def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- 4x4 determinant, Laplace expansion along row 0. -/
def det4 {R : Type*} [CommRing R] (m : Fin 4 → Fin 4 → R) : R :=
  m 0 0 * det3 (m 1 1) (m 1 2) (m 1 3) (m 2 1) (m 2 2) (m 2 3) (m 3 1) (m 3 2) (m 3 3)
  - m 0 1 * det3 (m 1 0) (m 1 2) (m 1 3) (m 2 0) (m 2 2) (m 2 3) (m 3 0) (m 3 2) (m 3 3)
  + m 0 2 * det3 (m 1 0) (m 1 1) (m 1 3) (m 2 0) (m 2 1) (m 2 3) (m 3 0) (m 3 1) (m 3 3)
  - m 0 3 * det3 (m 1 0) (m 1 1) (m 1 2) (m 2 0) (m 2 1) (m 2 2) (m 3 0) (m 3 1) (m 3 2)

theorem det4_eq {R : Type*} [CommRing R] (m : Fin 4 → Fin 4 → R) :
    (Matrix.of m).det = det4 m := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, det4, det3, Fin.succAbove]
  ring

/-- determinant of the integer matrix with columns `v, k1, k2, k3` -/
def detC (v k1 k2 k3 : Fin 4 → ℤ) : ℤ :=
  det4 (fun r c => ![v r, k1 r, k2 r, k3 r] c)

/-- the 2x2 minor `k_j v_i - k_i v_j` -/
def gf (v k : Fin 4 → ℤ) (i j : Fin 4) : ℤ := k j * v i - k i * v j

/-- `|g1| + |g2| + |g3|` -/
def sumG (v k1 k2 k3 : Fin 4 → ℤ) (i j : Fin 4) : ℤ :=
  |gf v k1 i j| + |gf v k2 i j| + |gf v k3 i j|

/-- The depth-0 certificate predicate. All six inequalities are non-strict. -/
def D0cert (v k1 k2 k3 : Fin 4 → ℤ) : Prop :=
  detC v k1 k2 k3 ≠ 0 ∧
  5 * sumG v k1 k2 k3 0 1 ≤ 3 * (v 0 + v 1) ∧
  5 * sumG v k1 k2 k3 0 2 ≤ 3 * (v 0 + v 2) ∧
  5 * sumG v k1 k2 k3 0 3 ≤ 3 * (v 0 + v 3) ∧
  5 * sumG v k1 k2 k3 1 2 ≤ 3 * (v 1 + v 2) ∧
  5 * sumG v k1 k2 k3 1 3 ≤ 3 * (v 1 + v 3) ∧
  5 * sumG v k1 k2 k3 2 3 ≤ 3 * (v 2 + v 3)

instance (v k1 k2 k3 : Fin 4 → ℤ) : Decidable (D0cert v k1 k2 k3) := by
  unfold D0cert; infer_instance

theorem sumG_comm (v k1 k2 k3 : Fin 4 → ℤ) (i j : Fin 4) :
    sumG v k1 k2 k3 i j = sumG v k1 k2 k3 j i := by
  have h : ∀ k : Fin 4 → ℤ, |gf v k i j| = |gf v k j i| := fun k => by
    unfold gf; exact abs_sub_comm _ _
  unfold sumG; rw [h k1, h k2, h k3]

theorem sumG_self (v k1 k2 k3 : Fin 4 → ℤ) (i : Fin 4) : sumG v k1 k2 k3 i i = 0 := by
  simp [sumG, gf]

/-- the six inequalities hold for every ordered pair -/
theorem pair_all {v k1 k2 k3 : Fin 4 → ℤ} (hv : ∀ i, 0 < v i) (h : D0cert v k1 k2 k3) (i j : Fin 4) :
    5 * sumG v k1 k2 k3 i j ≤ 3 * (v i + v j) := by
  obtain ⟨-, h01, h02, h03, h12, h13, h23⟩ := h
  have c := sumG_comm v k1 k2 k3
  have s := sumG_self v k1 k2 k3
  have p0 := hv 0; have p1 := hv 1; have p2 := hv 2; have p3 := hv 3
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | (rw [s]; omega)
    | omega
    | (rw [c]; omega)

end D0
end LRSpectrumFull
