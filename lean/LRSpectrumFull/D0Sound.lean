/-
# D0 certificate: soundness

`d0_sound`: if `D0cert v k1 k2 k3` and the speeds are positive, then for EVERY real phase vector `φ`
there is a real `t` with `1/5 ≤ tpDist (v i * t + φ i)` for all `i`.  All inequalities are closed.
Uses only: `0 < v i` (to divide) and `D0cert`; distinctness and gcd are not used.

Proof (hand proof of CERT_FEASIBILITY_2026_11_13 section 1): solve `φ - 1/2 = a0 v + Σ a_l k_l` (det ≠ 0),
round `a_l = n_l + y_l`, `|y_l| ≤ 1/2`; `X = Σ y_l k_l`; the one-dimensional intervals
`|X_i + s v_i| ≤ 3/10` have a common point `s` (largest left end ≤ every right end, which is the pair
inequality); `t = s - a0`.
-/
import LRSpectrumFull.D0Core

namespace LRSpectrumFull
namespace D0

open Matrix

theorem tpDist_ge_of_frac (x : ℝ) (n : ℤ) (h1 : 1 / 5 ≤ x - n) (h2 : x - n ≤ 4 / 5) :
    1 / 5 ≤ tpDist x := by
  unfold tpDist
  rcases le_or_gt (round x) n with hm | hm
  · have : ((round x : ℤ) : ℝ) ≤ n := by exact_mod_cast hm
    have := le_abs_self (x - round x)
    linarith
  · have hm' : n + 1 ≤ round x := hm
    have : ((n + 1 : ℤ) : ℝ) ≤ round x := by exact_mod_cast hm'
    push_cast at this
    have := neg_le_abs (x - round x)
    linarith

theorem solve4 (v k1 k2 k3 : Fin 4 → ℤ) (hdet : detC v k1 k2 k3 ≠ 0) (ψ : Fin 4 → ℝ) :
    ∃ a : Fin 4 → ℝ, ∀ r, ψ r = a 0 * v r + a 1 * k1 r + a 2 * k2 r + a 3 * k3 r := by
  set M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun r c => ![(v r : ℝ), k1 r, k2 r, k3 r] c with hM
  have hd : M.det ≠ 0 := by
    rw [hM, det4_eq]
    have : det4 (fun r c => ![(v r : ℝ), k1 r, k2 r, k3 r] c) = ((detC v k1 k2 k3 : ℤ) : ℝ) := by
      simp [detC, det4, det3]
    rw [this]; exact_mod_cast hdet
  refine ⟨M⁻¹ *ᵥ ψ, fun r => ?_⟩
  have h1 : M *ᵥ (M⁻¹ *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.one_mulVec]
  have h2 := congrFun h1 r
  rw [← h2]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hM]
  ring

theorem d0_sound (v k1 k2 k3 : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (h : D0cert v k1 k2 k3)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, 1 / 5 ≤ tpDist ((v i : ℝ) * t + φ i) := by
  have hall := pair_all hpos h
  obtain ⟨a, ha⟩ := solve4 v k1 k2 k3 h.1 (fun r => φ r - 1 / 2)
  set y : Fin 4 → ℝ := fun l => a l - round (a l) with hy
  have hyb : ∀ l, |y l| ≤ 1 / 2 := fun l => abs_sub_round (a l)
  set X : Fin 4 → ℝ := fun i => y 1 * k1 i + y 2 * k2 i + y 3 * k3 i with hX
  set K : Fin 4 → ℤ := fun i => round (a 1) * k1 i + round (a 2) * k2 i + round (a 3) * k3 i with hK
  have hψ : ∀ i, φ i = a 0 * v i + X i + K i + 1 / 2 := by
    intro i
    have := ha i
    simp only [hX, hK, hy]
    push_cast
    linarith
  have hvpos : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hpos i
  -- the pair inequality for X
  have hpair : ∀ i j, |X j * v i - X i * v j| ≤ 3 / 10 * (v i + v j) := by
    intro i j
    have e : X j * v i - X i * v j =
        y 1 * (gf v k1 i j : ℝ) + y 2 * (gf v k2 i j : ℝ) + y 3 * (gf v k3 i j : ℝ) := by
      simp only [hX, gf]; push_cast; ring
    have hb : ∀ (l : Fin 4) (g : ℤ), |y l * (g : ℝ)| ≤ 1 / 2 * |(g : ℝ)| := by
      intro l g
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hyb l) (abs_nonneg _)
    have hS : (5 : ℝ) * (|(gf v k1 i j : ℝ)| + |(gf v k2 i j : ℝ)| + |(gf v k3 i j : ℝ)|)
        ≤ 3 * (v i + v j) := by
      have := hall i j
      unfold sumG at this
      have h' : ((5 * (|gf v k1 i j| + |gf v k2 i j| + |gf v k3 i j|) : ℤ) : ℝ)
          ≤ ((3 * (v i + v j) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
    rw [e]
    calc |y 1 * (gf v k1 i j : ℝ) + y 2 * (gf v k2 i j : ℝ) + y 3 * (gf v k3 i j : ℝ)|
        ≤ |y 1 * (gf v k1 i j : ℝ) + y 2 * (gf v k2 i j : ℝ)| + |y 3 * (gf v k3 i j : ℝ)| :=
          abs_add_le _ _
      _ ≤ |y 1 * (gf v k1 i j : ℝ)| + |y 2 * (gf v k2 i j : ℝ)| + |y 3 * (gf v k3 i j : ℝ)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 1 / 2 * |(gf v k1 i j : ℝ)| + 1 / 2 * |(gf v k2 i j : ℝ)| + 1 / 2 * |(gf v k3 i j : ℝ)| := by
          have := hb 1 (gf v k1 i j); have := hb 2 (gf v k2 i j); have := hb 3 (gf v k3 i j)
          linarith
      _ ≤ 3 / 10 * (v i + v j) := by linarith
  -- one-dimensional Helly step: the largest left end is a common point
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ
    (fun i => (-3 / 10 - X i) / (v i : ℝ)) Finset.univ_nonempty
  set s : ℝ := (-3 / 10 - X i0) / (v i0 : ℝ) with hs
  have hsv : s * v i0 = -3 / 10 - X i0 := by
    rw [hs]; exact div_mul_cancel₀ _ (hvpos i0).ne'
  have hs_lo : ∀ j, -3 / 10 ≤ X j + s * v j := fun j => by
    have h1 := hi0 j (Finset.mem_univ _)
    rw [div_le_iff₀ (hvpos j)] at h1
    linarith
  have hs_hi : ∀ j, X j + s * v j ≤ 3 / 10 := fun j => by
    have h2 := (abs_le.mp (hpair i0 j)).2
    by_contra hcon
    replace hcon := not_le.mp hcon
    have e : (v i0 : ℝ) * (X j + s * v j - 3 / 10) =
        (X j * v i0 - X i0 * v j) - 3 / 10 * (v i0 + v j) := by
      linear_combination (v j : ℝ) * hsv
    have := mul_pos (hvpos i0) (sub_pos.mpr hcon)
    linarith
  refine ⟨s - a 0, fun i => ?_⟩
  apply tpDist_ge_of_frac _ (K i)
  · have := hs_lo i; have := hψ i
    nlinarith
  · have := hs_hi i; have := hψ i
    nlinarith

end D0
end LRSpectrumFull
