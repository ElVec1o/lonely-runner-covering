/-
# Theorem R5 (real phases), module W: Lemma 4 (window) and Lemma 6 (exact coincidence) with real phases

Paper proof: ROOMS/OPUS_REAL_PHASES_2026_11_12.md, Lemma 4 and Lemma 6 (centres `σ`, slow phase `φ_d` real).
Real twins of `TPFourCoset.lemma4` and `TPFourCoincide.exists_exact`; `σ` is the full phase difference
(the old `σ / 5`), `φ_d` the phase of the slow runner.  The coset lemma `exists_coset_far` and the perturbation
lemma `exists_perturb` are reused unchanged (they already take a real `y`).

* `coset_branchR_ne` : `D ∤ w`: some `x_k = (k - σ)/D` has `‖w x_k + φ_d‖ ≥ 1/5`.
* `lemma4R`          : `D ≠ 0`, `w ≥ 1`: some `x`, `m` with `|D x + σ - m| ≤ 1/5` and `‖w x + φ_d‖ ≥ 1/5`.
* `L6`, `exists_exactR` : if Lemma 6 does not fail for `(D, σ)`, some `x` has `D x + σ ∈ ℤ` and `‖w x + φ_d‖ ≥ 1/5`.
-/
import LRSpectrumFull.RFiveBase

namespace LRSpectrumFull

lemma coset_branchR (D : ℤ) (hD : 0 < D) (w : ℕ) (hdvd : ¬ D ∣ (w : ℤ)) (σ φd : ℝ) :
    ∃ k : ℤ, 1 / 5 ≤ tpDist ((w : ℝ) * (((k : ℝ) - σ) / D) + φd) := by
  obtain ⟨g, D', w', hg, hgcd, hD', hw'⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (w : ℤ) hD.ne')
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hD'pos : 0 < D' := by
    by_contra hle
    push Not at hle
    nlinarith
  have hcop : IsCoprime D' w' := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hD'2 : 2 ≤ D' := by
    by_contra hlt
    have h1 : D' = 1 := by omega
    apply hdvd
    exact ⟨w', by rw [hw', hD', h1]; ring⟩
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨k, hk⟩ := exists_coset_far D' w' hD'2 hcop (φd - (w : ℝ) * σ / D)
  refine ⟨k, ?_⟩
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hD'R : (D' : ℝ) ≠ 0 := by exact_mod_cast hD'pos.ne'
  have hDe : (D : ℝ) = D' * g := by exact_mod_cast hD'
  have hwe : (w : ℝ) = w' * g := by exact_mod_cast hw'
  have e : (w : ℝ) * (((k : ℝ) - σ) / D) + φd
      = (φd - (w : ℝ) * σ / D) + ((w' * k : ℤ) : ℝ) / (D' : ℝ) := by
    rw [hDe, hwe]; push_cast; field_simp; ring
  rw [e]
  exact hk

lemma coset_branchR_ne (D : ℤ) (hD : D ≠ 0) (w : ℕ) (hdvd : ¬ D ∣ (w : ℤ)) (σ φd : ℝ) :
    ∃ k : ℤ, 1 / 5 ≤ tpDist ((w : ℝ) * (((k : ℝ) - σ) / D) + φd) := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨k, hk⟩ := coset_branchR (-D) (by omega) w (fun hd => hdvd (neg_dvd.mp hd)) (-σ) φd
    refine ⟨-k, ?_⟩
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    have e : (((-k : ℤ) : ℝ) - σ) / D = ((k : ℝ) - (-σ)) / ((-D : ℤ) : ℝ) := by
      push_cast
      rw [div_eq_div_iff hDR (neg_ne_zero.mpr hDR)]
      ring
    rw [e]
    exact hk
  · exact coset_branchR D h w hdvd σ φd

lemma lemma4R_pos (D : ℤ) (hD : 0 < D) (w : ℕ) (hw : 1 ≤ w) (σ φd : ℝ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + σ - m| ≤ 1 / 5 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  by_cases hdvd : D ∣ (w : ℤ)
  · obtain ⟨w2, hw2⟩ := hdvd
    have hw2pos : 1 ≤ w2 := by
      by_contra hlt
      have : w2 ≤ 0 := by omega
      have : D * w2 ≤ 0 := by nlinarith
      omega
    have hDw : (D : ℝ) ≤ w := by
      have : (w : ℝ) = D * w2 := by exact_mod_cast hw2
      have : (1 : ℝ) ≤ w2 := by exact_mod_cast hw2pos
      nlinarith
    have hwne : (w : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < w).ne'
    set x0 : ℝ := -σ / D with hx0
    have hDx0 : (D : ℝ) * x0 + σ = 0 := by
      have := mul_div_cancel₀ (-σ) hDR.ne'
      rw [hx0]; linarith
    obtain ⟨δ, hδ, hfar⟩ := exists_perturb ((w : ℝ) * x0 + φd)
    have hwd : (w : ℝ) * (δ / w) = δ := mul_div_cancel₀ _ hwne
    refine ⟨x0 + δ / w, 0, ?_, ?_⟩
    · have e : (D : ℝ) * (x0 + δ / w) + σ - ((0 : ℤ) : ℝ) = D * δ / w := by
        push_cast; linear_combination hDx0
      rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < w), abs_mul, abs_of_pos hDR,
        div_le_iff₀ (by linarith : (0 : ℝ) < w)]
      have := mul_le_mul_of_nonneg_left hδ hDR.le
      nlinarith
    · have e : (w : ℝ) * (x0 + δ / w) + φd = ((w : ℝ) * x0 + φd) + δ := by
        rw [mul_add, hwd]; ring
      rw [e]
      exact hfar
  · obtain ⟨k, hk⟩ := coset_branchR D hD w hdvd σ φd
    refine ⟨((k : ℝ) - σ) / D, k, ?_, hk⟩
    have := mul_div_cancel₀ ((k : ℝ) - σ) hDR.ne'
    have h0 : (D : ℝ) * (((k : ℝ) - σ) / D) + σ - k = 0 := by linarith
    rw [h0]; norm_num

lemma lemma4R (D : ℤ) (hD : D ≠ 0) (w : ℕ) (hw : 1 ≤ w) (σ φd : ℝ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + σ - m| ≤ 1 / 5 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨x, m, h1, h2⟩ := lemma4R_pos (-D) (by omega) w hw (-σ) φd
    refine ⟨x, -m, ?_, h2⟩
    have : (D : ℝ) * x + σ - ((-m : ℤ) : ℝ) = -(((-D : ℤ) : ℝ) * x + (-σ) - m) := by
      push_cast; ring
    rw [this, abs_neg]; exact h1
  · exact lemma4R_pos D h w hw σ φd

/-- "Lemma 6 fails for `(D, σ)`": `D ∣ w`, `w = D t`, and the single slow value `φ_d - t σ` is within `1/5` of `ℤ`. -/
def L6 (D : ℤ) (w : ℕ) (σ φd : ℝ) : Prop :=
  ∃ t : ℤ, (w : ℤ) = D * t ∧ tpDist (φd - (t : ℝ) * σ) < 1 / 5

lemma exists_exactR (D : ℤ) (hD : D ≠ 0) (w : ℕ) (σ φd : ℝ) (hnot : ¬ L6 D w σ φd) :
    ∃ x : ℝ, ∃ m : ℤ, (D : ℝ) * x + σ = m ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  by_cases hdvd : D ∣ (w : ℤ)
  · obtain ⟨t, ht⟩ := hdvd
    have hge : 1 / 5 ≤ tpDist (φd - (t : ℝ) * σ) := by
      by_contra hlt
      exact hnot ⟨t, ht, not_le.mp hlt⟩
    have hx := mul_div_cancel₀ (-σ) hDR
    refine ⟨-σ / D, 0, ?_, ?_⟩
    · push_cast
      linarith
    · have htR : (w : ℝ) = D * t := by exact_mod_cast ht
      have e : (w : ℝ) * (-σ / D) + φd = φd - (t : ℝ) * σ := by
        rw [htR]
        linear_combination (t : ℝ) * hx
      rw [e]
      exact hge
  · obtain ⟨k, hk⟩ := coset_branchR_ne D hD w hdvd σ φd
    refine ⟨((k : ℝ) - σ) / D, k, ?_, hk⟩
    have := mul_div_cancel₀ ((k : ℝ) - σ) hDR
    linarith

end LRSpectrumFull
