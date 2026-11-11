/-
# TP'(4), module M5: Lemma 4 (two-runner window) and the coset lemma

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 4 (with the v2 fixes 4 and 5: representative
`c_0 = w x_0 - round (w x_0)`, boundary `1/5` included).

* `far_of_between`    : `1/5 ≤ y - n0 ≤ 4/5` gives `1/5 ≤ tpDist y`.
* `exists_coset_far`  : (Bezout, once) for coprime `p ≥ 2`, `q` and any real `y`, some integer `k` has
  `1/5 ≤ tpDist (y + q k / p)`; the values `q k / p` run over all multiples of `1/p` modulo 1.
* `lemma4`            : for `D ≠ 0`, `w ≥ 1`, `σ` integers there are `x` and an integer `m` with
  `|D x + σ/5 - m| ≤ 1/5` and `1/5 ≤ tpDist (w x)`.
-/
import LRSpectrumFull.TPFourBridge

namespace LRSpectrumFull

lemma far_of_between (y : ℝ) (n0 : ℤ) (h1 : 1 / 5 ≤ y - n0) (h2 : y - n0 ≤ 4 / 5) :
    1 / 5 ≤ tpDist y := by
  unfold tpDist
  rcases le_or_gt (round y) n0 with h | h
  · have h' : ((round y : ℤ) : ℝ) ≤ n0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h'' : n0 + 1 ≤ round y := h
    have h' : (n0 : ℝ) + 1 ≤ ((round y : ℤ) : ℝ) := by exact_mod_cast h''
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma bezout_solve (p q : ℤ) (h : IsCoprime p q) (r : ℤ) : ∃ k b : ℤ, q * k = r + p * b := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨b * r, -(a * r), by linear_combination r * hab⟩

lemma exists_coset_far (p q : ℤ) (hp : 2 ≤ p) (hc : IsCoprime p q) (y : ℝ) :
    ∃ k : ℤ, 1 / 5 ≤ tpDist (y + ((q * k : ℤ) : ℝ) / (p : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  set r : ℤ := ⌈(1 / 5 - y) * p⌉ with hr
  obtain ⟨k, b, hkb⟩ := bezout_solve p q hc r
  refine ⟨k, far_of_between _ b ?_ ?_⟩
  all_goals
    have hz : ((q * k : ℤ) : ℝ) = (r : ℝ) + (p : ℝ) * b := by exact_mod_cast hkb
    have e : y + ((q * k : ℤ) : ℝ) / (p : ℝ) - b = y + (r : ℝ) / p := by
      rw [hz]; field_simp; ring
    rw [e]
    have r1 : (1 / 5 - y) * p ≤ r := Int.le_ceil _
    have r2 : (r : ℝ) < (1 / 5 - y) * p + 1 := Int.ceil_lt_add_one _
  · have : 1 / 5 - y ≤ (r : ℝ) / p := by rw [le_div_iff₀ hpos]; exact r1
    linarith
  · have : (r : ℝ) / p < 7 / 10 - y := by
      rw [div_lt_iff₀ hpos]; nlinarith
    linarith

/-- The coset branch (`D ∤ w`): some `x_k = (k - σ/5)/D` puts the pinned runner far from 0. -/
lemma coset_branch (D : ℤ) (hD : 0 < D) (w : ℕ) (hdvd : ¬ D ∣ (w : ℤ)) (σ : ℤ) :
    ∃ k : ℤ, 1 / 5 ≤ tpDist ((w : ℝ) * (((k : ℝ) - σ / 5) / D)) := by
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
  obtain ⟨k, hk⟩ := exists_coset_far D' w' hD'2 hcop (-((w : ℝ) * ((σ : ℝ) / 5) / D))
  refine ⟨k, ?_⟩
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hD'R : (D' : ℝ) ≠ 0 := by exact_mod_cast hD'pos.ne'
  have hDe : (D : ℝ) = D' * g := by exact_mod_cast hD'
  have hwe : (w : ℝ) = w' * g := by exact_mod_cast hw'
  have e : (w : ℝ) * (((k : ℝ) - σ / 5) / D)
      = -((w : ℝ) * ((σ : ℝ) / 5) / D) + ((w' * k : ℤ) : ℝ) / (D' : ℝ) := by
    rw [hDe, hwe]; push_cast; field_simp; ring
  rw [e]
  exact hk

lemma lemma4_pos (D : ℤ) (hD : 0 < D) (w : ℕ) (hw : 1 ≤ w) (σ : ℤ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + (σ : ℝ) / 5 - m| ≤ 1 / 5 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  by_cases hdvd : D ∣ (w : ℤ)
  · -- w = D * w'': the perturbation branch
    obtain ⟨w2, hw2⟩ := hdvd
    have hw2pos : 1 ≤ w2 := by
      by_contra hlt
      have : w2 ≤ 0 := by omega
      have : D * w2 ≤ 0 := by nlinarith
      omega
    have hDw : (D : ℝ) ≤ w := by
      have : (w : ℝ) = D * w2 := by exact_mod_cast hw2
      have : (1 : ℝ) ≤ w2 := by exact_mod_cast hw2pos
      nlinarith
    set x0 : ℝ := -((σ : ℝ) / 5) / D with hx0
    have hDx0 : (D : ℝ) * x0 + σ / 5 = 0 := by rw [hx0]; field_simp; ring
    set y : ℝ := (w : ℝ) * x0 with hy
    by_cases hfar : 1 / 5 ≤ tpDist y
    · exact ⟨x0, 0, by rw [hDx0]; norm_num, hfar⟩
    · push Not at hfar
      set c0 : ℝ := y - round y with hc0
      have hc0abs : |c0| < 1 / 5 := hfar
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hc0abs
      set δ : ℝ := (if 0 ≤ c0 then 1 / 5 else -(1 / 5)) - c0 with hδ
      have hδb : |δ| ≤ 1 / 5 := by
        rw [hδ]; split_ifs with h
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      refine ⟨x0 + δ / w, 0, ?_, ?_⟩
      · have e : (D : ℝ) * (x0 + δ / w) + σ / 5 - ((0 : ℤ) : ℝ) = D * δ / w := by
          push_cast; linear_combination hDx0
        rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < w), abs_mul, abs_of_pos hDR,
          div_le_iff₀ (by linarith : (0 : ℝ) < w)]
        have := mul_le_mul_of_nonneg_left hδb hDR.le
        nlinarith
      · have e : (w : ℝ) * (x0 + δ / w) = y + δ := by
          rw [hy]; field_simp
        rw [e, hδ]
        split_ifs with h
        · refine far_of_between _ (round y) ?_ ?_ <;> linarith
        · refine far_of_between _ (round y - 1) ?_ ?_ <;> push_cast <;> linarith
  · obtain ⟨k, hk⟩ := coset_branch D hD w hdvd σ
    refine ⟨((k : ℝ) - σ / 5) / D, k, ?_, hk⟩
    have : (D : ℝ) * (((k : ℝ) - σ / 5) / D) + σ / 5 - k = 0 := by field_simp; ring
    rw [this]; norm_num

lemma lemma4 (D : ℤ) (hD : D ≠ 0) (w : ℕ) (hw : 1 ≤ w) (σ : ℤ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + (σ : ℝ) / 5 - m| ≤ 1 / 5 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x) := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨x, m, h1, h2⟩ := lemma4_pos (-D) (by omega) w hw (-σ)
    refine ⟨x, -m, ?_, h2⟩
    have : (D : ℝ) * x + σ / 5 - ((-m : ℤ) : ℝ) = -(((-D : ℤ) : ℝ) * x + ((-σ : ℤ) : ℝ) / 5 - m) := by
      push_cast; ring
    rw [this, abs_neg]; exact h1
  · exact lemma4_pos D h w hw σ

end LRSpectrumFull
