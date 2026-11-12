/-
# RQ3, module S: the mixed-threshold sweep for three runners (real phases)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem Q3" (needs window threshold 7/30
for the third runner) and ROOMS/R7_LEAN_AND_Q3_COST_2026_11_12.md, Task B.  The `1/4` sweep of `TPThreeA`
(`pairBox`, `cSweep`, `sweepCase`) is reused by import and not edited.  Here: the same sweep with arbitrary
thresholds `τa, τb, τc ≤ 1/2`, obtained from `pairBox` by shifting the phases, and a new `cSweep`.

* `Q3GoodT τ y`      : `y ∈ [τ, 1 - τ] + ℤ`.
* `q3PairBox`        : `pairBox` for the arcs `[τa, τa + W]`, `[τb, τb + H]`.
* `q3CSweep`         : the runner `c` is made `τ`-good by a shift `s ∈ [0, 2τ]`.
* `q3Sweep`          : sorted `a < b < c`, `gcd a b` arbitrary in the hypothesis `gcd ≤ b W + a H`.
* `q3Sweep123`       : the speeds `(1, 2, 3)`, thresholds `1/5, 1/5, 7/30` in any placement of the `7/30`.
-/
import LRSpectrumFull.TPThreeA

namespace LRSpectrumFull

/-- `y ∈ [τ, 1 - τ] + ℤ` -/
def Q3GoodT (τ y : ℝ) : Prop := ∃ w : ℤ, τ ≤ y - w ∧ y - w ≤ 1 - τ

/-- the three allowed threshold patterns: exactly one `7/30`, the other two `1/5` -/
def Q3Pat (x y z : ℝ) : Prop :=
  (x = 1 / 5 ∧ y = 1 / 5 ∧ z = 7 / 30) ∨ (x = 7 / 30 ∧ y = 1 / 5 ∧ z = 1 / 5) ∨
    (x = 1 / 5 ∧ y = 7 / 30 ∧ z = 1 / 5)

lemma q3Pat_perm {x y z : ℝ} (h : Q3Pat x y z) :
    Q3Pat y x z ∧ Q3Pat x z y ∧ Q3Pat y z x ∧ Q3Pat z x y ∧ Q3Pat z y x := by
  unfold Q3Pat at *
  tauto

lemma q3Pat_le {x y z : ℝ} (h : Q3Pat x y z) :
    (0 ≤ x ∧ x ≤ 1 / 4) ∧ (0 ≤ y ∧ y ≤ 1 / 4) ∧ (0 ≤ z ∧ z ≤ 1 / 4) := by
  unfold Q3Pat at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h1 h2 h3 <;> norm_num

lemma q3_tpDist_of_goodT {τ y : ℝ} (h : Q3GoodT τ y) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) :
    τ ≤ tpDist y := by
  obtain ⟨w, h1', h2'⟩ := h
  exact tpDist_ge_win τ y w h1' h2' h0 h1

lemma q3_goodT_of_goodQ {y : ℝ} (h : GoodQ y) {τ : ℝ} (hτ : τ ≤ 1 / 4) : Q3GoodT τ y := by
  obtain ⟨w, h1, h2⟩ := h
  exact ⟨w, by linarith, by linarith⟩

lemma q3PairBox (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τa τb W H α β : ℝ) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (hg : (Nat.gcd a b : ℝ) ≤ b * W + a * H) :
    ∃ (t : ℝ) (j k : ℤ), τa ≤ a * t + α - j ∧ a * t + α - j ≤ τa + W ∧
      τb ≤ b * t + β - k ∧ b * t + β - k ≤ τb + H := by
  obtain ⟨t, j, k, h1, h2, h3, h4⟩ :=
    pairBox a b ha hb W H (α + (1 / 4 - τa)) (β + (1 / 4 - τb)) hW hH hg
  refine ⟨t, j, k, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma q3CSweep (τ z0 : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * τ ∧ Q3GoodT τ (z0 + s) := by
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = ⌈z0 - (1 - τ)⌉ := ⟨_, rfl⟩
  have e1 : z0 - (1 - τ) ≤ w := by rw [hw]; exact Int.le_ceil _
  have e2 : (w : ℝ) < z0 - (1 - τ) + 1 := by rw [hw]; exact Int.ceil_lt_add_one _
  by_cases h : (w : ℝ) + τ ≤ z0
  · exact ⟨0, le_refl _, by linarith, w, by linarith, by linarith⟩
  · rw [not_le] at h
    exact ⟨w + τ - z0, by linarith, by linarith, w, by linarith, by linarith⟩

lemma q3Sweep (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (τa τb τc : ℝ)
    (hτc0 : 0 ≤ τc) (hτc : τc ≤ 1 / 2)
    (hW : 0 ≤ 1 - 2 * τa - ((a : ℝ) / c) * (2 * τc))
    (hH : 0 ≤ 1 - 2 * τb - ((b : ℝ) / c) * (2 * τc))
    (hg : (Nat.gcd a b : ℝ) ≤ b * (1 - 2 * τa - ((a : ℝ) / c) * (2 * τc)) +
      a * (1 - 2 * τb - ((b : ℝ) / c) * (2 * τc))) (α β γ : ℝ) :
    ∃ τ : ℝ, Q3GoodT τa ((a : ℝ) * τ + α) ∧ Q3GoodT τb ((b : ℝ) * τ + β) ∧
      Q3GoodT τc ((c : ℝ) * τ + γ) := by
  have hb : 0 < b := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  obtain ⟨t, j, k, h1, h2, h3, h4⟩ := q3PairBox a b ha hb τa τb _ _ α β hW hH hg
  obtain ⟨s, hs0, hs1, hgood⟩ := q3CSweep τc ((c : ℝ) * t + γ) hτc0 hτc
  have hqa0 : 0 ≤ (a : ℝ) * (s / c) := by positivity
  have hqb0 : 0 ≤ (b : ℝ) * (s / c) := by positivity
  have hqa : (a : ℝ) * (s / c) ≤ ((a : ℝ) / c) * (2 * τc) := by
    have e : (a : ℝ) * (s / c) = ((a : ℝ) / c) * s := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hqb : (b : ℝ) * (s / c) ≤ ((b : ℝ) / c) * (2 * τc) := by
    have e : (b : ℝ) * (s / c) = ((b : ℝ) / c) * s := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hs1 (by positivity)
  refine ⟨t + s / c, ⟨j, ?_, ?_⟩, ⟨k, ?_, ?_⟩, ?_⟩
  · have : (a : ℝ) * (t + s / c) + α - j = ((a : ℝ) * t + α - j) + a * (s / c) := by ring
    rw [this]; linarith
  · have : (a : ℝ) * (t + s / c) + α - j = ((a : ℝ) * t + α - j) + a * (s / c) := by ring
    rw [this]; linarith
  · have : (b : ℝ) * (t + s / c) + β - k = ((b : ℝ) * t + β - k) + b * (s / c) := by ring
    rw [this]; linarith
  · have : (b : ℝ) * (t + s / c) + β - k = ((b : ℝ) * t + β - k) + b * (s / c) := by ring
    rw [this]; linarith
  · have : (c : ℝ) * (t + s / c) + γ = ((c : ℝ) * t + γ) + s := by field_simp; ring
    rw [this]; exact hgood

/-- speeds `(1, 2, 3)`: with thresholds `1/5, 1/5, 7/30` in any placement of the `7/30` there is a common time. -/
lemma q3Sweep123 (τa τb τc : ℝ) (hτ : Q3Pat τa τb τc) (α β γ : ℝ) :
    ∃ x : ℝ, Q3GoodT τa (((1 : ℕ) : ℝ) * x + α) ∧ Q3GoodT τb (((2 : ℕ) : ℝ) * x + β) ∧
      Q3GoodT τc (((3 : ℕ) : ℝ) * x + γ) := by
  have hc0 : 0 ≤ τc ∧ τc ≤ 1 / 2 := by
    obtain ⟨_, _, ⟨h0, h1⟩⟩ := q3Pat_le hτ
    constructor <;> linarith
  unfold Q3Pat at hτ
  rcases hτ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h1 h2 h3 <;>
    exact q3Sweep 1 2 3 (by norm_num) (by norm_num) (by norm_num) _ _ _ hc0.1 hc0.2
      (by norm_num) (by norm_num) (by norm_num) α β γ

end LRSpectrumFull
