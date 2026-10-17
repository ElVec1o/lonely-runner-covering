/-
# Toward Piece A: the confinement lemma

The crux of the coordinate bound. If `‖r·t‖ ≤ c < 1/2` holds for *all* `t`
in an interval `[t₀, t₁]`, then `r·t` is trapped in a single "good band"
`[k−c, k+c]` (the near-integer set has gaps of width `1−2c > 0`), so the
interval can't be too long:  `r·(t₁−t₀) ≤ 2c`.

No abstract IVT is needed: if `r·t₁` escaped the band `[k−c, k+c]` of
`r·t₀`'s nearest integer `k`, the explicit point `t' = (k+1/2)/r` (or `t₁`
itself) lands where `‖r·t'‖ > c`, contradicting the hypothesis.
No `sorry`.
-/

import LRSpectrumFull.NearestIntLipschitz

namespace LRSpectrumFull

/-- `‖k + 1/2‖ = 1/2`. -/
theorem nearestIntDist_half_int (k : ℤ) : nearestIntDist ((k : ℝ) + 1 / 2) = 1 / 2 := by
  rw [add_comm, nearestIntDist_add_int]
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- For `x ∈ [0, 1/2]`, `‖x‖ = x`. -/
theorem nearestIntDist_eq_self_of_le_half (x : ℝ) (h0 : 0 ≤ x) (h : x ≤ 1 / 2) :
    nearestIntDist x = x := by
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨h0, by linarith⟩, min_eq_left (by linarith)]

/-- For an integer `k` and `y` with `k ≤ y ≤ k + 1/2`, `‖y‖ = y − k`. -/
theorem nearestIntDist_sub_int (k : ℤ) (y : ℝ) (h0 : (k : ℝ) ≤ y) (h : y ≤ (k : ℝ) + 1 / 2) :
    nearestIntDist y = y - k := by
  have key : nearestIntDist (y - (k : ℝ)) = y - (k : ℝ) :=
    nearestIntDist_eq_self_of_le_half _ (by linarith) (by linarith)
  have e : y = (y - (k : ℝ)) + ((k : ℤ) : ℝ) := by ring
  conv_lhs => rw [e, nearestIntDist_add_int]
  exact key

/-- **Confinement.** If `‖r·t‖ ≤ c < 1/2` for all `t ∈ [t₀, t₁]` (with
`r > 0`), then `r·(t₁ − t₀) ≤ 2c`. -/
theorem nid_confined (r : ℝ) (hr : 0 < r) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    (t₀ t₁ : ℝ) (hle : t₀ ≤ t₁)
    (h : ∀ t, t₀ ≤ t → t ≤ t₁ → nearestIntDist (r * t) ≤ c) :
    r * (t₁ - t₀) ≤ 2 * c := by
  -- `r·t₀` is within `c` of some integer `k`
  obtain ⟨k, hk⟩ := nearestIntDist_eq_abs (r * t₀)
  have hk0 : nearestIntDist (r * t₀) ≤ c := h t₀ le_rfl hle
  rw [hk] at hk0
  rw [abs_le] at hk0  -- -c ≤ r*t₀ - k ≤ c
  -- Claim: r·t₁ ≤ k + c. Suppose not.
  have hub : r * t₁ ≤ (k : ℝ) + c := by
    by_contra hcon
    push Not at hcon  -- (k:ℝ) + c < r * t₁
    rcases le_or_gt ((k : ℝ) + 1 / 2) (r * t₁) with hge | hlt
    · -- r·t₁ ≥ k + 1/2 : the point t' = (k+1/2)/r is in range and bad
      set t' := ((k : ℝ) + 1 / 2) / r with ht'
      have hrt' : r * t' = (k : ℝ) + 1 / 2 := by rw [ht']; field_simp
      have h0 : t₀ ≤ t' := by
        have : r * t₀ ≤ r * t' := by rw [hrt']; linarith [hk0.2]
        exact le_of_mul_le_mul_left this hr
      have h1 : t' ≤ t₁ := by
        have : r * t' ≤ r * t₁ := by rw [hrt']; linarith
        exact le_of_mul_le_mul_left this hr
      have := h t' h0 h1
      rw [hrt', nearestIntDist_half_int] at this
      linarith
    · -- k + c < r·t₁ < k + 1/2 : t₁ itself is bad
      have hb := h t₁ hle le_rfl
      rw [nearestIntDist_sub_int k (r * t₁) (by linarith [hk0.2]) (by linarith)] at hb
      linarith
  -- r·t₀ ≥ k - c, so r·(t₁ - t₀) ≤ 2c
  have hlb : (k : ℝ) - c ≤ r * t₀ := by linarith [hk0.1]
  have : r * (t₁ - t₀) = r * t₁ - r * t₀ := by ring
  rw [this]; linarith

end LRSpectrumFull
