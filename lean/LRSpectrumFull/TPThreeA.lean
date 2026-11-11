/-
# TP'(3), Case A: a uniform proof (no lattice reduction)

Hand proof: private/INVENTION_2026_11/CASEA_REPORT.md (Opus seat, reviewed here by me line by line).
`pairBox` (Bezout): times where runners `a, b` lie in prescribed arcs; `cSweep`: runner `c` can be made good by a
shift of at most `1/(2c)` in time; `sweepCase` (gcd(a,b) = 1); `shiftCase` (gcd(a,b) ≥ 2, shift by `j / g`).
-/
import LRSpectrumFull.TPThreeRed

namespace LRSpectrumFull

/-- `x ∈ [1/4, 3/4] + ℤ` -/
def GoodQ (x : ℝ) : Prop := ∃ w : ℤ, 1 / 4 ≤ x - w ∧ x - w ≤ 3 / 4

lemma tpDist_of_goodQ {x : ℝ} (h : GoodQ x) : 1 / 4 ≤ tpDist x := by
  obtain ⟨w, h1, h2⟩ := h
  exact tpDist_ge_win _ _ w h1 (by linarith) (by norm_num) (by norm_num)

lemma pairBox (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (W H α β : ℝ) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (hg : (Nat.gcd a b : ℝ) ≤ b * W + a * H) :
    ∃ (t : ℝ) (j k : ℤ), 1 / 4 ≤ a * t + α - j ∧ a * t + α - j ≤ 1 / 4 + W ∧
      1 / 4 ≤ b * t + β - k ∧ b * t + β - k ≤ 1 / 4 + H := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hgpos : (0 : ℝ) < (Nat.gcd a b : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left _ ha
  set g : ℝ := (Nat.gcd a b : ℝ) with hgdef
  have hbez : (g : ℝ) = a * (Nat.gcdA a b : ℝ) + b * (Nat.gcdB a b : ℝ) := by
    have := Nat.gcd_eq_gcd_ab a b
    rw [hgdef]; exact_mod_cast this
  set x : ℤ := Nat.gcdA a b with hx
  set y : ℤ := Nat.gcdB a b with hy
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = ((a : ℝ) - b) / 4 + b * α - a * β := ⟨_, rfl⟩
  set n : ℤ := ⌈(-(a * H) - C0) / g⌉ with hn
  have hn1 : (-(a * H) - C0) / g ≤ n := Int.le_ceil _
  have hn2 : (n : ℝ) < (-(a * H) - C0) / g + 1 := Int.ceil_lt_add_one _
  have hn1' : -(a * H) - C0 ≤ n * g := (div_le_iff₀ hgpos).mp hn1
  have hn2' : ((n : ℝ) - 1) * g < -(a * H) - C0 := by
    have : (n : ℝ) - 1 < (-(a * H) - C0) / g := by linarith
    exact (lt_div_iff₀ hgpos).mp this
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = C0 + g * n := ⟨_, rfl⟩
  have hz1 : -(a * H) ≤ z := by rw [hz]; linarith
  have hzb : z ≤ b * W := by rw [hz]; linarith
  obtain ⟨u, v, hu0, huW, hv0, hvH, huv⟩ :
      ∃ u v : ℝ, 0 ≤ u ∧ u ≤ W ∧ 0 ≤ v ∧ v ≤ H ∧ b * u - a * v = z := by
    by_cases hzn : 0 ≤ z
    · refine ⟨z / b, 0, by positivity, ?_, le_refl _, hH, ?_⟩
      · rw [div_le_iff₀ hbR]; linarith
      · field_simp; ring
    · rw [not_le] at hzn
      refine ⟨0, -z / a, le_refl _, hW, by apply div_nonneg <;> linarith, ?_, ?_⟩
      · rw [div_le_iff₀ haR]; linarith
      · field_simp; ring
  have hgn : (a : ℝ) * ((n * x : ℤ) : ℝ) - b * ((-(n * y) : ℤ) : ℝ) = g * n := by
    push_cast; linear_combination (n : ℝ) * (-hbez)
  refine ⟨(1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) / a, -(n * y), n * x, ?_, ?_, ?_, ?_⟩
  · have : (a : ℝ) * ((1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) / a) + α - ((-(n * y) : ℤ) : ℝ)
        = 1 / 4 + u := by field_simp; ring
    rw [this]; linarith
  · have : (a : ℝ) * ((1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) / a) + α - ((-(n * y) : ℤ) : ℝ)
        = 1 / 4 + u := by field_simp; ring
    rw [this]; linarith
  · have hk : (b : ℝ) * (1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) + a * β - a * ((n * x : ℤ) : ℝ)
        = a * (1 / 4 + v) := by linarith
    have : (b : ℝ) * ((1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) / a) + β - ((n * x : ℤ) : ℝ)
        = 1 / 4 + v := by
      field_simp
      linarith
    rw [this]; linarith
  · have hk : (b : ℝ) * (1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) + a * β - a * ((n * x : ℤ) : ℝ)
        = a * (1 / 4 + v) := by linarith
    have : (b : ℝ) * ((1 / 4 + ((-(n * y) : ℤ) : ℝ) + u - α) / a) + β - ((n * x : ℤ) : ℝ)
        = 1 / 4 + v := by
      field_simp
      linarith
    rw [this]; linarith

lemma cSweep (z0 : ℝ) : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧ GoodQ (z0 + s) := by
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = ⌈z0 - 3 / 4⌉ := ⟨_, rfl⟩
  have h1 : z0 - 3 / 4 ≤ w := by rw [hw]; exact Int.le_ceil _
  have h2 : (w : ℝ) < z0 - 3 / 4 + 1 := by rw [hw]; exact Int.ceil_lt_add_one _
  by_cases h : (w : ℝ) + 3 / 4 - z0 ≤ 1 / 2
  · exact ⟨w + 3 / 4 - z0, by linarith, h, w, by linarith, by linarith⟩
  · rw [not_le] at h
    exact ⟨w + 3 / 4 - z0 - 1 / 2, by linarith, by linarith, w, by linarith, by linarith⟩

lemma sweepCase (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hg : Nat.gcd a b = 1)
    (hineq : 2 * a * b + 2 * c ≤ c * (a + b)) (α β γ : ℝ) :
    ∃ τ : ℝ, GoodQ ((a : ℝ) * τ + α) ∧ GoodQ ((b : ℝ) * τ + β) ∧ GoodQ ((c : ℝ) * τ + γ) := by
  have hb : 0 < b := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hac : (a : ℝ) ≤ c := by exact_mod_cast (by omega : a ≤ c)
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hineqR : 2 * (a : ℝ) * b + 2 * c ≤ c * (a + b) := by exact_mod_cast hineq
  have hW : 0 ≤ 1 / 2 - (a : ℝ) / (2 * c) := by
    have : (a : ℝ) / (2 * c) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hH : 0 ≤ 1 / 2 - (b : ℝ) / (2 * c) := by
    have : (b : ℝ) / (2 * c) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hcond : (Nat.gcd a b : ℝ) ≤ b * (1 / 2 - (a : ℝ) / (2 * c)) + a * (1 / 2 - (b : ℝ) / (2 * c)) := by
    rw [hg]
    have e : (b : ℝ) * (1 / 2 - (a : ℝ) / (2 * c)) + a * (1 / 2 - (b : ℝ) / (2 * c))
        = ((a : ℝ) + b) / 2 - a * b / c := by field_simp; ring
    rw [e]
    have : (a : ℝ) * b / c ≤ ((a : ℝ) + b) / 2 - 1 := by
      rw [div_le_iff₀ hcR]; nlinarith
    push_cast; linarith
  obtain ⟨t, j, k, h1, h2, h3, h4⟩ := pairBox a b ha hb _ _ α β hW hH hcond
  obtain ⟨s, hs0, hs1, hgood⟩ := cSweep ((c : ℝ) * t + γ)
  have hq0 : 0 ≤ s / c := by positivity
  have hqa : (a : ℝ) * (s / c) ≤ a / (2 * c) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hcR (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg haR.le hcR.le) (sub_nonneg.mpr hs1)]
  have hqb : (b : ℝ) * (s / c) ≤ b / (2 * c) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hcR (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hbR.le hcR.le) (sub_nonneg.mpr hs1)]
  have hqa0 : 0 ≤ (a : ℝ) * (s / c) := by positivity
  have hqb0 : 0 ≤ (b : ℝ) * (s / c) := by positivity
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

lemma shiftCase (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hg2 : 2 ≤ Nat.gcd a b)
    (hcop : Nat.Coprime (Nat.gcd a b) c) (α β γ : ℝ) :
    ∃ τ : ℝ, GoodQ ((a : ℝ) * τ + α) ∧ GoodQ ((b : ℝ) * τ + β) ∧ GoodQ ((c : ℝ) * τ + γ) := by
  have hb : 0 < b := by omega
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = Nat.gcd a b := ⟨_, rfl⟩
  rw [← hgdef] at hg2 hcop
  have hga : g ∣ a := hgdef ▸ Nat.gcd_dvd_left a b
  have hgb : g ∣ b := hgdef ▸ Nat.gcd_dvd_right a b
  obtain ⟨a', ha'⟩ := hga
  obtain ⟨b', hb'⟩ := hgb
  have hgpos : 0 < g := by omega
  have ha'1 : 1 ≤ a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · subst h; simp at ha'; omega
    · exact h
  have hab' : a' < b' := by
    rw [ha', hb'] at hab; exact Nat.lt_of_mul_lt_mul_left hab
  have hsum : 3 * g ≤ a + b := by
    rw [ha', hb']
    nlinarith [Nat.mul_le_mul_left g (show 3 ≤ a' + b' by omega)]
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hgR0 : (0 : ℝ) < g := by linarith
  have hsumR : 3 * (g : ℝ) ≤ a + b := by exact_mod_cast hsum
  have hcond : (Nat.gcd a b : ℝ) ≤ b * (1 / 2) + a * (1 / 2) := by
    rw [← hgdef]; linarith
  obtain ⟨t0, j0, k0, h1, h2, h3, h4⟩ := pairBox a b ha hb (1 / 2) (1 / 2) α β (by norm_num) (by norm_num) hcond
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = ⌈g * (1 / 4 - ((c : ℝ) * t0 + γ))⌉ := ⟨_, rfl⟩
  have hr1 : (g : ℝ) * (1 / 4 - ((c : ℝ) * t0 + γ)) ≤ r := by rw [hr]; exact Int.le_ceil _
  have hr2 : (r : ℝ) < g * (1 / 4 - ((c : ℝ) * t0 + γ)) + 1 := by rw [hr]; exact Int.ceil_lt_add_one _
  have hcZ : IsCoprime (c : ℤ) (g : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨u, v, huv⟩ := hcZ
  -- c * (u r) = r + g * (-(v r))
  have hcj : (c : ℤ) * (u * r) = r + g * (-(v * r)) := by linear_combination r * huv
  refine ⟨t0 + ((u * r : ℤ) : ℝ) / g, ⟨j0 + a' * (u * r), ?_, ?_⟩, ⟨k0 + b' * (u * r), ?_, ?_⟩,
    ⟨-(v * r), ?_, ?_⟩⟩
  · have : (a : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + α - ((j0 + a' * (u * r) : ℤ) : ℝ)
        = ((a : ℝ) * t0 + α - j0) := by
      rw [ha']; push_cast; field_simp; ring
    rw [this]; linarith
  · have : (a : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + α - ((j0 + a' * (u * r) : ℤ) : ℝ)
        = ((a : ℝ) * t0 + α - j0) := by
      rw [ha']; push_cast; field_simp; ring
    rw [this]; linarith
  · have : (b : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + β - ((k0 + b' * (u * r) : ℤ) : ℝ)
        = ((b : ℝ) * t0 + β - k0) := by
      rw [hb']; push_cast; field_simp; ring
    rw [this]; linarith
  · have : (b : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + β - ((k0 + b' * (u * r) : ℤ) : ℝ)
        = ((b : ℝ) * t0 + β - k0) := by
      rw [hb']; push_cast; field_simp; ring
    rw [this]; linarith
  · have hc' : (c : ℝ) * ((u * r : ℤ) : ℝ) = r + g * ((-(v * r) : ℤ) : ℝ) := by exact_mod_cast hcj
    have : (c : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + γ - ((-(v * r) : ℤ) : ℝ)
        = ((c : ℝ) * t0 + γ) + (r : ℝ) / g := by
      field_simp
      linarith
    rw [this]
    have e1 : 1 / 4 - ((c : ℝ) * t0 + γ) ≤ (r : ℝ) / g := by rw [le_div_iff₀ hgR0]; linarith
    linarith
  · have hc' : (c : ℝ) * ((u * r : ℤ) : ℝ) = r + g * ((-(v * r) : ℤ) : ℝ) := by exact_mod_cast hcj
    have : (c : ℝ) * (t0 + ((u * r : ℤ) : ℝ) / g) + γ - ((-(v * r) : ℤ) : ℝ)
        = ((c : ℝ) * t0 + γ) + (r : ℝ) / g := by
      field_simp
      linarith
    rw [this]
    have e2 : (r : ℝ) / g ≤ 1 / 4 - ((c : ℝ) * t0 + γ) + 1 / 2 := by
      rw [div_le_iff₀ hgR0]
      have : (1 : ℝ) ≤ g / 2 := by linarith
      nlinarith
    linarith

lemma ineqL4 (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : 4 ≤ c) :
    2 * a * b + 2 * c ≤ c * (a + b) := by
  by_cases hb2 : b = 2
  · subst hb2
    have : a = 1 := by omega
    subst this
    nlinarith
  · obtain ⟨e, rfl⟩ : ∃ e, b = a + 1 + e := ⟨b - a - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, c = (a + 1 + e) + 1 + d := ⟨c - (a + 1 + e) - 1, by omega⟩
    have hb3 : 3 ≤ a + 1 + e := by omega
    nlinarith [Nat.zero_le (a * e), Nat.zero_le (d * a), Nat.zero_le (d * e), Nat.zero_le (e * e),
      Nat.mul_le_mul hb3 hb3, Nat.zero_le d, Nat.mul_le_mul_left d hb3]

theorem caseA : CaseA := by
  intro a b c ha hab hbc hc16 _ hprim sa sb sc
  have key : ∃ τ : ℝ, GoodQ ((a : ℝ) * τ + (sa : ℝ) / 4) ∧ GoodQ ((b : ℝ) * τ + (sb : ℝ) / 4) ∧
      GoodQ ((c : ℝ) * τ + (sc : ℝ) / 4) := by
    rcases Nat.lt_or_ge (Nat.gcd a b) 2 with h | h
    · have hg : Nat.gcd a b = 1 := by
        have := Nat.gcd_pos_of_pos_left b ha
        omega
      exact sweepCase a b c ha hab hbc hg (ineqL4 a b c ha hab hbc (by omega)) _ _ _
    · exact shiftCase a b c ha hab h hprim _ _ _
  obtain ⟨τ, h1, h2, h3⟩ := key
  exact ⟨τ, tpDist_of_goodQ h1, tpDist_of_goodQ h2, tpDist_of_goodQ h3⟩

/-- TP' for three runners, all speeds, all torsion phases. -/
theorem TPp_three : TPp 3 := TPp_three_of_caseA caseA

end LRSpectrumFull
