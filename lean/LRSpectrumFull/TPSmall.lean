/-
# TP' (torsion phases, distinct speeds), small m

`TPp m`: for every family of `m` distinct positive integer speeds and every choice of phases `s i / (m+1)`
there is a time `t` with `‖v i * t + s i / (m+1)‖ ≥ 1/(m+1)` for all `i`.
(Non-primitive speed families reduce to primitive ones by rescaling `t`, so no primitivity hypothesis is needed.)

Proved here for ALL speeds (not a finite box): `TPp 1`, `TPp 2`.  TP' for general `m` is open.
Method for `m = 2`: pivot runner placed exactly at `1/2`, the other runner reached by a congruence; the
residual case `b = 2a` is a 3x3 table.
-/
import Mathlib

set_option linter.unusedSimpArgs false

namespace LRSpectrumFull

/-- distance to the nearest integer -/
noncomputable def tpDist (x : ℝ) : ℝ := |x - round x|

/-- TP' for `m` runners. -/
def TPp (m : ℕ) : Prop :=
  ∀ (v : Fin m → ℕ), (∀ i, 0 < v i) → Function.Injective v → ∀ s : Fin m → ℤ,
    ∃ t : ℝ, ∀ i, 1 / ((m : ℝ) + 1) ≤ tpDist ((v i : ℝ) * t + (s i : ℝ) / ((m : ℝ) + 1))

lemma tpDist_ge_third_of (x : ℝ) (w : ℤ) (h1 : 1 / 3 ≤ x - w) (h2 : x - w ≤ 2 / 3) :
    1 / 3 ≤ tpDist x := by
  unfold tpDist
  have hx : x = (x - w) + (w : ℤ) := by ring
  set y := x - w with hy
  have hr : round x = round y + w := by
    rw [hx]; exact round_add_intCast y w
  rw [hr]
  have : x - ((round y + w : ℤ) : ℝ) = y - round y := by push_cast; rw [hy]; ring
  rw [this]
  rw [round_eq]
  by_cases h : y < 1 / 2
  · have : ⌊y + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [this]; simp only [Int.cast_zero, sub_zero]
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : ⌊y + 1 / 2⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [this]; push_cast
    rw [abs_of_nonpos (by linarith)]; linarith

/-- the pivot construction: runner `a = a'g` at `1/2`, runner `b = b'g` reached by a congruence. -/
lemma pivot (a' b' g : ℕ) (hcop : Nat.Coprime a' b') (ha' : 3 ≤ a') (hg : 0 < g) (sa sb : ℤ) :
    ∃ t : ℝ, 1 / 3 ≤ tpDist (((a' * g : ℕ) : ℝ) * t + (sa : ℝ) / 3) ∧
      1 / 3 ≤ tpDist (((b' * g : ℕ) : ℝ) * t + (sb : ℝ) / 3) := by
  have hb' : IsCoprime (b' : ℤ) (a' : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr hcop.symm
    exact_mod_cast this
  obtain ⟨x, y, hxy⟩ := hb'
  set A : ℤ := (a' : ℤ) with hA
  set B : ℤ := (b' : ℤ) with hB
  set c : ℤ := B * (3 - 2 * sa) + 2 * A * sb with hc
  set q0 : ℤ := (c - 2 * A) / 6 with hq0
  set r : ℤ := c - 6 * q0 with hr
  have hmod : r = 2 * A + (c - 2 * A) % 6 := by
    have := Int.mul_ediv_add_emod (c - 2 * A) 6
    rw [hr, hq0]; linarith
  have hr1 : 2 * A ≤ r := by
    rw [hmod]; have := Int.emod_nonneg (c - 2 * A) (by norm_num : (6:ℤ) ≠ 0); linarith
  have hr2 : r ≤ 4 * A := by
    rw [hmod]; have := Int.emod_lt_of_pos (c - 2 * A) (by norm_num : (0:ℤ) < 6)
    have h3 : (3:ℤ) ≤ A := by rw [hA]; exact_mod_cast ha'
    omega
  set k : ℤ := -q0 * x with hk
  set w : ℤ := q0 * y with hw
  have hkw : B * k = -q0 + A * w := by
    rw [hk, hw]; linear_combination (-q0) * hxy
  have hAne : (A : ℝ) ≠ 0 := by
    have h3 : (3:ℤ) ≤ A := by rw [hA]; exact_mod_cast ha'
    have : (0:ℤ) < A := by omega
    exact_mod_cast this.ne'
  have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hAr : (A : ℝ) = (a' : ℝ) := by simp [hA]
  have hBr : (B : ℝ) = (b' : ℝ) := by simp [hB]
  have hint : (B : ℝ) * (3 - 2 * (sa : ℝ)) + 6 * B * k + 2 * A * sb = r + 6 * A * w := by
    have : B * (3 - 2 * sa) + 6 * B * k + 2 * A * sb = r + 6 * A * w := by
      have h6 : 6 * (B * k) = 6 * (-q0 + A * w) := by rw [hkw]
      rw [hr]; nlinarith [hc, h6]
    exact_mod_cast this
  refine ⟨(3 - 2 * (sa : ℝ) + 6 * (k : ℝ)) / (6 * A * g), ?_, ?_⟩
  · have h1 : (((a' * g : ℕ) : ℝ)) * ((3 - 2 * (sa : ℝ) + 6 * (k : ℝ)) / (6 * A * g)) + (sa : ℝ) / 3
        = 1 / 2 + k := by
      push_cast; rw [← hAr]; field_simp; ring
    rw [h1]
    exact tpDist_ge_third_of _ k (by linarith) (by linarith)
  · have h2 : (((b' * g : ℕ) : ℝ)) * ((3 - 2 * (sa : ℝ) + 6 * (k : ℝ)) / (6 * A * g)) + (sb : ℝ) / 3
        = (r : ℝ) / (6 * A) + w := by
      push_cast; rw [← hBr]
      have : (B : ℝ) * g * ((3 - 2 * (sa : ℝ) + 6 * (k : ℝ)) / (6 * A * g)) + (sb : ℝ) / 3
          = ((B : ℝ) * (3 - 2 * (sa : ℝ)) + 6 * B * k + 2 * A * sb) / (6 * A) := by
        field_simp; ring
      rw [this, hint]; field_simp
    rw [h2]
    have hApos : (0 : ℝ) < A := by
      have : (3:ℤ) ≤ A := by rw [hA]; exact_mod_cast ha'
      have : (0:ℤ) < A := by omega
      exact_mod_cast this
    have e1 : (2 : ℝ) * A ≤ r := by exact_mod_cast hr1
    have e2 : (r : ℝ) ≤ 4 * A := by exact_mod_cast hr2
    apply tpDist_ge_third_of _ w
    · have : 1 / 3 ≤ (r : ℝ) / (6 * A) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · have : (r : ℝ) / (6 * A) ≤ 2 / 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith


lemma tpDist_half (k : ℤ) : tpDist (1 / 2 + k) = 1 / 2 := by
  unfold tpDist
  rw [round_eq]
  have : ⌊(1 / 2 + (k : ℝ)) + 1 / 2⌋ = k + 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [this]; push_cast
  rw [abs_of_nonpos (by linarith)]; ring

theorem TPp_one : TPp 1 := by
  intro v hv _ s
  refine ⟨(1 - (s 0 : ℝ)) / (2 * (v 0 : ℝ)), ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have hv0 : (0 : ℝ) < v 0 := by exact_mod_cast hv 0
  have h1 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
  rw [h1]
  have : (v 0 : ℝ) * ((1 - (s 0 : ℝ)) / (2 * (v 0 : ℝ))) + (s 0 : ℝ) / 2 = 1 / 2 + ((0 : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [this, tpDist_half]

lemma table12 (sa sb : ℤ) : ∃ τ : ℝ, 1 / 3 ≤ tpDist (τ + (sa : ℝ) / 3) ∧
    1 / 3 ≤ tpDist (2 * τ + (sb : ℝ) / 3) := by
  have hsa : (sa : ℝ) = 3 * ((sa / 3 : ℤ) : ℝ) + ((sa % 3 : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod sa 3).symm
  have hsb : (sb : ℝ) = 3 * ((sb / 3 : ℤ) : ℝ) + ((sb % 3 : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod sb 3).symm
  have ca : (sa : ℝ) / 3 = ((sa / 3 : ℤ) : ℝ) + ((sa % 3 : ℤ) : ℝ) / 3 := by linarith
  have cb : (sb : ℝ) / 3 = ((sb / 3 : ℤ) : ℝ) + ((sb % 3 : ℤ) : ℝ) / 3 := by linarith
  rw [ca, cb]
  have key : ∀ (τ : ℝ) (ra rb : ℤ) (w0 w1 : ℤ),
      1 / 3 ≤ τ + (ra : ℝ) / 3 - w0 → τ + (ra : ℝ) / 3 - w0 ≤ 2 / 3 →
      1 / 3 ≤ 2 * τ + (rb : ℝ) / 3 - w1 → 2 * τ + (rb : ℝ) / 3 - w1 ≤ 2 / 3 →
      1 / 3 ≤ tpDist (τ + (((sa / 3 : ℤ) : ℝ) + (ra : ℝ) / 3)) ∧
      1 / 3 ≤ tpDist (2 * τ + (((sb / 3 : ℤ) : ℝ) + (rb : ℝ) / 3)) := by
    intro τ ra rb w0 w1 a1 a2 b1 b2
    constructor
    · apply tpDist_ge_third_of _ (sa / 3 + w0) <;> push_cast <;> linarith
    · apply tpDist_ge_third_of _ (sb / 3 + w1) <;> push_cast <;> linarith
  have ha : sa % 3 = 0 ∨ sa % 3 = 1 ∨ sa % 3 = 2 := by omega
  have hb : sb % 3 = 0 ∨ sb % 3 = 1 ∨ sb % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · exact ⟨1/3, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨1/2, key _ (sa % 3) (sb % 3) 0 1 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨1/2, key _ (sa % 3) (sb % 3) 0 1 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨1/3, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨0, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨0, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨2/3, key _ (sa % 3) (sb % 3) 1 1 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨0, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩
  · exact ⟨0, key _ (sa % 3) (sb % 3) 0 0 (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num) (by simp only [ha, hb]; norm_num)⟩


lemma split_gcd (a b : ℕ) (ha : 0 < a) :
    ∃ g a' b' : ℕ, 0 < g ∧ Nat.Coprime a' b' ∧ a = a' * g ∧ b = b' * g := by
  refine ⟨Nat.gcd a b, a / Nat.gcd a b, b / Nat.gcd a b, Nat.gcd_pos_of_pos_left _ ha,
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ ha), ?_, ?_⟩
  · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a b)).symm
  · exact (Nat.div_mul_cancel (Nat.gcd_dvd_right a b)).symm

lemma pair_main (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) (sa sb : ℤ) :
    ∃ t : ℝ, 1 / 3 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 3) ∧
      1 / 3 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 3) := by
  obtain ⟨g, a', b', hg, hcop, rfl, rfl⟩ := split_gcd a b ha
  have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  by_cases h1 : 3 ≤ a'
  · exact pivot a' b' g hcop h1 hg sa sb
  by_cases h2 : 3 ≤ b'
  · obtain ⟨t, ht1, ht2⟩ := pivot b' a' g hcop.symm h2 hg sb sa
    exact ⟨t, ht2, ht1⟩
  have ha' : 0 < a' := Nat.pos_of_mul_pos_right ha
  have hb' : 0 < b' := Nat.pos_of_mul_pos_right hb
  have : a' ≤ 2 := by omega
  have : b' ≤ 2 := by omega
  interval_cases a' <;> interval_cases b'
  · exact absurd rfl hne
  · obtain ⟨τ, h1, h2⟩ := table12 sa sb
    refine ⟨τ / g, ?_, ?_⟩
    · have : (((1 * g : ℕ)) : ℝ) * (τ / g) = τ := by push_cast; field_simp
      rw [this]; exact h1
    · have : (((2 * g : ℕ)) : ℝ) * (τ / g) = 2 * τ := by push_cast; field_simp
      rw [this]; exact h2
  · obtain ⟨τ, h1, h2⟩ := table12 sb sa
    refine ⟨τ / g, ?_, ?_⟩
    · have : (((2 * g : ℕ)) : ℝ) * (τ / g) = 2 * τ := by push_cast; field_simp
      rw [this]; exact h2
    · have : (((1 * g : ℕ)) : ℝ) * (τ / g) = τ := by push_cast; field_simp
      rw [this]; exact h1
  · exact absurd hcop (by decide)

theorem TPp_two : TPp 2 := by
  intro v hv hinj s
  have hne : v 0 ≠ v 1 := fun h => absurd (hinj h) (by decide)
  obtain ⟨t, h0, h1⟩ := pair_main (v 0) (v 1) (hv 0) (hv 1) hne (s 0) (s 1)
  refine ⟨t, ?_⟩
  have e : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  intro i
  rw [e]
  fin_cases i
  · simpa using h0
  · simpa using h1

end LRSpectrumFull
