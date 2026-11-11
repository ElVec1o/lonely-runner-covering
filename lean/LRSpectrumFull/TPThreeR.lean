/-
# TP'(3), Case R: speeds `a, b, a + b`

For coprime `a ≠ b` with `a` odd, every choice of phases `sa, sb, sc` (phase `s/4`) admits a time `t` with
all three of `a, b, c = a + b` at distance `≥ 1/4` from an integer.  Method: `t = P / (4c)`, runner `a`
lands in the window `[1/2, 3/4]` (numerator `u ∈ [2c, 3c]`), runner `b` is then determined by
`bP + c sb = c e - u + 4c(·)` with `e ∈ {0, 1}`, runner `c` sits at `(P + sc)/4`.
Hand proof: private/INVENTION_2026_11/TP3_REPORT.md, Case R.
-/
import LRSpectrumFull.TPSmall

set_option linter.unusedSimpArgs false

namespace LRSpectrumFull

lemma tpDist_ge_win (d x : ℝ) (w : ℤ) (h1 : d ≤ x - w) (h2 : x - w ≤ 1 - d) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    d ≤ tpDist x := by
  unfold tpDist
  have hx : x = (x - w) + (w : ℤ) := by ring
  set y := x - w with hy
  have hr : round x = round y + w := by
    rw [hx]; exact round_add_intCast y w
  rw [hr]
  have : x - ((round y + w : ℤ) : ℝ) = y - round y := by push_cast; rw [hy]; ring
  rw [this, round_eq]
  by_cases h : y < 1 / 2
  · have : ⌊y + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [this]; simp only [Int.cast_zero, sub_zero]
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : ⌊y + 1 / 2⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [this]; push_cast
    rw [abs_of_nonpos (by linarith)]; linarith

/-- Case R core, `a` odd. -/
lemma caseR_core (a b : ℕ) (ha : Odd a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hne : a ≠ b)
    (sa sb sc : ℤ) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧
      1 / 4 ≤ tpDist (((a + b : ℕ) : ℝ) * t + (sc : ℝ) / 4) := by
  obtain ⟨k, hk⟩ := ha
  have ha1 : 1 ≤ a := by omega
  have hc3 : (3 : ℤ) ≤ (a : ℤ) + b := by omega
  have hcopZ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  set c : ℤ := (a : ℤ) + b with hc
  set A : ℤ := (a : ℤ) with hA
  set B : ℤ := (b : ℤ) with hB
  obtain ⟨p, q, hpq⟩ := hcopZ
  -- IsCoprime A (4c)
  have hA4 : IsCoprime A 4 := ⟨A, -(k * k + k), by
    have : A = 2 * k + 1 := by rw [hA]; exact_mod_cast hk
    rw [this]; ring⟩
  have hAc : IsCoprime A c := ⟨p - q, q, by rw [hc]; linear_combination hpq⟩
  obtain ⟨x, y, hxy⟩ := hA4.mul_right hAc
  -- hxy : x * A + y * (4 * c) = 1
  -- choice of e and pi
  set X : ℤ := (sa + sb - sc) % 4 with hX
  set e : ℤ := if X = 0 then 1 else 0 with he
  have he01 : e = 0 ∨ e = 1 := by rw [he]; split_ifs <;> simp
  have heX : (e - X) % 4 ≠ 0 := by
    rw [he]; split_ifs with h
    · rw [h]; norm_num
    · have h4 : 0 ≤ X := Int.emod_nonneg _ (by norm_num)
      have h5 : X < 4 := Int.emod_lt_of_pos _ (by norm_num)
      omega
  set π : ℤ := e - sa - sb with hπ
  set r0 : ℤ := A * π + c * sa with hr0
  set u : ℤ := 2 * c + (r0 - 2 * c) % 4 with hu
  have hu1 : 2 * c ≤ u := by
    rw [hu]; have := Int.emod_nonneg (r0 - 2 * c) (by norm_num : (4:ℤ) ≠ 0); omega
  have hu2 : u ≤ 3 * c := by
    rw [hu]; have := Int.emod_lt_of_pos (r0 - 2 * c) (by norm_num : (0:ℤ) < 4); omega
  have hu4 : u = r0 - 4 * ((r0 - 2 * c) / 4) := by
    have := Int.mul_ediv_add_emod (r0 - 2 * c) 4
    rw [hu]; linarith
  set P : ℤ := x * (u - c * sa) with hP
  set z0 : ℤ := -(y * (u - c * sa)) with hz0
  have hPa : A * P + c * sa = u + 4 * c * z0 := by
    rw [hP, hz0]; linear_combination (u - c * sa) * hxy
  -- P ≡ π (mod 4)
  have hdiv : (4 : ℤ) ∣ A * (P - π) := by
    have : A * (P - π) = (u - r0) + 4 * c * z0 + 0 := by
      have : A * P = u - c * sa + 4 * c * z0 := by linarith
      rw [mul_sub, this, hr0]; ring
    rw [this]
    exact ⟨-((r0 - 2 * c) / 4) + c * z0, by rw [hu4]; ring⟩
  have h4P : (4 : ℤ) ∣ P - π := hA4.symm.dvd_of_dvd_mul_left hdiv
  obtain ⟨j, hj⟩ := h4P
  have hcpos : (0 : ℝ) < c := by
    have : (0 : ℤ) < c := by omega
    exact_mod_cast this
  have h4c : (4 * (c : ℝ)) ≠ 0 := by positivity
  refine ⟨(P : ℝ) / (4 * c), ?_, ?_, ?_⟩
  · -- runner a
    have hid : (a : ℝ) * ((P : ℝ) / (4 * c)) + (sa : ℝ) / 4 = (u : ℝ) / (4 * c) + z0 := by
      have h : ((A * P + c * sa : ℤ) : ℝ) = ((u + 4 * c * z0 : ℤ) : ℝ) := by rw [hPa]
      push_cast at h
      have hAr : (A : ℝ) = (a : ℝ) := by simp [hA]
      rw [hAr] at h
      field_simp
      linarith
    rw [hid]
    have e1 : (2 : ℝ) * c ≤ u := by exact_mod_cast hu1
    have e2 : (u : ℝ) ≤ 3 * c := by exact_mod_cast hu2
    refine tpDist_ge_win _ _ z0 ?_ ?_ (by norm_num) (by norm_num)
    · have : 1 / 4 ≤ (u : ℝ) / (4 * c) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · have : (u : ℝ) / (4 * c) ≤ 3 / 4 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  · -- runner b
    have hBc : (b : ℝ) = (c : ℝ) - (a : ℝ) := by
      rw [hc, hA, hB]; push_cast; ring
    have hid : (b : ℝ) * ((P : ℝ) / (4 * c)) + (sb : ℝ) / 4
        = (e : ℝ) / 4 - (u : ℝ) / (4 * c) + (j - z0) := by
      have h : ((A * P + c * sa : ℤ) : ℝ) = ((u + 4 * c * z0 : ℤ) : ℝ) := by rw [hPa]
      push_cast at h
      have hAr : (A : ℝ) = (a : ℝ) := by simp [hA]
      rw [hAr] at h
      have hPj : (P : ℝ) = π + 4 * j := by exact_mod_cast (by linarith : P = π + 4 * j)
      have hπr : (π : ℝ) = e - sa - sb := by rw [hπ]; push_cast; ring
      rw [hBc]
      field_simp
      nlinarith [h, hPj, hπr]
    rw [hid]
    have e1 : (2 : ℝ) * c ≤ u := by exact_mod_cast hu1
    have e2 : (u : ℝ) ≤ 3 * c := by exact_mod_cast hu2
    have q1 : 1 / 2 ≤ (u : ℝ) / (4 * c) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have q2 : (u : ℝ) / (4 * c) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have ee0 : (0 : ℝ) ≤ e := by rcases he01 with h | h <;> rw [h] <;> norm_num
    have ee1 : (e : ℝ) ≤ 1 := by rcases he01 with h | h <;> rw [h] <;> norm_num
    refine tpDist_ge_win _ _ (j - z0 - 1) ?_ ?_ (by norm_num) (by norm_num)
    · push_cast; linarith
    · push_cast; linarith
  · -- runner c
    have hm := Int.mul_ediv_add_emod (sa + sb - sc) 4
    have hn := Int.mul_ediv_add_emod (e - X) 4
    set M : ℤ := (sa + sb - sc) / 4 with hM
    set N : ℤ := (e - X) / 4 with hN
    set R : ℤ := (e - X) % 4 with hR
    have hR0 : 0 ≤ R := Int.emod_nonneg _ (by norm_num)
    have hR4 : R < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hR1 : 1 ≤ R := by
      have : R ≠ 0 := heX
      omega
    have hPsc : P + sc = R + 4 * (N + j - M) := by
      have hX' : X = (sa + sb - sc) % 4 := hX
      linarith
    have hid : ((a + b : ℕ) : ℝ) * ((P : ℝ) / (4 * c)) + (sc : ℝ) / 4
        = (R : ℝ) / 4 + ((N + j - M : ℤ) : ℝ) := by
      have hcc : ((a : ℝ) + b) = (c : ℝ) := by rw [hc, hA, hB]; push_cast; ring
      have h : ((P + sc : ℤ) : ℝ) = ((R + 4 * (N + j - M) : ℤ) : ℝ) := by rw [hPsc]
      push_cast at h ⊢
      have h' : (P : ℝ) = R + 4 * (N + j - M) - sc := by linarith
      rw [hcc, h']
      field_simp
      ring
    rw [hid]
    have r1 : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    have r3 : (R : ℝ) ≤ 3 := by exact_mod_cast (by omega : R ≤ 3)
    refine tpDist_ge_win _ _ (N + j - M) ?_ ?_ (by norm_num) (by norm_num)
    · linarith
    · linarith

/-- Case R, either parity: `a, b` coprime and distinct, third speed `a + b`. -/
theorem caseR (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hne : a ≠ b)
    (sa sb sc : ℤ) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧
      1 / 4 ≤ tpDist (((a + b : ℕ) : ℝ) * t + (sc : ℝ) / 4) := by
  by_cases hodd : Odd a
  · exact caseR_core a b hodd hb hcop hne sa sb sc
  · have hbodd : Odd b := by
      rcases Nat.even_or_odd b with hbe | hbo
      · exfalso
        have h2a : 2 ∣ a := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
        have h2b : 2 ∣ b := even_iff_two_dvd.mp hbe
        have := Nat.dvd_gcd h2a h2b
        rw [hcop] at this
        omega
      · exact hbo
    obtain ⟨t, h1, h2, h3⟩ := caseR_core b a hbodd ha hcop.symm hne.symm sb sa sc
    refine ⟨t, h2, h1, ?_⟩
    rwa [Nat.add_comm b a] at h3

end LRSpectrumFull
