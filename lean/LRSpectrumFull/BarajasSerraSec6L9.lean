import LRSpectrumFull.BarajasSerraSec6

/-!
# E6 session 17: Barajas-Serra Remark 8 / Lemma 9 (compressing a triple), multiplier levels recorded

`B = {b1, b2, b3}`, `x = b1 - b3`, `y = b2 - b3` (residues mod `N = 7^(m+1)`, via `dsub`).
`ellq m b1 b2 b3 = l({q(b1), q(b2), q(b3)})`.

* `lemma9_i`: `nu x ≠ nu y` gives a unit `lam` with `l(q(lam B)) ≤ 2`, and
  `lam ≡ 1 [MOD 7^(m - max(nu x, nu y))]` (so by G2 it fixes `q` at levels above that max).
* `lemma9_ii_two`: `nu x = nu y = h < m`, `r(y) = 2 r(x)`: `lam = lam2 * lam1` with `lam2 ∈ Lam h`,
  `lam1 ∈ {1} ∪ Lam (nu e) ∪ LamTop` (`e = 2x - y`), `q(lam y) ∈ {0, 6}`, `l(q(lam B)) ≤ 2`.
  Paper: "choose lam in Lam_h such that q(lam e) = 0" is read as lam in `Lam_(nu e)` (e lies above
  level h, where `Lam_h` acts trivially), or a top-level unit if `nu e = m`.
* `lemma9_ii_three`: `r(y) = 3 r(x)`: `lam ∈ Lam h`, `q(lam y) ∈ {0, 5, 6}`, `l(q(lam B)) ≤ 3`.

The paper assumes `nu(B) = {0}` and equal `r(b_i)`; the proofs below do not use either hypothesis.
Falsified first: (development file, not part of this archive) simulates exactly these multiplier choices
(m = 2 exhaustive on class 1, m = 3 with `b3` subsampled by 3): 0 failures at every step.
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- `l(q(B))` for `B = {b1, b2, b3}`. -/
def ellq (m b1 b2 b3 : ℕ) : ℕ :=
  Z7.ell {((qq m b1 : ℕ) : ZMod 7), ((qq m b2 : ℕ) : ZMod 7), ((qq m b3 : ℕ) : ZMod 7)}

/-! ## Z7 wrappers (Remark 8 in the form used here) -/

theorem ell3_fin2 : ∀ q1 q2 q3 : Fin 7,
    (((q1 : ℕ) + 7 - q3) % 7 = 0 ∨ ((q1 : ℕ) + 7 - q3) % 7 = 1 ∨ ((q1 : ℕ) + 7 - q3) % 7 = 6) →
    (((q2 : ℕ) + 7 - q3) % 7 = 0 ∨ ((q2 : ℕ) + 7 - q3) % 7 = 1 ∨ ((q2 : ℕ) + 7 - q3) % 7 = 6) →
    (((q2 : ℕ) + 7 - q1) % 7 = 0 ∨ ((q2 : ℕ) + 7 - q1) % 7 = 1 ∨ ((q2 : ℕ) + 7 - q1) % 7 = 6) →
    Z7.ell {(((q1 : ℕ) : ℕ) : ZMod 7), (((q2 : ℕ) : ℕ) : ZMod 7), (((q3 : ℕ) : ℕ) : ZMod 7)} ≤ 2 := by
  decide +kernel

theorem ell3_fin3 : ∀ q1 q2 q3 : Fin 7,
    (((q1 : ℕ) + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ ((q1 : ℕ) + 7 - q3) % 7) →
    (((q2 : ℕ) + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ ((q2 : ℕ) + 7 - q3) % 7) →
    (((q2 : ℕ) + 7 - q1) % 7 ≤ 2 ∨ 5 ≤ ((q2 : ℕ) + 7 - q1) % 7) →
    Z7.ell {(((q1 : ℕ) : ℕ) : ZMod 7), (((q2 : ℕ) : ℕ) : ZMod 7), (((q3 : ℕ) : ℕ) : ZMod 7)} ≤ 3 := by
  decide +kernel

theorem ell3_core2 (q1 q2 q3 : ℕ) (h1 : q1 < 7) (h2 : q2 < 7) (h3 : q3 < 7)
    (a : (q1 + 7 - q3) % 7 = 0 ∨ (q1 + 7 - q3) % 7 = 1 ∨ (q1 + 7 - q3) % 7 = 6)
    (b : (q2 + 7 - q3) % 7 = 0 ∨ (q2 + 7 - q3) % 7 = 1 ∨ (q2 + 7 - q3) % 7 = 6)
    (c : (q2 + 7 - q1) % 7 = 0 ∨ (q2 + 7 - q1) % 7 = 1 ∨ (q2 + 7 - q1) % 7 = 6) :
    Z7.ell {((q1 : ℕ) : ZMod 7), ((q2 : ℕ) : ZMod 7), ((q3 : ℕ) : ZMod 7)} ≤ 2 :=
  ell3_fin2 ⟨q1, h1⟩ ⟨q2, h2⟩ ⟨q3, h3⟩ a b c

theorem ell3_core3 (q1 q2 q3 : ℕ) (h1 : q1 < 7) (h2 : q2 < 7) (h3 : q3 < 7)
    (a : (q1 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q1 + 7 - q3) % 7)
    (b : (q2 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q3) % 7)
    (c : (q2 + 7 - q1) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q1) % 7) :
    Z7.ell {((q1 : ℕ) : ZMod 7), ((q2 : ℕ) : ZMod 7), ((q3 : ℕ) : ZMod 7)} ≤ 3 :=
  ell3_fin3 ⟨q1, h1⟩ ⟨q2, h2⟩ ⟨q3, h3⟩ a b c

/-! ## pure digit arithmetic (omega in an empty context) -/

theorem arith9_final2 (q1 q2 q3 X Y Z c1 c2 c5 : ℕ) (h1 : q1 < 7) (h2 : q2 < 7) (h3 : q3 < 7)
    (hc1 : c1 < 2) (hc2 : c2 < 2) (hc5 : c5 < 2) (hX : X = 0 ∨ X = 6) (hY : Y = 0 ∨ Y = 6)
    (hZ : Z = 0 ∨ Z = 6) (e1 : q1 = (q3 + X + c1) % 7) (e2 : q2 = (q3 + Y + c2) % 7)
    (e5 : q2 = (q1 + Z + c5) % 7) :
    ((q1 + 7 - q3) % 7 = 0 ∨ (q1 + 7 - q3) % 7 = 1 ∨ (q1 + 7 - q3) % 7 = 6) ∧
    ((q2 + 7 - q3) % 7 = 0 ∨ (q2 + 7 - q3) % 7 = 1 ∨ (q2 + 7 - q3) % 7 = 6) ∧
    ((q2 + 7 - q1) % 7 = 0 ∨ (q2 + 7 - q1) % 7 = 1 ∨ (q2 + 7 - q1) % 7 = 6) := by
  omega

theorem arith9_key (qx1 qy1 K X Y Z D cd c c4 cz t : ℕ) (hqx1 : qx1 < 7) (hqy1 : qy1 < 7)
    (hK : K < 7) (hZ : Z < 7) (hcd : cd < 2) (hc : c < 2) (hc4 : c4 < 2) (hcz : cz < 2)
    (eX : X = (qx1 + K) % 7) (eY : Y = (qy1 + 2 * K) % 7) (eD : D = (2 * X + cd) % 7)
    (ht : t = if (2 * qx1 + 14 - qy1) % 7 = 6 then 6 else 0) (eXt : X = t)
    (eZ : Y = (X + Z + cz) % 7)
    (hcase : (D = (Y + 0 + c) % 7 ∧ X = (Z + 0 + c4) % 7) ∨ (D = (Y + 1) % 7 ∧ X = (Z + 1) % 7)) :
    (X = 0 ∨ X = 6) ∧ (Y = 0 ∨ Y = 6) ∧ (Z = 0 ∨ Z = 6) := by
  split_ifs at ht <;> omega

theorem arith9_three (q1 q2 q3 qx qy K T c1 c2 : ℕ) (h1 : q1 < 7) (h2 : q2 < 7) (h3 : q3 < 7)
    (hc1 : c1 < 2) (hc2 : c2 < 2) (hT : T = 0 ∨ T = 5 ∨ T = 6)
    (hTe : (qy + 3 * K) % 7 = T)
    (htab : ((qx + K) % 7 ≤ 1 ∨ 5 ≤ (qx + K) % 7) ∧
      (((qy + 3 * K) % 7 + 7 - (qx + K) % 7) % 7 ≤ 1 ∨
        ((qy + 3 * K) % 7 + 7 - (qx + K) % 7) % 7 = 6))
    (e1 : q1 = (q3 + (qx + K) % 7 + c1) % 7) (e2 : q2 = (q3 + (qy + 3 * K) % 7 + c2) % 7) :
    ((q1 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q1 + 7 - q3) % 7) ∧
    ((q2 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q3) % 7) ∧
    ((q2 + 7 - q1) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q1) % 7) := by
  omega

/-! ## carry helpers in `ℕ` -/

theorem qq_add_nat {m a b s : ℕ} (h : a ≡ b + s [MOD 7 ^ (m + 1)]) :
    ∃ c < 2, qq m a = (qq m b + qq m s + c) % 7 := by
  obtain ⟨c, hc, h'⟩ := qarc_add_carry 7 m (by norm_num) b s
  exact ⟨c, hc, by unfold qq; rw [qarc_congr h]; exact h'⟩

theorem qq_top_nat {m a b : ℕ} (h : a ≡ b + 7 ^ m [MOD 7 ^ (m + 1)]) : qq m a = (qq m b + 1) % 7 := by
  unfold qq; rw [qarc_congr h]
  have := qarc_add_topmul 7 m (by norm_num) b 1 (by norm_num)
  rwa [mul_one] at this

theorem qq_double_nat (m a : ℕ) : ∃ c < 2, qq m (2 * a) = (2 * qq m a + c) % 7 := by
  obtain ⟨c, hc, h⟩ := qarc_add_carry 7 m (by norm_num) a a
  refine ⟨c, hc, ?_⟩
  unfold qq; rw [show 2 * a = a + a by ring, h]; omega

theorem qq_zero (m : ℕ) (mu : ℕ) : qq m (mu * 0) = 0 := by simp [qq, qarc]

theorem modEq_of_cast {N a b : ℕ} (h : (a : ZMod N) = b) : a ≡ b [MOD N] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp h

theorem nu_le_of_lt {m e : ℕ} (he : e ≠ 0) (hlt : e < 7 ^ (m + 1)) : nu 7 e ≤ m := by
  by_contra hc
  have hd : 7 ^ (m + 1) ∣ e := (pow_dvd_pow 7 (by omega)).trans (pow_nu_dvd 7 e)
  exact he (Nat.eq_zero_of_dvd_of_lt hd hlt)

theorem top_form {m e : ℕ} (he : e ≠ 0) (hlt : e < 7 ^ (m + 1)) (hnu : nu 7 e = m) :
    ∃ w, 0 < w ∧ w < 7 ∧ e = 7 ^ m * w := by
  obtain ⟨w, hw⟩ := hnu ▸ pow_nu_dvd 7 e
  refine ⟨w, ?_, ?_, hw⟩
  · rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0, mul_zero] at hw; exact absurd hw he
    · exact h0
  · by_contra hc; push Not at hc
    have : 7 ^ m * 7 ≤ 7 ^ m * w := Nat.mul_le_mul_left _ hc
    rw [← pow_succ] at this; omega

theorem exists_top_inv {w : ℕ} (h0 : 0 < w) (h7 : w < 7) : ∃ l ∈ LamTop 7, l * w % 7 = 1 := by
  have key : ∀ w < 7, 0 < w → ∃ l < 7, 1 ≤ l ∧ l * w % 7 = 1 := by decide
  obtain ⟨l, hl7, hl1, hlw⟩ := key w h7 h0
  exact ⟨l, (mem_LamTop 7 l).mpr ⟨hl1, by omega⟩, hlw⟩

theorem top_mul {m e w l : ℕ} (he : e = 7 ^ m * w) (hl : l * w % 7 = 1) :
    l * e ≡ 7 ^ m [MOD 7 ^ (m + 1)] := by
  obtain ⟨t, ht⟩ : ∃ t, l * w = 7 * t + 1 := ⟨l * w / 7, by have := Nat.div_add_mod (l * w) 7; omega⟩
  have : l * e = 7 ^ m + 7 ^ (m + 1) * t := by
    rw [he, show l * (7 ^ m * w) = 7 ^ m * (l * w) by ring, ht, pow_succ]; ring
  unfold Nat.ModEq; rw [this, Nat.add_mul_mod_self_left]

theorem rp_mul_unit {l x : ℕ} (hl : ¬ 7 ∣ l) (hx : x ≠ 0) : rp 7 (l * x) = (l * rp 7 x) % 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hl0 : l ≠ 0 := by rintro rfl; exact hl (dvd_zero 7)
  have hcop : Nat.Coprime l 7 := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hl)
  unfold rp
  rw [nu_mul_coprime 7 l x hcop hl0 hx, Nat.mul_div_assoc l (pow_nu_dvd 7 x)]
  rw [Nat.mul_mod, Nat.mul_mod l ((x / 7 ^ nu 7 x) % 7), Nat.mod_mod]

theorem not_dvd_of_coprime {l : ℕ} (h : Nat.Coprime l 7) : ¬ 7 ∣ l := by
  intro hd
  have := Nat.Coprime.coprime_dvd_right hd (Nat.coprime_comm.mp h)
  norm_num at this

/-- `2x - y` is divisible by `7^(h+1)` when `x, y` sit at level `h` with `r(y) = 2 r(x)`. -/
theorem dvd_dsub_two {m h x y : ℕ} (hhm : h ≤ m) (hx : nu 7 x = h) (hy : nu 7 y = h)
    (hr : rp 7 y = 2 * rp 7 x % 7) : 7 ^ (h + 1) ∣ dsub (7 ^ (m + 1)) (2 * x) y := by
  set u := x / 7 ^ h
  set w := y / 7 ^ h
  have hxu : x = 7 ^ h * u := (Nat.mul_div_cancel' (hx ▸ pow_nu_dvd 7 x)).symm
  have hyw : y = 7 ^ h * w := (Nat.mul_div_cancel' (hy ▸ pow_nu_dvd 7 y)).symm
  have hru : rp 7 x = u % 7 := by unfold rp; rw [hx]
  have hrw : rp 7 y = w % 7 := by unfold rp; rw [hy]
  have h2 : 2 * u ≡ w [MOD 7] := by unfold Nat.ModEq; omega
  have h3 : 2 * x ≡ y [MOD 7 ^ (h + 1)] := by
    have := h2.mul_left' (7 ^ h)
    rw [pow_succ, hxu, hyw, show 2 * (7 ^ h * u) = 7 ^ h * (2 * u) by ring]; exact this
  have h4 : 2 * x ≡ y + dsub (7 ^ (m + 1)) (2 * x) y [MOD 7 ^ (h + 1)] :=
    Nat.ModEq.of_dvd (pow_dvd_pow 7 (by omega)) (modEq_add_dsub _ _ _ (N_pos m))
  have h5 : y + dsub (7 ^ (m + 1)) (2 * x) y ≡ y + 0 [MOD 7 ^ (h + 1)] := by
    rw [add_zero]; exact h4.symm.trans h3
  exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' y h5)

/-! ## Lemma 9 (i) -/

/-- Step A of Lemma 9 (i) and Lemma 9 (ii) (first multiplier): for a residue `e` divisible by
`7^v`, `v ≤ m`, find a unit `lam1` such that every `mu ≡ 1 [MOD 7^(m+1-v)]` gives
`q(mu lam1 e) = 0` or `mu lam1 e ≡ 7^m`. `lam1` is `1`, in `Lam (nu e)`, or in `LamTop`. -/
theorem step_top_or_zero (m v e : ℕ) (hvm : v ≤ m) (helt : e < 7 ^ (m + 1)) (hdvd : 7 ^ v ∣ e) :
    ∃ lam1, (lam1 = 1 ∨ (nu 7 e < m ∧ lam1 ∈ Lam (nu 7 e) m 7) ∨ lam1 ∈ LamTop 7) ∧
      Nat.Coprime lam1 7 ∧ lam1 ≠ 0 ∧ lam1 ≡ 1 [MOD 7 ^ (m - nu 7 e)] ∧
      ∀ mu, mu ≡ 1 [MOD 7 ^ (m + 1 - v)] →
        (qq m (mu * (lam1 * e)) = 0 ∨ mu * (lam1 * e) ≡ 7 ^ m [MOD 7 ^ (m + 1)]) := by
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · subst he0
    refine ⟨1, Or.inl rfl, by norm_num, by norm_num, Nat.ModEq.refl _, ?_⟩
    intro mu _; left; simp [qq, qarc]
  have hle := nu_le_of_lt he0.ne' helt
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 e) (m := m) (x := e) (t := 0)
      (by norm_num) hle rfl he0.ne' (by norm_num)
    have hmem : 1 + 7 ^ (m - nu 7 e) * k ∈ Lam (nu 7 e) m 7 :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    have h7 := Lam_modEq_seven hlt hmem
    obtain ⟨hcop, hne⟩ := coprime_of_modEq_one (by norm_num) h7
    refine ⟨_, Or.inr (Or.inl ⟨hlt, hmem⟩), hcop, hne, Lam_modEq_one hmem, ?_⟩
    intro mu hmu; left
    unfold qq
    rw [qarc_mul_fix (by omega) hmu (dvd_mul_of_dvd_right hdvd _)]
    exact hkq
  · obtain ⟨w, hw0, hw7, hw⟩ := top_form he0.ne' helt heq
    obtain ⟨l, hlmem, hlw⟩ := exists_top_inv hw0 hw7
    have hcop := LamTop_coprime 7 (by norm_num) l hlmem
    have hl0 : l ≠ 0 := by rw [mem_LamTop] at hlmem; omega
    refine ⟨l, Or.inr (Or.inr hlmem), hcop, hl0, by rw [heq, Nat.sub_self, pow_zero]; exact Nat.modEq_one, ?_⟩
    intro mu hmu; right
    have hmu7 : mu ≡ 1 [MOD 7 ^ (m + 1 - m)] := modEq_one_mono hmu (by omega)
    have hd : 7 ^ m ∣ l * e := by rw [hw]; exact Dvd.intro_left (l * w) (by ring)
    exact (mul_modEq_self_of_dvd (by omega) hmu7 hd).trans (top_mul hw hlw)

theorem lemma9_i_core (m b1 b2 b3 x y : ℕ) (hxd : x = dsub (7 ^ (m + 1)) b1 b3)
    (hyd : y = dsub (7 ^ (m + 1)) b2 b3) (hx0 : x ≠ 0) (hy : y = 0 ∨ (y ≠ 0 ∧ nu 7 y < nu 7 x)) :
    ∃ lam, Nat.Coprime lam 7 ∧ lam ≡ 1 [MOD 7 ^ (m - nu 7 x)] ∧
      ellq m (lam * b1) (lam * b2) (lam * b3) ≤ 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  have hxlt : x < 7 ^ (m + 1) := hxd ▸ dsub_lt _ _ _ hN
  have hxm := nu_le_of_lt hx0 hxlt
  obtain ⟨lam1, _, hc1, hne1, hmod1, hstep⟩ :=
    step_top_or_zero m (nu 7 x) x hxm hxlt (pow_nu_dvd 7 x)
  -- the second multiplier
  obtain ⟨lam2, hc2, hmod2, hmu2, hqy⟩ : ∃ lam2, Nat.Coprime lam2 7 ∧
      lam2 ≡ 1 [MOD 7 ^ (m - nu 7 x)] ∧ lam2 ≡ 1 [MOD 7 ^ (m + 1 - nu 7 x)] ∧
      qq m (lam2 * (lam1 * y)) = 0 := by
    rcases hy with hy0 | ⟨hy0, hlt⟩
    · refine ⟨1, by norm_num, Nat.ModEq.refl _, Nat.ModEq.refl _, ?_⟩
      rw [hy0, mul_zero]; exact qq_zero m 1
    · have hnu1 : nu 7 (lam1 * y) = nu 7 y := nu_mul_coprime 7 lam1 y hc1 hne1 hy0
      obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 y) (m := m) (x := lam1 * y)
        (t := 0) (by norm_num) (by omega) hnu1 (Nat.mul_ne_zero hne1 hy0) (by norm_num)
      have hmem : 1 + 7 ^ (m - nu 7 y) * k ∈ Lam (nu 7 y) m 7 :=
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      have hl := Lam_modEq_one hmem
      obtain ⟨hcop, _⟩ := coprime_of_modEq_one (by norm_num) (Lam_modEq_seven (by omega) hmem)
      exact ⟨_, hcop, modEq_one_mono hl (by omega), modEq_one_mono hl (by omega), hkq⟩
  refine ⟨lam2 * lam1, Nat.Coprime.mul_left hc2 hc1, modEq_one_mul hmod2 hmod1, ?_⟩
  -- relations
  have hb1 : lam2 * lam1 * b1 ≡ lam2 * lam1 * b3 + lam2 * (lam1 * x) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hxd, dsub_cast _ _ _ hN]; ring
  have hb2 : lam2 * lam1 * b2 ≡ lam2 * lam1 * b3 + lam2 * (lam1 * y) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hyd, dsub_cast _ _ _ hN]; ring
  obtain ⟨c2, hc2', hq2⟩ := qq_add_nat hb2
  rw [hqy] at hq2
  have h1 := qq_lt m (lam2 * lam1 * b1); have h2 := qq_lt m (lam2 * lam1 * b2)
  have h3 := qq_lt m (lam2 * lam1 * b3)
  unfold ellq
  rcases hstep lam2 hmu2 with hz | htop
  · obtain ⟨c1, hc1', hq1⟩ := qq_add_nat hb1
    rw [hz] at hq1
    exact ell3_core2 _ _ _ h1 h2 h3 (by omega) (by omega) (by omega)
  · have hq1 := qq_top_nat (hb1.trans (htop.add_left _))
    exact ell3_core2 _ _ _ h1 h2 h3 (by omega) (by omega) (by omega)

theorem ellq_swap12 (m a b c : ℕ) : ellq m a b c = ellq m b a c := by
  unfold ellq; rw [Finset.insert_comm]

/-- **Lemma 9 (i).** `x = b1 - b3`, `y = b2 - b3` (residues) with `nu x ≠ nu y`: some unit
`lam ≡ 1 [MOD 7^(m - max(nu x, nu y))]` has `l(q(lam B)) ≤ 2`. -/
theorem lemma9_i (m b1 b2 b3 x y : ℕ) (hxd : x = dsub (7 ^ (m + 1)) b1 b3)
    (hyd : y = dsub (7 ^ (m + 1)) b2 b3) (hne : nu 7 x ≠ nu 7 y) :
    ∃ lam, Nat.Coprime lam 7 ∧ lam ≡ 1 [MOD 7 ^ (m - max (nu 7 x) (nu 7 y))] ∧
      ellq m (lam * b1) (lam * b2) (lam * b3) ≤ 2 := by
  have h00 : nu 7 0 = 0 := by simp [nu]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- y is higher: swap the roles of b1 and b2
    have hy0 : y ≠ 0 := by rintro rfl; rw [h00] at hlt; omega
    have hx : x = 0 ∨ (x ≠ 0 ∧ nu 7 x < nu 7 y) := by
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨hx0, hlt⟩
    obtain ⟨lam, hc, hmod, hell⟩ := lemma9_i_core m b2 b1 b3 y x hyd hxd hy0 hx
    refine ⟨lam, hc, by rw [max_eq_right hlt.le]; exact hmod, ?_⟩
    rw [ellq_swap12]; exact hell
  · have hx0 : x ≠ 0 := by rintro rfl; rw [h00] at hgt; omega
    have hy : y = 0 ∨ (y ≠ 0 ∧ nu 7 y < nu 7 x) := by
      by_cases hy0 : y = 0
      · exact Or.inl hy0
      · exact Or.inr ⟨hy0, hgt⟩
    obtain ⟨lam, hc, hmod, hell⟩ := lemma9_i_core m b1 b2 b3 x y hxd hyd hx0 hy
    exact ⟨lam, hc, by rw [max_eq_left hgt.le]; exact hmod, hell⟩

/-! ## Lemma 9 (ii), j = 3 -/

/-- The paper's table: target `q(lam y)` from `3 q(y) + 5 q(x)`. -/
def T3 (s : ℕ) : ℕ := if s = 0 ∨ s = 2 then 0 else if s = 3 ∨ s = 5 then 5 else 6

theorem tab3_fin : ∀ qx qy K : Fin 7,
    ((qy : ℕ) + 3 * K) % 7 = T3 ((3 * (qy : ℕ) + 5 * qx) % 7) →
    (((qx : ℕ) + K) % 7 ≤ 1 ∨ 5 ≤ ((qx : ℕ) + K) % 7) ∧
      ((((qy : ℕ) + 3 * K) % 7 + 7 - ((qx : ℕ) + K) % 7) % 7 ≤ 1 ∨
        (((qy : ℕ) + 3 * K) % 7 + 7 - ((qx : ℕ) + K) % 7) % 7 = 6) := by
  decide +kernel

theorem tab3_core' (qx qy K : ℕ) (hx : qx < 7) (hy : qy < 7) (hK : K < 7)
    (h : (qy + 3 * K) % 7 = T3 ((3 * qy + 5 * qx) % 7)) :
    ((qx + K) % 7 ≤ 1 ∨ 5 ≤ (qx + K) % 7) ∧
      (((qy + 3 * K) % 7 + 7 - (qx + K) % 7) % 7 ≤ 1 ∨
        ((qy + 3 * K) % 7 + 7 - (qx + K) % 7) % 7 = 6) :=
  tab3_fin ⟨qx, hx⟩ ⟨qy, hy⟩ ⟨K, hK⟩ h

theorem T3_lt (s : ℕ) : T3 s < 7 := by unfold T3; split_ifs <;> norm_num

theorem T3_mem (s : ℕ) : T3 s = 0 ∨ T3 s = 5 ∨ T3 s = 6 := by unfold T3; split_ifs <;> simp

/-- **Lemma 9 (ii), `j = 3`.** `x, y` nonzero residues at level `h < m` with `r(y) = 3 r(x)`:
some `lam ∈ Lam h m 7` has `q(lam y) ∈ {0, 5, 6}` and `l(q(lam B)) ≤ 3`. -/
theorem lemma9_ii_three (m h b1 b2 b3 x y : ℕ) (hhm : h < m) (hxd : x = dsub (7 ^ (m + 1)) b1 b3)
    (hyd : y = dsub (7 ^ (m + 1)) b2 b3) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = h)
    (hy : nu 7 y = h) (hr : rp 7 y = 3 * rp 7 x % 7) :
    ∃ lam ∈ Lam h m 7, (qq m (lam * y) = 0 ∨ qq m (lam * y) = 5 ∨ qq m (lam * y) = 6) ∧
      ellq m (lam * b1) (lam * b2) (lam * b3) ≤ 3 := by
  have hN := N_pos m
  set s := (3 * qq m y + 5 * qq m x) % 7
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := y) (t := T3 s)
    (by norm_num) hhm.le hy hy0 (T3_lt s)
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  refine ⟨_, hmem, ?_, ?_⟩
  · have hq : qq m ((1 + 7 ^ (m - h) * k) * y) = T3 s := hkq
    rw [hq]; exact T3_mem s
  set lam := 1 + 7 ^ (m - h) * k with hlam
  have hqx : qq m (lam * x) = (qq m x + k * rp 7 x) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk x hx
  have hqy : qq m (lam * y) = (qq m y + k * rp 7 y) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk y hy
  have hK : (k * rp 7 y) % 7 = (3 * ((k * rp 7 x) % 7)) % 7 := by
    have := ((show rp 7 y ≡ 3 * rp 7 x [MOD 7] by rw [hr]; exact Nat.mod_modEq _ _).mul_left k)
    unfold Nat.ModEq at this
    rw [show k * (3 * rp 7 x) = 3 * (k * rp 7 x) by ring] at this; omega
  have hT : (qq m y + 3 * ((k * rp 7 x) % 7)) % 7 = T3 s := by
    rw [← hkq]; unfold qq at hqy ⊢; rw [hqy]; omega
  have htab := tab3_core' (qq m x) (qq m y) ((k * rp 7 x) % 7) (qq_lt m x) (qq_lt m y)
    (Nat.mod_lt _ (by norm_num)) hT
  have hb1 : lam * b1 ≡ lam * b3 + lam * x [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hxd, dsub_cast _ _ _ hN]; ring
  have hb2 : lam * b2 ≡ lam * b3 + lam * y [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hyd, dsub_cast _ _ _ hN]; ring
  obtain ⟨c1, hc1, hq1⟩ := qq_add_nat hb1
  obtain ⟨c2, hc2, hq2⟩ := qq_add_nat hb2
  have h1 := qq_lt m (lam * b1); have h2 := qq_lt m (lam * b2); have h3 := qq_lt m (lam * b3)
  have hqx' : qq m (lam * x) = (qq m x + (k * rp 7 x) % 7) % 7 := by rw [hqx, Nat.add_mod_mod]
  have hqy' : qq m (lam * y) = (qq m y + 3 * ((k * rp 7 x) % 7)) % 7 := by
    rw [hqy, ← Nat.add_mod_mod, hK, Nat.add_mod_mod]
  rw [hqx'] at hq1; rw [hqy'] at hq2
  have hTe : (qq m y + 3 * ((k * rp 7 x) % 7)) % 7 = T3 s := hT
  obtain ⟨a1, a2, a3⟩ := arith9_three _ _ _ _ _ _ _ _ _ h1 h2 h3 hc1 hc2 (T3_mem s) hTe htab hq1 hq2
  unfold ellq
  exact ell3_core3 _ _ _ h1 h2 h3 a1 a2 a3

/-! ## Lemma 9 (ii), j = 2 -/

/-- **Lemma 9 (ii), `j = 2`.** `x, y` nonzero residues at level `h < m` with `r(y) = 2 r(x)`,
`e = e(x, y) = 2x - y`: `lam = lam2 * lam1` with `lam2 ∈ Lam h m 7`, `lam1` equal to `1`, in
`Lam (nu e) m 7`, or in `LamTop 7`, such that `q(lam y) ∈ {0, 6}` and `l(q(lam B)) ≤ 2`. -/
theorem lemma9_ii_two (m h b1 b2 b3 x y : ℕ) (hhm : h < m) (hxd : x = dsub (7 ^ (m + 1)) b1 b3)
    (hyd : y = dsub (7 ^ (m + 1)) b2 b3) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = h)
    (hy : nu 7 y = h) (hr : rp 7 y = 2 * rp 7 x % 7) :
    ∃ lam1 lam2, lam2 ∈ Lam h m 7 ∧
      (lam1 = 1 ∨ (nu 7 (ediff m x y) < m ∧ lam1 ∈ Lam (nu 7 (ediff m x y)) m 7) ∨ lam1 ∈ LamTop 7) ∧
      Nat.Coprime (lam2 * lam1) 7 ∧
      (qq m (lam2 * lam1 * y) = 0 ∨ qq m (lam2 * lam1 * y) = 6) ∧
      ellq m (lam2 * lam1 * b1) (lam2 * lam1 * b2) (lam2 * lam1 * b3) ≤ 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  set e := dsub (7 ^ (m + 1)) (2 * x) y with he
  have hediff : ediff m x y = e := (ediff_branch1 m x y hr).1
  rw [hediff]
  have hdvd : 7 ^ (h + 1) ∣ e := dvd_dsub_two hhm.le hx hy hr
  obtain ⟨lam1, hrec1, hc1, hne1, _, hstep⟩ :=
    step_top_or_zero m (h + 1) e (by omega) (dsub_lt _ _ _ hN) hdvd
  have hnx1 : nu 7 (lam1 * x) = h := (nu_mul_coprime 7 lam1 x hc1 hne1 hx0).trans hx
  have hny1 : nu 7 (lam1 * y) = h := (nu_mul_coprime 7 lam1 y hc1 hne1 hy0).trans hy
  have hx10 : lam1 * x ≠ 0 := Nat.mul_ne_zero hne1 hx0
  have hr1 : rp 7 (lam1 * y) = 2 * rp 7 (lam1 * x) % 7 := by
    rw [rp_mul_unit (not_dvd_of_coprime hc1) hy0, rp_mul_unit (not_dvd_of_coprime hc1) hx0, hr]
    have a := (Nat.mod_modEq (2 * rp 7 x) 7).mul_left lam1
    unfold Nat.ModEq at a
    rw [show lam1 * (2 * rp 7 x) = 2 * (lam1 * rp 7 x) by ring] at a
    omega
  -- target for q(lam2 lam1 x)
  obtain ⟨t, ht⟩ : ∃ t, t = if (2 * qq m (lam1 * x) + 14 - qq m (lam1 * y)) % 7 = 6 then 6 else 0 :=
    ⟨_, rfl⟩
  have htlt : t < 7 := by rw [ht]; split_ifs <;> norm_num
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := lam1 * x) (t := t)
    (by norm_num) hhm.le hnx1 hx10 htlt
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 :=
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  set lam2 := 1 + 7 ^ (m - h) * k with hlam2
  obtain ⟨hc2, _⟩ := coprime_of_modEq_one (by norm_num) (Lam_modEq_seven hhm hmem)
  refine ⟨lam1, lam2, hmem, hrec1, Nat.Coprime.mul_left hc2 hc1, ?_⟩
  -- digit facts
  have hqx : qq m (lam2 * (lam1 * x)) = (qq m (lam1 * x) + k * rp 7 (lam1 * x)) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk _ hnx1
  have hqy : qq m (lam2 * (lam1 * y)) = (qq m (lam1 * y) + k * rp 7 (lam1 * y)) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk _ hny1
  have hK : (k * rp 7 (lam1 * y)) % 7 = (2 * ((k * rp 7 (lam1 * x)) % 7)) % 7 := by
    have := ((show rp 7 (lam1 * y) ≡ 2 * rp 7 (lam1 * x) [MOD 7] by
      rw [hr1]; exact Nat.mod_modEq _ _).mul_left k)
    unfold Nat.ModEq at this
    rw [show k * (2 * rp 7 (lam1 * x)) = 2 * (k * rp 7 (lam1 * x)) by ring] at this; omega
  have hxt : qq m (lam2 * (lam1 * x)) = t := hkq
  -- 2 x' ≡ y' + e'
  have h2x : 2 * (lam2 * (lam1 * x)) ≡ lam2 * (lam1 * y) + lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [he, dsub_cast _ _ _ hN]; push_cast; ring
  obtain ⟨cd, hcd, hdouble⟩ := qq_double_nat m (lam2 * (lam1 * x))
  have hyz : lam2 * (lam1 * y) ≡ lam2 * (lam1 * x) +
      dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast
    rw [hxd, hyd]; simp only [dsub_cast _ _ _ hN]; push_cast; ring
  have hxz : lam2 * (lam1 * x) ≡ dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1) +
      lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast
    have a1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2x
    have a2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hyz
    push_cast at a1 a2 ⊢
    linear_combination a1 + a2
  obtain ⟨cz, hcz, hqz⟩ := qq_add_nat hyz
  have hbx : lam2 * lam1 * b1 ≡ lam2 * lam1 * b3 + lam2 * (lam1 * x) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hxd, dsub_cast _ _ _ hN]; ring
  have hby : lam2 * lam1 * b2 ≡ lam2 * lam1 * b3 + lam2 * (lam1 * y) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [hyd, dsub_cast _ _ _ hN]; ring
  have hb21 : lam2 * lam1 * b2 ≡ lam2 * lam1 * b1 +
      dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1) [MOD 7 ^ (m + 1)] :=
    modEq_add_dsub _ _ _ hN
  obtain ⟨c1, hc1', hq1⟩ := qq_add_nat hbx
  obtain ⟨c2, hc2', hq2⟩ := qq_add_nat hby
  obtain ⟨c5, hc5, hq5⟩ := qq_add_nat hb21
  have hmu : lam2 ≡ 1 [MOD 7 ^ (m + 1 - (h + 1))] := by
    rw [show m + 1 - (h + 1) = m - h by omega]; exact Lam_modEq_one hmem
  have hX := qq_lt m (lam1 * x); have hY := qq_lt m (lam1 * y)
  have hZ := qq_lt m (dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1))
  have hXl := qq_lt m (lam2 * (lam1 * x)); have hYl := qq_lt m (lam2 * (lam1 * y))
  have h1 := qq_lt m (lam2 * lam1 * b1); have h2 := qq_lt m (lam2 * lam1 * b2)
  have h3 := qq_lt m (lam2 * lam1 * b3)
  have hqx' : qq m (lam2 * (lam1 * x)) = (qq m (lam1 * x) + (k * rp 7 (lam1 * x)) % 7) % 7 := by
    rw [hqx, Nat.add_mod_mod]
  have hqy' : qq m (lam2 * (lam1 * y)) = (qq m (lam1 * y) + 2 * ((k * rp 7 (lam1 * x)) % 7)) % 7 := by
    rw [hqy, ← Nat.add_mod_mod, hK, Nat.add_mod_mod]
  have hKx : (k * rp 7 (lam1 * x)) % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hyx : lam2 * lam1 * y = lam2 * (lam1 * y) := by ring
  have key : (qq m (lam2 * (lam1 * x)) = 0 ∨ qq m (lam2 * (lam1 * x)) = 6) ∧
      (qq m (lam2 * (lam1 * y)) = 0 ∨ qq m (lam2 * (lam1 * y)) = 6) ∧
      (qq m (dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1)) = 0 ∨
        qq m (dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1)) = 6) := by
    rcases hstep lam2 hmu with hz0 | htop
    · obtain ⟨c, hc, hqa⟩ := qq_add_nat h2x
      obtain ⟨c4, hc4, hqb⟩ := qq_add_nat hxz
      rw [hz0] at hqa hqb
      exact arith9_key _ _ _ _ _ _ _ cd c c4 cz t hX hY hKx hZ hcd hc hc4 hcz hqx' hqy' hdouble ht
        hxt hqz (Or.inl ⟨hqa, hqb⟩)
    · have hqa := qq_top_nat (h2x.trans (Nat.ModEq.add_left _ htop))
      have hqb := qq_top_nat (hxz.trans (Nat.ModEq.add_left _ htop))
      exact arith9_key _ _ _ _ _ _ _ cd 0 0 cz t hX hY hKx hZ hcd (by norm_num) (by norm_num) hcz
        hqx' hqy' hdouble ht hxt hqz (Or.inr ⟨hqa, hqb⟩)
  obtain ⟨kX, kY, kZ⟩ := key
  refine ⟨by rw [hyx]; exact kY, ?_⟩
  obtain ⟨a1, a2, a3⟩ := arith9_final2 _ _ _ _ _ _ c1 c2 c5 h1 h2 h3 hc1' hc2' hc5 kX kY kZ hq1 hq2 hq5
  unfold ellq
  exact ell3_core2 _ _ _ h1 h2 h3 a1 a2 a3

end LRSpectrumFull.BarajasSerra.Sec6
