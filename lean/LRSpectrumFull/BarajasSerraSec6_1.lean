import LRSpectrumFull.BarajasSerraSec6L10

/-!
# E6 session 18: Barajas-Serra Section 6.1 (`|A1| = 5`), case (a), `m ≥ 2`

Five level-0 speeds in one class mod 7 (`A1`, after the sign flips; `A2 = A4 = ∅`). Conclusion:
a multiplier `lam` prime to 7 with `q(lam d) ∉ {0, 6}` for all five (`sec61`), and the real form
with one extra top speed (`nu = m`): `nearestIntDist (t d) ≥ 1/7` for all six (`sec61_witness`).

Route (paper, 6.1, with the recorded corrections):
* `nu(E) = {m}` (all ten differences nonzero at the top level): the offsets `w_i` are five distinct
  residues mod 7; a unit rescale puts them in a window of length 5 (`z7_sec61`).
* otherwise Lemma 10 (on `d0..d3`) plus `d4` gives a triple `B` with `nu(x) ≠ nu(y)` (Lemma 9 (i)),
  or one level `h < m` with `r(y) = 2 r(x)` (Lemma 9 (ii), `j = 2`), or all congruent. Lemma 9 is
  re-proved here with the stronger output the paper uses (via Remark 8 (i)): `B` lies in a closed
  window of width `N/7` (`Wb`). Then the multiplier `1` or `3` puts all five `q`-values in a window of
  length 5 (`trick3`; paper's "`q(3·A1) ⊂ {0,1,2,5,6}` or `{0,1,4,5,6}`"), and a `Lambda_0` shift ends.
Erratum (harmless): the paper writes "`ℓ(A1) ≤ 4`" when `{q(d4), q(d5)} ≠ {2, 4}`; the bound is 5.
Paper typo: the second "Suppose now that `ν(E) ≠ {m}`" means `ν(E) = {m}`.

Falsified first: `e6s18/lean18.rs` (`win`, `trick`, `sub`): window lemmas 0 failures (negative
control, width `M - 1`: 25284 failures at m = 2); `trick3` 0 failures (negative control, multiplier
1 only: 576240 failures); 6.1 conclusion m = 2 exhaustive over 5-multisets of class 1, 0 failures
(negative control, `Lambda_0` only: fails).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-! ## windows -/

/-- `x, y` lie in the closed window `[c, c + 7^m]` (circularly). -/
def Wb (m x y c : ℕ) : Prop := E m x c ≤ 7 ^ m ∧ E m y c ≤ 7 ^ m

theorem qq_bounds (m v : ℕ) :
    qq m v * 7 ^ m ≤ v % 7 ^ (m + 1) ∧ v % 7 ^ (m + 1) < (qq m v + 1) * 7 ^ m := by
  have hM : 0 < 7 ^ m := by positivity
  have hlt : v % 7 ^ (m + 1) < 7 * 7 ^ m := by rw [← pow_succ']; exact Nat.mod_lt _ (N_pos m)
  have hq : qq m v = v % 7 ^ (m + 1) / 7 ^ m := by
    unfold qq qarc; apply Nat.mod_eq_of_lt; exact (Nat.div_lt_iff_lt_mul hM).mpr hlt
  rw [hq]
  refine ⟨Nat.div_mul_le_self _ _, ?_⟩
  have := Nat.lt_div_mul_add (a := v % 7 ^ (m + 1)) hM
  rw [add_mul, one_mul]; exact this

theorem qq_small {m δ : ℕ} (h : δ < 7 ^ m) : qq m δ = 0 := by
  unfold qq qarc
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))),
    Nat.div_eq_of_lt h]

/-- carry with a small summand: `b ≡ c + δ`, `δ ≤ 7^m` gives `q(b) = q(c) + ε`, `ε ∈ {0, 1}`. -/
theorem carry_le {m b c δ : ℕ} (hb : b ≡ c + δ [MOD 7 ^ (m + 1)]) (hδ : δ ≤ 7 ^ m) :
    ∃ ε : ℕ, ε < 2 ∧ (qq m b : ZMod 7) = qq m c + ε := by
  rcases lt_or_eq_of_le hδ with hlt | heq
  · obtain ⟨c', hc', h⟩ := qq_add_nat hb
    rw [qq_small hlt] at h
    exact ⟨c', hc', by rw [h, ZMod.natCast_mod]; push_cast; ring⟩
  · subst heq
    refine ⟨1, by norm_num, ?_⟩
    rw [qq_top_nat hb, ZMod.natCast_mod]; push_cast; ring

theorem E_modEq (m x y : ℕ) : x ≡ y + E m x y [MOD 7 ^ (m + 1)] := modEq_add_dsub _ _ _ (N_pos m)

theorem E_eq_mod {m lam x y : ℕ} : E m (lam * x) (lam * y) = (lam * E m x y) % 7 ^ (m + 1) := by
  have h := dsub_mul (7 ^ (m + 1)) lam x y (N_pos m)
  unfold Nat.ModEq at h
  rw [← h, Nat.mod_eq_of_lt (E_lt m _ _)]

/-- the three-fold carry: `q(3x) = 3 q(x) + g`, `g ≤ 2`. -/
theorem qq_three (m x : ℕ) : ∃ g : ℕ, g < 3 ∧ (qq m (3 * x) : ZMod 7) = 3 * qq m x + g := by
  obtain ⟨g, hg, h⟩ := qarc_mul_smallint_carry 7 m (by norm_num) x 3 (by norm_num)
  refine ⟨g, by omega, ?_⟩
  unfold qq; rw [h, ZMod.natCast_mod]; push_cast; ring

theorem zmod_val_of_lt {a : ℕ} (h : a < 7) : ((a : ZMod 7)).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-! ## the multiplier-3 trick (6.1) -/

/-- `W5 a b c d e T`: the five values lie in `{T, ..., T+4}`. -/
def W5 (a b c d e T : ZMod 7) : Prop :=
  (a - T).val < 5 ∧ (b - T).val < 5 ∧ (c - T).val < 5 ∧ (d - T).val < 5 ∧ (e - T).val < 5

instance (a b c d e T : ZMod 7) : Decidable (W5 a b c d e T) := by unfold W5; infer_instance

theorem trick_z7 : ∀ e1 e2 q4 q5 : ZMod 7, e1.val < 2 → e2.val < 2 → (¬ ∃ T, W5 0 e1 e2 q4 q5 T) →
    ∀ c0 : ZMod 7, c0.val < 3 → ∀ g1 : ZMod 7, g1.val < 3 → (3 * e1 + g1 - c0).val < 4 →
    ∀ g2 : ZMod 7, g2.val < 3 → (3 * e2 + g2 - c0).val < 4 →
    ∀ g4 : ZMod 7, g4.val < 3 → ∀ g5 : ZMod 7, g5.val < 3 →
    ∃ T, W5 c0 (3 * e1 + g1) (3 * e2 + g2) (3 * q4 + g4) (3 * q5 + g5) T := by
  decide

theorem W5_shift (a b c d e T s : ZMod 7) (h : W5 a b c d e T) :
    W5 (a + s) (b + s) (c + s) (d + s) (e + s) (T + s) := by
  unfold W5 at *
  simp only [add_sub_add_right_eq_sub]; exact h

/-- three-step carry for `3 δ`, `δ ≤ 7^m`. -/
theorem carry_three {m b c δ : ℕ} (hb : b ≡ c + δ [MOD 7 ^ (m + 1)]) (hδ : δ ≤ 7 ^ m) :
    ∃ f : ℕ, f < 4 ∧ (qq m (3 * b) : ZMod 7) = qq m (3 * c) + f := by
  have h3 : 3 * b ≡ ((3 * c + δ) + δ) + δ [MOD 7 ^ (m + 1)] := by
    have := hb.mul_left 3; rw [show 3 * (c + δ) = ((3 * c + δ) + δ) + δ by ring] at this; exact this
  obtain ⟨e1, he1, h1⟩ := carry_le (Nat.ModEq.refl (3 * c + δ)) hδ
  obtain ⟨e2, he2, h2⟩ := carry_le (Nat.ModEq.refl ((3 * c + δ) + δ)) hδ
  obtain ⟨e3, he3, h4⟩ := carry_le h3 hδ
  refine ⟨e1 + e2 + e3, by omega, ?_⟩
  rw [h4, h2, h1]; push_cast; ring

theorem W5_of_eq {a b c d e T a' b' c' d' e' T' : ZMod 7} (h : W5 a b c d e T) (ha : a' - T' = a - T)
    (hb : b' - T' = b - T) (hc : c' - T' = c - T) (hd : d' - T' = d - T) (he : e' - T' = e - T) :
    W5 a' b' c' d' e' T' := by
  unfold W5 at *; rw [ha, hb, hc, hd, he]; exact h

theorem val_lt_of {a k : ℕ} (h : a < k) (hk : k ≤ 7) : ((a : ZMod 7)).val < k := by
  rw [zmod_val_of_lt (by omega)]; exact h

theorem trick_core (m b1 b2 c y1 y2 : ℕ) (hw : Wb m b1 b2 c) :
    ∃ μ, (μ = 1 ∨ μ = 3) ∧ ∃ T, W5 (qq m (μ * c)) (qq m (μ * b1)) (qq m (μ * b2)) (qq m (μ * y1))
      (qq m (μ * y2)) T := by
  obtain ⟨h1, h2⟩ := hw
  have hb1 := E_modEq m b1 c
  have hb2 := E_modEq m b2 c
  obtain ⟨e1, he1, q1⟩ := carry_le hb1 h1
  obtain ⟨e2, he2, q2⟩ := carry_le hb2 h2
  by_cases hW : ∃ T, W5 0 (e1 : ZMod 7) (e2 : ZMod 7) ((qq m y1 : ZMod 7) - (qq m c : ZMod 7))
      ((qq m y2 : ZMod 7) - (qq m c : ZMod 7)) T
  · obtain ⟨T, hT⟩ := hW
    refine ⟨1, Or.inl rfl, T + (qq m c : ZMod 7), ?_⟩
    simp only [one_mul]
    apply W5_of_eq hT <;> first | (rw [q1]; ring) | (rw [q2]; ring) | ring
  · obtain ⟨g0, hg0, t0⟩ := qq_three m c
    obtain ⟨g1, hg1, t1⟩ := qq_three m b1
    obtain ⟨g2, hg2, t2⟩ := qq_three m b2
    obtain ⟨g4, hg4, t4⟩ := qq_three m y1
    obtain ⟨g5, hg5, t5⟩ := qq_three m y2
    obtain ⟨f1, hf1, s1⟩ := carry_three hb1 h1
    obtain ⟨f2, hf2, s2⟩ := carry_three hb2 h2
    have v1 : (3 * (e1 : ZMod 7) + g1 - g0).val < 4 := by
      have : 3 * (e1 : ZMod 7) + g1 - g0 = (f1 : ZMod 7) := by
        have := s1; rw [t1, t0, q1] at this; linear_combination this
      rw [this]; exact val_lt_of hf1 (by norm_num)
    have v2 : (3 * (e2 : ZMod 7) + g2 - g0).val < 4 := by
      have : 3 * (e2 : ZMod 7) + g2 - g0 = (f2 : ZMod 7) := by
        have := s2; rw [t2, t0, q2] at this; linear_combination this
      rw [this]; exact val_lt_of hf2 (by norm_num)
    obtain ⟨T, hT⟩ := trick_z7 (e1 : ZMod 7) (e2 : ZMod 7) ((qq m y1 : ZMod 7) - (qq m c : ZMod 7))
      ((qq m y2 : ZMod 7) - (qq m c : ZMod 7)) (val_lt_of he1 (by norm_num))
      (val_lt_of he2 (by norm_num)) hW (g0 : ZMod 7) (val_lt_of hg0 (by norm_num))
      (g1 : ZMod 7) (val_lt_of hg1 (by norm_num)) v1 (g2 : ZMod 7) (val_lt_of hg2 (by norm_num)) v2
      (g4 : ZMod 7) (val_lt_of hg4 (by norm_num)) (g5 : ZMod 7) (val_lt_of hg5 (by norm_num))
    refine ⟨3, Or.inr rfl, T + 3 * (qq m c : ZMod 7), ?_⟩
    apply W5_of_eq hT
    · rw [t0]; ring
    · rw [t1, q1]; ring
    · rw [t2, q2]; ring
    · rw [t4]; ring
    · rw [t5]; ring

/-! ## residue arithmetic for windows -/

theorem two_cases {A B N : ℕ} (hA : A < N) (hB : B < 2 * N) (h : A ≡ B [MOD N]) : A = B ∨ A + N = B := by
  have hN : 0 < N := by omega
  have h1 : B % N = A := by unfold Nat.ModEq at h; rw [← h, Nat.mod_eq_of_lt hA]
  have h2 : B / N < 2 := (Nat.div_lt_iff_lt_mul hN).mpr (by linarith)
  have h3 := Nat.div_add_mod B N
  interval_cases hq : B / N
  · left; simp at h3; omega
  · right; simp at h3; omega

theorem E_add3 (m a b c : ℕ) :
    E m a c = E m b c + E m a b ∨ E m a c + 7 ^ (m + 1) = E m b c + E m a b := by
  have hc : E m a c ≡ E m b c + E m a b [MOD 7 ^ (m + 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast; rw [E_cast, E_cast, E_cast]; ring
  have := E_lt m a c; have := E_lt m b c; have := E_lt m a b
  exact two_cases (E_lt m a c) (by omega) hc

theorem E_swap_sum (m x y : ℕ) : E m y x + E m x y = 7 ^ (m + 1) ∨ (E m x y = 0 ∧ E m y x = 0) := by
  by_cases h0 : E m x y = 0
  · exact Or.inr ⟨h0, swap_zero m x y h0⟩
  · left
    have hc : 0 ≡ E m y x + E m x y [MOD 7 ^ (m + 1)] := by
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast; rw [E_cast, E_cast]; ring
    have := E_lt m x y; have := E_lt m y x
    rcases two_cases (N_pos m) (by omega) hc with h | h
    · omega
    · omega

theorem pos_of_qq {m v : ℕ} (h : qq m v = 0 ∨ qq m v = 6) :
    v % 7 ^ (m + 1) < 7 ^ m ∨ 6 * 7 ^ m ≤ v % 7 ^ (m + 1) := by
  obtain ⟨a, b⟩ := qq_bounds m v
  rcases h with h | h <;> rw [h] at a b
  · left; simpa using b
  · right; linarith

theorem win_of_three (M X Y Z A B C : ℕ) (hX : X < 7 * M) (hY : Y < 7 * M)
    (hZ : Z < 7 * M) (pX : X < M ∨ 6 * M ≤ X) (pY : Y < M ∨ 6 * M ≤ Y) (pZ : Z < M ∨ 6 * M ≤ Z)
    (rel : Y = X + Z ∨ Y + 7 * M = X + Z) (sA : A + X = 7 * M ∨ (X = 0 ∧ A = 0))
    (sB : B + Y = 7 * M ∨ (Y = 0 ∧ B = 0)) (sC : C + Z = 7 * M ∨ (Z = 0 ∧ C = 0)) :
    (X ≤ M ∧ Y ≤ M) ∨ (C ≤ M ∧ B ≤ M) ∨ (Z ≤ M ∧ A ≤ M) := by
  omega

/-! ## Lemma 9 with window output -/

theorem win9_i_core (m b1 b2 b3 x y : ℕ) (hxd : x = E m b1 b3) (hyd : y = E m b2 b3) (hx0 : x ≠ 0)
    (hy : y = 0 ∨ (y ≠ 0 ∧ nu 7 y < nu 7 x)) :
    ∃ lam, Nat.Coprime lam 7 ∧ Wb m (lam * b1) (lam * b2) (lam * b3) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  have hxlt : x < 7 ^ (m + 1) := hxd ▸ E_lt m b1 b3
  have hxm := nu_le_of_lt hx0 hxlt
  obtain ⟨lam1, _, hc1, hne1, _, hstep⟩ :=
    step_top_or_zero m (nu 7 x) x hxm hxlt (pow_nu_dvd 7 x)
  obtain ⟨lam2, hc2, hmu2, hqy⟩ : ∃ lam2, Nat.Coprime lam2 7 ∧
      lam2 ≡ 1 [MOD 7 ^ (m + 1 - nu 7 x)] ∧ qq m (lam2 * (lam1 * y)) = 0 := by
    rcases hy with hy0 | ⟨hy0, hlt⟩
    · refine ⟨1, by norm_num, Nat.ModEq.refl _, ?_⟩
      rw [hy0, mul_zero]; exact qq_zero m 1
    · have hnu1 : nu 7 (lam1 * y) = nu 7 y := nu_mul_coprime 7 lam1 y hc1 hne1 hy0
      obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 y) (m := m) (x := lam1 * y)
        (t := 0) (by norm_num) (by omega) hnu1 (Nat.mul_ne_zero hne1 hy0) (by norm_num)
      have hmem : 1 + 7 ^ (m - nu 7 y) * k ∈ Lam (nu 7 y) m 7 :=
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      have hl := Lam_modEq_one hmem
      obtain ⟨hcop, _⟩ := coprime_of_modEq_one (by norm_num) (Lam_modEq_seven (by omega) hmem)
      exact ⟨_, hcop, modEq_one_mono hl (by omega), hkq⟩
  refine ⟨lam2 * lam1, Nat.Coprime.mul_left hc2 hc1, ?_, ?_⟩
  · rw [E_eq_mod, ← hxd, mul_assoc]
    rcases hstep lam2 hmu2 with hz | htop
    · have := (qq_bounds m (lam2 * (lam1 * x))).2; rw [hz] at this; omega
    · rw [htop, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  · rw [E_eq_mod, ← hyd, mul_assoc]
    have := (qq_bounds m (lam2 * (lam1 * y))).2; rw [hqy] at this; omega

theorem Wb_swap {m x y c : ℕ} (h : Wb m x y c) : Wb m y x c := ⟨h.2, h.1⟩

/-- **Lemma 9 (i), window form.** -/
theorem win9_i (m b1 b2 b3 : ℕ) (hne : nu 7 (E m b1 b3) ≠ nu 7 (E m b2 b3)) :
    ∃ lam, Nat.Coprime lam 7 ∧ Wb m (lam * b1) (lam * b2) (lam * b3) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hy0 : E m b2 b3 ≠ 0 := by intro h; rw [h, nu_zero] at hlt; omega
    obtain ⟨lam, hc, hw⟩ := win9_i_core m b2 b1 b3 _ _ rfl rfl hy0
      (by by_cases hx0 : E m b1 b3 = 0; exact Or.inl hx0; exact Or.inr ⟨hx0, hlt⟩)
    exact ⟨lam, hc, Wb_swap hw⟩
  · have hx0 : E m b1 b3 ≠ 0 := by intro h; rw [h, nu_zero] at hgt; omega
    exact win9_i_core m b1 b2 b3 _ _ rfl rfl hx0
      (by by_cases hy0 : E m b2 b3 = 0; exact Or.inl hy0; exact Or.inr ⟨hy0, hgt⟩)

/-- the window predicate on an unordered triple. -/
def Win (m x y z : ℕ) : Prop := Wb m x y z ∨ Wb m z y x ∨ Wb m x z y

/-- **Lemma 9 (ii), `j = 2`, window form.** -/
theorem win9_ii (m h b1 b2 b3 x y : ℕ) (hhm : h < m) (hxd : x = E m b1 b3)
    (hyd : y = E m b2 b3) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = h)
    (hy : nu 7 y = h) (hr : rp 7 y = 2 * rp 7 x % 7) :
    ∃ lam, Nat.Coprime lam 7 ∧ Win m (lam * b1) (lam * b2) (lam * b3) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  set e := dsub (7 ^ (m + 1)) (2 * x) y with he
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
  obtain ⟨t, ht⟩ : ∃ t, t = if (2 * qq m (lam1 * x) + 14 - qq m (lam1 * y)) % 7 = 6 then 6 else 0 :=
    ⟨_, rfl⟩
  have htlt : t < 7 := by rw [ht]; split_ifs <;> norm_num
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := lam1 * x) (t := t)
    (by norm_num) hhm.le hnx1 hx10 htlt
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 :=
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  set lam2 := 1 + 7 ^ (m - h) * k with hlam2
  obtain ⟨hc2, _⟩ := coprime_of_modEq_one (by norm_num) (Lam_modEq_seven hhm hmem)
  refine ⟨lam2 * lam1, Nat.Coprime.mul_left hc2 hc1, ?_⟩
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
  have h2x : 2 * (lam2 * (lam1 * x)) ≡ lam2 * (lam1 * y) + lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [he, dsub_cast _ _ _ hN]; push_cast; ring
  obtain ⟨cd, hcd, hdouble⟩ := qq_double_nat m (lam2 * (lam1 * x))
  have hyz : lam2 * (lam1 * y) ≡ lam2 * (lam1 * x) +
      dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast
    rw [hxd, hyd]; simp only [E, dsub_cast _ _ _ hN]; push_cast; ring
  have hxz : lam2 * (lam1 * x) ≡ dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1) +
      lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast
    have a1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2x
    have a2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hyz
    push_cast at a1 a2 ⊢
    linear_combination a1 + a2
  obtain ⟨cz, hcz, hqz⟩ := qq_add_nat hyz
  have hmu : lam2 ≡ 1 [MOD 7 ^ (m + 1 - (h + 1))] := by
    rw [show m + 1 - (h + 1) = m - h by omega]; exact Lam_modEq_one hmem
  have hX := qq_lt m (lam1 * x); have hY := qq_lt m (lam1 * y)
  have hZ := qq_lt m (dsub (7 ^ (m + 1)) (lam2 * lam1 * b2) (lam2 * lam1 * b1))
  have hqx' : qq m (lam2 * (lam1 * x)) = (qq m (lam1 * x) + (k * rp 7 (lam1 * x)) % 7) % 7 := by
    rw [hqx, Nat.add_mod_mod]
  have hqy' : qq m (lam2 * (lam1 * y)) = (qq m (lam1 * y) + 2 * ((k * rp 7 (lam1 * x)) % 7)) % 7 := by
    rw [hqy, ← Nat.add_mod_mod, hK, Nat.add_mod_mod]
  have hKx : (k * rp 7 (lam1 * x)) % 7 < 7 := Nat.mod_lt _ (by norm_num)
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
  -- positions
  set L := lam2 * lam1 with hL
  have eX : E m (L * b1) (L * b3) = (lam2 * (lam1 * x)) % 7 ^ (m + 1) := by
    rw [E_eq_mod, ← hxd, hL, mul_assoc]
  have eY : E m (L * b2) (L * b3) = (lam2 * (lam1 * y)) % 7 ^ (m + 1) := by
    rw [E_eq_mod, ← hyd, hL, mul_assoc]
  have pX := pos_of_qq kX
  have pY := pos_of_qq kY
  have pZ := pos_of_qq kZ
  rw [Nat.mod_eq_of_lt (dsub_lt _ _ _ hN)] at pZ
  rw [← eX] at pX; rw [← eY] at pY
  have rel := E_add3 m (L * b2) (L * b1) (L * b3)
  have sA := E_swap_sum m (L * b1) (L * b3)
  have sB := E_swap_sum m (L * b2) (L * b3)
  have sC := E_swap_sum m (L * b2) (L * b1)
  have l1 := E_lt m (L * b1) (L * b3); have l2 := E_lt m (L * b2) (L * b3)
  have l3 := E_lt m (L * b2) (L * b1)
  unfold Win Wb
  have hpow : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hM : 0 < 7 ^ m := by positivity
  rw [hpow] at rel sA sB sC l1 l2 l3
  change dsub (7 ^ (m + 1)) (L * b2) (L * b1) < 7 ^ m ∨ 6 * 7 ^ m ≤ dsub (7 ^ (m + 1)) (L * b2) (L * b1) at pZ
  simp only [E] at *
  generalize dsub (7 ^ (m + 1)) (L * b1) (L * b3) = X at *
  generalize dsub (7 ^ (m + 1)) (L * b2) (L * b3) = Y at *
  generalize dsub (7 ^ (m + 1)) (L * b2) (L * b1) = Z at *
  generalize dsub (7 ^ (m + 1)) (L * b3) (L * b1) = A at *
  generalize dsub (7 ^ (m + 1)) (L * b3) (L * b2) = B at *
  generalize dsub (7 ^ (m + 1)) (L * b1) (L * b2) = C at *
  generalize 7 ^ m = M at *
  omega

/-! ## assembling 6.1 -/

theorem fin5_rest : ∀ i j l : Fin 5, i ≠ j → i ≠ l → j ≠ l →
    ∃ a b : Fin 5, ∀ x, x = l ∨ x = i ∨ x = j ∨ x = a ∨ x = b := by
  decide

/-- five values in a window of length 5 after a multiplier. -/
def Win5 (m μ : ℕ) (d : Fin 5 → ℕ) : Prop := ∃ T : ZMod 7, ∀ x, ((qq m (μ * d x) : ZMod 7) - T).val < 5

theorem trick5 (m : ℕ) (d : Fin 5 → ℕ) (i j l : Fin 5) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hw : Wb m (d i) (d j) (d l)) : ∃ μ, Nat.Coprime μ 7 ∧ Win5 m μ d := by
  obtain ⟨a, b, hcov⟩ := fin5_rest i j l hij hil hjl
  obtain ⟨μ, hμ, T, h1, h2, h3, h4, h5⟩ := trick_core m (d i) (d j) (d l) (d a) (d b) hw
  refine ⟨μ, by rcases hμ with rfl | rfl <;> norm_num, T, ?_⟩
  intro x
  rcases hcov x with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem trick5w (m : ℕ) (d : Fin 5 → ℕ) (i j l : Fin 5) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hw : Win m (d i) (d j) (d l)) : ∃ μ, Nat.Coprime μ 7 ∧ Win5 m μ d := by
  rcases hw with h | h | h
  · exact trick5 m d i j l hij hil hjl h
  · exact trick5 m d l j i (Ne.symm hjl) (Ne.symm hil) (Ne.symm hij) h
  · exact trick5 m d i l j hil hij (Ne.symm hjl) h

theorem trick5_scaled (m lam : ℕ) (d : Fin 5 → ℕ) (hlam : Nat.Coprime lam 7) (i j l : Fin 5)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hw : Win m (lam * d i) (lam * d j) (lam * d l)) :
    ∃ μ, Nat.Coprime μ 7 ∧ Win5 m μ d := by
  obtain ⟨μ, hμ, T, hT⟩ := trick5w m (fun x => lam * d x) i j l hij hil hjl hw
  exact ⟨μ * lam, Nat.Coprime.mul_left hμ hlam, T, fun x => by rw [mul_assoc]; exact hT x⟩

theorem z7_win_avoid : ∀ v T : ZMod 7, (v - T).val < 5 → v + 1 * (1 - T) ≠ 0 ∧ v + 1 * (1 - T) ≠ 6 := by
  decide

/-- a window of length 5 on one class is finished by a `Lambda_0` shift. -/
theorem win5_good (m : ℕ) (hm : 1 ≤ m) (d : Fin 5 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (μ : ℕ) (hμ : Nat.Coprime μ 7) (hw : Win5 m μ d) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6 := by
  obtain ⟨T, hT⟩ := hw
  have hdi : ∀ i, ¬ 7 ∣ μ * d i := fun i => not_dvd_mul hμ (hd i)
  have hρ : R (μ * d 0) ≠ 0 := R_ne_zero (fun h => hdi 0 (h ▸ dvd_zero 7))
  obtain ⟨k, hk, hshift⟩ := shift_class m hm (R (μ * d 0)) (1 - T) hρ
  refine ⟨(1 + 7 ^ m * k) * μ, Nat.Coprime.mul_left (Lam0_coprime m k hm) hμ, ?_⟩
  intro i
  have hRi : R (μ * d i) = 1 * R (μ * d 0) := by
    have h0 : ∀ j, d j ≠ 0 := fun j h => hd j (h ▸ dvd_zero 7)
    rw [one_mul, R_mul_unit hμ (h0 i), R_mul_unit hμ (h0 0), R_of_not_dvd (hd i), R_of_not_dvd (hd 0),
      hcl i 0]
  have hq := hshift (μ * d i) (hdi i) 1 hRi
  rw [show (1 + 7 ^ m * k) * μ * d i = (1 + 7 ^ m * k) * (μ * d i) by ring]
  obtain ⟨a, b⟩ := z7_win_avoid _ T (hT i)
  rw [← hq] at a b
  exact nat_avoid (qq_lt m _) a b

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem z7_sec61 : ∀ w1 w2 w3 w4 : ZMod 7, w1 ≠ 0 → w2 ≠ 0 → w3 ≠ 0 → w4 ≠ 0 → w1 ≠ w2 → w1 ≠ w3 →
    w1 ≠ w4 → w2 ≠ w3 → w2 ≠ w4 → w3 ≠ w4 → ∃ u : ZMod 7, u ≠ 0 ∧ ∃ T : ZMod 7,
      W5 0 (u * w1) (u * w2) (u * w3) (u * w4) T := by
  decide

theorem coprime_of_zmod_ne_zero {u : ZMod 7} (hu : u ≠ 0) : Nat.Coprime u.val 7 := by
  have h1 : u.val < 7 := ZMod.val_lt u
  have h2 : u.val ≠ 0 := (ZMod.val_ne_zero u).mpr hu
  have : ∀ v < 7, v ≠ 0 → Nat.Coprime v 7 := by decide
  exact this _ h1 h2

/-- `nu(E) = {m}`: all ten differences nonzero at the top level. -/
theorem sec61_top (m : ℕ) (d : Fin 5 → ℕ)
    (hT : ∀ i j, i ≠ j → E m (d i) (d j) ≠ 0 ∧ nu 7 (E m (d i) (d j)) = m) :
    ∃ μ, Nat.Coprime μ 7 ∧ Win5 m μ d := by
  set w : Fin 5 → ℕ := fun i => E m (d i) (d 0) / 7 ^ m with hw
  have hEw : ∀ i, E m (d i) (d 0) = 7 ^ m * w i := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hw]; simp only; rw [E_self]; simp
    · have hdv : 7 ^ m ∣ E m (d i) (d 0) := by
        have := pow_nu_dvd 7 (E m (d i) (d 0)); rwa [(hT i 0 hi).2] at this
      exact (Nat.mul_div_cancel' hdv).symm
  have hw7 : ∀ i, w i < 7 := by
    intro i
    have h1 := E_lt m (d i) (d 0)
    rw [hEw i, pow_succ] at h1
    exact (Nat.mul_lt_mul_left (by positivity)).mp h1
  have hmod : ∀ i, d i ≡ d 0 + 7 ^ m * w i [MOD 7 ^ (m + 1)] := fun i => by
    have := E_modEq m (d i) (d 0); rwa [hEw i] at this
  have hdist : ∀ i j, i ≠ j → (w i : ZMod 7) ≠ w j := by
    intro i j hij heq
    have hwij : w i = w j := nat_cast_zmod7_eq_of_lt (hw7 i) (hw7 j) heq
    apply (hT i j hij).1
    apply eq_of_cast_N (E_lt m _ _) (N_pos m)
    rw [E_cast]
    have a := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hmod i)
    have b := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hmod j)
    push_cast at a b ⊢
    rw [a, b, hwij]; ring
  have hw0 : w 0 = 0 := by
    have := hEw 0; rw [E_self] at this
    rcases Nat.mul_eq_zero.mp this.symm with h | h
    · exact absurd h (by positivity)
    · exact h
  have nz : ∀ i : Fin 5, i ≠ 0 → (w i : ZMod 7) ≠ 0 := by
    intro i hi h; apply hdist i 0 hi; rw [h, hw0]; simp
  obtain ⟨u, hu, T, hT5⟩ := z7_sec61 (w 1) (w 2) (w 3) (w 4) (nz 1 (by decide)) (nz 2 (by decide))
    (nz 3 (by decide)) (nz 4 (by decide)) (hdist 1 2 (by decide)) (hdist 1 3 (by decide))
    (hdist 1 4 (by decide)) (hdist 2 3 (by decide)) (hdist 2 4 (by decide)) (hdist 3 4 (by decide))
  refine ⟨u.val, coprime_of_zmod_ne_zero hu, (qq m (u.val * d 0) : ZMod 7) + T, ?_⟩
  have hsh : ∀ i, (qq m (u.val * d i) : ZMod 7) - ((qq m (u.val * d 0) : ZMod 7) + T) =
      u * (w i : ZMod 7) - T := by
    intro i; rw [top_shift m u.val _ _ _ (hmod i), ZMod.natCast_zmod_val]; ring
  obtain ⟨t0, t1, t2, t3, t4⟩ := hT5
  intro x
  rw [hsh x]
  fin_cases x
  · simp only [Fin.zero_eta, Fin.isValue]; rw [hw0]; simpa using t0
  · exact t1
  · exact t2
  · exact t3
  · exact t4

/-- **Section 6.1** (`|A1| = 5`, `m ≥ 2`): a multiplier prime to 7 keeps all five level-0 speeds
of one class off `q ∈ {0, 6}`. -/
theorem sec61 (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6 := by
  suffices h : ∃ μ, Nat.Coprime μ 7 ∧ Win5 m μ d by
    obtain ⟨μ, hμ, hw⟩ := h
    exact win5_good m (by omega) d hd hcl μ hμ hw
  set d' : Fin 4 → ℕ := fun i => d i.castSucc with hd'
  have hcl' : ∀ i j, d' i % 7 = d' j % 7 := fun i j => hcl _ _
  have cs_inj : ∀ a b : Fin 4, a ≠ b → a.castSucc ≠ b.castSucc := fun a b h h' =>
    h (Fin.castSucc_injective 4 h')
  rcases lemma10 m d' hcl' with hz | ⟨σ, hi | ⟨h, hall, h2, -⟩⟩
  · -- all congruent: any triple is a window
    have hw : Wb m (d 1) (d 2) (d 0) := by
      have a : E m (d 1) (d 0) = 0 := hz 1 0
      have b : E m (d 2) (d 0) = 0 := hz 2 0
      exact ⟨by rw [a]; positivity, by rw [b]; positivity⟩
    exact trick5 m d 1 2 0 (by decide) (by decide) (by decide) hw
  · obtain ⟨lam, hc, hw⟩ := win9_i m (d' (σ 1)) (d' (σ 2)) (d' (σ 0)) hi
    exact trick5_scaled m lam d hc _ _ _ (cs_inj _ _ (by simp)) (cs_inj _ _ (by simp))
      (cs_inj _ _ (by simp)) (Or.inl hw)
  · have n10 : σ 1 ≠ σ 0 := by simp
    have n20 : σ 2 ≠ σ 0 := by simp
    have hle : h ≤ m := by
      rw [← (hall _ _ n10).2]; exact nu_le_m (hall _ _ n10).1 (E_lt m _ _)
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hr : rp 7 (E m (d' (σ 2)) (d' (σ 0))) = 2 * rp 7 (E m (d' (σ 1)) (d' (σ 0))) % 7 := by
        apply nat_cast_zmod7_eq_of_lt (rp_lt _) (Nat.mod_lt _ (by norm_num))
        rw [ZMod.natCast_mod]; push_cast; exact h2
      obtain ⟨lam, hc, hw⟩ := win9_ii m h (d' (σ 1)) (d' (σ 2)) (d' (σ 0)) _ _ hlt rfl rfl
        (hall _ _ n10).1 (hall _ _ n20).1 (hall _ _ n10).2 (hall _ _ n20).2 hr
      exact trick5_scaled m lam d hc _ _ _ (cs_inj _ _ (by simp)) (cs_inj _ _ (by simp))
        (cs_inj _ _ (by simp)) hw
    · have heq' := heq.symm
      subst heq'
      by_cases hT : ∀ i : Fin 4, E m (d 4) (d' i) ≠ 0 ∧ nu 7 (E m (d 4) (d' i)) = m
      · apply sec61_top m d
        intro i j hij
        have c4 : ∀ a : Fin 5, a ≠ 4 → ∃ b : Fin 4, a = b.castSucc := by decide
        by_cases hi4 : i = 4
        · subst hi4
          obtain ⟨b, rfl⟩ := c4 j (Ne.symm hij)
          exact hT b
        by_cases hj4 : j = 4
        · subst hj4
          obtain ⟨a, rfl⟩ := c4 i hi4
          obtain ⟨h1, h2⟩ := hT a
          exact ⟨(swap_rule m _ _ h1).1, by rw [nu_swap]; exact h2⟩
        obtain ⟨a, rfl⟩ := c4 i hi4
        obtain ⟨b, rfl⟩ := c4 j hj4
        exact hall a b (fun h' => hij (by rw [h']))
      · push Not at hT
        obtain ⟨i, hi⟩ := hT
        have hne : nu 7 (E m (d 4) (d' i)) ≠ m := by
          intro heq
          by_cases hz : E m (d 4) (d' i) = 0
          · rw [hz, nu_zero] at heq; omega
          · exact hi hz heq
        obtain ⟨j, hji, -, -⟩ := fourth i i i
        have hj := (hall j i hji).2
        obtain ⟨lam, hc, hw⟩ := win9_i m (d 4) (d' j) (d' i) (by rw [hj]; exact hne)
        exact trick5_scaled m lam d hc 4 j.castSucc i.castSucc (by simp [Fin.ext_iff]; omega)
          (by simp [Fin.ext_iff]; omega) (cs_inj _ _ hji) (Or.inl hw)

/-- **Section 6.1, real form**: five level-0 speeds of one class and one top speed. -/
theorem sec61_witness (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hc, hlam⟩ := sec61 m hm d hd hcl
  obtain ⟨t, ht, hall⟩ := witness_of_lam m lam hc (List.ofFn d) [d6]
    (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hlam i)
    (by intro x hx; simp at hx; subst hx; exact ⟨h6, h6m⟩)
  exact ⟨t, ht, fun i => hall _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)),
    hall _ (List.mem_append_right _ (by simp))⟩

end LRSpectrumFull.BarajasSerra.Sec6
