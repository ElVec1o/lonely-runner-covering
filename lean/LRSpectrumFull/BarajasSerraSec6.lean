import LRSpectrumFull.BarajasSerraG
import LRSpectrumFull.BarajasSerraZ7

/-!
# E6 session 17: Barajas-Serra Section 6, G3 (eq. (13)), Lemma 4 (corrected), Lemma 7

Throughout `p = 7`, `N = 7^(m+1)`, `q = qarc 7 m N`. Differences are residues in `[0, N)` (`dsub`).

* `ediff m x y`, `etilde m x y`: the paper's `e(x,y)` and `e~(x,y)` of eq. (13), branches in the
  order `r(y) = 2r(x)`, `r(x) = 2r(y)`, otherwise `x - y` (the paper's third case `r(x) = r(y)`).
* Lemma 4 (ii) CORRECTED: `e~ - q(e) ∈ {-1, 0, 1}` always, and `∈ {0, 1}` when `r(x) = r(y)`
  (the paper prints `{0, 6}`, FALSE). Part (ii) needs no level hypothesis.
* Lemma 4 (i): invariance of `e~` under `Lam i m 7`, `i ≤ j = nu x = nu y < m`, related pair.
* Lemma 7 (i), (ii) (steering `e~`); (ii) uses `m ≥ 2` through the carry argument on `7d`.

Falsified first: (development file, not part of this archive) mirrors these exact definitions
(m = 2 over `[0, 2N)^2`, m = 3 over `[0, N+50)^2`): 0 failures; negative controls fire.
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- `q(x)` for `p = 7`, `N = 7^(m+1)`. -/
def qq (m x : ℕ) : ℕ := qarc 7 m (7 ^ (m + 1)) x

/-- `e(x, y)` of eq. (13), as a residue in `[0, N)`. -/
noncomputable def ediff (m x y : ℕ) : ℕ :=
  if rp 7 y = 2 * rp 7 x % 7 then dsub (7 ^ (m + 1)) (2 * x) y
  else if rp 7 x = 2 * rp 7 y % 7 then dsub (7 ^ (m + 1)) (2 * y) x
  else dsub (7 ^ (m + 1)) x y

/-- `e~(x, y)` of eq. (13), in `ZMod 7`. -/
noncomputable def etilde (m x y : ℕ) : ZMod 7 :=
  if rp 7 y = 2 * rp 7 x % 7 then 2 * (qq m x : ZMod 7) - qq m y
  else if rp 7 x = 2 * rp 7 y % 7 then 2 * (qq m y : ZMod 7) - qq m x
  else (qq m x : ZMod 7) - qq m y

/-! ## basic lemmas -/

theorem qq_lt (m x : ℕ) : qq m x < 7 := by unfold qq qarc; exact Nat.mod_lt _ (by norm_num)

theorem N_pos (m : ℕ) : 0 < 7 ^ (m + 1) := by positivity

theorem dsub_lt (N x y : ℕ) (hN : 0 < N) : dsub N x y < N := by unfold dsub; exact Nat.mod_lt _ hN

/-- `x ≡ y + (x - y) [MOD N]`. -/
theorem modEq_add_dsub (N x y : ℕ) (hN : 0 < N) : x ≡ y + dsub N x y [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [dsub_cast N x y hN]; ring

/-- carry fact used everywhere: `q(x) = q(y) + q(x - y) + c`, `c ∈ {0,1}`, in `ZMod 7`. -/
theorem qq_dsub_carry (m x y : ℕ) :
    ∃ c : ℕ, c < 2 ∧ (qq m x : ZMod 7) = qq m y + qq m (dsub (7 ^ (m + 1)) x y) + c := by
  obtain ⟨c, hc, h⟩ := qarc_add_carry 7 m (by norm_num) y (dsub (7 ^ (m + 1)) x y)
  refine ⟨c, hc, ?_⟩
  have hx : qq m x = qarc 7 m (7 ^ (m + 1)) (y + dsub (7 ^ (m + 1)) x y) :=
    qarc_congr (modEq_add_dsub _ x y (N_pos m))
  rw [hx, h]; unfold qq
  rw [ZMod.natCast_mod]; push_cast; try ring

/-- `q(2x) = 2 q(x) + c`, `c ∈ {0,1}`, in `ZMod 7`. -/
theorem qq_two_mul (m x : ℕ) : ∃ c : ℕ, c < 2 ∧ (qq m (2 * x) : ZMod 7) = 2 * (qq m x : ZMod 7) + c := by
  obtain ⟨c, hc, h⟩ := qarc_add_carry 7 m (by norm_num) x x
  refine ⟨c, hc, ?_⟩
  unfold qq; rw [show 2 * x = x + x by ring, h, ZMod.natCast_mod]; push_cast; try ring

theorem zmod7_cases_c (c c' : ℕ) (hc : c < 2) (hc' : c' < 2) :
    ((c : ZMod 7) - c' = 0 ∨ (c : ZMod 7) - c' = 1 ∨ (c : ZMod 7) - c' = -1) := by
  interval_cases c <;> interval_cases c' <;> first | decide | simp

/-! ## Lemma 4 (ii), corrected -/

/-- **Lemma 4 (ii), first part.** `e~(x,y) - q(e(x,y)) ∈ {0, 1, -1}` for all `x, y`. -/
theorem lemma4_ii (m x y : ℕ) :
    etilde m x y - qq m (ediff m x y) = 0 ∨ etilde m x y - qq m (ediff m x y) = 1 ∨
      etilde m x y - qq m (ediff m x y) = -1 := by
  unfold etilde ediff
  split_ifs
  · obtain ⟨c, hc, h⟩ := qq_dsub_carry m (2 * x) y
    obtain ⟨c', hc', h'⟩ := qq_two_mul m x
    have : 2 * (qq m x : ZMod 7) - qq m y - qq m (dsub (7 ^ (m + 1)) (2 * x) y) = c - c' := by
      linear_combination h - h'
    rw [this]; exact zmod7_cases_c c c' hc hc'
  · obtain ⟨c, hc, h⟩ := qq_dsub_carry m (2 * y) x
    obtain ⟨c', hc', h'⟩ := qq_two_mul m y
    have : 2 * (qq m y : ZMod 7) - qq m x - qq m (dsub (7 ^ (m + 1)) (2 * y) x) = c - c' := by
      linear_combination h - h'
    rw [this]; exact zmod7_cases_c c c' hc hc'
  · obtain ⟨c, hc, h⟩ := qq_dsub_carry m x y
    have : (qq m x : ZMod 7) - qq m y - qq m (dsub (7 ^ (m + 1)) x y) = c := by
      linear_combination h
    rw [this]; interval_cases c <;> first | decide | simp

theorem rp_ne_zero (x : ℕ) (hx : x ≠ 0) : rp 7 x ≠ 0 := by
  intro h
  have := rp_coprime 7 x (by norm_num) hx
  rw [h] at this; norm_num at this

theorem rp_lt (x : ℕ) : rp 7 x < 7 := by unfold rp; exact Nat.mod_lt _ (by norm_num)

/-- **Lemma 4 (ii), second part, CORRECTED.** If `r(x) = r(y)` then `e~(x,y) - q(e(x,y)) ∈ {0, 1}`.
The paper prints `{0, 6}`; that version is FALSE (session 15, Rust). -/
theorem lemma4_ii_eq (m x y : ℕ) (hx : x ≠ 0) (hr : rp 7 x = rp 7 y) :
    etilde m x y - qq m (ediff m x y) = 0 ∨ etilde m x y - qq m (ediff m x y) = 1 := by
  have h0 := rp_ne_zero x hx
  have hl := rp_lt x
  have hn1 : ¬ rp 7 y = 2 * rp 7 x % 7 := by rw [← hr]; omega
  have hn2 : ¬ rp 7 x = 2 * rp 7 y % 7 := by rw [← hr]; omega
  simp only [etilde, ediff, if_neg hn1, if_neg hn2]
  obtain ⟨c, hc, h⟩ := qq_dsub_carry m x y
  have : (qq m x : ZMod 7) - qq m y - qq m (dsub (7 ^ (m + 1)) x y) = c := by
    linear_combination h
  rw [this]
  interval_cases c <;> first | decide | simp

/-! ## Lemma 4 (i) -/

theorem Lam_mem {i m lam : ℕ} (h : lam ∈ Lam i m 7) : ∃ k < 7, lam = 1 + 7 ^ (m - i) * k := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
  exact ⟨k, Finset.mem_range.mp hk, rfl⟩

theorem Lam_modEq_seven {i m lam : ℕ} (him : i < m) (h : lam ∈ Lam i m 7) : lam ≡ 1 [MOD 7] := by
  have := Lam_modEq_one h
  have h2 := modEq_one_mono (p := 7) (s := m - i) (t := 1) this (by omega)
  simpa using h2

/-- `q` of `lam * x` for `lam ∈ Lam i m 7`, `i ≤ nu x`: in `ZMod 7` it is `q x + [i = nu x] k r(x)`. -/
theorem qq_lam (m i j k x : ℕ) (hjm : j < m) (hij : i ≤ j) (hk : k < 7) (hx : nu 7 x = j) :
    (qq m ((1 + 7 ^ (m - i) * k) * x) : ZMod 7) =
      qq m x + (if i = j then (k : ZMod 7) * rp 7 x else 0) := by
  unfold qq
  split_ifs with hij'
  · subst hij'
    rw [qarc_mul_lam_eq 7 i m (by norm_num) (by omega) k hk x hx, ZMod.natCast_mod]; push_cast; try ring
  · rw [qarc_mul_lam_gt 7 i m (by omega) k x (by omega)]; simp

/-- **Lemma 4 (i).** For `x, y ≠ 0` with `nu x = nu y = j < m`, related residues
(`r(y) ∈ {r(x), 2 r(x)}` or `r(x) = 2 r(y)`, mod 7), and `lam ∈ Lam i m 7` with `i ≤ j`:
`e~(lam x, lam y) = e~(x, y)`. -/
theorem lemma4_i (m i j lam x y : ℕ) (hjm : j < m) (hij : i ≤ j) (hlam : lam ∈ Lam i m 7)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = j) (hy : nu 7 y = j)
    (hrel : rp 7 y = rp 7 x ∨ rp 7 y = 2 * rp 7 x % 7 ∨ rp 7 x = 2 * rp 7 y % 7) :
    etilde m (lam * x) (lam * y) = etilde m x y := by
  have h7 := Lam_modEq_seven (by omega) hlam
  have hrx : rp 7 (lam * x) = rp 7 x := rp_mul_of_modEq_one (by norm_num) h7 hx0
  have hry : rp 7 (lam * y) = rp 7 y := rp_mul_of_modEq_one (by norm_num) h7 hy0
  obtain ⟨k, hk, rfl⟩ := Lam_mem hlam
  have qx := qq_lam m i j k x hjm hij hk hx
  have qy := qq_lam m i j k y hjm hij hk hy
  have cast2 : ∀ a b : ℕ, a = 2 * b % 7 → (a : ZMod 7) = 2 * (b : ZMod 7) := by
    intro a b h; rw [h, ZMod.natCast_mod]; push_cast; try ring
  rcases eq_or_ne i j with rfl | hne
  · rw [if_pos rfl] at qx qy
    unfold etilde
    rw [hrx, hry, qx, qy]
    split_ifs with h1 h2
    · rw [cast2 _ _ h1]; ring
    · rw [cast2 _ _ h2]; ring
    · have : rp 7 y = rp 7 x := by
        rcases hrel with h | h | h
        · exact h
        · exact absurd h h1
        · exact absurd h h2
      rw [this]; ring
  · rw [if_neg hne, add_zero] at qx qy
    unfold etilde
    rw [hrx, hry, qx, qy]

/-! ## Lemma 7 -/

/-- Z7 fact behind Lemma 7 (i): `l(X) ≤ 4` leaves three consecutive values outside `X`. -/
theorem three_gap_core : ∀ n < 128, Z7.ellM n ≤ 4 →
    ∃ t : ZMod 7, t ∉ Z7.ofMask n ∧ t - 1 ∉ Z7.ofMask n ∧ t - 2 ∉ Z7.ofMask n := by
  decide +kernel

theorem three_gap (X : Finset (ZMod 7)) (hX : Z7.ell X ≤ 4) :
    ∃ t : ZMod 7, t ∉ X ∧ t - 1 ∉ X ∧ t - 2 ∉ X := by
  obtain ⟨n, hn, rfl⟩ := Z7.exists_ofMask X
  rw [Z7.ell_ofMask] at hX
  exact three_gap_core n hn hX

/-- `e(lam d, lam d') ≡ lam e(d, d')` when the branch is unchanged (`r(d') = 2 r(d)` branch). -/
theorem ediff_branch1 (m x y : ℕ) (h : rp 7 y = 2 * rp 7 x % 7) :
    ediff m x y = dsub (7 ^ (m + 1)) (2 * x) y ∧ etilde m x y = 2 * (qq m x : ZMod 7) - qq m y := by
  refine ⟨?_, ?_⟩ <;> simp only [ediff, etilde, if_pos h]

theorem nat_cast_zmod7_eq_of_lt {a b : ℕ} (ha : a < 7) (hb : b < 7) (h : (a : ZMod 7) = b) : a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b 7).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- **Lemma 7 (i).** `d, d'` prime to 7 with `r(d') = 2 r(d)`, `e = e(d, d') = 2d - d'` nonzero mod `N`
with `nu(e) < m`, and `l(X) ≤ 4`: some `lam ∈ Lam h m 7`, `h < m`, has `e~(lam d, lam d') ∉ X`. -/
theorem lemma7_i (m d d' : ℕ) (X : Finset (ZMod 7)) (hd : ¬ 7 ∣ d) (hd' : ¬ 7 ∣ d')
    (hr : rp 7 d' = 2 * rp 7 d % 7) (he0 : ediff m d d' ≠ 0) (hem : nu 7 (ediff m d d') < m)
    (hX : Z7.ell X ≤ 4) :
    ∃ h < m, ∃ lam ∈ Lam h m 7, etilde m (lam * d) (lam * d') ∉ X := by
  obtain ⟨t, ht0, ht1, ht2⟩ := three_gap X hX
  set e := ediff m d d' with he
  set h := nu 7 e with hh
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := e)
    (t := (t - 1).val) (by norm_num) hem.le rfl he0 (ZMod.val_lt _)
  refine ⟨h, hem, 1 + 7 ^ (m - h) * k, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, ?_⟩
  set lam := 1 + 7 ^ (m - h) * k with hlam
  have hlmem : lam ∈ Lam h m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have h7 := Lam_modEq_seven hem hlmem
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero 7)
  have hd'0 : d' ≠ 0 := by rintro rfl; exact hd' (dvd_zero 7)
  have hr' : rp 7 (lam * d') = 2 * rp 7 (lam * d) % 7 := by
    rw [rp_mul_of_modEq_one (by norm_num) h7 hd0, rp_mul_of_modEq_one (by norm_num) h7 hd'0]; exact hr
  -- q(e(lam d, lam d')) = q(lam e) = t - 1
  have hq : (qq m (ediff m (lam * d) (lam * d')) : ZMod 7) = t - 1 := by
    rw [(ediff_branch1 m _ _ hr').1]
    have hc : dsub (7 ^ (m + 1)) (2 * (lam * d)) (lam * d') ≡ lam * e [MOD 7 ^ (m + 1)] := by
      rw [he, (ediff_branch1 m d d' hr).1, show 2 * (lam * d) = lam * (2 * d) by ring]
      exact dsub_mul _ lam _ _ (N_pos m)
    unfold qq; rw [qarc_congr hc, hkq]; simp
  intro hmem
  rcases lemma4_ii m (lam * d) (lam * d') with h0 | h1 | h2
  · have : etilde m (lam * d) (lam * d') = t - 1 := by rw [← hq]; linear_combination h0
    rw [this] at hmem; exact ht1 hmem
  · have : etilde m (lam * d) (lam * d') = t := by
      have := h1; rw [hq] at this; linear_combination this
    rw [this] at hmem; exact ht0 hmem
  · have : etilde m (lam * d) (lam * d') = t - 2 := by
      have := h2; rw [hq] at this; linear_combination this
    rw [this] at hmem; exact ht2 hmem

/-- Carry argument of Lemma 7 (ii): with `c` the doubling carry of `y` (`q(2y) = 2q(y) + c`),
`q(7y) = 0` forces `c = 0` and `q(7y) = 6` forces `c = 1`. -/
theorem seven_carry (m y : ℕ) :
    ∃ c < 2, qq m (2 * y) = (2 * qq m y + c) % 7 ∧ (qq m (7 * y) = 0 → c = 0) ∧
      (qq m (7 * y) = 6 → c = 1) := by
  have hp : (0 : ℕ) < 7 := by norm_num
  obtain ⟨c, hc, h2⟩ := qarc_add_carry 7 m hp y y
  obtain ⟨c1, hc1, h4⟩ := qarc_add_carry 7 m hp (2 * y) (2 * y)
  obtain ⟨c2, hc2, h6⟩ := qarc_add_carry 7 m hp (4 * y) (2 * y)
  obtain ⟨c3, hc3, h7⟩ := qarc_add_carry 7 m hp (6 * y) y
  rw [show y + y = 2 * y by ring] at h2
  rw [show 2 * y + 2 * y = 4 * y by ring] at h4
  rw [show 4 * y + 2 * y = 6 * y by ring] at h6
  rw [show 6 * y + y = 7 * y by ring] at h7
  have hq := qq_lt m y
  unfold qq at hq ⊢
  generalize qarc 7 m (7 ^ (m + 1)) y = a at *
  generalize qarc 7 m (7 ^ (m + 1)) (2 * y) = b at *
  generalize qarc 7 m (7 ^ (m + 1)) (4 * y) = b4 at *
  generalize qarc 7 m (7 ^ (m + 1)) (6 * y) = b6 at *
  generalize qarc 7 m (7 ^ (m + 1)) (7 * y) = b7 at *
  subst h2 h4 h6 h7
  refine ⟨c, hc, by omega, ?_, ?_⟩ <;> intro H <;> omega

theorem nu_seven_mul (d : ℕ) (hd : ¬ 7 ∣ d) : nu 7 (7 * d) = 1 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero 7)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  unfold nu
  rw [padicValNat.mul (by norm_num) hd0, padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hd]

/-- core identity: for `lam ∈ Lam 1 m 7` and doubling carry `c` of `lam d`,
`e~(lam d, lam d') = r(e) - c`. -/
theorem lemma7_ii_core (m d d' : ℕ) (hm : 2 ≤ m) (hd0 : d ≠ 0) (hd'0 : d' ≠ 0)
    (hr : rp 7 d' = 2 * rp 7 d % 7) (hem : nu 7 (ediff m d d') = m) (he0 : ediff m d d' ≠ 0)
    (helt : ediff m d d' < 7 ^ (m + 1)) (w : ℕ) (hw : ediff m d d' = 7 ^ m * w) (hwlt : w < 7)
    (k : ℕ) (hk : k < 7) (c : ℕ)
    (hq2 : qq m (2 * ((1 + 7 ^ (m - 1) * k) * d)) = (2 * qq m ((1 + 7 ^ (m - 1) * k) * d) + c) % 7) :
    etilde m ((1 + 7 ^ (m - 1) * k) * d) ((1 + 7 ^ (m - 1) * k) * d') = (w : ZMod 7) - c := by
  set lam := 1 + 7 ^ (m - 1) * k with hlam
  have hlmem : lam ∈ Lam 1 m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have h7 := Lam_modEq_seven (by omega) hlmem
  have hr' : rp 7 (lam * d') = 2 * rp 7 (lam * d) % 7 := by
    rw [rp_mul_of_modEq_one (by norm_num) h7 hd0, rp_mul_of_modEq_one (by norm_num) h7 hd'0]; exact hr
  rw [(ediff_branch1 m _ _ hr').2]
  -- 2 lam d ≡ lam d' + lam e ≡ lam d' + e  [MOD N]
  have hle : lam * ediff m d d' ≡ ediff m d d' [MOD 7 ^ (m + 1)] := by
    apply mul_modEq_self_of_dvd (v := m) (by omega)
    · have := Lam_modEq_one hlmem
      exact modEq_one_mono this (by omega)
    · rw [hw]; exact dvd_mul_right _ _
  have h2 : 2 * (lam * d) ≡ lam * d' + 7 ^ m * w [MOD 7 ^ (m + 1)] := by
    have hb := modEq_add_dsub (7 ^ (m + 1)) (2 * (lam * d)) (lam * d') (N_pos m)
    have hc : dsub (7 ^ (m + 1)) (2 * (lam * d)) (lam * d') ≡ lam * ediff m d d' [MOD 7 ^ (m + 1)] := by
      rw [(ediff_branch1 m d d' hr).1, show 2 * (lam * d) = lam * (2 * d) by ring]
      exact dsub_mul _ lam _ _ (N_pos m)
    rw [← hw]
    exact hb.trans ((hc.trans hle).add_left _)
  have hq2' : qq m (2 * (lam * d)) = (qq m (lam * d') + w) % 7 := by
    unfold qq; rw [qarc_congr h2]; exact qarc_add_topmul 7 m (by norm_num) _ w hwlt
  have A : (qq m (2 * (lam * d)) : ZMod 7) = qq m (lam * d') + w := by
    rw [hq2', ZMod.natCast_mod]; push_cast; try ring
  have B : (qq m (2 * (lam * d)) : ZMod 7) = 2 * (qq m (lam * d) : ZMod 7) + c := by
    rw [hq2, ZMod.natCast_mod]; push_cast; try ring
  linear_combination A - B


/-- **Lemma 7 (ii)** (needs `m ≥ 2`). `d, d'` prime to 7 with `r(d') = 2 r(d)`, `nu(e(d,d')) = m`,
and `r(e) ∉ X ∩ (X + 1)`: some `lam ∈ Lam 1 m 7` has `e~(lam d, lam d') ∉ X`. -/
theorem lemma7_ii (m d d' : ℕ) (X : Finset (ZMod 7)) (hm : 2 ≤ m) (hd : ¬ 7 ∣ d) (hd' : ¬ 7 ∣ d')
    (hr : rp 7 d' = 2 * rp 7 d % 7) (hem : nu 7 (ediff m d d') = m)
    (hX : ¬ ((rp 7 (ediff m d d') : ZMod 7) ∈ X ∧ (rp 7 (ediff m d d') : ZMod 7) - 1 ∈ X)) :
    ∃ lam ∈ Lam 1 m 7, etilde m (lam * d) (lam * d') ∉ X := by
  set e := ediff m d d' with he
  set r := rp 7 e with hrdef
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero 7)
  have hd'0 : d' ≠ 0 := by rintro rfl; exact hd' (dvd_zero 7)
  have hN := N_pos m
  have he0 : e ≠ 0 := by
    intro h0
    have h00 : nu 7 0 = 0 := by simp [nu]
    rw [h0, h00] at hem; omega
  have helt : e < 7 ^ (m + 1) := by rw [he, (ediff_branch1 m d d' hr).1]; exact dsub_lt _ _ _ hN
  -- e = 7^m * r
  have hpe : 7 ^ m ∣ e := hem ▸ pow_nu_dvd 7 e
  obtain ⟨w, hw⟩ := hpe
  have hwlt : w < 7 := by
    by_contra hc; push Not at hc
    have : 7 ^ m * 7 ≤ 7 ^ m * w := Nat.mul_le_mul_left _ hc
    rw [← pow_succ] at this; omega
  have hwr : r = w := by
    rw [hrdef]; unfold rp; rw [hem, hw, Nat.mul_div_cancel_left w (by positivity), Nat.mod_eq_of_lt hwlt]
  -- the target carry value
  by_cases hcase : (r : ZMod 7) ∉ X
  · -- choose q(lam 7d) = 0, then carry 0, e~ = r
    obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := 1) (m := m) (x := 7 * d) (t := 0)
      (by norm_num) (by omega) (nu_seven_mul d hd) (by omega) (by norm_num)
    refine ⟨1 + 7 ^ (m - 1) * k, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, ?_⟩
    have key := lemma7_ii_core m d d' hm hd0 hd'0 hr hem he0 helt w hw hwlt k hk
    obtain ⟨c, hc, hq2, hc0, _⟩ := seven_carry m ((1 + 7 ^ (m - 1) * k) * d)
    have hc0' : c = 0 := hc0 (by unfold qq; rw [show 7 * ((1 + 7 ^ (m - 1) * k) * d) =
      (1 + 7 ^ (m - 1) * k) * (7 * d) by ring]; exact hkq)
    rw [key c hq2, hc0', ← hwr]; simpa using hcase
  · -- choose q(lam 7d) = 6, then carry 1, e~ = r - 1
    have hX1 : (r : ZMod 7) - 1 ∉ X := by
      push Not at hcase; intro h; exact hX ⟨hcase, h⟩
    obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := 1) (m := m) (x := 7 * d) (t := 6)
      (by norm_num) (by omega) (nu_seven_mul d hd) (by omega) (by norm_num)
    refine ⟨1 + 7 ^ (m - 1) * k, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, ?_⟩
    have key := lemma7_ii_core m d d' hm hd0 hd'0 hr hem he0 helt w hw hwlt k hk
    obtain ⟨c, hc, hq2, _, hc6⟩ := seven_carry m ((1 + 7 ^ (m - 1) * k) * d)
    have hc1 : c = 1 := hc6 (by unfold qq; rw [show 7 * ((1 + 7 ^ (m - 1) * k) * d) =
      (1 + 7 ^ (m - 1) * k) * (7 * d) by ring]; exact hkq)
    rw [key c hq2, hc1, ← hwr]; simpa using hX1

end LRSpectrumFull.BarajasSerra.Sec6
