import LRSpectrumFull.BarajasSerraSec6_3a

/-!
# E6 session 19: Barajas-Serra Section 6.3 (`|A1| = 3`, `|A2| = |A4| = 1`), case (a), `m ≥ 2`

`A1 = {d0, d1, d2}` (class `ρ`), `d4` (class `2ρ`), `d5` (class `4ρ`), all level 0. Conclusion: a
multiplier prime to 7 keeping all five off `q ∈ {0, 6}` (`sec63`), real form with a top speed
(`sec63_witness`). Part 1 (`BarajasSerraSec6_3a`): window case and `h = m`.

This module: Lemma 11 (ii.2) with `h < m` (the paper's (ii.2.a), (ii.2.b)); `e45 = e(d4, d5) = 2d4 - d5`.
* `e45` zero or below `h`: Lemma 9 (ii) `j = 3` (difference form) first, then Lemma 2 below `h`.
* `e45` above `h`: Lemma 2 (`q(e45) = 6`) first, then Lemma 9; `e~45 ∈ {5,6,0}`; Lemma 5 at `(3,1,1)`.
* `e45` at level `h`: the paper's table (ii.2.b), in a robust form. With `t = 5 r(e45)` in Lemma 11,
  `r(e13) = ±r(e45)`; `w = ±e45`, `f = e13 - w` (session-16 erratum: `f = e13 - e45`, not `e45 - e13`),
  Lemma 2 on `f` gives `δ = q(e13) - q(w) ∈ {0,1}`; the carry `c3` of `e13 = e12 + e23` and
  `u = 3q(e13) + 5q(e23)` are invariant under `Lambda_h`. The target `q(e13) = T63(δ, u, c3)` (one
  factor of `Lambda_h`) makes every `Lambda_0`-completion work for all carries (`z63tabP`, `z63tabN`),
  except `(δ, u) = (0, 3)`, where `q(e13) = 3` and the doubling finishes (`z63dbl`). `T63` agrees with the
  paper's table (rows `q(e13)`), including the `c3`-dependent entry at `u = 4`, `δ = 1`.
Falsified first: `e6s19/tab63.rs` (the robust table: exactly the four cases `δ = 0, u = 3` need the
doubling) and `e6s19/z63.rs` (the decide statements below, 1638 cases per sign, 0 failures; negative
control with the `c3` entry swapped fails).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-! ## finite facts -/

/-- the robust form of the table of 6.3 (ii.2.b): target for `q(e13)`. -/
def T63 (dl u c3 : ZMod 7) : ZMod 7 :=
  if dl = 0 then (if u = 1 ∨ u = 4 ∨ u = 6 then 6 else if u = 3 then 3 else 0)
  else (if u = 1 ∨ u = 3 then 1 else if u = 6 then 6 else if u = 4 then (if c3 = 0 then 6 else 0) else 0)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem z63tabP : ∀ dl u c3 : ZMod 7, (dl = 0 ∨ dl = 1) → (c3 = 0 ∨ c3 = 1) → ¬ (dl = 0 ∧ u = 3) →
    ∀ c1 c2 c3' : ZMod 7, (c1 = 0 ∨ c1 = 1) → (c2 = 0 ∨ c2 = 1) → (c3' = 0 ∨ c3' = 1) →
    c1 = c2 - c3 + c3' → ∀ s : ZMod 7, (s = 0 ∨ s = 1 ∨ s = -1) → ∀ p4 : ZMod 7,
    ∃ K, ok7 K ∧ ok7 (T63 dl u c3 + c1 + K) ∧ ok7 (3 * u - 2 * T63 dl u c3 + c2 + K) ∧
      ok7 (p4 + 2 * K) ∧ ok7 (2 * p4 - ((T63 dl u c3 - dl) + s) + 4 * K) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem z63tabN : ∀ dl u c3 : ZMod 7, (dl = 0 ∨ dl = 1) → (c3 = 0 ∨ c3 = 1) → ¬ (dl = 0 ∧ u = 3) →
    ∀ c1 c2 c3' : ZMod 7, (c1 = 0 ∨ c1 = 1) → (c2 = 0 ∨ c2 = 1) → (c3' = 0 ∨ c3' = 1) →
    c1 = c2 - c3 + c3' → ∀ s : ZMod 7, (s = 0 ∨ s = 1 ∨ s = -1) → ∀ p4 : ZMod 7,
    ∃ K, ok7 K ∧ ok7 (T63 dl u c3 + c1 + K) ∧ ok7 (3 * u - 2 * T63 dl u c3 + c2 + K) ∧
      ok7 (p4 + 2 * K) ∧ ok7 (2 * p4 - ((-(T63 dl u c3 - dl) - 1) + s) + 4 * K) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem z63dbl : ∀ g1 g2 g3 c1 c2 : ZMod 7, (g1 = 0 ∨ g1 = 1) → (g2 = 0 ∨ g2 = 1) → (g3 = 0 ∨ g3 = 1) →
    (c1 = 0 ∨ c1 = 1) → (c2 = 0 ∨ c2 = 1) → ∀ s : ZMod 7, (s = 0 ∨ s = 1 ∨ s = -1) → ∀ p4 : ZMod 7,
    ∃ K, ok7 K ∧ ok7 (6 + g1 + c1 + K) ∧ ok7 (6 + g2 + c2 + K) ∧ ok7 (p4 + 2 * K) ∧
      ok7 (2 * p4 - (6 + g3 + s) + 4 * K) := by
  decide +kernel

theorem z7_seven : (7 : ZMod 7) = 0 := by decide

theorem T63_exc : ∀ c : ZMod 7, T63 0 3 c = 3 := by decide

theorem z7_three_self : ∀ a : ZMod 7, 3 * a = a → a = 0 := by decide

theorem ell_single : ∀ x : ZMod 7, Z7.ell {x} = 1 := by decide

theorem z01 (c : ℕ) (hc : c < 2) : (c : ZMod 7) = 0 ∨ (c : ZMod 7) = 1 := by
  interval_cases c <;> simp

theorem z7_not24 : ∀ q s : ZMod 7, (q = 0 ∨ q = 6) → (s = 0 ∨ s = 1 ∨ s = -1) →
    q + s ∉ ({2, 4} : Finset (ZMod 7)) := by decide

/-! ## tools -/

/-- `e~45 - q(μ e45) ∈ {0, 1, -1}` for any unit `μ` (Lemma 4 (ii)). -/
theorem et45 (m μ d4 d5 : ℕ) (hμ : Nat.Coprime μ 7) (h4 : d4 ≠ 0) (h5 : d5 ≠ 0)
    (hr : rp 7 d5 = 2 * rp 7 d4 % 7) :
    ∃ s : ZMod 7, (s = 0 ∨ s = 1 ∨ s = -1) ∧
      2 * (qq m (μ * d4) : ZMod 7) - qq m (μ * d5) = qq m (μ * ediff m d4 d5) + s := by
  have hr' : rp 7 (μ * d5) = 2 * rp 7 (μ * d4) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h5, R_mul_unit hμ h4]
    have := congrArg (fun n : ℕ => (n : ZMod 7)) hr; simp only at this
    unfold R; rw [this, ZMod.natCast_mod]; push_cast; ring
  have hq : qq m (ediff m (μ * d4) (μ * d5)) = qq m (μ * ediff m d4 d5) := by
    unfold qq; apply qarc_congr
    rw [(ediff_branch1 m _ _ hr').1, (ediff_branch1 m _ _ hr).1, show 2 * (μ * d4) = μ * (2 * d4) by ring]
    exact dsub_mul _ μ _ _ (N_pos m)
  have := lemma4_ii m (μ * d4) (μ * d5)
  rw [(ediff_branch1 m _ _ hr').2, hq] at this
  refine ⟨2 * (qq m (μ * d4) : ZMod 7) - qq m (μ * d5) - qq m (μ * ediff m d4 d5), ?_, by ring⟩
  rcases this with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-- finish from `l(A1) ≤ 3` and `e~45 ∉ {2, 4}` (Lemma 5 at `(3,1,1)`). -/
theorem finish63_ell (m : ℕ) (hm : 1 ≤ m) (C B A d4 d5 : ℕ) (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (hell : ellq m (μ * B) (μ * A) (μ * C) ≤ 3)
    (he : 2 * (qq m (μ * d4) : ZMod 7) - qq m (μ * d5) ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  unfold ellq at hell
  have hs : Z7.ell {((qq m (μ * B) : ℕ) : ZMod 7), ((qq m (μ * A) : ℕ) : ZMod 7), ((qq m (μ * C) : ℕ) : ZMod 7)} +
      Z7.ell {((qq m (μ * d4) : ℕ) : ZMod 7)} + Z7.ell {((qq m (μ * d5) : ℕ) : ZMod 7)} ≤ 5 := by
    rw [ell_single, ell_single]; omega
  rcases Z7.lemma5 _ _ _ hs (by rw [ell_single, ell_single]; simp) with ⟨k, hk1, hk2, hk4⟩ | ⟨-, -, -, hexc⟩
  · apply finish63 m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ k
    · intro x hx
      rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
      · exact hk1 _ (by simp)
      · exact hk1 _ (by simp)
      · exact hk1 _ (by simp)
    · exact hk2 _ (by simp)
    · exact hk4 _ (by simp)
  · exfalso; apply he
    rcases hexc _ (Finset.mem_singleton_self _) _ (Finset.mem_singleton_self _) with h | h <;> rw [h] <;> simp

/-- `a + b ≡ 0`, `7^m ∤ b`: `q(a) + q(b) = 6`. -/
theorem qq_neg (m a b : ℕ) (hab : a + b ≡ 0 [MOD 7 ^ (m + 1)]) (hb : ¬ 7 ^ m ∣ b) :
    qq m a + qq m b = 6 := by
  have hM : 0 < 7 ^ m := by positivity
  have hN : 7 ^ (m + 1) = 7 * 7 ^ m := by rw [pow_succ]; ring
  have hMN : 7 ^ m ∣ 7 ^ (m + 1) := pow_dvd_pow 7 (by omega)
  obtain ⟨la, ua⟩ := qq_bounds m a
  obtain ⟨lb, ub⟩ := qq_bounds m b
  have hBd : ¬ 7 ^ m ∣ b % 7 ^ (m + 1) := fun h => hb ((Nat.dvd_mod_iff hMN).mp h)
  have hB0 : b % 7 ^ (m + 1) ≠ 0 := fun h => hBd (by rw [h]; exact dvd_zero _)
  have hsum : a % 7 ^ (m + 1) + b % 7 ^ (m + 1) = 7 ^ (m + 1) := by
    have h1 : (a % 7 ^ (m + 1) + b % 7 ^ (m + 1)) % 7 ^ (m + 1) = 0 := by
      rw [← Nat.add_mod]; exact hab
    have h2 := Nat.mod_lt a (N_pos m)
    have h3 := Nat.mod_lt b (N_pos m)
    have h4 := Nat.div_add_mod (a % 7 ^ (m + 1) + b % 7 ^ (m + 1)) (7 ^ (m + 1))
    rw [h1, add_zero] at h4
    have h5 : (a % 7 ^ (m + 1) + b % 7 ^ (m + 1)) / 7 ^ (m + 1) < 2 :=
      (Nat.div_lt_iff_lt_mul (N_pos m)).mpr (by omega)
    interval_cases hq : (a % 7 ^ (m + 1) + b % 7 ^ (m + 1)) / 7 ^ (m + 1)
    · omega
    · omega
  have hstrict : qq m b * 7 ^ m < b % 7 ^ (m + 1) := by
    rcases lt_or_eq_of_le lb with h | h
    · exact h
    · exact absurd ⟨qq m b, by rw [← h]; ring⟩ hBd
  have h1 : (qq m a + qq m b) * 7 ^ m < 7 * 7 ^ m := by
    have := add_lt_add_of_le_of_lt la hstrict; rw [hsum, hN] at this; linarith
  have h2 : 7 * 7 ^ m < (qq m a + qq m b + 2) * 7 ^ m := by
    have := add_lt_add ua ub; rw [hsum, hN] at this; linarith
  have h1' := Nat.lt_of_mul_lt_mul_right h1
  have h2' := Nat.lt_of_mul_lt_mul_right h2
  omega

theorem E_zero_right (m v : ℕ) (hv : v < 7 ^ (m + 1)) : E m v 0 = v := by
  unfold E dsub; simp [Nat.mod_eq_of_lt hv]

/-! ## (ii.2), `h < m`, `e45` off level `h` -/

theorem low63_off (m : ℕ) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C))
    (hv : ediff m d4 d5 = 0 ∨ (ediff m d4 d5 ≠ 0 ∧ nu 7 (ediff m d4 d5) ≠ h)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hr45 : rp 7 d5 = 2 * rp 7 d4 % 7 := by apply rp_of_R; rw [hr5, hr4]; ring
  set v := ediff m d4 d5 with hvdef
  -- final step: a unit `μ` with `l(A1) ≤ 3` and `q(μ v) ∈ {0, 6}`
  have fin : ∀ μ, Nat.Coprime μ 7 → ellq m (μ * B) (μ * A) (μ * C) ≤ 3 →
      (qq m (μ * v) = 0 ∨ qq m (μ * v) = 6) →
      ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
    intro μ hμ hell hq
    obtain ⟨s, hs, he⟩ := et45 m μ d4 d5 hμ h40 h50 hr45
    apply finish63_ell m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hell
    rw [he]
    exact z7_not24 _ _ (by rcases hq with h | h <;> rw [h] <;> simp) hs
  by_cases hup : v ≠ 0 ∧ h < nu 7 v
  · -- Lemma 2 first (`q = 6`), then Lemma 9
    obtain ⟨l1, hc1, hq1⟩ := target6 m v hup.1 (ediff_lt m _ _)
    obtain ⟨hx1, hnx1, hRx1⟩ := E_scale m l1 B C hc1 hB.1
    obtain ⟨hy1, hny1, hRy1⟩ := E_scale m l1 A C hc1 hA.1
    have hr1 : rp 7 (E m (l1 * A) (l1 * C)) = 3 * rp 7 (E m (l1 * B) (l1 * C)) % 7 := by
      apply rp_of_R3; rw [hRy1, hRx1, h3]; ring
    obtain ⟨l2, hl2, qy, qx, qxy⟩ := l9diff m h _ _ hhm hx1 hy1 (hnx1.trans hB.2) (hny1.trans hA.2) hr1
    have hl27 := Lam_modEq_seven hhm hl2
    have hc2 : Nat.Coprime l2 7 := (coprime_of_modEq_one (by norm_num) hl27).1
    apply fin (l2 * l1) (Nat.Coprime.mul_left hc2 hc1)
    · apply diff3 m _ _ _ (l2 * E m (l1 * B) (l1 * C)) (l2 * E m (l1 * A) (l1 * C)) _ _ qy qx qxy
      · have := (E_modEq m (l1 * B) (l1 * C)).mul_left l2
        rw [mul_add] at this; rw [mul_assoc, mul_assoc]; exact this
      · have := (E_modEq m (l1 * A) (l1 * C)).mul_left l2
        rw [mul_add] at this; rw [mul_assoc, mul_assoc]; exact this
    · right
      rw [mul_assoc]
      have hfix : qq m (l2 * (l1 * v)) = qq m (l1 * v) := by
        unfold qq
        apply qarc_mul_fix (v := h + 1) (by omega)
        · rw [show m + 1 - (h + 1) = m - h by omega]; exact Lam_modEq_one hl2
        · exact Dvd.dvd.mul_left ((pow_dvd_pow 7 (by omega)).trans (pow_nu_dvd 7 _)) _
      rw [hfix, hq1]
  · -- Lemma 9 first, then Lemma 2 below `h` (or `v = 0`)
    have hbelow : v = 0 ∨ (v ≠ 0 ∧ nu 7 v < h) := by
      rcases hv with h0 | ⟨h0, hne⟩
      · exact Or.inl h0
      · right; refine ⟨h0, ?_⟩; push Not at hup; have := hup h0; omega
    obtain ⟨lam2, hlam2, qy, qx, qxy⟩ := l9diff m h _ _ hhm hB.1 hA.1 hB.2 hA.2 (rp_of_R3 h3)
    have hl27 := Lam_modEq_seven hhm hlam2
    have hc2 : Nat.Coprime lam2 7 := (coprime_of_modEq_one (by norm_num) hl27).1
    have hne2 : lam2 ≠ 0 := (coprime_of_modEq_one (by norm_num) hl27).2
    obtain ⟨lam', hl', hc', hz⟩ : ∃ lam', lam' ≡ 1 [MOD 7 ^ (m + 1 - h)] ∧ Nat.Coprime lam' 7 ∧
        qq m (lam' * (lam2 * v)) = 0 := by
      rcases hbelow with h0 | ⟨h0, hlt⟩
      · refine ⟨1, Nat.ModEq.refl 1, by norm_num, ?_⟩
        rw [h0]; simp [qq, qarc]
      · have hnu : nu 7 (lam2 * v) = nu 7 v := nu_mul_coprime 7 lam2 _ hc2 hne2 h0
        obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 v) (m := m)
          (x := lam2 * v) (t := 0) (by norm_num) (by omega) hnu (Nat.mul_ne_zero hne2 h0)
          (by norm_num)
        have hmem : 1 + 7 ^ (m - nu 7 v) * k ∈ Lam (nu 7 v) m 7 :=
          Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
        refine ⟨_, modEq_one_mono (Lam_modEq_one hmem) (by omega),
          (coprime_of_modEq_one (by norm_num) (Lam_modEq_seven (by omega) hmem)).1, hkq⟩
    have fix : ∀ e, 7 ^ h ∣ e → lam' * e ≡ e [MOD 7 ^ (m + 1)] := fun e he =>
      mul_modEq_self_of_dvd (by omega) hl' he
    have hdx : ∀ z, E m z C ≠ 0 → nu 7 (E m z C) = h → 7 ^ h ∣ lam2 * E m z C := fun z hz hn =>
      Dvd.dvd.mul_left (hn ▸ pow_nu_dvd 7 _) _
    apply fin (lam' * lam2) (Nat.Coprime.mul_left hc' hc2)
    · apply diff3 m _ _ _ (lam2 * E m B C) (lam2 * E m A C) _ _ qy qx qxy
      · have := (E_modEq m B C).mul_left (lam' * lam2)
        rw [mul_add] at this
        refine this.trans (Nat.ModEq.add_left _ ?_)
        rw [mul_assoc]; exact fix _ (hdx B hB.1 hB.2)
      · have := (E_modEq m A C).mul_left (lam' * lam2)
        rw [mul_add] at this
        refine this.trans (Nat.ModEq.add_left _ ?_)
        rw [mul_assoc]; exact fix _ (hdx A hA.1 hA.2)
    · left; rw [mul_assoc]; exact hz

/-! ## (ii.2), `h < m`, `e45` at level `h`: the table -/

theorem tab63 (m : ℕ) (hm : 2 ≤ m) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C)) (hv0 : ediff m d4 d5 ≠ 0) (hvh : nu 7 (ediff m d4 d5) = h)
    (hsg : R (E m A C) = R (ediff m d4 d5) ∨ R (E m A C) = -R (ediff m d4 d5)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hr45 : rp 7 d5 = 2 * rp 7 d4 % 7 := by apply rp_of_R; rw [hr5, hr4]; ring
  set v := ediff m d4 d5 with hvdef
  set y := E m A C with hy
  set x := E m B C with hx
  set z := E m A B with hz
  have hvlt : v < 7 ^ (m + 1) := ediff_lt m _ _
  -- `e12` at level `h` with `r(e12) = r(e13) - r(e23)`
  have hRne : R y ≠ R x := by
    rw [h3]; intro he
    exact R_ne_zero hB.1 (z7_three_self _ he)
  obtain ⟨hz0, hzν, hzR⟩ := (sub_rule m A B C h hA.1 hB.1 hA.2 hB.2).2 hRne
  -- `w = ±v` with `r(w) = r(y)`, and the relation between `q(μ v)` and `q(μ w)`
  obtain ⟨w, hw0, hwν, hwR, hwv⟩ : ∃ w, w ≠ 0 ∧ nu 7 w = h ∧ R w = R y ∧
      ((∀ μ, qq m (μ * v) = qq m (μ * w)) ∨ (∀ μ, v * μ + w * μ ≡ 0 [MOD 7 ^ (m + 1)])) := by
    rcases hsg with hp | hn
    · exact ⟨v, hv0, hvh, hp.symm, Or.inl (fun _ => rfl)⟩
    · have hv' : E m v 0 = v := E_zero_right m v hvlt
      obtain ⟨hne', hnu', hR'⟩ := swap_rule m v 0 (by rw [hv']; exact hv0)
      rw [hv'] at hnu' hR'
      refine ⟨E m 0 v, hne', hnu'.trans hvh, by rw [hR', hn], Or.inr (fun μ => ?_)⟩
      apply modEq_of_cast; push_cast; rw [E_cast]; ring
  -- Lemma 2 on `f = y - w`
  have hfdvd : 7 ^ (h + 1) ∣ E m y w := by
    apply dvd_dsub_one hhm.le hA.2 hwν
    apply nat_cast_zmod7_eq_of_lt (rp_lt _) (rp_lt _); exact hwR.symm
  obtain ⟨l1, -, hc1, hne1, -, hstep⟩ := step_top_or_zero m (h + 1) (E m y w) (by omega) (E_lt m _ _) hfdvd
  -- scaled data (unreduced)
  have nuS : ∀ e, e ≠ 0 → nu 7 e = h → nu 7 (l1 * e) = h := fun e he hn =>
    (nu_mul_coprime 7 l1 e hc1 hne1 he).trans hn
  have RS : ∀ e, e ≠ 0 → R (l1 * e) = (l1 : ZMod 7) * R e := fun e he => R_mul_unit hc1 he
  -- `δ`
  obtain ⟨δ, hδ, hδq⟩ : ∃ δ : ℕ, δ < 2 ∧ (qq m (l1 * y) : ZMod 7) = qq m (l1 * w) + δ := by
    have hyw : l1 * y ≡ l1 * w + l1 * E m y w [MOD 7 ^ (m + 1)] := by
      have := (E_modEq m y w).mul_left l1; rwa [mul_add] at this
    rcases hstep 1 (by simp [Nat.ModEq, Nat.one_mod_eq_one]) with hq0 | htop
    · rw [one_mul] at hq0
      obtain ⟨c, hc, hq⟩ := qq_add_nat hyw
      rw [hq0] at hq
      exact ⟨c, hc, by rw [hq, ZMod.natCast_mod]; push_cast; ring⟩
    · rw [one_mul] at htop
      have hq := qq_top_nat (hyw.trans (Nat.ModEq.add_left _ htop))
      exact ⟨1, by norm_num, by rw [hq, ZMod.natCast_mod]; push_cast; ring⟩
  -- `c3`
  obtain ⟨c3, hc3, hc3q⟩ : ∃ c3 : ℕ, c3 < 2 ∧
      (qq m (l1 * y) : ZMod 7) = qq m (l1 * z) + qq m (l1 * x) + c3 := by
    have hyzx : l1 * y ≡ l1 * z + l1 * x [MOD 7 ^ (m + 1)] := by
      apply modEq_of_cast; push_cast; rw [hy, hz, hx, E_cast, E_cast, E_cast]; ring
    obtain ⟨c, hc, hq⟩ := qq_add_nat hyzx
    exact ⟨c, hc, by rw [hq, ZMod.natCast_mod]; push_cast; ring⟩
  set u : ZMod 7 := 3 * (qq m (l1 * y) : ZMod 7) + 5 * (qq m (l1 * x) : ZMod 7) with hu
  set Y : ZMod 7 := T63 (δ : ZMod 7) u (c3 : ZMod 7) with hY
  -- the `Lambda_h` factor
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := l1 * y) (t := Y.val)
    (by norm_num) hhm.le (nuS y hA.1 hA.2) (Nat.mul_ne_zero hne1 hA.1) (ZMod.val_lt _)
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  set l2 := 1 + 7 ^ (m - h) * k with hl2
  have hl27 := Lam_modEq_seven hhm hmem
  have hc2 : Nat.Coprime l2 7 := (coprime_of_modEq_one (by norm_num) hl27).1
  have shift : ∀ e, e ≠ 0 → nu 7 e = h →
      (qq m (l2 * (l1 * e)) : ZMod 7) = qq m (l1 * e) + (k : ZMod 7) * R (l1 * e) := by
    intro e he hn
    have := qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk (l1 * e) (nuS e he hn)
    unfold qq; rw [this, ZMod.natCast_mod]; unfold R; push_cast; ring
  have sy := shift y hA.1 hA.2
  have sx := shift x hB.1 hB.2
  have sz := shift z hz0 hzν
  have sw := shift w hw0 hwν
  have Ry := RS y hA.1; have Rx := RS x hB.1; have Rz := RS z hz0; have Rw := RS w hw0
  have hYv : (qq m (l2 * (l1 * y)) : ZMod 7) = Y := by
    have : qq m (l2 * (l1 * y)) = Y.val := hkq
    rw [this, ZMod.natCast_zmod_val]
  set κ : ZMod 7 := (k : ZMod 7) * (l1 : ZMod 7) * R x with hκ
  have e7 := z7_seven
  have QY : (qq m (l1 * y) : ZMod 7) + 3 * κ = Y := by
    rw [← hYv, sy, Ry, h3]; ring
  have QX : (qq m (l2 * (l1 * x)) : ZMod 7) = 3 * u - 2 * Y := by
    rw [sx, Rx, ← QY, hu]; linear_combination (-(qq m (l1 * y) : ZMod 7) - 2 * (qq m (l1 * x) : ZMod 7) + κ) * e7
  have QW : (qq m (l2 * (l1 * w)) : ZMod 7) = Y - δ := by
    rw [sw, Rw, hwR, h3, ← QY]; linear_combination hδq.symm
  have QZ : (qq m (l2 * (l1 * z)) : ZMod 7) = Y - (3 * u - 2 * Y) - c3 := by
    rw [← QX, sz, Rz, hzR, h3, sx, Rx, ← QY]; linear_combination -hc3q
  -- the final multiplier and the A1 relations
  set μ := l2 * l1 with hμdef
  have hμ : Nat.Coprime μ 7 := Nat.Coprime.mul_left hc2 hc1
  have rel : ∀ P Q, μ * P ≡ μ * Q + l2 * (l1 * E m P Q) [MOD 7 ^ (m + 1)] := fun P Q => by
    have := (E_modEq m P Q).mul_left μ; rw [mul_add] at this; rw [hμdef, mul_assoc]
    simpa only [hμdef, mul_assoc] using this
  obtain ⟨c1, hc1', q1⟩ := qq_add_nat (rel A C)
  obtain ⟨c2, hc2', q2⟩ := qq_add_nat (rel B C)
  obtain ⟨c3', hc3', q3⟩ := qq_add_nat (rel A B)
  have Q1 : (qq m (μ * A) : ZMod 7) = qq m (μ * C) + Y + c1 := by
    rw [q1, ZMod.natCast_mod]; push_cast; rw [← hy, hYv]
  have Q2 : (qq m (μ * B) : ZMod 7) = qq m (μ * C) + (3 * u - 2 * Y) + c2 := by
    rw [q2, ZMod.natCast_mod]; push_cast; rw [← hx, QX]
  have Q3 : (qq m (μ * A) : ZMod 7) = qq m (μ * B) + (Y - (3 * u - 2 * Y) - c3) + c3' := by
    rw [q3, ZMod.natCast_mod]; push_cast; rw [← hz, QZ]
  have hcc : (c1 : ZMod 7) = c2 - c3 + c3' := by linear_combination Q3 - Q1 + Q2
  -- `q(μ v)`
  have hwμ : ¬ 7 ^ m ∣ l2 * (l1 * w) := by
    intro hd
    have h0 : l2 * (l1 * w) ≠ 0 := Nat.mul_ne_zero (coprime_of_modEq_one (by norm_num) hl27).2
      (Nat.mul_ne_zero hne1 hw0)
    have := (padicValNat_dvd_iff_le (p := 7) h0).mp hd
    have hn : nu 7 (l2 * (l1 * w)) = h :=
      (nu_mul_coprime 7 l2 _ hc2 (coprime_of_modEq_one (by norm_num) hl27).2 (Nat.mul_ne_zero hne1 hw0)).trans
        (nuS w hw0 hwν)
    unfold nu at hn; omega
  have hvμ : ∀ ν', ν' = μ → (qq m (ν' * v) : ZMod 7) = Y - δ ∨ (qq m (ν' * v) : ZMod 7) = -(Y - δ) - 1 := by
    intro ν' hν'; subst hν'
    rcases hwv with hp | hn
    · left; rw [hp, hμdef, mul_assoc, QW]
    · right
      have hs := qq_neg m (μ * v) (l2 * (l1 * w)) (by
        have := hn μ; rw [show l2 * (l1 * w) = w * μ by rw [hμdef]; ring, mul_comm μ v]; exact this) hwμ
      have hs' : (qq m (μ * v) : ZMod 7) + qq m (l2 * (l1 * w)) = 6 := by exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 7)) hs
      rw [QW] at hs'; linear_combination hs' + e7
  obtain ⟨s, hs, hes⟩ := et45 m μ d4 d5 hμ h40 h50 hr45
  have hδ01 := z01 δ hδ
  have hc301 := z01 c3 hc3
  have hc101 := z01 c1 hc1'
  have hc201 := z01 c2 hc2'
  have hc3'01 := z01 c3' hc3'
  by_cases hexc : (δ : ZMod 7) = 0 ∧ u = 3
  · -- the doubling
    have hY3 : Y = 3 := by rw [hY, hexc.1, hexc.2]; exact T63_exc _
    have hμ2 : Nat.Coprime (2 * μ) 7 := Nat.Coprime.mul_left (by norm_num) hμ
    obtain ⟨g1, hg1, d1⟩ := qq_double_nat m (l2 * (l1 * y))
    obtain ⟨g2, hg2, d2⟩ := qq_double_nat m (l2 * (l1 * x))
    obtain ⟨g3, hg3, d3⟩ := qq_double_nat m (μ * v)
    have rel2 : ∀ P Q, 2 * μ * P ≡ 2 * μ * Q + 2 * (l2 * (l1 * E m P Q)) [MOD 7 ^ (m + 1)] := fun P Q => by
      have := (rel P Q).mul_left 2; rw [mul_add] at this; simpa only [mul_assoc] using this
    obtain ⟨b1, hb1, r1⟩ := qq_add_nat (rel2 A C)
    obtain ⟨b2, hb2, r2⟩ := qq_add_nat (rel2 B C)
    obtain ⟨s', hs', hes'⟩ := et45 m (2 * μ) d4 d5 hμ2 h40 h50 hr45
    have D1 : (qq m (2 * (l2 * (l1 * y))) : ZMod 7) = 2 * Y + g1 := by
      rw [d1, ZMod.natCast_mod]; push_cast; rw [hYv]
    have D2 : (qq m (2 * (l2 * (l1 * x))) : ZMod 7) = 2 * (3 * u - 2 * Y) + g2 := by
      rw [d2, ZMod.natCast_mod]; push_cast; rw [QX]
    have D3 : (qq m (2 * μ * v) : ZMod 7) = 6 + g3 := by
      rw [mul_assoc, d3, ZMod.natCast_mod]; push_cast
      rcases hvμ μ rfl with e | e <;> rw [e, hY3, hexc.1]
      · ring
      · linear_combination (-2 : ZMod 7) * e7
    have QA : (qq m (2 * μ * A) : ZMod 7) = qq m (2 * μ * C) + (2 * Y + g1) + b1 := by
      rw [r1, ZMod.natCast_mod]; push_cast; rw [← hy, D1]
    have QB : (qq m (2 * μ * B) : ZMod 7) = qq m (2 * μ * C) + (2 * (3 * u - 2 * Y) + g2) + b2 := by
      rw [r2, ZMod.natCast_mod]; push_cast; rw [← hx, D2]
    rw [hY3] at QA QB; rw [hexc.2] at QB
    obtain ⟨K, k0, k1, k2, k4, k5⟩ := z63dbl g1 g2 g3 b1 b2 (z01 g1 hg1) (z01 g2 hg2) (z01 g3 hg3)
      (z01 b1 hb1) (z01 b2 hb2) s' hs' ((qq m (2 * μ * d4) : ZMod 7) - 2 * qq m (2 * μ * C))
    apply finish63 m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 (2 * μ) hμ2 (K - qq m (2 * μ * C))
    · intro x' hx'
      rcases (show x' = C ∨ x' = B ∨ x' = A by simpa using hx') with rfl | rfl | rfl
      · exact ok7_congr k0 (by ring)
      · exact ok7_congr k2 (by rw [QB]; ring)
      · exact ok7_congr k1 (by rw [QA]; ring)
    · exact ok7_congr k4 (by ring)
    · refine ok7_congr k5 ?_
      rw [D3] at hes'
      linear_combination -hes'
  · obtain ⟨s, hs, hes⟩ := et45 m μ d4 d5 hμ h40 h50 hr45
    rcases hvμ μ rfl with e | e
    · obtain ⟨K, k0, k1, k2, k4, k5⟩ := z63tabP δ u c3 hδ01 hc301 hexc c1 c2 c3' hc101 hc201 hc3'01 hcc
        s hs ((qq m (μ * d4) : ZMod 7) - 2 * qq m (μ * C))
      rw [← hY] at k1 k2 k5
      apply finish63 m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ (K - qq m (μ * C))
      · intro x' hx'
        rcases (show x' = C ∨ x' = B ∨ x' = A by simpa using hx') with rfl | rfl | rfl
        · exact ok7_congr k0 (by ring)
        · exact ok7_congr k2 (by rw [Q2]; ring)
        · exact ok7_congr k1 (by rw [Q1]; ring)
      · exact ok7_congr k4 (by ring)
      · refine ok7_congr k5 ?_
        rw [e] at hes
        linear_combination -hes
    · obtain ⟨K, k0, k1, k2, k4, k5⟩ := z63tabN δ u c3 hδ01 hc301 hexc c1 c2 c3' hc101 hc201 hc3'01 hcc
        s hs ((qq m (μ * d4) : ZMod 7) - 2 * qq m (μ * C))
      rw [← hY] at k1 k2 k5
      apply finish63 m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ (K - qq m (μ * C))
      · intro x' hx'
        rcases (show x' = C ∨ x' = B ∨ x' = A by simpa using hx') with rfl | rfl | rfl
        · exact ok7_congr k0 (by ring)
        · exact ok7_congr k2 (by rw [Q2]; ring)
        · exact ok7_congr k1 (by rw [Q1]; ring)
      · exact ok7_congr k4 (by ring)
      · refine ok7_congr k5 ?_
        rw [e] at hes
        linear_combination -hes

/-! ## assembling 6.3 -/

/-- (ii.2), `h < m`. -/
theorem low63 (m : ℕ) (hm : 2 ≤ m) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C) (t : ZMod 7)
    (htE : ediff m d4 d5 ≠ 0 → t = 5 * R (ediff m d4 d5))
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C)) (ht : R (E m B C) = t ∨ R (E m B C) = -t) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  by_cases hlev : ediff m d4 d5 ≠ 0 ∧ nu 7 (ediff m d4 d5) = h
  · have hsg := z7_sgn65 _ _ _ h3 (by rw [← htE hlev.1]; exact ht)
    exact tab63 m hm h hhm A B C d4 d5 hd h4 h5 hr4 hr5 hB hA h3 hlev.1 hlev.2 hsg
  · apply low63_off m h hhm A B C d4 d5 hd h4 h5 hr4 hr5 hB hA h3
    by_cases h0 : ediff m d4 d5 = 0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, fun he => hlev ⟨h0, he⟩⟩

/-- **Section 6.3** (`|A1| = 3`, `|A2| = |A4| = 1`, `m ≥ 2`). -/
theorem sec63 (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R (d 0)) (hr5 : R d5 = 4 * R (d 0)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      (qq m (lam * d4) ≠ 0 ∧ qq m (lam * d4) ≠ 6) ∧ (qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6) := by
  have hm1 : 1 ≤ m := by omega
  have Rd : ∀ i, R (d i) = R (d 0) := fun i => by
    rw [R_of_not_dvd (hd i), R_of_not_dvd (hd 0), hcl i 0]
  have cls : ∀ a b c : Fin 3, ∀ x ∈ [d a, d b, d c], ¬ 7 ∣ x ∧ x % 7 = d a % 7 := by
    intro a b c x hx
    rcases (show x = d a ∨ x = d b ∨ x = d c by simpa using hx) with rfl | rfl | rfl <;>
      exact ⟨hd _, hcl _ _⟩
  have r4 : ∀ i, R d4 = 2 * R (d i) := fun i => by rw [Rd]; exact hr4
  have r5 : ∀ i, R d5 = 4 * R (d i) := fun i => by rw [Rd]; exact hr5
  set t : ZMod 7 := if ediff m d4 d5 = 0 then 1 else 5 * R (ediff m d4 d5) with htdef
  have ht0 : t ≠ 0 := by
    rw [htdef]; split_ifs with h
    · decide
    · exact z7_five_ne _ (R_ne_zero h)
  have htE : ediff m d4 d5 ≠ 0 → t = 5 * R (ediff m d4 d5) := by
    intro h0; rw [htdef, if_neg h0]
  rcases lemma11 m d hcl t ht0 with hz | ⟨σ, hi | ⟨h, hall, h2 | ⟨h3, hpm⟩⟩⟩
  · have hw : Wb m (1 * d 0) (1 * d 1) (1 * d 2) := by
      simp only [one_mul]
      exact ⟨by rw [hz 0 2]; exact Nat.zero_le _, by rw [hz 1 2]; exact Nat.zero_le _⟩
    obtain ⟨lam, hc, hl⟩ := win63 m hm1 (d 0) (d 1) (d 2) d4 d5 (cls 2 1 0) h4 h5 (r4 2) (r5 2) 1
      (by norm_num) hw
    exact ⟨lam, hc, concl65 m lam (Equiv.refl _) _ _ _ (by simp) hl⟩
  · obtain ⟨lam, hc, hw⟩ := win9_i m (d (σ 0)) (d (σ 1)) (d (σ 2)) hi
    obtain ⟨lam', hc', hl⟩ := win63 m hm1 (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
      (r4 _) (r5 _) lam hc hw
    exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
  all_goals
    have n02 : σ 0 ≠ σ 2 := by simp
    have n12 : σ 1 ≠ σ 2 := by simp
    have hle : h ≤ m := by
      rw [← (hall _ _ n02).2]; exact nu_le_m (hall _ _ n02).1 (E_lt m _ _)
  · rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam, hc, hw⟩ := win9_ii m h (d (σ 1)) (d (σ 0)) (d (σ 2)) _ _ hlt rfl rfl
        (hall _ _ n12).1 (hall _ _ n02).1 (hall _ _ n12).2 (hall _ _ n02).2 (rp_of_R h2)
      rcases hw with hw | hw | hw
      · obtain ⟨lam', hc', hl⟩ := win63 m hm1 (d (σ 1)) (d (σ 0)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
      · obtain ⟨lam', hc', hl⟩ := win63 m hm1 (d (σ 2)) (d (σ 0)) (d (σ 1)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
      · obtain ⟨lam', hc', hl⟩ := win63 m hm1 (d (σ 1)) (d (σ 2)) (d (σ 0)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := top1_63 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) (hall _ _ n12) (hall _ _ n02) h2
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam, hc, hl⟩ := low63 m hm h hlt (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) t htE (hall _ _ n12) (hall _ _ n02) h3 hpm
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := top2_63 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) (hall _ _ n12) (hall _ _ n02) h3
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩

/-- **Section 6.3, real form** with one top speed. -/
theorem sec63_witness (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R (d 0)) (hr5 : R d5 = 4 * R (d 0)) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d4) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d5) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hc, hlam, hl4, hl5⟩ := sec63 m hm d hd hcl d4 d5 h4 h5 hr4 hr5
  obtain ⟨t, ht, hall⟩ := witness_of_lam m lam hc (d4 :: d5 :: List.ofFn d) [d6]
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hl4
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hl5
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hlam i)
    (by intro x hx; simp at hx; subst hx; exact ⟨h6, h6m⟩)
  exact ⟨t, ht, fun i => hall _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_ofFn.mpr ⟨i, rfl⟩)))), hall _ (by simp), hall _ (by simp), hall _ (by simp)⟩

end LRSpectrumFull.BarajasSerra.Sec6
