import LRSpectrumFull.BarajasSerraSec6_2

/-!
# E6 session 18: Barajas-Serra Section 6.4 (`|A1| = 3`, `|A2| = 2`), case (a), `m ≥ 2`

`A1 = {d0, d1, d2}` (level 0, one class), `A2 = {d4, d5}` (level 0, class `2 r(A1)`).
Conclusion: a multiplier prime to 7 keeping all five off `q ∈ {0, 6}` (`sec64`), real form with a
top speed (`sec64_witness`).

Route (paper 6.4 with corrections): Lemma 11 with `t = r(e45)` (or `1` if `e45 ≡ 0`).
* (i), (ii) with `h < m`, all congruent: Lemma 9 gives `l(A1) ≤ 3`, then Lemma 12 (i) (`Z7.lemma12_i`).
* (ii.1), `h = m`: rescale, offsets `{0, 1, 2}`, `z7_sec64i`.
* (ii.2), `h = m`: rescale, offsets `(3, 1, 0)` for `(d1, d2, d3)` (labels of Lemma 11).
  If `e(d3, d4)` (or `e(d3, d5)`) is nonzero below the top: Lemma 7 (i) with `X = {2,3,4,5}` and the
  one-element form of Lemma 12 (ii) (`z7_sec64a`; the VERIFIED `Z7.lemma12_ii` asks the condition for
  both elements of `A2`, the paper's proof needs it for one). Otherwise both are `7^m z4`, `7^m z5`:
  `z4 = z5` gives `q(d4) = q(d5)` and Lemma 5 (`z7_sec64b`); `z4 ≠ z5` gives `e45 ≡ ±N/7` after the
  rescale (this is where `t` is used), Lemma 7 (ii) (extended) on the lower element with `X = {4}`,
  and Lemma 6 (ii) (`z7_sec64c`).
Paper typos: "if r ν(e35) < m" (read `ν(e35) < m`); 6.4 needs `e45 = 0` handled (the paper's `ν(e45) = m`
silently assumes `d4 ≢ d5 mod N`).
Falsified first: `e6s18/lean18.rs` (`sub`): 6.4 conclusion, m = 2, all class-1 3-multisets and class-2
2-multisets mod N: 25510625 configurations, 0 failures (negative control `Lambda_0` only fails).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- `E` under a unit multiplier. -/
theorem E_scale (m μ x y : ℕ) (hμ : Nat.Coprime μ 7) (h0 : E m x y ≠ 0) :
    E m (μ * x) (μ * y) ≠ 0 ∧ nu 7 (E m (μ * x) (μ * y)) = nu 7 (E m x y) ∧
      R (E m (μ * x) (μ * y)) = (μ : ZMod 7) * R (E m x y) := by
  obtain ⟨n, hn, hn7, hR⟩ := form_of h0
  have hle := nu_le_m h0 (E_lt m x y)
  have key := levZ (m := m) (h := nu 7 (E m x y)) (e := E m (μ * x) (μ * y)) (u := ((μ * n : ℕ) : ℤ))
    (E_lt m _ _) hle (by exact_mod_cast not_dvd_mul hμ hn7)
    (by
      rw [E_cast]
      have h1 := E_cast m x y
      rw [hn] at h1
      push_cast at h1 ⊢
      linear_combination -(μ : ZMod (7 ^ (m + 1))) * h1)
  refine ⟨key.1, key.2.1, ?_⟩
  rw [key.2.2, hR]; push_cast; ring

theorem qq_eq_of_E0 {m x y : ℕ} (h : E m x y = 0) (μ : ℕ) : qq m (μ * x) = qq m (μ * y) := by
  have := E_modEq m x y; rw [h, add_zero] at this
  unfold qq; exact qarc_congr (this.mul_left μ)

theorem rp_of_R3 {x y : ℕ} (h : R y = 3 * R x) : rp 7 y = 3 * rp 7 x % 7 := by
  apply nat_cast_zmod7_eq_of_lt (rp_lt _) (Nat.mod_lt _ (by norm_num))
  rw [ZMod.natCast_mod]; push_cast; exact h

theorem z7_sec64i : ∀ a' p q : ZMod 7,
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 1 + K) ∧ ok7 (a' + 2 + K) ∧ ok7 (p + 2 * K) ∧ ok7 (q + 2 * K) := by
  decide

theorem z7_sec64a : ∀ a' p q : ZMod 7, (2 * a' - p = 0 ∨ 2 * a' - p = 1 ∨ 2 * a' - p = 6) →
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 1 + K) ∧ ok7 (a' + 3 + K) ∧ ok7 (p + 2 * K) ∧ ok7 (q + 2 * K) := by
  decide

theorem z7_sec64b : ∀ a' p : ZMod 7,
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 1 + K) ∧ ok7 (a' + 3 + K) ∧ ok7 (p + 2 * K) := by
  decide

theorem z7_sec64c : ∀ a' p : ZMod 7, 2 * a' - p ≠ 4 →
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 1 + K) ∧ ok7 (a' + 3 + K) ∧ ok7 (p + 2 * K) ∧
      ok7 (p + 1 + 2 * K) := by
  decide

theorem mem_list5 {x a b c d e : ℕ} (hx : x ∈ [a, b, c, d, e]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  simpa using hx

/-- the 6.4 finish for a labeled triple `(a, b, c)` of `A1` and `A2 = {d4, d5}`. -/
theorem finish64 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [a, b, c], ¬ 7 ∣ x ∧ x % 7 = a % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R a) (hr5 : R d5 = 2 * R a) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (K : ZMod 7) (hK : ∀ x ∈ [a, b, c], ok7 ((qq m (μ * x) : ZMod 7) + K))
    (hK4 : ok7 ((qq m (μ * d4) : ZMod 7) + 2 * K)) (hK5 : ok7 ((qq m (μ * d5) : ZMod 7) + 2 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [a, b, c, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have ha := (hd a (by simp)).1
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; exact ha (dvd_zero 7)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hρ : R (μ * a) ≠ 0 := R_ne_zero (Nat.mul_ne_zero hμ0 ha0)
  obtain ⟨lam, hc, hall⟩ := finish_list m hm μ hμ _ hρ
    ([(a, 1), (b, 1), (c, 1), (d4, 2), (d5, 2)])
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨ha, by ring⟩
      · obtain ⟨h7, hcl⟩ := hd b (by simp)
        have hx0 : b ≠ 0 := by intro h; rw [h] at h7; exact h7 (dvd_zero 7)
        refine ⟨h7, ?_⟩
        rw [R_mul_unit hμ hx0, R_mul_unit hμ ha0, R_of_not_dvd h7, R_of_not_dvd ha, hcl]; ring
      · obtain ⟨h7, hcl⟩ := hd c (by simp)
        have hx0 : c ≠ 0 := by intro h; rw [h] at h7; exact h7 (dvd_zero 7)
        refine ⟨h7, ?_⟩
        rw [R_mul_unit hμ hx0, R_mul_unit hμ ha0, R_of_not_dvd h7, R_of_not_dvd ha, hcl]; ring
      · exact ⟨h4, by rw [R_mul_unit hμ h40, R_mul_unit hμ ha0, hr4]; ring⟩
      · exact ⟨h5, by rw [R_mul_unit hμ h50, R_mul_unit hμ ha0, hr5]; ring⟩) K
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · simpa using hK a (by simp)
      · simpa using hK b (by simp)
      · simpa using hK c (by simp)
      · exact hK4
      · exact hK5)
  refine ⟨lam, hc, ?_⟩
  intro x hx
  rcases mem_list5 hx with rfl | rfl | rfl | rfl | rfl
  · exact hall (x, 1) (by simp)
  · exact hall (x, 1) (by simp)
  · exact hall (x, 1) (by simp)
  · exact hall (x, 2) (by simp)
  · exact hall (x, 2) (by simp)

/-- `l(A1) ≤ 3` after `μ` finishes 6.4 (Lemma 12 (i)). -/
theorem ell64 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [a, b, c], ¬ 7 ∣ x ∧ x % 7 = a % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R a) (hr5 : R d5 = 2 * R a) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (hell : ellq m (μ * a) (μ * b) (μ * c) ≤ 3) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [a, b, c, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨k, h1, h2, -⟩ := Z7.lemma12_i _ {((qq m (μ * d4) : ℕ) : ZMod 7), ((qq m (μ * d5) : ℕ) : ZMod 7)}
    (Finset.card_le_two) hell
  apply finish64 m hm a b c d4 d5 hd h4 h5 hr4 hr5 μ hμ k
  · intro x hx
    rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
    · exact h1 _ (by simp)
    · exact h1 _ (by simp)
    · exact h1 _ (by simp)
  · exact h2 _ (by simp)
  · exact h2 _ (by simp)

/-! ## `h = m` -/

theorem scale_top {m μ x y n k : ℕ} (h : x ≡ y + 7 ^ m * n [MOD 7 ^ (m + 1)]) (hk : k < 7)
    (hmn : ((μ * n : ℕ) : ZMod 7) = k) : μ * x ≡ μ * y + 7 ^ m * k [MOD 7 ^ (m + 1)] := by
  have hmod : (μ * n) % 7 = k := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hmn; rwa [Nat.mod_eq_of_lt hk] at this
  have h2 := h.mul_left μ
  refine h2.trans ?_
  have h3 : μ * (y + 7 ^ m * n) = μ * y + 7 ^ m * k + 7 ^ (m + 1) * (μ * n / 7) := by
    have := Nat.div_add_mod (μ * n) 7
    rw [pow_succ, ← hmod]
    calc μ * (y + 7 ^ m * n) = μ * y + 7 ^ m * (μ * n) := by ring
      _ = μ * y + 7 ^ m * (7 * (μ * n / 7) + μ * n % 7) := by rw [this]
      _ = _ := by ring
  rw [h3]; unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]

theorem qq_of_top1 {m x y k : ℕ} (h : x ≡ y + 7 ^ m * k [MOD 7 ^ (m + 1)]) :
    (qq m x : ZMod 7) = qq m y + k := by
  have := top_shift m 1 x y k h; simpa using this

theorem z7_not2345 : ∀ v : ZMod 7, v ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) → (v = 0 ∨ v = 1 ∨ v = 6) := by
  decide
theorem ell2345 : Z7.ell {2, 3, 4, 5} ≤ 4 := by decide
theorem ell4 : Z7.ell {4} ≤ 4 := by decide
theorem z7_x4 : ∀ z : ZMod 7, ¬ (z ∈ ({4} : Finset (ZMod 7)) ∧ z - 1 ∈ ({4} : Finset (ZMod 7))) := by
  decide

theorem not_dvd_of_class {x c : ℕ} (hc : ¬ 7 ∣ c) (h : x % 7 = c % 7) : ¬ 7 ∣ x := by omega

/-- (ii.2), `h = m`, Lemma 7 (i) branch: `e(C, lo)` nonzero below the top. -/
theorem fin64_sub (m : ℕ) (hm : 2 ≤ m) (C B A lo ot : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (hlo : ¬ 7 ∣ lo) (hot : ¬ 7 ∣ ot)
    (hrlo : R lo = 2 * R C) (hrot : R ot = 2 * R C) (μ : ℕ) (hμ : Nat.Coprime μ 7)
    (hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)]) (hAm : μ * A ≡ μ * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)])
    (hsub : ediff m (μ * C) (μ * lo) ≠ 0 ∧ nu 7 (ediff m (μ * C) (μ * lo)) < m) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, lo, ot], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have hC := (hd C (by simp)).1
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; exact hC (dvd_zero 7)
  have hlo0 : lo ≠ 0 := by intro h; rw [h] at hlo; exact hlo (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hr : rp 7 (μ * lo) = 2 * rp 7 (μ * C) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ hlo0, R_mul_unit hμ hC0, hrlo]; ring
  obtain ⟨h', hh', lam, hlam, hX⟩ := lemma7_i m (μ * C) (μ * lo) {2, 3, 4, 5} (not_dvd_mul hμ hC)
    (not_dvd_mul hμ hlo) hr hsub.1 hsub.2 ell2345
  have hl := Lam_modEq_seven hh' hlam
  have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
  rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 hC0) (Nat.mul_ne_zero hμ0 hlo0) hr] at hX
  set μ' := lam * μ with hμ'
  rw [show lam * (μ * C) = μ' * C by rw [hμ', mul_assoc],
    show lam * (μ * lo) = μ' * lo by rw [hμ', mul_assoc]] at hX
  have oB := qq_of_top1 (show μ' * B ≡ μ' * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] by
    rw [hμ', mul_assoc, mul_assoc]; exact top_keep hl hBm)
  have oA := qq_of_top1 (show μ' * A ≡ μ' * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)] by
    rw [hμ', mul_assoc, mul_assoc]; exact top_keep hl hAm)
  obtain ⟨K, k0, k1, k3, k4, k5⟩ := z7_sec64a (qq m (μ' * C)) (qq m (μ' * lo)) (qq m (μ' * ot))
    (z7_not2345 _ hX)
  apply finish64 m (by omega) C B A lo ot hd hlo hot hrlo hrot μ' (Nat.Coprime.mul_left hlc hμ) K
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [oB]; push_cast; ring)
    · exact ok7_congr k3 (by rw [oA]; push_cast; ring)
  · exact k4
  · exact k5

/-- (ii.2), `h = m`, `e45 ≡ ±N/7`: Lemma 7 (ii) on the lower element, then Lemma 6 (ii). -/
theorem fin64_lower (m : ℕ) (hm : 2 ≤ m) (C B A up lo : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (hup : ¬ 7 ∣ up) (hlo : ¬ 7 ∣ lo)
    (hrup : R up = 2 * R C) (hrlo : R lo = 2 * R C) (μ : ℕ) (hμ : Nat.Coprime μ 7)
    (hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)]) (hAm : μ * A ≡ μ * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)])
    (hul : μ * up ≡ μ * lo + 7 ^ m * 1 [MOD 7 ^ (m + 1)]) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, up, lo], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have hC := (hd C (by simp)).1
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; exact hC (dvd_zero 7)
  have hlo0 : lo ≠ 0 := by intro h; rw [h] at hlo; exact hlo (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hr : rp 7 (μ * lo) = 2 * rp 7 (μ * C) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ hlo0, R_mul_unit hμ hC0, hrlo]; ring
  obtain ⟨lam, hl, hX⟩ := steer m hm (μ * C) (μ * lo) (not_dvd_mul hμ hC) (not_dvd_mul hμ hlo) hr {4}
    ell4 (fun z _ _ => z7_x4 z)
  have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
  rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 hC0) (Nat.mul_ne_zero hμ0 hlo0) hr] at hX
  set μ' := lam * μ with hμ'
  rw [show lam * (μ * C) = μ' * C by rw [hμ', mul_assoc],
    show lam * (μ * lo) = μ' * lo by rw [hμ', mul_assoc]] at hX
  have oB := qq_of_top1 (show μ' * B ≡ μ' * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] by
    rw [hμ', mul_assoc, mul_assoc]; exact top_keep hl hBm)
  have oA := qq_of_top1 (show μ' * A ≡ μ' * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)] by
    rw [hμ', mul_assoc, mul_assoc]; exact top_keep hl hAm)
  have oU := qq_of_top1 (show μ' * up ≡ μ' * lo + 7 ^ m * 1 [MOD 7 ^ (m + 1)] by
    rw [hμ', mul_assoc, mul_assoc]; exact top_keep hl hul)
  simp only [Finset.mem_singleton] at hX
  obtain ⟨K, k0, k1, k3, k4, k5⟩ := z7_sec64c (qq m (μ' * C)) (qq m (μ' * lo)) hX
  apply finish64 m (by omega) C B A up lo hd hup hlo hrup hrlo μ' (Nat.Coprime.mul_left hlc hμ) K
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [oB]; push_cast; ring)
    · exact ok7_congr k3 (by rw [oA]; push_cast; ring)
  · exact ok7_congr k5 (by rw [oU]; push_cast; ring)
  · exact k4

theorem list5_swap {P : ℕ → Prop} {C B A x y : ℕ} (h : ∀ z ∈ [C, B, A, x, y], P z) :
    ∀ z ∈ [C, B, A, y, x], P z := by
  intro z hz; apply h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; tauto

theorem z7_pm : ∀ u w t : ZMod 7, u * w = 1 → (w = t ∨ w = -t) → (u * t = 1 ∨ u * t = -1) := by
  decide

theorem z7_x_of_cast {n : ℕ} (hn : n < 7) (h : (n : ZMod 7) = 1) : n = 1 :=
  nat_cast_zmod7_eq_of_lt hn (by norm_num) (by rw [h]; rfl)

/-- 6.4, Lemma 11 (ii.2) with `h = m` (labels `A, B, C` = the paper's `d1, d2, d3`). -/
theorem sec64_top2 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 2 * R C) (t : ZMod 7)
    (htE : E m d4 d5 ≠ 0 → R (E m d4 d5) = t)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = m) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = m)
    (h3 : R (E m A C) = 3 * R (E m B C)) (ht : R (E m B C) = t ∨ R (E m B C) = -t) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨nB, -, hBm0, hRB⟩ := off_of_top m B C hB.1 hB.2
  obtain ⟨nA, -, hAm0, hRA⟩ := off_of_top m A C hA.1 hA.2
  set w := R (E m B C) with hw
  have hw0 : w ≠ 0 := R_ne_zero hB.1
  obtain ⟨u, hu⟩ := z7_solve w 1 hw0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  set μ := u.val
  have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
  have hμ : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
    scale_top hBm0 (by norm_num) (by push_cast; rw [hμu, hRB, hu])
  have hAm : μ * A ≡ μ * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)] :=
    scale_top hAm0 (by norm_num) (by push_cast; rw [hμu, hRA, h3]; linear_combination 3 * hu)
  have hC := (hd C (by simp)).1
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; exact hC (dvd_zero 7)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hr4' : rp 7 (μ * d4) = 2 * rp 7 (μ * C) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h40, R_mul_unit hμ hC0, hr4]; ring
  have hr5' : rp 7 (μ * d5) = 2 * rp 7 (μ * C) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h50, R_mul_unit hμ hC0, hr5]; ring
  by_cases hs4 : ediff m (μ * C) (μ * d4) ≠ 0 ∧ nu 7 (ediff m (μ * C) (μ * d4)) < m
  · exact fin64_sub m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hBm hAm hs4
  by_cases hs5 : ediff m (μ * C) (μ * d5) ≠ 0 ∧ nu 7 (ediff m (μ * C) (μ * d5)) < m
  · obtain ⟨lam, hc, hl⟩ := fin64_sub m hm C B A d5 d4 hd h5 h4 hr5 hr4 μ hμ hBm hAm hs5
    exact ⟨lam, hc, list5_swap hl⟩
  have tz : ∀ y, rp 7 (μ * y) = 2 * rp 7 (μ * C) % 7 →
      ¬ (ediff m (μ * C) (μ * y) ≠ 0 ∧ nu 7 (ediff m (μ * C) (μ * y)) < m) →
      ∃ z, z < 7 ∧ (((2 * (μ * C) : ℕ) : ZMod (7 ^ (m + 1))) - ((μ * y : ℕ) : ZMod (7 ^ (m + 1))) =
        ((7 ^ m * z : ℕ) : ZMod (7 ^ (m + 1)))) := by
    intro y hry hs
    have h0 : ediff m (μ * C) (μ * y) = 0 ∨ nu 7 (ediff m (μ * C) (μ * y)) = m := by
      by_cases h0 : ediff m (μ * C) (μ * y) = 0
      · exact Or.inl h0
      · right; have := nu_le_m h0 (ediff_lt m _ _); push Not at hs; have := hs h0; omega
    obtain ⟨z, hz7, hze⟩ := top_or_zero (ediff_lt m _ _) h0
    refine ⟨z, hz7, ?_⟩
    rw [← hze, (ediff_branch1 m _ _ hry).1, dsub_cast _ _ _ (N_pos m)]
  obtain ⟨z4, hz4, e4⟩ := tz d4 hr4' hs4
  obtain ⟨z5, hz5, e5⟩ := tz d5 hr5' hs5
  have c45 : ((E m (μ * d4) (μ * d5) : ℕ) : ZMod (7 ^ (m + 1))) =
      (((7 : ℤ) ^ m * ((z5 : ℤ) - z4) : ℤ) : ZMod (7 ^ (m + 1))) := by
    rw [E_cast]; push_cast at e4 e5 ⊢; linear_combination e5 - e4
  by_cases hzz : z4 = z5
  · have hE0 : E m (μ * d4) (μ * d5) = 0 := by
      apply eq_of_cast_N (E_lt m _ _) (N_pos m); rw [c45, hzz]; simp
    have hq45 := qq_eq_of_E0 hE0 1
    simp only [one_mul] at hq45
    have oB := qq_of_top1 hBm
    have oA := qq_of_top1 hAm
    obtain ⟨K, k0, k1, k3, k4⟩ := z7_sec64b (qq m (μ * C)) (qq m (μ * d4))
    apply finish64 m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ K
    · intro x hx
      rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
      · exact k0
      · exact ok7_congr k1 (by rw [oB]; push_cast; ring)
      · exact ok7_congr k3 (by rw [oA]; push_cast; ring)
    · exact k4
    · rw [← hq45]; exact k4
  · have hnd : ¬ (7 : ℤ) ∣ ((z5 : ℤ) - z4) := by omega
    obtain ⟨hne, hnu, hR45⟩ := levZ (E_lt m (μ * d4) (μ * d5)) le_rfl hnd c45
    have hE45 : E m d4 d5 ≠ 0 := by
      intro h0
      apply hne
      apply eq_of_cast_N (E_lt m _ _) (N_pos m)
      rw [E_cast]
      have := E_cast m d4 d5; rw [h0] at this; push_cast at this ⊢
      linear_combination -(μ : ZMod (7 ^ (m + 1))) * this
    have hsc := (E_scale m μ d4 d5 hμ hE45).2.2
    rw [htE hE45, hμu] at hsc
    rcases z7_pm u w t hu ht with hp | hp
    · -- e45 ≡ +N/7: d4 upper, d5 lower
      obtain ⟨n, hn7, hnm, hnR⟩ := off_of_top m (μ * d4) (μ * d5) hne hnu
      have hn1 : n = 1 := z7_x_of_cast hn7 (by rw [hnR, hsc, hp])
      rw [hn1] at hnm
      exact fin64_lower m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hBm hAm hnm
    · -- e45 ≡ -N/7: d5 upper, d4 lower
      obtain ⟨hne', hnu', hR'⟩ := swap_rule m (μ * d4) (μ * d5) hne
      obtain ⟨n, hn7, hnm, hnR⟩ := off_of_top m (μ * d5) (μ * d4) hne' (by rw [hnu', hnu])
      have hn1 : n = 1 := z7_x_of_cast hn7 (by rw [hnR, hR', hsc, hp]; ring)
      rw [hn1] at hnm
      obtain ⟨lam, hc, hl⟩ := fin64_lower m hm C B A d5 d4 hd h5 h4 hr5 hr4 μ hμ hBm hAm hnm
      exact ⟨lam, hc, list5_swap hl⟩

/-- 6.4, Lemma 11 (ii.1) with `h = m`: offsets `(2, 1, 0)`. -/
theorem sec64_top1 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 2 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = m) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = m)
    (h2 : R (E m A C) = 2 * R (E m B C)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨nB, -, hBm0, hRB⟩ := off_of_top m B C hB.1 hB.2
  obtain ⟨nA, -, hAm0, hRA⟩ := off_of_top m A C hA.1 hA.2
  set w := R (E m B C) with hw
  have hw0 : w ≠ 0 := R_ne_zero hB.1
  obtain ⟨u, hu⟩ := z7_solve w 1 hw0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  set μ := u.val
  have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
  have hμ : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
  have oB := qq_of_top1 (scale_top (μ := μ) hBm0 (k := 1) (by norm_num) (by push_cast; rw [hμu, hRB, hu]))
  have oA := qq_of_top1 (scale_top (μ := μ) hAm0 (k := 2) (by norm_num)
    (by push_cast; rw [hμu, hRA, h2]; linear_combination 2 * hu))
  obtain ⟨K, k0, k1, k2, k4, k5⟩ := z7_sec64i (qq m (μ * C)) (qq m (μ * d4)) (qq m (μ * d5))
  apply finish64 m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ K
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [oB]; push_cast; ring)
    · exact ok7_congr k2 (by rw [oA]; push_cast; ring)
  · exact k4
  · exact k5

theorem concl64 {d : Fin 3 → ℕ} {d4 d5 : ℕ} (σ : Equiv.Perm (Fin 3)) (i1 i2 i3 : Fin 3)
    (hcov : ∀ k : Fin 3, k = i1 ∨ k = i2 ∨ k = i3) {P : ℕ → Prop}
    (h : ∀ x ∈ [d (σ i1), d (σ i2), d (σ i3), d4, d5], P x) : (∀ i, P (d i)) ∧ P d4 ∧ P d5 := by
  refine ⟨fun i => ?_, h _ (by simp), h _ (by simp)⟩
  have hi : i = σ (σ.symm i) := by simp
  rw [hi]
  rcases hcov (σ.symm i) with e | e | e <;> rw [e] <;> exact h _ (by simp)

theorem cov012 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
theorem cov102 : ∀ k : Fin 3, k = 1 ∨ k = 0 ∨ k = 2 := by decide
theorem cov210 : ∀ k : Fin 3, k = 2 ∨ k = 1 ∨ k = 0 := by decide

/-- **Section 6.4** (`|A1| = 3`, `|A2| = 2`, `m ≥ 2`). -/
theorem sec64 (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R (d 0)) (hr5 : R d5 = 2 * R (d 0)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      (qq m (lam * d4) ≠ 0 ∧ qq m (lam * d4) ≠ 6) ∧ (qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6) := by
  have hm1 : 1 ≤ m := by omega
  have Rd : ∀ i, R (d i) = R (d 0) := fun i => by
    rw [R_of_not_dvd (hd i), R_of_not_dvd (hd 0), hcl i 0]
  have cls : ∀ a b c : Fin 3, ∀ x ∈ [d a, d b, d c], ¬ 7 ∣ x ∧ x % 7 = d a % 7 := by
    intro a b c x hx
    rcases (show x = d a ∨ x = d b ∨ x = d c by simpa using hx) with rfl | rfl | rfl <;>
      exact ⟨hd _, hcl _ _⟩
  set t : ZMod 7 := if R (E m d4 d5) = 0 then 1 else R (E m d4 d5) with htdef
  have ht0 : t ≠ 0 := by rw [htdef]; split_ifs with h; exacts [by decide, h]
  have htE : E m d4 d5 ≠ 0 → R (E m d4 d5) = t := by
    intro h0; rw [htdef, if_neg (R_ne_zero h0)]
  rcases lemma11 m d hcl t ht0 with hz | ⟨σ, hi | ⟨h, hall, h2 | ⟨h3, hpm⟩⟩⟩
  · -- all congruent
    have hell : ellq m (1 * d 0) (1 * d 1) (1 * d 2) ≤ 2 := by
      have e1 := qq_eq_of_E0 (hz 1 0) 1
      have e2 := qq_eq_of_E0 (hz 2 0) 1
      unfold ellq
      rw [e1, e2]
      apply ell3_core2 _ _ _ (qq_lt m _) (qq_lt m _) (qq_lt m _) <;> omega
    obtain ⟨lam, hc, hl⟩ := ell64 m hm1 (d 0) (d 1) (d 2) d4 d5 (cls 0 1 2) h4 h5 hr4 hr5 1
      (by norm_num) (le_trans hell (by norm_num))
    exact ⟨lam, hc, concl64 (Equiv.refl _) 0 1 2 cov012 hl⟩
  · obtain ⟨lam, hc, -, hell⟩ := lemma9_i m (d (σ 0)) (d (σ 1)) (d (σ 2)) _ _ rfl rfl hi
    obtain ⟨lam', hc', hl⟩ := ell64 m hm1 (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
      (by rw [Rd]; exact hr4) (by rw [Rd]; exact hr5) lam hc (le_trans hell (by norm_num))
    exact ⟨lam', hc', concl64 σ 0 1 2 cov012 hl⟩
  all_goals
    have n02 : σ 0 ≠ σ 2 := by simp
    have n12 : σ 1 ≠ σ 2 := by simp
    have hle : h ≤ m := by
      rw [← (hall _ _ n02).2]; exact nu_le_m (hall _ _ n02).1 (E_lt m _ _)
  · rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam1, lam2, -, -, hc, -, hell⟩ := lemma9_ii_two m h (d (σ 1)) (d (σ 0)) (d (σ 2)) _ _ hlt
        rfl rfl (hall _ _ n12).1 (hall _ _ n02).1 (hall _ _ n12).2 (hall _ _ n02).2 (rp_of_R h2)
      obtain ⟨lam', hc', hl⟩ := ell64 m hm1 (d (σ 1)) (d (σ 0)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (by rw [Rd]; exact hr4) (by rw [Rd]; exact hr5) _ hc (le_trans hell (by norm_num))
      exact ⟨lam', hc', concl64 σ 1 0 2 cov102 hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := sec64_top1 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (by rw [Rd]; exact hr4) (by rw [Rd]; exact hr5) (hall _ _ n12) (hall _ _ n02) h2
      exact ⟨lam, hc, concl64 σ 2 1 0 cov210 hl⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam, hlam, -, hell⟩ := lemma9_ii_three m h (d (σ 1)) (d (σ 0)) (d (σ 2)) _ _ hlt
        rfl rfl (hall _ _ n12).1 (hall _ _ n02).1 (hall _ _ n12).2 (hall _ _ n02).2 (rp_of_R3 h3)
      have hc := (coprime_of_modEq_one (by norm_num) (Lam_modEq_seven hlt hlam)).1
      obtain ⟨lam', hc', hl⟩ := ell64 m hm1 (d (σ 1)) (d (σ 0)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (by rw [Rd]; exact hr4) (by rw [Rd]; exact hr5) _ hc hell
      exact ⟨lam', hc', concl64 σ 1 0 2 cov102 hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := sec64_top2 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (by rw [Rd]; exact hr4) (by rw [Rd]; exact hr5) t htE (hall _ _ n12) (hall _ _ n02) h3 hpm
      exact ⟨lam, hc, concl64 σ 2 1 0 cov210 hl⟩

/-- **Section 6.4, real form** with one top speed. -/
theorem sec64_witness (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R (d 0)) (hr5 : R d5 = 2 * R (d 0)) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d4) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d5) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hc, hlam, hl4, hl5⟩ := sec64 m hm d hd hcl d4 d5 h4 h5 hr4 hr5
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
