import LRSpectrumFull.BarajasSerraSec6_4

/-!
# E6 session 19: Barajas-Serra Section 6.5 (`|A1| = 3`, `|A4| = 2`), case (a), `m ≥ 2`

`A1 = {d0, d1, d2}` (level 0, one class `ρ`), `A4 = {d4, d5}` (level 0, class `4ρ`).
Conclusion: a multiplier prime to 7 keeping all five off `q ∈ {0, 6}` (`sec65`), real form with a
top speed (`sec65_witness`).

Route (paper 6.5 with corrections; the paper's heading `A2 = {d4, d5}` means `A4`).
Lemma 11 with `t = 5 r(e45)` (`1` if `e45 ≡ 0`), so that `r(e13) = ±r(e45)` in (ii.2).
* all congruent, (i), (ii.1) with `h < m`: Lemma 9 in window form (`Wb`, `win9_i`, `win9_ii`), then the
  multiplier `μ ∈ {1, 2, 3}` chosen from the position of `e45` (`range3`: `q(e45) ∈ {0,1,5,6}`, or
  `q(2 e45) ∈ {5,6,0,1}`, or `q(3 e45) ∈ {6,0}`), and eq. (14) in the explicit form `z65w1/2/3`.
* (ii.2), `h < m`: Lemma 9 (ii) `j = 3` in difference form (`l9diff`, `diff3`), with Lemma 2 on `e45`
  (level above `h`), on `f = e45 - e13` (level `h`, after the sign choice), or after Lemma 9 (level
  below `h`); `q(e45)` lands in `{5,6,0,1}`, eq. (14).
* (ii.1), `h = m`: offsets `(0,1,2)`; `e45` zero or below the top: Lemma 2; top `zN/7`, `z ∈ {1,2,5,6}`:
  direct; `z ∈ {3,4}` (after renaming `z = 4`): Lemma 7 with `X = {3,4}` on `(lo, d3)`, and in the
  exceptional case `e(lo, d3) = 4N/7` (the session-16 erratum: the paper's `5N/2`) the doubling
  `2 * Lam_1 * Lam_0`: after doubling `e = N/7`, Lemma 7 (ii) with `X = {2,4,6}`.
* (ii.2), `h = m`: offsets `(0,5,1)` after the rescale `(3 r(e23))⁻¹`; `e45` below the top: Lemma 2; top:
  `e45 = ±N/7` by the choice of `t`; eq. (14) with `l(A1) = 4`, `l(A4) ≤ 2` (`zt051`).
Falsified first: `e6s19/lean19.rs`: 6.5 conclusion m = 2, all class-1 3-multisets and class-4
2-multisets mod N: 25510625 configurations, 0 failures (negative control `Lambda_0` only: 3479049
failures); `range3` m = 2, 3: 0 failures (control without `μ = 3` fails); window pair trick 0 failures
(control `μ = 1` only fails); (ii.2) `q(λ e45) ∈ {5,6,0,1}`: 0 failures m = 2, 3.
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-! ## finishing -/

/-- the 6.5 finish for a labeled triple `(a, b, c)` of `A1` and `A4 = {d4, d5}`. -/
theorem finish65 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [a, b, c], ¬ 7 ∣ x ∧ x % 7 = a % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 4 * R a) (hr5 : R d5 = 4 * R a) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (K : ZMod 7) (hK : ∀ x ∈ [a, b, c], ok7 ((qq m (μ * x) : ZMod 7) + K))
    (hK4 : ok7 ((qq m (μ * d4) : ZMod 7) + 4 * K)) (hK5 : ok7 ((qq m (μ * d5) : ZMod 7) + 4 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [a, b, c, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have ha := (hd a (by simp)).1
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; exact ha (dvd_zero 7)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hρ : R (μ * a) ≠ 0 := R_ne_zero (Nat.mul_ne_zero hμ0 ha0)
  obtain ⟨lam, hc, hall⟩ := finish_list m hm μ hμ _ hρ
    ([(a, 1), (b, 1), (c, 1), (d4, 4), (d5, 4)])
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
  · exact hall (x, 4) (by simp)
  · exact hall (x, 4) (by simp)

/-- finish from explicit offsets: `q(B) = q(C) + β`, `q(A) = q(C) + α`, `q(up) = q(lo) + o`. -/
theorem finish65' (m : ℕ) (hm : 1 ≤ m) (C B A up lo : ℕ) (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7)
    (hup : ¬ 7 ∣ up) (hlo : ¬ 7 ∣ lo) (hrup : R up = 4 * R C) (hrlo : R lo = 4 * R C) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (β α o : ZMod 7)
    (hB : (qq m (μ * B) : ZMod 7) = qq m (μ * C) + β) (hA : (qq m (μ * A) : ZMod 7) = qq m (μ * C) + α)
    (hp : (qq m (μ * up) : ZMod 7) = qq m (μ * lo) + o)
    (hZ : ∃ K, ok7 ((qq m (μ * C) : ZMod 7) + K) ∧ ok7 ((qq m (μ * C) : ZMod 7) + β + K) ∧
      ok7 ((qq m (μ * C) : ZMod 7) + α + K) ∧ ok7 ((qq m (μ * lo) : ZMod 7) + 4 * K) ∧
      ok7 ((qq m (μ * lo) : ZMod 7) + o + 4 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, up, lo], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨K, k0, k1, k2, k4, k5⟩ := hZ
  apply finish65 m hm C B A up lo hd hup hlo hrup hrlo μ hμ K
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [hB])
    · exact ok7_congr k2 (by rw [hA])
  · exact ok7_congr k5 (by rw [hp])
  · exact k4

/-! ## carries and the position lemma -/

/-- two-step carry for `2 δ`, `δ ≤ 7^m`. -/
theorem carry_two {m b c δ : ℕ} (hb : b ≡ c + δ [MOD 7 ^ (m + 1)]) (hδ : δ ≤ 7 ^ m) :
    ∃ f : ℕ, f < 3 ∧ (qq m (2 * b) : ZMod 7) = qq m (2 * c) + f := by
  have h2 : 2 * b ≡ (2 * c + δ) + δ [MOD 7 ^ (m + 1)] := by
    have := hb.mul_left 2; rw [show 2 * (c + δ) = (2 * c + δ) + δ by ring] at this; exact this
  obtain ⟨e1, he1, h1⟩ := carry_le (Nat.ModEq.refl (2 * c + δ)) hδ
  obtain ⟨e2, he2, h3⟩ := carry_le h2 hδ
  refine ⟨e1 + e2, by omega, ?_⟩
  rw [h3, h1]; push_cast; ring

/-- `q(μ x) = q(μ y) + q(μ (x - y)) + c`. -/
theorem pair_off (m μ x y : ℕ) : ∃ c : ℕ, c < 2 ∧
    (qq m (μ * x) : ZMod 7) = qq m (μ * y) + qq m (μ * E m x y) + c := by
  have h : μ * x ≡ μ * y + μ * E m x y [MOD 7 ^ (m + 1)] := by
    have := (E_modEq m x y).mul_left μ; rwa [mul_add] at this
  obtain ⟨c, hc, h'⟩ := qq_add_nat h
  exact ⟨c, hc, by rw [h', ZMod.natCast_mod]; push_cast; ring⟩

theorem qq_ge {m x a : ℕ} (h : a ≤ qq m x) : a * 7 ^ m ≤ x % 7 ^ (m + 1) :=
  le_trans (Nat.mul_le_mul_right _ h) (qq_bounds m x).1

theorem qq_le {m x b : ℕ} (h : qq m x ≤ b) : x % 7 ^ (m + 1) < (b + 1) * 7 ^ m :=
  lt_of_lt_of_le (qq_bounds m x).2 (Nat.mul_le_mul_right _ (by omega))

theorem range3_arith (M v w2 w3 k2 k3 : ℕ) (hv : v < 7 * M) (l1 : 2 * M ≤ v) (u1 : v < (4 + 1) * M)
    (l2 : 2 * M ≤ w2) (u2 : w2 < (4 + 1) * M) (l3 : 1 * M ≤ w3) (u3 : w3 < (5 + 1) * M)
    (d2 : 7 * M * k2 + w2 = 2 * v) (d3 : 7 * M * k3 + w3 = 3 * v) (k2l : k2 < 2) (k3l : k3 < 3) :
    False := by
  interval_cases k2 <;> interval_cases k3 <;> omega

/-- position of a residue `v`: one of `v, 2v, 3v` is close to `0`. -/
theorem range3 (m v : ℕ) (hv : v < 7 ^ (m + 1)) :
    (qq m v ≤ 1 ∨ 5 ≤ qq m v) ∨ (qq m (2 * v) ≤ 1 ∨ 5 ≤ qq m (2 * v)) ∨
      (qq m (3 * v) = 0 ∨ qq m (3 * v) = 6) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, c1, c2⟩ := hc
  have q3 := qq_lt m (3 * v)
  have l1 := qq_ge (m := m) (x := v) (a := 2) (by omega)
  have u1 := qq_le (m := m) (x := v) (b := 4) (by omega)
  have l2 := qq_ge (m := m) (x := 2 * v) (a := 2) (by omega)
  have u2 := qq_le (m := m) (x := 2 * v) (b := 4) (by omega)
  have l3 := qq_ge (m := m) (x := 3 * v) (a := 1) (by omega)
  have u3 := qq_le (m := m) (x := 3 * v) (b := 5) (by omega)
  have hN : 7 ^ (m + 1) = 7 * 7 ^ m := by rw [pow_succ]; ring
  have m1 : v % 7 ^ (m + 1) = v := Nat.mod_eq_of_lt hv
  have d2 := Nat.div_add_mod (2 * v) (7 ^ (m + 1))
  have d3 := Nat.div_add_mod (3 * v) (7 ^ (m + 1))
  have k2 : (2 * v) / 7 ^ (m + 1) < 2 := (Nat.div_lt_iff_lt_mul (N_pos m)).mpr (by omega)
  have k3 : (3 * v) / 7 ^ (m + 1) < 3 := (Nat.div_lt_iff_lt_mul (N_pos m)).mpr (by omega)
  rw [m1] at l1 u1
  rw [hN] at hv l2 u2 l3 u3 d2 d3 k2 k3
  exact range3_arith (7 ^ m) v _ _ _ _ hv l1 u1 l2 u2 l3 u3 d2 d3 k2 k3

/-! ## the finite `Z/7` facts (checked first in `e6s19/lean19.rs`, mode `z7`) -/

theorem z65w1 : ∀ a g1 g2 p o : ZMod 7, g1.val < 2 → g2.val < 2 →
    (o = 5 ∨ o = 6 ∨ o = 0 ∨ o = 1 ∨ o = 2) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + g1 + K) ∧ ok7 (a + g2 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + o + 4 * K) := by
  decide +kernel

theorem z65w2 : ∀ a g1 g2 p o : ZMod 7, g1.val < 3 → g2.val < 3 →
    (o = 5 ∨ o = 6 ∨ o = 0 ∨ o = 1 ∨ o = 2) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + g1 + K) ∧ ok7 (a + g2 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + o + 4 * K) := by
  decide +kernel

theorem z65w3 : ∀ a g1 g2 p o : ZMod 7, g1.val < 4 → g2.val < 4 → (o = 6 ∨ o = 0 ∨ o = 1) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + g1 + K) ∧ ok7 (a + g2 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + o + 4 * K) := by
  decide +kernel

theorem zt012 : ∀ o : ZMod 7, (o = 5 ∨ o = 6 ∨ o = 0 ∨ o = 1 ∨ o = 2) → ∀ a p : ZMod 7,
    ∃ K, ok7 (a + K) ∧ ok7 (a + 1 + K) ∧ ok7 (a + 2 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + o + 4 * K) := by
  decide +kernel

theorem zt051 : ∀ o : ZMod 7, (o = 6 ∨ o = 0 ∨ o = 1) → ∀ a p : ZMod 7,
    ∃ K, ok7 (a + K) ∧ ok7 (a + 5 + K) ∧ ok7 (a + 1 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + o + 4 * K) := by
  decide +kernel

/-- (ii.1)(b): offsets `(0,1,2)`, `A4 = {p, p+4}`; bad iff `e~(lo, d3) = 2p - a ∈ {3, 4}`. -/
theorem zb65 : ∀ a p : ZMod 7, 2 * p - a ∉ ({3, 4} : Finset (ZMod 7)) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + 1 + K) ∧ ok7 (a + 2 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + 4 + 4 * K) := by
  decide +kernel

/-- exceptional branch after doubling: offsets `(0,2,4)`, `A4 = {p, p+1}`; bad iff `2p - a ∈ {2,4,6}`. -/
theorem ze65 : ∀ a p : ZMod 7, 2 * p - a ∉ ({2, 4, 6} : Finset (ZMod 7)) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + 2 + K) ∧ ok7 (a + 4 + K) ∧ ok7 (p + 4 * K) ∧ ok7 (p + 1 + 4 * K) := by
  decide +kernel

theorem ell_pair3 : ∀ p o : ZMod 7, (o = 5 ∨ o = 6 ∨ o = 0 ∨ o = 1 ∨ o = 2) →
    Z7.ell {p + o, p} ≤ 3 := by
  decide +kernel

theorem ell34 : Z7.ell {3, 4} ≤ 4 := by decide
theorem z7_34 : ∀ z : ZMod 7, z ∈ ({3, 4} : Finset (ZMod 7)) → z - 1 ∈ ({3, 4} : Finset (ZMod 7)) → z = 4 := by
  decide
theorem z7_246 : ¬ (((1 : ℕ) : ZMod 7) ∈ ({2, 4, 6} : Finset (ZMod 7)) ∧
    ((1 : ℕ) : ZMod 7) - 1 ∈ ({2, 4, 6} : Finset (ZMod 7))) := by decide
theorem z7_u3 : ∀ u w : ZMod 7, u * (3 * w) = 1 → u * w = 5 := by decide
theorem z7_pm65 : ∀ u w r : ZMod 7, u * (3 * w) = 1 → (w = 5 * r ∨ w = -(5 * r)) → u * r = 1 ∨ u * r = 6 := by
  decide
theorem z7_sgn65 : ∀ a b c : ZMod 7, a = 3 * b → (b = 5 * c ∨ b = -(5 * c)) → a = c ∨ a = -c := by decide
theorem z7_five_ne : ∀ x : ZMod 7, x ≠ 0 → 5 * x ≠ 0 := by decide

theorem oset_w (q c : ℕ) (hq : q < 7) (hc : c < 2) (h : q ≤ 1 ∨ 5 ≤ q) :
    ((q : ZMod 7) + c = 5 ∨ (q : ZMod 7) + c = 6 ∨ (q : ZMod 7) + c = 0 ∨ (q : ZMod 7) + c = 1 ∨
      (q : ZMod 7) + c = 2) := by
  interval_cases q <;> interval_cases c <;> first | omega | decide

theorem oset_w3 (q c : ℕ) (hc : c < 2) (h : q = 0 ∨ q = 6) :
    ((q : ZMod 7) + c = 6 ∨ (q : ZMod 7) + c = 0 ∨ (q : ZMod 7) + c = 1) := by
  rcases h with rfl | rfl <;> interval_cases c <;> decide

theorem oset_c (c : ℕ) (hc : c < 2) : ((c : ZMod 7) = 6 ∨ (c : ZMod 7) = 0 ∨ (c : ZMod 7) = 1) := by
  interval_cases c <;> decide

/-! ## window + pair (all congruent, (i), (ii.1) with `h < m`) -/

theorem win65 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [c, b, a], ¬ 7 ∣ x ∧ x % 7 = c % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 4 * R c) (hr5 : R d5 = 4 * R c) (μ0 : ℕ)
    (hμ0 : Nat.Coprime μ0 7) (hw : Wb m (μ0 * a) (μ0 * b) (μ0 * c)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [c, b, a, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨hA, hB⟩ := hw
  have ea := E_modEq m (μ0 * a) (μ0 * c)
  have eb := E_modEq m (μ0 * b) (μ0 * c)
  set v := E m (μ0 * d4) (μ0 * d5) with hv
  have ev := E_modEq m (μ0 * d4) (μ0 * d5)
  rcases range3 m v (E_lt m _ _) with h1 | h2 | h3
  · obtain ⟨e1, he1, qa⟩ := carry_le ea hA
    obtain ⟨e2, he2, qb⟩ := carry_le eb hB
    obtain ⟨c', hc', qp⟩ := qq_add_nat ev
    have qp' : (qq m (μ0 * d4) : ZMod 7) = qq m (μ0 * d5) + ((qq m v : ZMod 7) + c') := by
      rw [qp, ZMod.natCast_mod]; push_cast; ring
    obtain ⟨K, k0, k1, k2, k4, k5⟩ := z65w1 (qq m (μ0 * c)) (e2 : ZMod 7) (e1 : ZMod 7)
      (qq m (μ0 * d5)) ((qq m v : ZMod 7) + c') (val_lt_of he2 (by norm_num))
      (val_lt_of he1 (by norm_num)) (oset_w _ _ (qq_lt m v) hc' h1)
    apply finish65 m hm c b a d4 d5 hd h4 h5 hr4 hr5 μ0 hμ0 K
    · intro x hx
      rcases (show x = c ∨ x = b ∨ x = a by simpa using hx) with rfl | rfl | rfl
      · exact k0
      · exact ok7_congr k1 (by rw [qb])
      · exact ok7_congr k2 (by rw [qa])
    · exact ok7_congr k5 (by rw [qp'])
    · exact k4
  · obtain ⟨e1, he1, qa⟩ := carry_two ea hA
    obtain ⟨e2, he2, qb⟩ := carry_two eb hB
    have ev2 : 2 * (μ0 * d4) ≡ 2 * (μ0 * d5) + 2 * v [MOD 7 ^ (m + 1)] := by
      have := ev.mul_left 2; rwa [mul_add] at this
    obtain ⟨c', hc', qp⟩ := qq_add_nat ev2
    have qp' : (qq m (2 * (μ0 * d4)) : ZMod 7) = qq m (2 * (μ0 * d5)) + ((qq m (2 * v) : ZMod 7) + c') := by
      rw [qp, ZMod.natCast_mod]; push_cast; ring
    obtain ⟨K, k0, k1, k2, k4, k5⟩ := z65w2 (qq m (2 * (μ0 * c))) (e2 : ZMod 7) (e1 : ZMod 7)
      (qq m (2 * (μ0 * d5))) ((qq m (2 * v) : ZMod 7) + c') (val_lt_of he2 (by norm_num))
      (val_lt_of he1 (by norm_num)) (oset_w _ _ (qq_lt m _) hc' h2)
    have hμ : Nat.Coprime (2 * μ0) 7 := Nat.Coprime.mul_left (by norm_num) hμ0
    have r : ∀ x, qq m (2 * μ0 * x) = qq m (2 * (μ0 * x)) := fun x => by rw [mul_assoc]
    apply finish65 m hm c b a d4 d5 hd h4 h5 hr4 hr5 (2 * μ0) hμ K
    · intro x hx
      rcases (show x = c ∨ x = b ∨ x = a by simpa using hx) with rfl | rfl | rfl
      · rw [r]; exact k0
      · rw [r]; exact ok7_congr k1 (by rw [qb])
      · rw [r]; exact ok7_congr k2 (by rw [qa])
    · rw [r]; exact ok7_congr k5 (by rw [qp'])
    · rw [r]; exact k4
  · obtain ⟨e1, he1, qa⟩ := carry_three ea hA
    obtain ⟨e2, he2, qb⟩ := carry_three eb hB
    have ev3 : 3 * (μ0 * d4) ≡ 3 * (μ0 * d5) + 3 * v [MOD 7 ^ (m + 1)] := by
      have := ev.mul_left 3; rwa [mul_add] at this
    obtain ⟨c', hc', qp⟩ := qq_add_nat ev3
    have qp' : (qq m (3 * (μ0 * d4)) : ZMod 7) = qq m (3 * (μ0 * d5)) + ((qq m (3 * v) : ZMod 7) + c') := by
      rw [qp, ZMod.natCast_mod]; push_cast; ring
    obtain ⟨K, k0, k1, k2, k4, k5⟩ := z65w3 (qq m (3 * (μ0 * c))) (e2 : ZMod 7) (e1 : ZMod 7)
      (qq m (3 * (μ0 * d5))) ((qq m (3 * v) : ZMod 7) + c') (val_lt_of he2 (by norm_num))
      (val_lt_of he1 (by norm_num)) (oset_w3 _ _ hc' h3)
    have hμ : Nat.Coprime (3 * μ0) 7 := Nat.Coprime.mul_left (by norm_num) hμ0
    have r : ∀ x, qq m (3 * μ0 * x) = qq m (3 * (μ0 * x)) := fun x => by rw [mul_assoc]
    apply finish65 m hm c b a d4 d5 hd h4 h5 hr4 hr5 (3 * μ0) hμ K
    · intro x hx
      rcases (show x = c ∨ x = b ∨ x = a by simpa using hx) with rfl | rfl | rfl
      · rw [r]; exact k0
      · rw [r]; exact ok7_congr k1 (by rw [qb])
      · rw [r]; exact ok7_congr k2 (by rw [qa])
    · rw [r]; exact ok7_congr k5 (by rw [qp'])
    · rw [r]; exact k4

/-! ## Lemma 2 on a pair -/

/-- `x - y` zero or below the top: some `lam ≡ 1 [MOD 7]` gives `q(lam x) - q(lam y) ∈ {0, 1}`. -/
theorem pair_low (m x y : ℕ) (h : E m x y = 0 ∨ (E m x y ≠ 0 ∧ nu 7 (E m x y) < m)) :
    ∃ lam, lam ≡ 1 [MOD 7] ∧ ∃ c : ℕ, c < 2 ∧ (qq m (lam * x) : ZMod 7) = qq m (lam * y) + c := by
  rcases h with h0 | ⟨h0, hlt⟩
  · refine ⟨1, Nat.ModEq.refl 1, 0, by norm_num, ?_⟩
    rw [qq_eq_of_E0 h0 1]; simp
  · obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 (E m x y)) (m := m) (x := E m x y)
      (t := 0) (by norm_num) hlt.le rfl h0 (by norm_num)
    have hmem : 1 + 7 ^ (m - nu 7 (E m x y)) * k ∈ Lam (nu 7 (E m x y)) m 7 :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    refine ⟨_, Lam_modEq_seven hlt hmem, ?_⟩
    obtain ⟨c, hc, hq⟩ := pair_off m (1 + 7 ^ (m - nu 7 (E m x y)) * k) x y
    refine ⟨c, hc, ?_⟩
    have h0' : qq m ((1 + 7 ^ (m - nu 7 (E m x y)) * k) * E m x y) = 0 := hkq
    rw [hq, h0']; push_cast; ring

/-! ## `h = m` -/

theorem qq_top_eq {m x y n : ℕ} (h : x ≡ y + 7 ^ m * n [MOD 7 ^ (m + 1)]) (lam : ℕ) (hl : lam ≡ 1 [MOD 7]) :
    (qq m (lam * x) : ZMod 7) = qq m (lam * y) + n := qq_of_top1 (top_keep hl h)

/-- (ii.1)(b): `up ≡ lo + 4N/7`, offsets `(0,1,2)`. -/
theorem top4_65 (m : ℕ) (hm : 2 ≤ m) (C B A up lo : ℕ) (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7)
    (hup : ¬ 7 ∣ up) (hlo : ¬ 7 ∣ lo) (hrup : R up = 4 * R C) (hrlo : R lo = 4 * R C) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)])
    (hAm : μ * A ≡ μ * C + 7 ^ m * 2 [MOD 7 ^ (m + 1)]) (hul : μ * up ≡ μ * lo + 7 ^ m * 4 [MOD 7 ^ (m + 1)]) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, up, lo], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have hC := (hd C (by simp)).1
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; exact hC (dvd_zero 7)
  have hlo0 : lo ≠ 0 := by intro h; rw [h] at hlo; exact hlo (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hr : rp 7 (μ * C) = 2 * rp 7 (μ * lo) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ hC0, R_mul_unit hμ hlo0, hrlo]
    linear_combination (μ : ZMod 7) * (z7_eight (R C)).symm
  by_cases hex : ediff m (μ * lo) (μ * C) = 7 ^ m * 4
  · -- exceptional: double
    have h2 : Nat.Coprime 2 7 := by norm_num
    have hBm2 : 2 * (μ * B) ≡ 2 * (μ * C) + 7 ^ m * 2 [MOD 7 ^ (m + 1)] :=
      scale_top hBm (by norm_num) (by decide)
    have hAm2 : 2 * (μ * A) ≡ 2 * (μ * C) + 7 ^ m * 4 [MOD 7 ^ (m + 1)] :=
      scale_top hAm (by norm_num) (by decide)
    have hul2 : 2 * (μ * up) ≡ 2 * (μ * lo) + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
      scale_top hul (by norm_num) (by decide)
    have hd2C : ¬ 7 ∣ 2 * (μ * C) := not_dvd_mul h2 (not_dvd_mul hμ hC)
    have hd2lo : ¬ 7 ∣ 2 * (μ * lo) := not_dvd_mul h2 (not_dvd_mul hμ hlo)
    have hr2 : rp 7 (2 * (μ * C)) = 2 * rp 7 (2 * (μ * lo)) % 7 := by
      apply rp_of_R
      rw [R_mul_unit h2 (Nat.mul_ne_zero hμ0 hC0), R_mul_unit h2 (Nat.mul_ne_zero hμ0 hlo0),
        R_mul_unit hμ hC0, R_mul_unit hμ hlo0, hrlo]
      linear_combination (2 * (μ : ZMod 7)) * (z7_eight (R C)).symm
    have hz : ediff m (2 * (μ * lo)) (2 * (μ * C)) ≡ 7 ^ m * 1 [MOD 7 ^ (m + 1)] := by
      apply modEq_of_cast
      rw [(ediff_branch1 m _ _ hr2).1, dsub_cast _ _ _ (N_pos m)]
      have he := congrArg (fun n : ℕ => (n : ZMod (7 ^ (m + 1)))) hex
      simp only at he
      rw [(ediff_branch1 m _ _ hr).1, dsub_cast _ _ _ (N_pos m)] at he
      have hz0 : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 := ZMod.natCast_self _
      push_cast at he hz0 ⊢
      linear_combination 2 * he + hz0
    obtain ⟨lam, hlam, hX⟩ := lemma7_ii_ext m (2 * (μ * lo)) (2 * (μ * C)) 1 {2, 4, 6} hm hd2lo hd2C hr2
      hz z7_246
    have hl := Lam_modEq_seven (by omega : 1 < m) hlam
    have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
    rw [etilde_b1 m lam _ _ hl (by positivity) (by positivity) hr2] at hX
    have hB' := qq_top_eq hBm2 lam hl
    have hA' := qq_top_eq hAm2 lam hl
    have hp' := qq_top_eq hul2 lam hl
    set μ' := lam * (2 * μ) with hμ'
    have r : ∀ x, lam * (2 * (μ * x)) = μ' * x := fun x => by rw [hμ']; ring
    rw [r, r] at hB' hA' hp' hX
    obtain ⟨K, k0, k2, k4, kl, ku⟩ := ze65 (qq m (μ' * C)) (qq m (μ' * lo)) hX
    apply finish65' m (by omega) C B A up lo hd hup hlo hrup hrlo μ'
      (Nat.Coprime.mul_left hlc (Nat.Coprime.mul_left h2 hμ)) 2 4 1 (by rw [hB']; push_cast; ring)
      (by rw [hA']; push_cast; ring) (by rw [hp']; push_cast; ring) ⟨K, k0, k2, k4, kl, ku⟩
  · have hz : ∀ z, z < 7 → ediff m (μ * lo) (μ * C) = 7 ^ m * z →
        ¬ ((z : ZMod 7) ∈ ({3, 4} : Finset (ZMod 7)) ∧ (z : ZMod 7) - 1 ∈ ({3, 4} : Finset (ZMod 7))) := by
      intro z hz7 hze hmem
      have h4 := z7_34 _ hmem.1 hmem.2
      have : z = 4 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h4]; rfl)
      exact hex (by rw [hze, this])
    obtain ⟨lam, hl, hX⟩ := steer m hm (μ * lo) (μ * C) (not_dvd_mul hμ hlo) (not_dvd_mul hμ hC) hr
      {3, 4} ell34 hz
    have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
    rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 hlo0) (Nat.mul_ne_zero hμ0 hC0) hr] at hX
    have hB' := qq_top_eq hBm lam hl
    have hA' := qq_top_eq hAm lam hl
    have hp' := qq_top_eq hul lam hl
    set μ' := lam * μ with hμ'
    have r : ∀ x, lam * (μ * x) = μ' * x := fun x => by rw [hμ']; ring
    rw [r, r] at hB' hA' hp' hX
    obtain ⟨K, k0, k1, k2, kl, ku⟩ := zb65 (qq m (μ' * C)) (qq m (μ' * lo)) hX
    apply finish65' m (by omega) C B A up lo hd hup hlo hrup hrlo μ'
      (Nat.Coprime.mul_left hlc hμ) 1 2 4 (by rw [hB']; push_cast; ring)
      (by rw [hA']; push_cast; ring) (by rw [hp']; push_cast; ring) ⟨K, k0, k1, k2, kl, ku⟩

theorem list5_swap45 {P : ℕ → Prop} {C B A x y : ℕ} (h : ∀ z ∈ [C, B, A, x, y], P z) :
    ∀ z ∈ [C, B, A, y, x], P z := list5_swap h

theorem modEq_top_swap {m x y : ℕ} (h : x ≡ y + 7 ^ m * 3 [MOD 7 ^ (m + 1)]) :
    y ≡ x + 7 ^ m * 4 [MOD 7 ^ (m + 1)] := by
  apply modEq_of_cast
  have h' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hz0 : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 := ZMod.natCast_self _
  push_cast at h' hz0 ⊢
  linear_combination -h' - hz0

/-- pair after exact top offsets for `A1`: zero/low/top `z ∈ {1,2,5,6}` finish directly, top `z ∈ {3,4}`
goes to `top4_65`. -/
theorem top1_65 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C)
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
  have hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
    scale_top hBm0 (by norm_num) (by push_cast; rw [hμu, hRB, hu])
  have hAm : μ * A ≡ μ * C + 7 ^ m * 2 [MOD 7 ^ (m + 1)] :=
    scale_top hAm0 (by norm_num) (by push_cast; rw [hμu, hRA, h2]; linear_combination 2 * hu)
  set v := E m (μ * d4) (μ * d5) with hv
  by_cases hlow : v = 0 ∨ (v ≠ 0 ∧ nu 7 v < m)
  · obtain ⟨lam, hl, c, hc, hp⟩ := pair_low m (μ * d4) (μ * d5) hlow
    have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
    have hB' := qq_top_eq hBm lam hl
    have hA' := qq_top_eq hAm lam hl
    set μ' := lam * μ with hμ'
    have r : ∀ x, lam * (μ * x) = μ' * x := fun x => by rw [hμ']; ring
    rw [r, r] at hB' hA' hp
    apply finish65' m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ' (Nat.Coprime.mul_left hlc hμ) 1 2 c
      (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring) hp
    have ho : (c : ZMod 7) = 5 ∨ (c : ZMod 7) = 6 ∨ (c : ZMod 7) = 0 ∨ (c : ZMod 7) = 1 ∨ (c : ZMod 7) = 2 := by
      rcases oset_c c hc with h | h | h <;> simp [h]
    simpa using zt012 _ ho (qq m (μ' * C)) (qq m (μ' * d5))
  · have hv0 : v ≠ 0 := by intro h; exact hlow (Or.inl h)
    have hnu : nu 7 v = m := by
      have := nu_le_m hv0 (E_lt m _ _); push Not at hlow; have := hlow.2 hv0; omega
    obtain ⟨n, hn7, hnm, hnR⟩ := off_of_top m (μ * d4) (μ * d5) hv0 hnu
    have hn0 : n ≠ 0 := by
      rintro rfl; exact R_ne_zero hv0 (by rw [← hnR]; simp)
    have hdirect : (n : ZMod 7) = 5 ∨ (n : ZMod 7) = 6 ∨ (n : ZMod 7) = 0 ∨ (n : ZMod 7) = 1 ∨
        (n : ZMod 7) = 2 → ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5],
          qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
      intro ho
      have hB' := qq_top_eq hBm 1 (Nat.ModEq.refl 1)
      have hA' := qq_top_eq hAm 1 (Nat.ModEq.refl 1)
      have hp' := qq_top_eq hnm 1 (Nat.ModEq.refl 1)
      simp only [one_mul] at hB' hA' hp'
      apply finish65' m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ 1 2 n
        (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring) hp'
      simpa using zt012 _ ho (qq m (μ * C)) (qq m (μ * d5))
    by_cases h34 : n = 3 ∨ n = 4
    · rcases h34 with rfl | rfl
      · obtain ⟨lam, hc, hl⟩ := top4_65 m hm C B A d5 d4 hd h5 h4 hr5 hr4 μ hμ hBm hAm
          (modEq_top_swap hnm)
        exact ⟨lam, hc, list5_swap hl⟩
      · exact top4_65 m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hBm hAm hnm
    · apply hdirect
      push Not at h34
      interval_cases n <;> simp_all <;> decide

/-- (ii.2), `h = m`: rescale by `(3 r(e23))⁻¹`, offsets `(0,5,1)`; `e45 = ±N/7` by the choice of `t`. -/
theorem top2_65 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C) (t : ZMod 7)
    (htE : E m d4 d5 ≠ 0 → t = 5 * R (E m d4 d5))
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = m) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = m)
    (h3 : R (E m A C) = 3 * R (E m B C)) (ht : R (E m B C) = t ∨ R (E m B C) = -t) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨nB, -, hBm0, hRB⟩ := off_of_top m B C hB.1 hB.2
  obtain ⟨nA, -, hAm0, hRA⟩ := off_of_top m A C hA.1 hA.2
  set w := R (E m B C) with hw
  have hw0 : w ≠ 0 := R_ne_zero hB.1
  have h3w : 3 * w ≠ 0 := by rw [← h3]; exact R_ne_zero hA.1
  obtain ⟨u, hu⟩ := z7_solve (3 * w) 1 h3w
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  set μ := u.val
  have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
  have hμ : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hBm : μ * B ≡ μ * C + 7 ^ m * 5 [MOD 7 ^ (m + 1)] :=
    scale_top hBm0 (by norm_num) (by push_cast; rw [hμu, hRB]; exact z7_u3 u w hu)
  have hAm : μ * A ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
    scale_top hAm0 (by norm_num) (by push_cast; rw [hμu, hRA, h3, hu])
  set v := E m (μ * d4) (μ * d5) with hv
  by_cases hlow : v = 0 ∨ (v ≠ 0 ∧ nu 7 v < m)
  · obtain ⟨lam, hl, c, hc, hp⟩ := pair_low m (μ * d4) (μ * d5) hlow
    have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
    have hB' := qq_top_eq hBm lam hl
    have hA' := qq_top_eq hAm lam hl
    set μ' := lam * μ with hμ'
    have r : ∀ x, lam * (μ * x) = μ' * x := fun x => by rw [hμ']; ring
    rw [r, r] at hB' hA' hp
    apply finish65' m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ' (Nat.Coprime.mul_left hlc hμ) 5 1 c
      (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring) hp
    simpa using zt051 _ (oset_c c hc) (qq m (μ' * C)) (qq m (μ' * d5))
  · have hv0 : v ≠ 0 := by intro h; exact hlow (Or.inl h)
    have hnu : nu 7 v = m := by
      have := nu_le_m hv0 (E_lt m _ _); push Not at hlow; have := hlow.2 hv0; omega
    obtain ⟨n, hn7, hnm, hnR⟩ := off_of_top m (μ * d4) (μ * d5) hv0 hnu
    have hE45 : E m d4 d5 ≠ 0 := by
      intro h0
      apply hv0
      apply eq_of_cast_N (E_lt m _ _) (N_pos m)
      rw [E_cast]
      have := E_cast m d4 d5; rw [h0] at this; push_cast at this ⊢
      linear_combination -(μ : ZMod (7 ^ (m + 1))) * this
    have hsc := (E_scale m μ d4 d5 hμ hE45).2.2
    have hpm := z7_pm65 u w (R (E m d4 d5)) hu (by rw [← htE hE45]; exact ht)
    have hn : (n : ZMod 7) = 1 ∨ (n : ZMod 7) = 6 := by
      rw [hnR, hsc, hμu]; exact hpm
    have hB' := qq_top_eq hBm 1 (Nat.ModEq.refl 1)
    have hA' := qq_top_eq hAm 1 (Nat.ModEq.refl 1)
    have hp' := qq_top_eq hnm 1 (Nat.ModEq.refl 1)
    simp only [one_mul] at hB' hA' hp'
    apply finish65' m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ 5 1 n
      (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring) hp'
    have ho : (n : ZMod 7) = 6 ∨ (n : ZMod 7) = 0 ∨ (n : ZMod 7) = 1 := by
      rcases hn with h | h <;> simp [h]
    simpa using zt051 _ ho (qq m (μ * C)) (qq m (μ * d5))

/-! ## (ii.2), `h < m` -/

/-- **Lemma 9 (ii), `j = 3`, difference form.** -/
theorem l9diff (m h x y : ℕ) (hhm : h < m) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = h)
    (hy : nu 7 y = h) (hr : rp 7 y = 3 * rp 7 x % 7) :
    ∃ lam ∈ Lam h m 7, (qq m (lam * y) = 0 ∨ qq m (lam * y) = 5 ∨ qq m (lam * y) = 6) ∧
      (qq m (lam * x) ≤ 1 ∨ 5 ≤ qq m (lam * x)) ∧
      ((qq m (lam * y) + 7 - qq m (lam * x)) % 7 ≤ 1 ∨ (qq m (lam * y) + 7 - qq m (lam * x)) % 7 = 6) := by
  set s := (3 * qq m y + 5 * qq m x) % 7
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := y) (t := T3 s)
    (by norm_num) hhm.le hy hy0 (T3_lt s)
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  refine ⟨_, hmem, ?_⟩
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
  have hqx' : qq m (lam * x) = (qq m x + (k * rp 7 x) % 7) % 7 := by rw [hqx, Nat.add_mod_mod]
  have hqy' : qq m (lam * y) = (qq m y + 3 * ((k * rp 7 x) % 7)) % 7 := by
    rw [hqy, ← Nat.add_mod_mod, hK, Nat.add_mod_mod]
  have hTy : qq m (lam * y) = T3 s := by rw [hqy', hT]
  refine ⟨by rw [hTy]; exact T3_mem s, ?_⟩
  rw [hqx', hqy']
  exact htab

theorem arith65 (q1 q2 q3 X Y c1 c2 : ℕ) (h1 : q1 < 7) (h2 : q2 < 7) (h3 : q3 < 7) (hX7 : X < 7)
    (hc1 : c1 < 2) (hc2 : c2 < 2) (hY : Y = 0 ∨ Y = 5 ∨ Y = 6) (hX : X ≤ 1 ∨ 5 ≤ X)
    (hXY : (Y + 7 - X) % 7 ≤ 1 ∨ (Y + 7 - X) % 7 = 6)
    (e1 : q1 = (q3 + X + c1) % 7) (e2 : q2 = (q3 + Y + c2) % 7) :
    ((q1 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q1 + 7 - q3) % 7) ∧
    ((q2 + 7 - q3) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q3) % 7) ∧
    ((q2 + 7 - q1) % 7 ≤ 2 ∨ 5 ≤ (q2 + 7 - q1) % 7) := by
  omega

/-- Remark 8 (ii) with carries: the difference form gives `l ≤ 3`. -/
theorem diff3 (m b1 b2 b3 X Y : ℕ) (h1 : b1 ≡ b3 + X [MOD 7 ^ (m + 1)])
    (h2 : b2 ≡ b3 + Y [MOD 7 ^ (m + 1)]) (hY : qq m Y = 0 ∨ qq m Y = 5 ∨ qq m Y = 6)
    (hX : qq m X ≤ 1 ∨ 5 ≤ qq m X)
    (hXY : (qq m Y + 7 - qq m X) % 7 ≤ 1 ∨ (qq m Y + 7 - qq m X) % 7 = 6) : ellq m b1 b2 b3 ≤ 3 := by
  obtain ⟨c1, hc1, e1⟩ := qq_add_nat h1
  obtain ⟨c2, hc2, e2⟩ := qq_add_nat h2
  have a1 := qq_lt m b1; have a2 := qq_lt m b2; have a3 := qq_lt m b3
  obtain ⟨x1, x2, x3⟩ := arith65 _ _ _ _ _ _ _ a1 a2 a3 (qq_lt m X) hc1 hc2 hY hX hXY e1 e2
  unfold ellq
  exact ell3_core3 _ _ _ a1 a2 a3 x1 x2 x3

/-- finish from `l(A1) ≤ 3` and `q(d4) - q(d5) ∈ {5,6,0,1,2}` (eq. (14)). -/
theorem finish65_ell (m : ℕ) (hm : 1 ≤ m) (C B A d4 d5 : ℕ) (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (hell : ellq m (μ * B) (μ * A) (μ * C) ≤ 3) (o : ZMod 7)
    (ho : o = 5 ∨ o = 6 ∨ o = 0 ∨ o = 1 ∨ o = 2)
    (hp : (qq m (μ * d4) : ZMod 7) = qq m (μ * d5) + o) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have e4 : Z7.ell {((qq m (μ * d4) : ℕ) : ZMod 7), ((qq m (μ * d5) : ℕ) : ZMod 7)} ≤ 3 := by
    rw [hp]; exact ell_pair3 _ _ ho
  obtain ⟨k, hk1, -, hk4⟩ := Z7.eq14 {((qq m (μ * B) : ℕ) : ZMod 7), ((qq m (μ * A) : ℕ) : ZMod 7),
    ((qq m (μ * C) : ℕ) : ZMod 7)} {((qq m (μ * d4) : ℕ) : ZMod 7), ((qq m (μ * d5) : ℕ) : ZMod 7)}
    Finset.card_le_three Finset.card_le_two (Or.inl ⟨hell, e4⟩)
  apply finish65 m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ k
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact hk1 _ (by simp)
    · exact hk1 _ (by simp)
    · exact hk1 _ (by simp)
  · exact hk4 _ (by simp)
  · exact hk4 _ (by simp)

theorem dvd_dsub_one {m h x y : ℕ} (hhm : h ≤ m) (hx : nu 7 x = h) (hy : nu 7 y = h)
    (hr : rp 7 x = rp 7 y) : 7 ^ (h + 1) ∣ dsub (7 ^ (m + 1)) x y := by
  set u := x / 7 ^ h
  set w := y / 7 ^ h
  have hxu : x = 7 ^ h * u := (Nat.mul_div_cancel' (hx ▸ pow_nu_dvd 7 x)).symm
  have hyw : y = 7 ^ h * w := (Nat.mul_div_cancel' (hy ▸ pow_nu_dvd 7 y)).symm
  have hru : rp 7 x = u % 7 := by unfold rp; rw [hx]
  have hrw : rp 7 y = w % 7 := by unfold rp; rw [hy]
  have h2 : u ≡ w [MOD 7] := by unfold Nat.ModEq; omega
  have h3 : x ≡ y [MOD 7 ^ (h + 1)] := by
    have := h2.mul_left' (7 ^ h)
    rw [pow_succ, hxu, hyw]; exact this
  have h4 : x ≡ y + dsub (7 ^ (m + 1)) x y [MOD 7 ^ (h + 1)] :=
    Nat.ModEq.of_dvd (pow_dvd_pow 7 (by omega)) (modEq_add_dsub _ _ _ (N_pos m))
  have h5 : y + dsub (7 ^ (m + 1)) x y ≡ y + 0 [MOD 7 ^ (h + 1)] := by
    rw [add_zero]; exact h4.symm.trans h3
  exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' y h5)

theorem qq_topval (m : ℕ) {a : ℕ} (h : a ≡ 7 ^ m [MOD 7 ^ (m + 1)]) : qq m a = 1 := by
  have := qq_top_nat (m := m) (a := a) (b := 0) (by simpa using h)
  rw [this]; simp [qq, qarc]

/-- (ii.2), `h < m`, core, with the orientation `r(e13) = r(e45)` when `nu(e45) = h`. -/
theorem low2_core (m : ℕ) (hm : 2 ≤ m) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C)) (hv0 : E m d4 d5 ≠ 0) (hle : h ≤ nu 7 (E m d4 d5))
    (hRv : nu 7 (E m d4 d5) = h → R (E m A C) = R (E m d4 d5)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set v := E m d4 d5 with hvdef
  set x := E m B C with hxdef
  set y := E m A C with hydef
  have hN := N_pos m
  -- the element `g` handled by Lemma 2, divisible by `7^(h+1)`, and how `v` is recovered
  obtain ⟨g, hgdvd, hglt, hgv⟩ : ∃ g, 7 ^ (h + 1) ∣ g ∧ g < 7 ^ (m + 1) ∧
      ((nu 7 v = h ∧ v ≡ y + g [MOD 7 ^ (m + 1)]) ∨ g = v) := by
    by_cases hj : nu 7 v = h
    · refine ⟨E m v y, ?_, E_lt m _ _, Or.inl ⟨hj, E_modEq m v y⟩⟩
      apply dvd_dsub_one (le_of_lt hhm) hj hA.2
      apply nat_cast_zmod7_eq_of_lt (rp_lt _) (rp_lt _)
      exact (hRv hj).symm
    · refine ⟨v, ?_, E_lt m _ _, Or.inr rfl⟩
      have : h + 1 ≤ nu 7 v := by omega
      exact (pow_dvd_pow 7 this).trans (pow_nu_dvd 7 v)
  obtain ⟨lam1, -, hc1, hne1, -, hstep⟩ := step_top_or_zero m (h + 1) g (by omega) hglt hgdvd
  -- Lemma 9 (ii), `j = 3`, on the scaled triple
  obtain ⟨hx1, hnx1, hRx1⟩ := E_scale m lam1 B C hc1 hB.1
  obtain ⟨hy1, hny1, hRy1⟩ := E_scale m lam1 A C hc1 hA.1
  have hr1 : rp 7 (E m (lam1 * A) (lam1 * C)) = 3 * rp 7 (E m (lam1 * B) (lam1 * C)) % 7 := by
    apply rp_of_R3; rw [hRy1, hRx1, h3]; ring
  obtain ⟨lam2, hlam2, qy, qx, qxy⟩ := l9diff m h _ _ hhm hx1 hy1 (hnx1.trans hB.2) (hny1.trans hA.2) hr1
  have hl2 := Lam_modEq_one hlam2
  have hl27 := Lam_modEq_seven hhm hlam2
  have hc2 : Nat.Coprime lam2 7 := (coprime_of_modEq_one (by norm_num) hl27).1
  set μ := lam2 * lam1 with hμdef
  have hμ : Nat.Coprime μ 7 := Nat.Coprime.mul_left hc2 hc1
  -- `l(A1) ≤ 3`
  have hell : ellq m (μ * B) (μ * A) (μ * C) ≤ 3 := by
    apply diff3 m _ _ _ (lam2 * E m (lam1 * B) (lam1 * C)) (lam2 * E m (lam1 * A) (lam1 * C)) _ _ qy qx qxy
    · have := (E_modEq m (lam1 * B) (lam1 * C)).mul_left lam2
      rw [mul_add] at this; rw [hμdef, mul_assoc, mul_assoc]; exact this
    · have := (E_modEq m (lam1 * A) (lam1 * C)).mul_left lam2
      rw [mul_add] at this; rw [hμdef, mul_assoc, mul_assoc]; exact this
  -- `q(μ v) ∈ {5,6,0,1}`
  have hstep' := hstep lam2 (by simpa [show m + 1 - (h + 1) = m - h by omega] using hl2)
  rw [← mul_assoc] at hstep'
  have hqv : qq m (μ * v) ≤ 1 ∨ 5 ≤ qq m (μ * v) := by
    rcases hgv with ⟨-, hvg⟩ | rfl
    · -- `μ v ≡ lam2 * y1 + μ g`
      have hyy : μ * y ≡ lam2 * E m (lam1 * A) (lam1 * C) [MOD 7 ^ (m + 1)] := by
        rw [E_eq_mod, hμdef, mul_assoc]
        exact ((Nat.mod_modEq _ _).mul_left lam2).symm
      have hvg' : μ * v ≡ lam2 * E m (lam1 * A) (lam1 * C) + μ * g [MOD 7 ^ (m + 1)] := by
        have := hvg.mul_left μ; rw [mul_add] at this; exact this.trans (Nat.ModEq.add_right _ hyy)
      have qyl := qq_lt m (lam2 * E m (lam1 * A) (lam1 * C))
      rcases hstep' with hz | htop
      · obtain ⟨c, hc, hq⟩ := qq_add_nat hvg'
        rw [hz] at hq
        omega
      · have hvt : μ * v ≡ lam2 * E m (lam1 * A) (lam1 * C) + 7 ^ m [MOD 7 ^ (m + 1)] :=
          hvg'.trans (Nat.ModEq.add_left _ htop)
        have hq := qq_top_nat hvt
        omega
    · rcases hstep' with hz | htop
      · left; rw [hz]; norm_num
      · left; rw [qq_topval m htop]
  obtain ⟨c, hc, hp⟩ := pair_off m μ d4 d5
  apply finish65_ell m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hell _
    (oset_w _ _ (qq_lt m _) hc hqv) (by rw [hp]; ring)

/-- (ii.2), `h < m`, `nu(e45) < h`: Lemma 9 first, then Lemma 2 below `h` (keeps the differences). -/
theorem low2_below (m : ℕ) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C))
    (hv : E m d4 d5 = 0 ∨ (E m d4 d5 ≠ 0 ∧ nu 7 (E m d4 d5) < h)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨lam2, hlam2, qy, qx, qxy⟩ := l9diff m h _ _ hhm hB.1 hA.1 hB.2 hA.2 (rp_of_R3 h3)
  have hl27 := Lam_modEq_seven hhm hlam2
  have hc2 : Nat.Coprime lam2 7 := (coprime_of_modEq_one (by norm_num) hl27).1
  have hne2 : lam2 ≠ 0 := (coprime_of_modEq_one (by norm_num) hl27).2
  -- a further `lam' ≡ 1 [MOD 7^(m+1-h)]` with `q(lam' lam2 v) = 0` (or `v = 0`)
  obtain ⟨lam', hl', hc', hz⟩ : ∃ lam', lam' ≡ 1 [MOD 7 ^ (m + 1 - h)] ∧ Nat.Coprime lam' 7 ∧
      qq m (lam' * (lam2 * E m d4 d5)) = 0 := by
    rcases hv with h0 | ⟨h0, hlt⟩
    · refine ⟨1, Nat.ModEq.refl 1, by norm_num, ?_⟩
      rw [h0]; simp [qq, qarc]
    · have hnu : nu 7 (lam2 * E m d4 d5) = nu 7 (E m d4 d5) := nu_mul_coprime 7 lam2 _ hc2 hne2 h0
      obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 (E m d4 d5)) (m := m)
        (x := lam2 * E m d4 d5) (t := 0) (by norm_num) (by omega) hnu (Nat.mul_ne_zero hne2 h0)
        (by norm_num)
      have hmem : 1 + 7 ^ (m - nu 7 (E m d4 d5)) * k ∈ Lam (nu 7 (E m d4 d5)) m 7 :=
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      refine ⟨_, modEq_one_mono (Lam_modEq_one hmem) (by omega),
        (coprime_of_modEq_one (by norm_num) (Lam_modEq_seven (by omega) hmem)).1, hkq⟩
  set μ := lam' * lam2 with hμdef
  have hμ : Nat.Coprime μ 7 := Nat.Coprime.mul_left hc' hc2
  have fix : ∀ e, 7 ^ h ∣ e → lam' * e ≡ e [MOD 7 ^ (m + 1)] := fun e he =>
    mul_modEq_self_of_dvd (by omega) hl' he
  have hdx : ∀ z, E m z C ≠ 0 → nu 7 (E m z C) = h → 7 ^ h ∣ lam2 * E m z C := fun z hz hn =>
    Dvd.dvd.mul_left (hn ▸ pow_nu_dvd 7 _) _
  have hell : ellq m (μ * B) (μ * A) (μ * C) ≤ 3 := by
    apply diff3 m _ _ _ (lam2 * E m B C) (lam2 * E m A C) _ _ qy qx qxy
    · have := (E_modEq m B C).mul_left μ
      rw [mul_add] at this
      refine this.trans (Nat.ModEq.add_left _ ?_)
      rw [hμdef, mul_assoc]; exact fix _ (hdx B hB.1 hB.2)
    · have := (E_modEq m A C).mul_left μ
      rw [mul_add] at this
      refine this.trans (Nat.ModEq.add_left _ ?_)
      rw [hμdef, mul_assoc]; exact fix _ (hdx A hA.1 hA.2)
  obtain ⟨c, hc, hp⟩ := pair_off m μ d4 d5
  have hq0 : qq m (μ * E m d4 d5) = 0 := by rw [hμdef, mul_assoc]; exact hz
  apply finish65_ell m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ hell _
    (oset_w 0 c (by norm_num) hc (Or.inl (by norm_num))) (by rw [hp, hq0]; push_cast; ring)

/-- (ii.2), `h < m`. -/
theorem low2_65 (m : ℕ) (hm : 2 ≤ m) (h : ℕ) (hhm : h < m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R C) (hr5 : R d5 = 4 * R C) (t : ZMod 7)
    (htE : E m d4 d5 ≠ 0 → t = 5 * R (E m d4 d5))
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = h) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = h)
    (h3 : R (E m A C) = 3 * R (E m B C)) (ht : R (E m B C) = t ∨ R (E m B C) = -t) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  by_cases hbelow : E m d4 d5 = 0 ∨ (E m d4 d5 ≠ 0 ∧ nu 7 (E m d4 d5) < h)
  · exact low2_below m h hhm A B C d4 d5 hd h4 h5 hr4 hr5 hB hA h3 hbelow
  have hv0 : E m d4 d5 ≠ 0 := fun h0 => hbelow (Or.inl h0)
  have hle : h ≤ nu 7 (E m d4 d5) := by
    by_contra hc; push Not at hc; exact hbelow (Or.inr ⟨hv0, hc⟩)
  have hsg := z7_sgn65 _ _ _ h3 (by rw [← htE hv0]; exact ht)
  rcases hsg with hp | hn
  · exact low2_core m hm h hhm A B C d4 d5 hd h4 h5 hr4 hr5 hB hA h3 hv0 hle (fun _ => hp)
  · obtain ⟨hne', hnu', hR'⟩ := swap_rule m d4 d5 hv0
    obtain ⟨lam, hc, hl⟩ := low2_core m hm h hhm A B C d5 d4 hd h5 h4 hr5 hr4 hB hA h3 hne'
      (by rw [hnu']; exact hle) (fun _ => by rw [hR', hn])
    exact ⟨lam, hc, list5_swap hl⟩

/-! ## assembling 6.5 -/

theorem cover3 : ∀ (σ : Equiv.Perm (Fin 3)) (i : Fin 3), i = σ 0 ∨ i = σ 1 ∨ i = σ 2 := by decide

theorem concl65 (m lam : ℕ) {d : Fin 3 → ℕ} {d4 d5 : ℕ} (σ : Equiv.Perm (Fin 3)) (a b c : ℕ)
    (hcov : d (σ 0) ∈ [a, b, c] ∧ d (σ 1) ∈ [a, b, c] ∧ d (σ 2) ∈ [a, b, c])
    (hL : ∀ x ∈ [a, b, c, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6) :
    (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      (qq m (lam * d4) ≠ 0 ∧ qq m (lam * d4) ≠ 6) ∧ (qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6) := by
  have sub : ∀ x, x ∈ [a, b, c] → x ∈ [a, b, c, d4, d5] := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢; tauto
  refine ⟨fun i => ?_, hL _ (by simp), hL _ (by simp)⟩
  rcases cover3 σ i with e | e | e <;> rw [e]
  · exact hL _ (sub _ hcov.1)
  · exact hL _ (sub _ hcov.2.1)
  · exact hL _ (sub _ hcov.2.2)

/-- **Section 6.5** (`|A1| = 3`, `|A4| = 2`, `m ≥ 2`). -/
theorem sec65 (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R (d 0)) (hr5 : R d5 = 4 * R (d 0)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      (qq m (lam * d4) ≠ 0 ∧ qq m (lam * d4) ≠ 6) ∧ (qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6) := by
  have hm1 : 1 ≤ m := by omega
  have Rd : ∀ i, R (d i) = R (d 0) := fun i => by
    rw [R_of_not_dvd (hd i), R_of_not_dvd (hd 0), hcl i 0]
  have cls : ∀ a b c : Fin 3, ∀ x ∈ [d a, d b, d c], ¬ 7 ∣ x ∧ x % 7 = d a % 7 := by
    intro a b c x hx
    rcases (show x = d a ∨ x = d b ∨ x = d c by simpa using hx) with rfl | rfl | rfl <;>
      exact ⟨hd _, hcl _ _⟩
  have r4 : ∀ i, R d4 = 4 * R (d i) := fun i => by rw [Rd]; exact hr4
  have r5 : ∀ i, R d5 = 4 * R (d i) := fun i => by rw [Rd]; exact hr5
  set t : ZMod 7 := if E m d4 d5 = 0 then 1 else 5 * R (E m d4 d5) with htdef
  have ht0 : t ≠ 0 := by
    rw [htdef]; split_ifs with h
    · decide
    · exact z7_five_ne _ (R_ne_zero h)
  have htE : E m d4 d5 ≠ 0 → t = 5 * R (E m d4 d5) := by
    intro h0; rw [htdef, if_neg h0]
  rcases lemma11 m d hcl t ht0 with hz | ⟨σ, hi | ⟨h, hall, h2 | ⟨h3, hpm⟩⟩⟩
  · -- all congruent: a window with `E = 0`
    have hw : Wb m (1 * d 0) (1 * d 1) (1 * d 2) := by
      simp only [one_mul]
      exact ⟨by rw [hz 0 2]; exact Nat.zero_le _, by rw [hz 1 2]; exact Nat.zero_le _⟩
    obtain ⟨lam, hc, hl⟩ := win65 m hm1 (d 0) (d 1) (d 2) d4 d5 (cls 2 1 0) h4 h5 (r4 2) (r5 2) 1
      (by norm_num) hw
    exact ⟨lam, hc, concl65 m lam (Equiv.refl _) _ _ _ (by simp) hl⟩
  · obtain ⟨lam, hc, hw⟩ := win9_i m (d (σ 0)) (d (σ 1)) (d (σ 2)) hi
    obtain ⟨lam', hc', hl⟩ := win65 m hm1 (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
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
      · obtain ⟨lam', hc', hl⟩ := win65 m hm1 (d (σ 1)) (d (σ 0)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
      · obtain ⟨lam', hc', hl⟩ := win65 m hm1 (d (σ 2)) (d (σ 0)) (d (σ 1)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
      · obtain ⟨lam', hc', hl⟩ := win65 m hm1 (d (σ 1)) (d (σ 2)) (d (σ 0)) d4 d5 (cls _ _ _) h4 h5
          (r4 _) (r5 _) lam hc hw
        exact ⟨lam', hc', concl65 m lam' σ _ _ _ (by simp) hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := top1_65 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) (hall _ _ n12) (hall _ _ n02) h2
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam, hc, hl⟩ := low2_65 m hm h hlt (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) t htE (hall _ _ n12) (hall _ _ n02) h3 hpm
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩
    · have heq' := heq.symm
      subst heq'
      obtain ⟨lam, hc, hl⟩ := top2_65 m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) d4 d5 (cls _ _ _) h4 h5
        (r4 _) (r5 _) t htE (hall _ _ n12) (hall _ _ n02) h3 hpm
      exact ⟨lam, hc, concl65 m lam σ _ _ _ (by simp) hl⟩

/-- **Section 6.5, real form** with one top speed. -/
theorem sec65_witness (m : ℕ) (hm : 2 ≤ m) (d : Fin 3 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d4 d5 : ℕ) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 4 * R (d 0)) (hr5 : R d5 = 4 * R (d 0)) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d4) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d5) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hc, hlam, hl4, hl5⟩ := sec65 m hm d hd hcl d4 d5 h4 h5 hr4 hr5
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
