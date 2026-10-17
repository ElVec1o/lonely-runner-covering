import LRSpectrumFull.BarajasSerraSec6_1

/-!
# E6 session 18: Barajas-Serra Section 6.2 (`|A1| = 4`), case (a), `m ≥ 2`

`A1 = {d0, ..., d3}` (level 0, one class), `d5` of class `2 r(A1)` or `4 r(A1)` (`A2` or `A4`).
Conclusion: a multiplier prime to 7 keeping all five off `q ∈ {0, 6}` (`sec62`), real form with a
top speed (`sec62_witness`).

Route (paper 6.2 with corrections):
* `nu(E) ≠ {m}`: as in 6.1, a triple of `A1` in a window of width `N/7`; then multiplier `1` or `2`
  and a `Lambda_0` shift (`z7_sec62a`: the paper's "`q(d4) = 3` then `q(2 A1) ⊂ {0,1,5,6}`" plus
  Lemma 5 with one extra element, as one finite check).
* `nu(E) = {m}`, Lemma 10 (ii.1): rescale to offsets `{0,1,2,3}`, then `Lambda_0` (`z7_sec62b1`).
* Lemma 10 (ii.2): rescale by `u` with `u r(e21) = 6`: offsets `(0, 6, 5, 3)` for `(d1,d2,d3,d4)`,
  the window `{3,...,0}` starts at `d4`. Lemma 7 on `(d4, d5)` (`A2`, avoid `{2,3}`) or `(d5, d4)`
  (`A4`, avoid `{4,6}`), then Lemma 6 (i) (`z7_sec62b2`, `z7_sec62b4`).
  Exception `A2`, `e(d4,d5) ≡ 3 N/7`: multiply by 2; offsets `(0,5,3,6)`, the window starts at `d3`,
  and `e(2d3, 2d5) ≡ 0`, so Lemma 7 (ii) (extended to `z = 0`) applies to `(2d3, 2d5)`.
Errata (Rule 0, harmless): the paper's normalisation "`q({e13, e24, e34}) ⊂ {1,2,4}`" is impossible
under (ii.2) (`-2w, -3w` cannot both lie in `{1,2,4}`); the used form is `e21 ≡ 6N/7`. In the
exception the relevant pair after doubling is `(2d3, 2d5)` (paper: `(2d4, 2d5)`), with `e ≡ 0`.
Falsified first: `e6s18/lean18.rs` (`sub`): 6.2 conclusion, m = 2, all 4-multisets of class 1 with
`d5` of class 2 or 4: 26531050 configurations, 0 failures (negative control `Lambda_0` only fails).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- `v ∉ {0, 6}`. -/
def ok7 (v : ZMod 7) : Prop := v ≠ 0 ∧ v ≠ 6

instance (v : ZMod 7) : Decidable (ok7 v) := by unfold ok7; infer_instance

/-- general `Lambda_0` finish: a list of (speed, class multiplier) pairs. -/
theorem finish_list (m : ℕ) (hm : 1 ≤ m) (μ : ℕ) (hμ : Nat.Coprime μ 7) (ρ : ZMod 7) (hρ : ρ ≠ 0)
    (S : List (ℕ × ZMod 7)) (hS : ∀ p ∈ S, ¬ 7 ∣ p.1 ∧ R (μ * p.1) = p.2 * ρ) (K : ZMod 7)
    (hK : ∀ p ∈ S, ok7 ((qq m (μ * p.1) : ZMod 7) + p.2 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ p ∈ S, qq m (lam * p.1) ≠ 0 ∧ qq m (lam * p.1) ≠ 6 := by
  obtain ⟨k, hk, hshift⟩ := shift_class m hm ρ K hρ
  refine ⟨(1 + 7 ^ m * k) * μ, Nat.Coprime.mul_left (Lam0_coprime m k hm) hμ, ?_⟩
  intro p hp
  obtain ⟨h7, hR⟩ := hS p hp
  have hq := hshift (μ * p.1) (not_dvd_mul hμ h7) p.2 hR
  rw [show (1 + 7 ^ m * k) * μ * p.1 = (1 + 7 ^ m * k) * (μ * p.1) by ring]
  obtain ⟨a, b⟩ := hK p hp
  rw [← hq] at a b
  exact nat_avoid (qq_lt m _) a b

/-- the class data of 6.2 after a multiplier `μ`. -/
theorem class62 (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i) (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ)
    (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hr5 : R d5 = j5 * R (d 0)) (μ : ℕ) (hμ : Nat.Coprime μ 7) :
    R (μ * d 0) ≠ 0 ∧ (∀ i, R (μ * d i) = 1 * R (μ * d 0)) ∧ R (μ * d5) = j5 * R (μ * d 0) := by
  have h0 : ∀ j, d j ≠ 0 := fun j h => hd j (h ▸ dvd_zero 7)
  have h50 : d5 ≠ 0 := fun h => hd5 (h ▸ dvd_zero 7)
  refine ⟨R_ne_zero (Nat.mul_ne_zero (fun h => by rw [h] at hμ; norm_num at hμ) (h0 0)), ?_, ?_⟩
  · intro i
    rw [one_mul, R_mul_unit hμ (h0 i), R_mul_unit hμ (h0 0), R_of_not_dvd (hd i), R_of_not_dvd (hd 0),
      hcl i 0]
  · rw [R_mul_unit hμ h50, R_mul_unit hμ (h0 0), hr5]; ring

/-- the 6.2 finish, from a shift `K` that works after the multiplier `μ`. -/
theorem finish62 (m : ℕ) (hm : 1 ≤ m) (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7)
    (hr5 : R d5 = j5 * R (d 0)) (μ : ℕ) (hμ : Nat.Coprime μ 7) (K : ZMod 7)
    (hK : ∀ i, ok7 ((qq m (μ * d i) : ZMod 7) + K)) (hK5 : ok7 ((qq m (μ * d5) : ZMod 7) + j5 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  obtain ⟨hρ, hA, hB⟩ := class62 d hd hcl d5 hd5 j5 hr5 μ hμ
  obtain ⟨lam, hc, hall⟩ := finish_list m hm μ hμ _ hρ ((d5, j5) :: (List.ofFn d).map (fun x => (x, 1)))
    (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hd5, hB⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact ⟨hd i, hA i⟩) K
    (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hK5
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        simpa using hK i)
  refine ⟨lam, hc, fun i => hall (d i, 1) (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨d i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)), hall (d5, j5) (List.mem_cons_self)⟩

/-! ## `nu(E) ≠ {m}` -/

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem z7_sec62a : ∀ e1 e2 : ZMod 7, e1.val < 2 → e2.val < 2 → ∀ v4 v5 j : ZMod 7, (j = 2 ∨ j = 4) →
    (∃ K, ok7 K ∧ ok7 (e1 + K) ∧ ok7 (e2 + K) ∧ ok7 (v4 + K) ∧ ok7 (v5 + j * K)) ∨
    (∀ c0 : ZMod 7, c0.val < 2 → ∀ g1 : ZMod 7, g1.val < 2 → ∀ g2 : ZMod 7, g2.val < 2 →
      ∀ g4 : ZMod 7, g4.val < 2 → ∀ g5 : ZMod 7, g5.val < 2 →
      ∃ K, ok7 (c0 + K) ∧ ok7 (2 * e1 + g1 + K) ∧ ok7 (2 * e2 + g2 + K) ∧ ok7 (2 * v4 + g4 + K) ∧
        ok7 (2 * v5 + g5 + j * K)) := by
  decide

theorem fin4_rest : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
    ∃ a : Fin 4, ∀ x, x = l ∨ x = i ∨ x = j ∨ x = a := by
  decide

theorem ok7_congr {a b : ZMod 7} (h : ok7 a) (e : b = a) : ok7 b := e ▸ h

/-- window of a triple of `A1` after `μ` finishes 6.2. -/
theorem win62 (m : ℕ) (hm : 1 ≤ m) (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hj5 : j5 = 2 ∨ j5 = 4)
    (hr5 : R d5 = j5 * R (d 0)) (μ : ℕ) (hμ : Nat.Coprime μ 7) (i j l : Fin 4) (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (hw : Wb m (μ * d i) (μ * d j) (μ * d l)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  obtain ⟨a, hcov⟩ := fin4_rest i j l hij hil hjl
  obtain ⟨h1, h2⟩ := hw
  obtain ⟨e1, he1, q1⟩ := carry_le (E_modEq m (μ * d i) (μ * d l)) h1
  obtain ⟨e2, he2, q2⟩ := carry_le (E_modEq m (μ * d j) (μ * d l)) h2
  set qc : ZMod 7 := (qq m (μ * d l) : ZMod 7) with hqc
  rcases z7_sec62a e1 e2 (val_lt_of he1 (by norm_num)) (val_lt_of he2 (by norm_num))
      ((qq m (μ * d a) : ZMod 7) - qc) ((qq m (μ * d5) : ZMod 7) - j5 * qc) j5 hj5 with
    ⟨K, k0, k1, k2, k4, k5⟩ | hall
  · apply finish62 m hm d hd hcl d5 hd5 j5 hr5 μ hμ (K - qc)
    · intro x
      rcases hcov x with rfl | rfl | rfl | rfl
      · exact ok7_congr k0 (by ring)
      · exact ok7_congr k1 (by rw [q1]; ring)
      · exact ok7_congr k2 (by rw [q2]; ring)
      · exact ok7_congr k4 (by ring)
    · exact ok7_congr k5 (by ring)
  · have two : ∀ x, ∃ g : ℕ, g < 2 ∧ (qq m (2 * (μ * x)) : ZMod 7) = 2 * qq m (μ * x) + g :=
      fun x => qq_two_mul m (μ * x)
    obtain ⟨c0, hc0, t0⟩ := two (d l)
    obtain ⟨g1, hg1, t1⟩ := two (d i)
    obtain ⟨g2, hg2, t2⟩ := two (d j)
    obtain ⟨g4, hg4, t4⟩ := two (d a)
    obtain ⟨g5, hg5, t5⟩ := two d5
    obtain ⟨K, k0, k1, k2, k4, k5⟩ := hall c0 (val_lt_of hc0 (by norm_num)) g1
      (val_lt_of hg1 (by norm_num)) g2 (val_lt_of hg2 (by norm_num)) g4 (val_lt_of hg4 (by norm_num))
      g5 (val_lt_of hg5 (by norm_num))
    apply finish62 m hm d hd hcl d5 hd5 j5 hr5 (2 * μ) (Nat.Coprime.mul_left (by norm_num) hμ)
      (K - 2 * qc)
    · intro x
      rcases hcov x with rfl | rfl | rfl | rfl
      · exact ok7_congr k0 (by rw [mul_assoc, t0]; ring)
      · exact ok7_congr k1 (by rw [mul_assoc, t1, q1]; ring)
      · exact ok7_congr k2 (by rw [mul_assoc, t2, q2]; ring)
      · exact ok7_congr k4 (by rw [mul_assoc, t4]; ring)
    · exact ok7_congr k5 (by rw [mul_assoc, t5]; ring)

theorem win62w (m : ℕ) (hm : 1 ≤ m) (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hj5 : j5 = 2 ∨ j5 = 4)
    (hr5 : R d5 = j5 * R (d 0)) (μ : ℕ) (hμ : Nat.Coprime μ 7) (i j l : Fin 4) (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (hw : Win m (μ * d i) (μ * d j) (μ * d l)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  rcases hw with h | h | h
  · exact win62 m hm d hd hcl d5 hd5 j5 hj5 hr5 μ hμ i j l hij hil hjl h
  · exact win62 m hm d hd hcl d5 hd5 j5 hj5 hr5 μ hμ l j i (Ne.symm hjl) (Ne.symm hil) (Ne.symm hij) h
  · exact win62 m hm d hd hcl d5 hd5 j5 hj5 hr5 μ hμ i l j hil hij (Ne.symm hjl) h

/-! ## `nu(E) = {m}` -/

theorem off_of_top (m x a : ℕ) (h0 : E m x a ≠ 0) (hnu : nu 7 (E m x a) = m) :
    ∃ n, n < 7 ∧ x ≡ a + 7 ^ m * n [MOD 7 ^ (m + 1)] ∧ (n : ZMod 7) = R (E m x a) := by
  obtain ⟨n, hn, -, hR⟩ := form_of h0
  rw [hnu] at hn
  refine ⟨n, ?_, by have := E_modEq m x a; rwa [hn] at this, hR.symm⟩
  have h1 := E_lt m x a
  rw [hn, pow_succ] at h1
  exact (Nat.mul_lt_mul_left (by positivity)).mp h1

theorem ediff_lt (m x y : ℕ) : ediff m x y < 7 ^ (m + 1) := by
  unfold ediff; split_ifs <;> exact dsub_lt _ _ _ (N_pos m)

theorem top_or_zero {m e : ℕ} (hlt : e < 7 ^ (m + 1)) (h : e = 0 ∨ nu 7 e = m) :
    ∃ z, z < 7 ∧ e = 7 ^ m * z := by
  by_cases he : e = 0
  · exact ⟨0, by norm_num, by rw [he]; ring⟩
  · obtain ⟨w, -, hw7, hw⟩ := top_form he hlt (h.resolve_left he)
    exact ⟨w, hw7, hw⟩

/-- Lemma 7, both parts, as one steering statement. -/
theorem steer (m : ℕ) (hm : 2 ≤ m) (P Q : ℕ) (hP : ¬ 7 ∣ P) (hQ : ¬ 7 ∣ Q)
    (hr : rp 7 Q = 2 * rp 7 P % 7) (X : Finset (ZMod 7)) (hX : Z7.ell X ≤ 4)
    (hz : ∀ z, z < 7 → ediff m P Q = 7 ^ m * z → ¬ ((z : ZMod 7) ∈ X ∧ (z : ZMod 7) - 1 ∈ X)) :
    ∃ lam, lam ≡ 1 [MOD 7] ∧ etilde m (lam * P) (lam * Q) ∉ X := by
  by_cases hc : ediff m P Q ≠ 0 ∧ nu 7 (ediff m P Q) < m
  · obtain ⟨h, hh, lam, hlam, hX'⟩ := lemma7_i m P Q X hP hQ hr hc.1 hc.2 hX
    exact ⟨lam, Lam_modEq_seven hh hlam, hX'⟩
  · have h0 : ediff m P Q = 0 ∨ nu 7 (ediff m P Q) = m := by
      by_cases h0 : ediff m P Q = 0
      · exact Or.inl h0
      · right; have := nu_le_m h0 (ediff_lt m P Q); push Not at hc; have := hc h0; omega
    obtain ⟨z, hz7, hze⟩ := top_or_zero (ediff_lt m P Q) h0
    obtain ⟨lam, hlam, hX'⟩ := lemma7_ii_ext m P Q z X hm hP hQ hr (by rw [hze]) (hz z hz7 hze)
    exact ⟨lam, Lam_modEq_seven (by omega) hlam, hX'⟩

theorem etilde_b1 (m lam P Q : ℕ) (hl : lam ≡ 1 [MOD 7]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hr : rp 7 Q = 2 * rp 7 P % 7) :
    etilde m (lam * P) (lam * Q) = 2 * (qq m (lam * P) : ZMod 7) - qq m (lam * Q) := by
  have hr' : rp 7 (lam * Q) = 2 * rp 7 (lam * P) % 7 := by
    rw [rp_mul_of_modEq_one (by norm_num) hl hP0, rp_mul_of_modEq_one (by norm_num) hl hQ0]; exact hr
  exact (ediff_branch1 m _ _ hr').2

theorem zmod7_of_modEq_one {lam : ℕ} (hl : lam ≡ 1 [MOD 7]) : (lam : ZMod 7) = 1 := by
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hl; simpa using this

theorem topZ (m : ℕ) (A : ℤ) (hA : (A : ZMod 7) = 0) :
    (((7 : ℤ) ^ m * A : ℤ) : ZMod (7 ^ (m + 1))) = 0 := by
  obtain ⟨t, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd A 7).mp hA
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact ⟨t, by ring⟩

theorem rp_of_R {x y : ℕ} (h : R y = 2 * R x) : rp 7 y = 2 * rp 7 x % 7 := by
  apply nat_cast_zmod7_eq_of_lt (rp_lt _) (Nat.mod_lt _ (by norm_num))
  rw [ZMod.natCast_mod]; push_cast; exact h

/-- five-element finish (`a, b, c, e` of one class, `d5` of class `j5`). -/
theorem finish5 (m : ℕ) (hm : 1 ≤ m) (a b c e d5 : ℕ) (hd : ∀ x ∈ [a, b, c, e], ¬ 7 ∣ x ∧ x % 7 = a % 7)
    (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hr5 : R d5 = j5 * R a) (μ : ℕ) (hμ : Nat.Coprime μ 7) (K : ZMod 7)
    (hK : ∀ x ∈ [a, b, c, e], ok7 ((qq m (μ * x) : ZMod 7) + K))
    (hK5 : ok7 ((qq m (μ * d5) : ZMod 7) + j5 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ x ∈ [a, b, c, e], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  have ha := (hd a (by simp)).1
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; exact ha (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at hd5; exact hd5 (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hρ : R (μ * a) ≠ 0 := R_ne_zero (Nat.mul_ne_zero hμ0 ha0)
  obtain ⟨lam, hc, hall⟩ := finish_list m hm μ hμ _ hρ
    ((d5, j5) :: [a, b, c, e].map (fun x => (x, 1)))
    (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨hd5, ?_⟩
        rw [R_mul_unit hμ h50, R_mul_unit hμ ha0, hr5]; ring
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨h7, hcl⟩ := hd x hx
        refine ⟨h7, ?_⟩
        simp only [one_mul]
        have hx0 : x ≠ 0 := by intro h; rw [h] at h7; exact h7 (dvd_zero 7)
        rw [R_mul_unit hμ hx0, R_mul_unit hμ ha0, R_of_not_dvd h7, R_of_not_dvd ha, hcl]) K
    (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hK5
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        simpa using hK x hx)
  refine ⟨lam, hc, fun x hx => hall (x, 1) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, hx, rfl⟩)),
    hall (d5, j5) List.mem_cons_self⟩

theorem z7_sec62b1 : ∀ j v5 : ZMod 7, (j = 2 ∨ j = 4) →
    ∃ K, ok7 K ∧ ok7 (1 + K) ∧ ok7 (2 + K) ∧ ok7 (3 + K) ∧ ok7 (v5 + j * K) := by
  decide

theorem z7_sec62b2 : ∀ a' q5 : ZMod 7, 2 * (a' + 3) - q5 ≠ 2 → 2 * (a' + 3) - q5 ≠ 3 →
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 6 + K) ∧ ok7 (a' + 5 + K) ∧ ok7 (a' + 3 + K) ∧ ok7 (q5 + 2 * K) := by
  decide

theorem z7_sec62b4 : ∀ a' q5 : ZMod 7, 2 * q5 - (a' + 3) ≠ 4 → 2 * q5 - (a' + 3) ≠ 6 →
    ∃ K, ok7 (a' + K) ∧ ok7 (a' + 6 + K) ∧ ok7 (a' + 5 + K) ∧ ok7 (a' + 3 + K) ∧ ok7 (q5 + 4 * K) := by
  decide

theorem z7_x23 : ∀ z : ZMod 7, z ∈ ({2, 3} : Finset (ZMod 7)) → z - 1 ∈ ({2, 3} : Finset (ZMod 7)) →
    z = 3 := by decide

theorem z7_x46 : ∀ z : ZMod 7, ¬ (z ∈ ({4, 6} : Finset (ZMod 7)) ∧ z - 1 ∈ ({4, 6} : Finset (ZMod 7))) := by
  decide

theorem ell23 : Z7.ell {2, 3} ≤ 4 := by decide
theorem ell46 : Z7.ell {4, 6} ≤ 4 := by decide

theorem z7_u1 : ∀ w u : ZMod 7, u * w = 1 → u * (2 * w) = 2 ∧ u * (3 * w) = 3 := by decide

theorem z7_u6 : ∀ w u : ZMod 7, u * w = 6 → u * (2 * w) = 5 ∧ u * (4 * w) = 3 ∧
    (2 * u) * w = 5 ∧ (2 * u) * (2 * w) = 3 ∧ (2 * u) * (4 * w) = 6 ∧
    2 * (u * (2 * w)) - 2 * (u * (4 * w)) + 3 = 0 := by decide

theorem z7_eight (x : ZMod 7) : 2 * (4 * x) = x := by
  have : (8 : ZMod 7) = 1 := by decide
  linear_combination x * this

theorem mem_list4 {x a b c e : ℕ} (hx : x ∈ [a, b, c, e]) : x = a ∨ x = b ∨ x = c ∨ x = e := by
  simpa using hx

/-- 6.2, `nu(E) = {m}` (labels `a, b, c, e` = the paper's `d1, d2, d3, d4` from Lemma 10 (ii)). -/
theorem sec62_top (m : ℕ) (hm : 2 ≤ m) (a b c e d5 : ℕ)
    (hd : ∀ x ∈ [a, b, c, e], ¬ 7 ∣ x ∧ x % 7 = a % 7) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7)
    (hj5 : j5 = 2 ∨ j5 = 4) (hr5 : R d5 = j5 * R a)
    (hb : E m b a ≠ 0 ∧ nu 7 (E m b a) = m) (hc : E m c a ≠ 0 ∧ nu 7 (E m c a) = m)
    (he : E m e a ≠ 0 ∧ nu 7 (E m e a) = m) (h2 : R (E m c a) = 2 * R (E m b a))
    (h34 : R (E m e a) = 3 * R (E m b a) ∨ R (E m e a) = 4 * R (E m b a)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ x ∈ [a, b, c, e], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  obtain ⟨nb, -, hbm, hRb⟩ := off_of_top m b a hb.1 hb.2
  obtain ⟨nc, -, hcm, hRc⟩ := off_of_top m c a hc.1 hc.2
  obtain ⟨ne, -, hem, hRe⟩ := off_of_top m e a he.1 he.2
  set w := R (E m b a) with hw
  have hw0 : w ≠ 0 := R_ne_zero hb.1
  have ha := (hd a (by simp)).1
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; exact ha (dvd_zero 7)
  have he7 := (hd e (by simp)).1
  have he0 : e ≠ 0 := by intro h; rw [h] at he7; exact he7 (dvd_zero 7)
  have hc7 := (hd c (by simp)).1
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc7; exact hc7 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at hd5; exact hd5 (dvd_zero 7)
  have Re : R e = R a := by rw [R_of_not_dvd he7, R_of_not_dvd ha, (hd e (by simp)).2]
  have Rc : R c = R a := by rw [R_of_not_dvd hc7, R_of_not_dvd ha, (hd c (by simp)).2]
  -- offsets after a multiplier
  have off : ∀ μ, (qq m (μ * b) : ZMod 7) = qq m (μ * a) + (μ : ZMod 7) * w ∧
      (qq m (μ * c) : ZMod 7) = qq m (μ * a) + (μ : ZMod 7) * (2 * w) ∧
      (qq m (μ * e) : ZMod 7) = qq m (μ * a) + (μ : ZMod 7) * R (E m e a) := by
    intro μ
    refine ⟨by rw [top_shift m μ b a nb hbm, hRb], by rw [top_shift m μ c a nc hcm, hRc, h2],
      by rw [top_shift m μ e a ne hem, hRe]⟩
  rcases h34 with h3 | h4
  · -- (ii.1)
    obtain ⟨u, hu⟩ := z7_solve w 1 hw0
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
    obtain ⟨u2, u3⟩ := z7_u1 w u hu
    set μ := u.val
    have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
    obtain ⟨K, k0, k1, k2, k3, k5⟩ :=
      z7_sec62b1 j5 ((qq m (μ * d5) : ZMod 7) - j5 * qq m (μ * a)) hj5
    obtain ⟨ob, oc, oe⟩ := off μ
    apply finish5 m (by omega) a b c e d5 hd hd5 j5 hr5 μ (coprime_of_zmod_ne_zero hu0)
      (K - qq m (μ * a))
    · intro x hx
      rcases mem_list4 hx with rfl | rfl | rfl | rfl
      · exact ok7_congr k0 (by ring)
      · exact ok7_congr k1 (by rw [ob, hμu, hu]; ring)
      · exact ok7_congr k2 (by rw [oc, hμu, u2]; ring)
      · exact ok7_congr k3 (by rw [oe, hμu, h3, u3]; ring)
    · exact ok7_congr k5 (by ring)
  · -- (ii.2)
    obtain ⟨u, hu⟩ := z7_solve w 6 hw0
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
    obtain ⟨u2, u4, v1, v2, v4, vz⟩ := z7_u6 w u hu
    set μ := u.val
    have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
    have hμc : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
    have hμ0 : μ ≠ 0 := by intro h; rw [h] at hμc; norm_num at hμc
    rcases hj5 with rfl | rfl
    · -- A2: Lemma 7 on (μ e, μ d5), avoid {2, 3}
      have hr : rp 7 (μ * d5) = 2 * rp 7 (μ * e) % 7 := by
        apply rp_of_R; rw [R_mul_unit hμc h50, R_mul_unit hμc he0, hr5, Re]; ring
      have hP : ¬ 7 ∣ μ * e := not_dvd_mul hμc he7
      have hQ : ¬ 7 ∣ μ * d5 := not_dvd_mul hμc hd5
      by_cases hexc : ediff m (μ * e) (μ * d5) = 7 ^ m * 3
      · -- exception: double
        set μ2 := 2 * μ with hμ2
        have hμ2c : Nat.Coprime μ2 7 := Nat.Coprime.mul_left (by norm_num) hμc
        have hr' : rp 7 (μ2 * d5) = 2 * rp 7 (μ2 * c) % 7 := by
          apply rp_of_R; rw [R_mul_unit hμ2c h50, R_mul_unit hμ2c hc0, hr5, Rc]; ring
        have hz0 : ediff m (μ2 * c) (μ2 * d5) = 0 := by
          rw [(ediff_branch1 m _ _ hr').1]
          apply eq_of_cast_N (dsub_lt _ _ _ (N_pos m)) (N_pos m)
          rw [dsub_cast _ _ _ (N_pos m)]
          have A := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcm
          have B := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hem
          have C := dsub_cast (7 ^ (m + 1)) (2 * (μ * e)) (μ * d5) (N_pos m)
          rw [← (ediff_branch1 m _ _ hr).1, hexc] at C
          have D := topZ m (2 * μ * nc - 2 * μ * ne + 3) (by
            push_cast; rw [hμu, ← hRc, ← hRe] at *; rw [hRc, hRe, h2, h4]; linear_combination vz)
          push_cast at A B C D ⊢
          rw [hμ2]; push_cast
          linear_combination 4 * (μ : ZMod (7 ^ (m + 1))) * A - 4 * (μ : ZMod (7 ^ (m + 1))) * B -
            2 * C + 2 * D
        obtain ⟨lam, hl, hX⟩ := steer m hm (μ2 * c) (μ2 * d5) (not_dvd_mul hμ2c hc7)
          (not_dvd_mul hμ2c hd5) hr' {2, 3} ell23 (by
            intro z hz7 hz
            rw [hz0] at hz
            have : z = 0 := by
              rcases Nat.mul_eq_zero.mp hz.symm with h | h
              · exact absurd h (by positivity)
              · exact h
            subst this; decide)
        have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
        have hl1 := zmod7_of_modEq_one hl
        rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero (by omega) hc0) (Nat.mul_ne_zero (by omega) h50) hr']
          at hX
        set μ' := lam * μ2 with hμ'
        have hμ'u : (μ' : ZMod 7) = 2 * u := by rw [hμ']; push_cast; rw [hl1, hμ2]; push_cast; rw [hμu]; ring
        rw [show lam * (μ2 * c) = μ' * c by rw [hμ', hμ2]; ring,
          show lam * (μ2 * d5) = μ' * d5 by rw [hμ', hμ2]; ring] at hX
        obtain ⟨ob, oc, oe⟩ := off μ'
        rw [hμ'u] at ob oc oe
        rw [h4] at oe
        rw [v2] at oc; rw [v1] at ob; rw [v4] at oe
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hX
        obtain ⟨K, k0, k6, k5, k3, k2⟩ := z7_sec62b2 (qq m (μ' * a)) (qq m (μ' * d5))
          (by rw [← oc]; exact hX.1) (by rw [← oc]; exact hX.2)
        apply finish5 m (by omega) a b c e d5 hd hd5 2 hr5 μ'
          (Nat.Coprime.mul_left hlc hμ2c) K
        · intro x hx
          rcases mem_list4 hx with rfl | rfl | rfl | rfl
          · exact k0
          · exact ok7_congr k5 (by rw [ob])
          · exact ok7_congr k3 (by rw [oc])
          · exact ok7_congr k6 (by rw [oe])
        · exact k2
      · obtain ⟨lam, hl, hX⟩ := steer m hm (μ * e) (μ * d5) hP hQ hr {2, 3} ell23 (by
            intro z hz7 hz hin
            have h3 := z7_x23 _ hin.1 hin.2
            have : z = 3 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h3]; rfl)
            rw [this] at hz; exact hexc hz)
        have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
        have hl1 := zmod7_of_modEq_one hl
        rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 he0) (Nat.mul_ne_zero hμ0 h50) hr] at hX
        set μ' := lam * μ with hμ'
        have hμ'u : (μ' : ZMod 7) = u := by rw [hμ']; push_cast; rw [hl1, hμu]; ring
        rw [show lam * (μ * e) = μ' * e by rw [hμ', mul_assoc],
          show lam * (μ * d5) = μ' * d5 by rw [hμ', mul_assoc]] at hX
        obtain ⟨ob, oc, oe⟩ := off μ'
        rw [hμ'u] at ob oc oe
        rw [h4, u4] at oe; rw [u2] at oc; rw [hu] at ob
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hX
        obtain ⟨K, k0, k6, k5, k3, k2⟩ := z7_sec62b2 (qq m (μ' * a)) (qq m (μ' * d5))
          (by rw [← oe]; exact hX.1) (by rw [← oe]; exact hX.2)
        apply finish5 m (by omega) a b c e d5 hd hd5 2 hr5 μ'
          (Nat.Coprime.mul_left hlc hμc) K
        · intro x hx
          rcases mem_list4 hx with rfl | rfl | rfl | rfl
          · exact k0
          · exact ok7_congr k6 (by rw [ob])
          · exact ok7_congr k5 (by rw [oc])
          · exact ok7_congr k3 (by rw [oe])
        · exact k2
    · -- A4: Lemma 7 on (μ d5, μ e), avoid {4, 6}
      have hr : rp 7 (μ * e) = 2 * rp 7 (μ * d5) % 7 := by
        apply rp_of_R; rw [R_mul_unit hμc h50, R_mul_unit hμc he0, hr5, Re]
        linear_combination (μ : ZMod 7) * (z7_eight (R a)).symm
      obtain ⟨lam, hl, hX⟩ := steer m hm (μ * d5) (μ * e) (not_dvd_mul hμc hd5) (not_dvd_mul hμc he7)
        hr {4, 6} ell46 (fun z _ _ => z7_x46 z)
      have hlc : Nat.Coprime lam 7 := (coprime_of_modEq_one (by norm_num) hl).1
      have hl1 := zmod7_of_modEq_one hl
      rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 h50) (Nat.mul_ne_zero hμ0 he0) hr] at hX
      set μ' := lam * μ with hμ'
      have hμ'u : (μ' : ZMod 7) = u := by rw [hμ']; push_cast; rw [hl1, hμu]; ring
      rw [show lam * (μ * d5) = μ' * d5 by rw [hμ', mul_assoc],
        show lam * (μ * e) = μ' * e by rw [hμ', mul_assoc]] at hX
      obtain ⟨ob, oc, oe⟩ := off μ'
      rw [hμ'u] at ob oc oe
      rw [h4, u4] at oe; rw [u2] at oc; rw [hu] at ob
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hX
      obtain ⟨K, k0, k6, k5, k3, k2⟩ := z7_sec62b4 (qq m (μ' * a)) (qq m (μ' * d5))
        (by rw [← oe]; exact hX.1) (by rw [← oe]; exact hX.2)
      apply finish5 m (by omega) a b c e d5 hd hd5 4 hr5 μ' (Nat.Coprime.mul_left hlc hμc) K
      · intro x hx
        rcases mem_list4 hx with rfl | rfl | rfl | rfl
        · exact k0
        · exact ok7_congr k6 (by rw [ob])
        · exact ok7_congr k5 (by rw [oc])
        · exact ok7_congr k3 (by rw [oe])
      · exact k2

/-- **Section 6.2** (`|A1| = 4`, `m ≥ 2`): `d0..d3` level 0 of one class, `d5` level 0 with
`r(d5) = j5 r(d0)`, `j5 ∈ {2, 4}`. A multiplier prime to 7 keeps all five off `q ∈ {0, 6}`. -/
theorem sec62 (m : ℕ) (hm : 2 ≤ m) (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hj5 : j5 = 2 ∨ j5 = 4)
    (hr5 : R d5 = j5 * R (d 0)) :
    ∃ lam, Nat.Coprime lam 7 ∧ (∀ i, qq m (lam * d i) ≠ 0 ∧ qq m (lam * d i) ≠ 6) ∧
      qq m (lam * d5) ≠ 0 ∧ qq m (lam * d5) ≠ 6 := by
  have hm1 : 1 ≤ m := by omega
  rcases lemma10 m d hcl with hz | ⟨σ, hi | ⟨h, hall, h2, h34⟩⟩
  · have hw : Wb m (1 * d 1) (1 * d 2) (1 * d 0) := by
      simp only [one_mul]; exact ⟨by rw [hz 1 0]; positivity, by rw [hz 2 0]; positivity⟩
    exact win62 m hm1 d hd hcl d5 hd5 j5 hj5 hr5 1 (by norm_num) 1 2 0 (by decide) (by decide)
      (by decide) hw
  · obtain ⟨lam, hc, hw⟩ := win9_i m (d (σ 1)) (d (σ 2)) (d (σ 0)) hi
    exact win62 m hm1 d hd hcl d5 hd5 j5 hj5 hr5 lam hc _ _ _ (by simp) (by simp) (by simp) hw
  · have n10 : σ 1 ≠ σ 0 := by simp
    have n20 : σ 2 ≠ σ 0 := by simp
    have n30 : σ 3 ≠ σ 0 := by simp
    have hle : h ≤ m := by
      rw [← (hall _ _ n10).2]; exact nu_le_m (hall _ _ n10).1 (E_lt m _ _)
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨lam, hc, hw⟩ := win9_ii m h (d (σ 1)) (d (σ 2)) (d (σ 0)) _ _ hlt rfl rfl
        (hall _ _ n10).1 (hall _ _ n20).1 (hall _ _ n10).2 (hall _ _ n20).2 (rp_of_R h2)
      exact win62w m hm1 d hd hcl d5 hd5 j5 hj5 hr5 lam hc _ _ _ (by simp) (by simp) (by simp) hw
    · have heq' := heq.symm
      subst heq'
      have h0 : ∀ i, d i ≠ 0 := fun i h => hd i (by rw [h]; exact dvd_zero 7)
      have hr5' : R d5 = j5 * R (d (σ 0)) := by
        rw [hr5, R_of_not_dvd (hd 0), R_of_not_dvd (hd (σ 0)), hcl (σ 0) 0]
      obtain ⟨lam, hc, hA, h5⟩ := sec62_top m hm (d (σ 0)) (d (σ 1)) (d (σ 2)) (d (σ 3)) d5
        (by
          intro x hx
          rcases mem_list4 hx with rfl | rfl | rfl | rfl <;> exact ⟨hd _, hcl _ _⟩)
        hd5 j5 hj5 hr5' (hall _ _ n10) (hall _ _ n20) (hall _ _ n30) h2 h34
      refine ⟨lam, hc, ?_, h5⟩
      intro i
      have hi : i = σ (σ.symm i) := by simp
      rw [hi]
      generalize σ.symm i = k
      fin_cases k
      · exact hA _ (by simp)
      · exact hA _ (by simp)
      · exact hA _ (by simp)
      · exact hA _ (by simp)

/-- **Section 6.2, real form** with one top speed. -/
theorem sec62_witness (m : ℕ) (hm : 2 ≤ m) (d : Fin 4 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i)
    (hcl : ∀ i j, d i % 7 = d j % 7) (d5 : ℕ) (hd5 : ¬ 7 ∣ d5) (j5 : ZMod 7) (hj5 : j5 = 2 ∨ j5 = 4)
    (hr5 : R d5 = j5 * R (d 0)) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d5) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hc, hlam, h5⟩ := sec62 m hm d hd hcl d5 hd5 j5 hj5 hr5
  obtain ⟨t, ht, hall⟩ := witness_of_lam m lam hc (d5 :: List.ofFn d) [d6]
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h5
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hlam i)
    (by intro x hx; simp at hx; subst hx; exact ⟨h6, h6m⟩)
  exact ⟨t, ht, fun i => hall _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_ofFn.mpr ⟨i, rfl⟩))), hall _ (List.mem_append_left _ List.mem_cons_self),
    hall _ (List.mem_append_right _ (by simp))⟩

end LRSpectrumFull.BarajasSerra.Sec6
