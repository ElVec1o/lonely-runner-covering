import LRSpectrumFull.BarajasSerraSec6L9

/-!
# E6 session 18: Barajas-Serra Lemmas 10 and 11 (labelings) and shared Section 6 tools

`N = 7^(m+1)`, `M = 7^m`, `E m x y = dsub N x y` (the residue of `x - y`), `R x = r(x)` in `ZMod 7`.
The convention `nu 0 = 0` is kept: a zero residue has level `0` in Lean (the paper: level `> m`).

* `levZ`, `form_of`: level/residue bookkeeping for residues mod `N`.
* `sub_rule`, `swap_rule`: `E x y` from `E x z`, `E y z` at a common level.
* **Lemma 10** (`lemma10`): four residues of one class mod 7. Either all congruent mod `N`, or a
  labeling `(d1,d2,d3,d4)` with `nu(e21) ≠ nu(e31)`, or all `e_ij` nonzero at one level `h` with
  `r(e31) = 2 r(e21)` and `r(e41) ∈ {3 r(e21), 4 r(e21)}`.
* **Lemma 11** (`lemma11`): three residues of one class, `t ≠ 0`: all congruent, or
  `nu(e13) ≠ nu(e23)`, or one level `h` with `r(e13) = 2 r(e23)` or `r(e13) = 3 r(e23) = ±3t`.
  (Paper: `3 r(e23) = ±s`; here the free parameter is `t = r(e23)` up to sign, `t = 5s`.)
* Finishing tools: `shift_class` (the `Lambda_0` shift on a class), `witness_of_lam` (bridge to
  `nearestIntDist ≥ 1/7`, one top speed allowed), `lemma7_ii_ext` (Lemma 7 (ii) with `e ≡ 7^m z`,
  `z = 0` allowed), `top_shift`.

Falsified first: (development file, not part of this archive) (Lemma 10: m=2 all 4-multisets of a class
in `[0, 2N)`, s = 1, 3; m=3 sampled; 0 failures; negative control "only (ii.1)" fails 539392 times.
Lemma 11: 0 failures; negative control "+t only" fails. Lemma 7 (ii)-ext: 0 failures).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- residue of `x - y` mod `7^(m+1)`. -/
abbrev E (m x y : ℕ) : ℕ := dsub (7 ^ (m + 1)) x y

/-- `r(x)` in `ZMod 7`. -/
noncomputable def R (x : ℕ) : ZMod 7 := ((rp 7 x : ℕ) : ZMod 7)

theorem E_lt (m x y : ℕ) : E m x y < 7 ^ (m + 1) := dsub_lt _ _ _ (N_pos m)

theorem E_cast (m x y : ℕ) : ((E m x y : ℕ) : ZMod (7 ^ (m + 1))) = (x : ZMod (7 ^ (m + 1))) - y :=
  dsub_cast _ _ _ (N_pos m)

theorem nu_zero : nu 7 0 = 0 := by simp [nu]

theorem eq_of_cast_N {m a b : ℕ} (ha : a < 7 ^ (m + 1)) (hb : b < 7 ^ (m + 1))
    (h : (a : ZMod (7 ^ (m + 1))) = b) : a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b _).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem E_self (m x : ℕ) : E m x x = 0 := by
  apply eq_of_cast_N (E_lt m x x) (N_pos m); rw [E_cast]; simp

/-! ## level and residue bookkeeping -/

theorem levZ {m h e : ℕ} {u : ℤ} (_he : e < 7 ^ (m + 1)) (hh : h ≤ m) (hu : ¬ (7 : ℤ) ∣ u)
    (hc : (e : ZMod (7 ^ (m + 1))) = (((7 : ℤ) ^ h * u : ℤ) : ZMod (7 ^ (m + 1)))) :
    e ≠ 0 ∧ nu 7 e = h ∧ R e = (u : ZMod 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc1 : ((e : ℤ) : ZMod (7 ^ (m + 1))) = (((7 : ℤ) ^ h * u : ℤ) : ZMod (7 ^ (m + 1))) := by
    rw [Int.cast_natCast]; exact hc
  have hc' := (ZMod.intCast_eq_intCast_iff_dvd_sub (e : ℤ) ((7 : ℤ) ^ h * u) (7 ^ (m + 1))).mp hc1
  push_cast at hc'
  obtain ⟨t, ht⟩ := hc'
  have hpow : (7 : ℤ) ^ (m + 1) = 7 ^ h * 7 ^ (m + 1 - h) := by rw [← pow_add]; congr 1; omega
  set v : ℤ := u - 7 ^ (m + 1 - h) * t with hv
  have hev : (e : ℤ) = 7 ^ h * v := by
    rw [hv, mul_sub, ← mul_assoc, ← hpow]; linarith
  have h7 : (7 : ℤ) ∣ 7 ^ (m + 1 - h) * t := Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) t
  have h7v : ¬ (7 : ℤ) ∣ v := by
    intro hd; apply hu
    have := dvd_add hd h7; rwa [hv, sub_add_cancel] at this
  have hvpos : 0 ≤ v := by
    by_contra hneg; push Not at hneg
    have h1 : (7 : ℤ) ^ h * v < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    have h2 : (0 : ℤ) ≤ e := by positivity
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hvpos).symm⟩
  have hen : e = 7 ^ h * n := by
    have : (e : ℤ) = ((7 ^ h * n : ℕ) : ℤ) := by rw [hev, hn]; push_cast; ring
    exact_mod_cast this
  have hn7 : ¬ 7 ∣ n := by
    intro hd; apply h7v; rw [hn]; exact_mod_cast hd
  have hn0 : n ≠ 0 := by rintro rfl; exact hn7 (dvd_zero _)
  have hnu : nu 7 e = h := by
    unfold nu
    rw [hen, padicValNat.mul (pow_ne_zero _ (by norm_num)) hn0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hn7, add_zero]
  refine ⟨by rw [hen]; exact Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hn0, hnu, ?_⟩
  unfold R rp
  rw [hnu, hen, Nat.mul_div_cancel_left _ (by positivity), ZMod.natCast_mod]
  have : ((n : ℤ) : ZMod 7) = (u : ZMod 7) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hn, hv]
    push_cast
    rw [show u - (u - 7 ^ (m + 1 - h) * t) = 7 ^ (m + 1 - h) * t by ring]
    exact h7
  rw [← this]; simp

theorem form_of {e : ℕ} (he0 : e ≠ 0) :
    ∃ n : ℕ, e = 7 ^ (nu 7 e) * n ∧ ¬ 7 ∣ n ∧ R e = (n : ZMod 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨e / 7 ^ nu 7 e, (Nat.mul_div_cancel' (pow_nu_dvd 7 e)).symm, ?_, ?_⟩
  · intro hd
    have h1 : 7 ^ (nu 7 e + 1) ∣ e := by
      rw [pow_succ]
      have := Nat.mul_dvd_mul_left (7 ^ nu 7 e) hd
      rwa [Nat.mul_div_cancel' (pow_nu_dvd 7 e)] at this
    exact pow_succ_padicValNat_not_dvd he0 h1
  · unfold R rp; rw [ZMod.natCast_mod]

theorem R_ne_zero {e : ℕ} (he0 : e ≠ 0) : R e ≠ 0 := by
  obtain ⟨n, -, hn, hR⟩ := form_of he0
  rw [hR]; intro h; exact hn ((ZMod.natCast_eq_zero_iff n 7).mp h)

theorem nu_le_m {m e : ℕ} (he0 : e ≠ 0) (hlt : e < 7 ^ (m + 1)) : nu 7 e ≤ m := nu_le_of_lt he0 hlt

/-- `E y x` from `E x y`: same level, opposite residue. -/
theorem swap_rule (m x y : ℕ) (h0 : E m x y ≠ 0) :
    E m y x ≠ 0 ∧ nu 7 (E m y x) = nu 7 (E m x y) ∧ R (E m y x) = - R (E m x y) := by
  obtain ⟨n, hn, hn7, hR⟩ := form_of h0
  have hle := nu_le_m h0 (E_lt m x y)
  have key := levZ (m := m) (h := nu 7 (E m x y)) (e := E m y x) (u := -(n : ℤ)) (E_lt m y x) hle
    (by rw [Int.dvd_neg]; exact_mod_cast hn7)
    (by
      rw [E_cast]
      have h1 := E_cast m x y
      rw [hn] at h1
      push_cast at h1 ⊢
      linear_combination h1)
  refine ⟨key.1, key.2.1, ?_⟩
  rw [key.2.2, hR]; push_cast; ring

theorem swap_zero (m x y : ℕ) (h0 : E m x y = 0) : E m y x = 0 := by
  apply eq_of_cast_N (E_lt m y x) (N_pos m)
  rw [E_cast]; have := E_cast m x y; rw [h0] at this; push_cast at this ⊢
  linear_combination this

theorem nu_swap (m x y : ℕ) : nu 7 (E m y x) = nu 7 (E m x y) := by
  by_cases h : E m x y = 0
  · rw [h, swap_zero m x y h]
  · exact (swap_rule m x y h).2.1

/-- common-level subtraction rule. -/
theorem sub_rule (m x y z h : ℕ) (hx0 : E m x z ≠ 0) (hy0 : E m y z ≠ 0) (hx : nu 7 (E m x z) = h)
    (hy : nu 7 (E m y z) = h) :
    (R (E m x z) = R (E m y z) → E m x y = 0 ∨ h < nu 7 (E m x y)) ∧
    (R (E m x z) ≠ R (E m y z) →
      E m x y ≠ 0 ∧ nu 7 (E m x y) = h ∧ R (E m x y) = R (E m x z) - R (E m y z)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha, ha7, hRa⟩ := form_of hx0
  obtain ⟨b, hb, hb7, hRb⟩ := form_of hy0
  rw [hx] at ha; rw [hy] at hb
  have hle : h ≤ m := hx ▸ nu_le_m hx0 (E_lt m x z)
  have hcast : ((E m x y : ℕ) : ZMod (7 ^ (m + 1))) =
      (((7 : ℤ) ^ h * ((a : ℤ) - b) : ℤ) : ZMod (7 ^ (m + 1))) := by
    rw [E_cast]
    have h1 := E_cast m x z; have h2 := E_cast m y z
    rw [ha] at h1; rw [hb] at h2
    push_cast at h1 h2 ⊢
    linear_combination h2 - h1
  constructor
  · intro hR
    rw [hRa, hRb] at hR
    have hd : (7 : ℤ) ∣ (a : ℤ) - b := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub (b : ℤ) (a : ℤ) 7).mp (by exact_mod_cast hR.symm)
      exact this
    by_cases hz : E m x y = 0
    · exact Or.inl hz
    · right
      obtain ⟨c, hc⟩ := hd
      -- 7^(h+1) ∣ E x y
      have hdvd : 7 ^ (h + 1) ∣ E m x y := by
        have hc2 : ((E m x y : ℕ) : ZMod (7 ^ (m + 1))) = (((7 ^ (h + 1) : ℕ) : ℤ) * c : ℤ) := by
          rw [hcast, hc]; push_cast; ring
        have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub (((7 ^ (h + 1) : ℕ) : ℤ) * c)
          ((E m x y : ℕ) : ℤ) (7 ^ (m + 1))).mp (by rw [Int.cast_natCast]; exact hc2.symm)
        have h4 : ((7 ^ (h + 1) : ℕ) : ℤ) ∣ ((7 ^ (m + 1) : ℕ) : ℤ) := by
          exact_mod_cast pow_dvd_pow 7 (by omega)
        have h5 := dvd_add (h4.trans h3) (dvd_mul_right (((7 ^ (h + 1) : ℕ) : ℤ)) c)
        rw [sub_add_cancel] at h5
        exact_mod_cast h5
      have := (padicValNat_dvd_iff_le (p := 7) hz).mp hdvd
      unfold nu; omega
  · intro hR
    rw [hRa, hRb] at hR
    have hnd : ¬ (7 : ℤ) ∣ (a : ℤ) - b := by
      intro hd; apply hR
      exact_mod_cast ((ZMod.intCast_eq_intCast_iff_dvd_sub (b : ℤ) (a : ℤ) 7).mpr hd).symm
    have key := levZ (E_lt m x y) hle hnd hcast
    refine ⟨key.1, key.2.1, ?_⟩
    rw [key.2.2, hRa, hRb]; push_cast; ring

/-- differences inside one class mod 7 are divisible by 7. -/
theorem nu_pos_of_class (m x y : ℕ) (hcl : x % 7 = y % 7) (h0 : E m x y ≠ 0) : 1 ≤ nu 7 (E m x y) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply one_le_padicValNat_of_dvd h0
  have h1 : ((E m x y : ℕ) : ZMod 7) = 0 := by
    have := congrArg (ZMod.castHom (show 7 ∣ 7 ^ (m + 1) from dvd_pow_self 7 (by omega)) (ZMod 7))
      (E_cast m x y)
    simp only [map_natCast, map_sub] at this
    rw [this, sub_eq_zero]
    exact (ZMod.natCast_eq_natCast_iff' x y 7).mpr hcl
  exact (ZMod.natCast_eq_zero_iff _ 7).mp h1

/-! ## permutations of small index sets -/

theorem mkPerm4 (a b c e : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = e := by
  have hinj : Function.Injective ![a, b, c, e] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  refine ⟨Equiv.ofBijective _ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, rfl, rfl, rfl, rfl⟩

theorem mkPerm3 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  have hinj : Function.Injective ![a, b, c] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  refine ⟨Equiv.ofBijective _ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, rfl, rfl, rfl⟩

theorem fourth (a b c : Fin 4) : ∃ e : Fin 4, e ≠ a ∧ e ≠ b ∧ e ≠ c := by
  revert a b c; decide

/-! ## Lemma 10 -/

theorem z7_pair_two : ∀ x1 x2 x3 : ZMod 7, x1 ≠ 0 → x2 ≠ 0 → x3 ≠ 0 → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
    (x2 = 2 * x1 ∨ x1 = 2 * x2 ∨ x3 = 2 * x1 ∨ x1 = 2 * x3 ∨ x3 = 2 * x2 ∨ x2 = 2 * x3) := by
  decide

theorem z7_third : ∀ x y : ZMod 7, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ 2 * x →
    (y = 3 * x ∨ y = 4 * x ∨ y = 5 * x ∨ y = 6 * x) := by
  decide

theorem z7_ne_two : ∀ x : ZMod 7, x ≠ 0 → x ≠ 2 * x := by decide

theorem z7_rebase : ∀ x : ZMod 7, (5 * x - 2 * x = 4 * (x - 2 * x)) ∧ (6 * x - 2 * x = 3 * (x - 2 * x)) ∧
    (- (2 * x) = 2 * (x - 2 * x)) := by decide

/-- the labeling step of Lemma 10, base index `0`. -/
theorem lemma10_lab (m h : ℕ) (d : Fin 4 → ℕ) (i j k : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hall : ∀ a b, a ≠ b → E m (d a) (d b) ≠ 0 ∧ nu 7 (E m (d a) (d b)) = h)
    (h2 : R (E m (d j) (d 0)) = 2 * R (E m (d i) (d 0)))
    (hy0 : R (E m (d k) (d 0)) ≠ R (E m (d i) (d 0)))
    (hy1 : R (E m (d k) (d 0)) ≠ R (E m (d j) (d 0))) :
    ∃ σ : Equiv.Perm (Fin 4),
      R (E m (d (σ 2)) (d (σ 0))) = 2 * R (E m (d (σ 1)) (d (σ 0))) ∧
        (R (E m (d (σ 3)) (d (σ 0))) = 3 * R (E m (d (σ 1)) (d (σ 0))) ∨
         R (E m (d (σ 3)) (d (σ 0))) = 4 * R (E m (d (σ 1)) (d (σ 0)))) := by
  set x := R (E m (d i) (d 0)) with hx
  set y := R (E m (d k) (d 0)) with hy
  have hx0 : x ≠ 0 := R_ne_zero (hall i 0 hi).1
  have hy00 : y ≠ 0 := R_ne_zero (hall k 0 hk).1
  rw [h2] at hy1
  rcases z7_third x y hx0 hy00 hy0 hy1 with e | e | e | e
  · obtain ⟨σ, s0, s1, s2, s3⟩ := mkPerm4 0 i j k (Ne.symm hi) (Ne.symm hj) (Ne.symm hk) hij hik hjk
    exact ⟨σ, by rw [s0, s1, s2, h2], Or.inl (by rw [s0, s1, s3, ← hy, e])⟩
  · obtain ⟨σ, s0, s1, s2, s3⟩ := mkPerm4 0 i j k (Ne.symm hi) (Ne.symm hj) (Ne.symm hk) hij hik hjk
    exact ⟨σ, by rw [s0, s1, s2, h2], Or.inr (by rw [s0, s1, s3, ← hy, e])⟩
  all_goals
    obtain ⟨σ, s0, s1, s2, s3⟩ := mkPerm4 j i 0 k (Ne.symm hij) hj hjk hi hik (Ne.symm hk)
    refine ⟨σ, ?_⟩
    rw [s0, s1, s2, s3]
    have hxj : R (E m (d i) (d 0)) ≠ R (E m (d j) (d 0)) := by rw [h2]; exact z7_ne_two x hx0
    have hkj : R (E m (d k) (d 0)) ≠ R (E m (d j) (d 0)) := by rw [h2]; exact hy1
    have A := ((sub_rule m (d i) (d j) (d 0) h (hall i 0 hi).1 (hall j 0 hj).1 (hall i 0 hi).2
      (hall j 0 hj).2).2 hxj).2.2
    have B := (swap_rule m (d j) (d 0) (hall j 0 hj).1).2.2
    have C := ((sub_rule m (d k) (d j) (d 0) h (hall k 0 hk).1 (hall j 0 hj).1 (hall k 0 hk).2
      (hall j 0 hj).2).2 hkj).2.2
    rw [A, B, C, h2, ← hx, ← hy, e]
    obtain ⟨r1, r2, r3⟩ := z7_rebase x
  · exact ⟨r3, Or.inr r1⟩
  · exact ⟨r3, Or.inl r2⟩

/-- **Lemma 10** (labeling, four elements of one class). -/
theorem lemma10 (m : ℕ) (d : Fin 4 → ℕ) (hcl : ∀ i j, d i % 7 = d j % 7) :
    (∀ i j, E m (d i) (d j) = 0) ∨
    ∃ σ : Equiv.Perm (Fin 4),
      nu 7 (E m (d (σ 1)) (d (σ 0))) ≠ nu 7 (E m (d (σ 2)) (d (σ 0))) ∨
      ∃ h, (∀ i j, i ≠ j → E m (d i) (d j) ≠ 0 ∧ nu 7 (E m (d i) (d j)) = h) ∧
        R (E m (d (σ 2)) (d (σ 0))) = 2 * R (E m (d (σ 1)) (d (σ 0))) ∧
        (R (E m (d (σ 3)) (d (σ 0))) = 3 * R (E m (d (σ 1)) (d (σ 0))) ∨
         R (E m (d (σ 3)) (d (σ 0))) = 4 * R (E m (d (σ 1)) (d (σ 0)))) := by
  by_cases hA : ∃ l i j : Fin 4, i ≠ l ∧ j ≠ l ∧ i ≠ j ∧
      nu 7 (E m (d i) (d l)) ≠ nu 7 (E m (d j) (d l))
  · obtain ⟨l, i, j, hil, hjl, hij, hne⟩ := hA
    obtain ⟨k, hkl, hki, hkj⟩ := fourth l i j
    obtain ⟨σ, s0, s1, s2, -⟩ := mkPerm4 l i j k (Ne.symm hil) (Ne.symm hjl) (Ne.symm hkl) hij
      (Ne.symm hki) (Ne.symm hkj)
    exact Or.inr ⟨σ, Or.inl (by rw [s0, s1, s2]; exact hne)⟩
  push Not at hA
  set h := nu 7 (E m (d 1) (d 0)) with hh
  have key0 : ∀ i : Fin 4, i ≠ 0 → nu 7 (E m (d i) (d 0)) = h := by
    intro i hi
    by_cases hi1 : i = 1
    · rw [hi1]
    · exact hA 0 i 1 hi (by decide) hi1
  have hall0 : ∀ i j, i ≠ j → nu 7 (E m (d i) (d j)) = h := by
    intro i j hij
    by_cases hj : j = 0
    · subst hj; exact key0 i hij
    by_cases hi : i = 0
    · subst hi; rw [nu_swap m (d j) (d 0)]; exact key0 j hj
    rw [hA j i 0 hij (Ne.symm hj) hi, nu_swap m (d j) (d 0)]; exact key0 j hj
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · left
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact E_self m _
    by_contra hne
    have := nu_pos_of_class m (d i) (d j) (hcl i j) hne
    rw [hall0 i j hij, h0] at this; omega
  right
  have hall : ∀ i j, i ≠ j → E m (d i) (d j) ≠ 0 ∧ nu 7 (E m (d i) (d j)) = h := by
    intro i j hij
    refine ⟨?_, hall0 i j hij⟩
    intro hz; have := hall0 i j hij; rw [hz, nu_zero] at this; omega
  have hdist : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → R (E m (d i) (d 0)) ≠ R (E m (d j) (d 0)) := by
    intro i j hi hj hij hR
    rcases (sub_rule m (d i) (d j) (d 0) h (hall i 0 hi).1 (hall j 0 hj).1 (hall i 0 hi).2
      (hall j 0 hj).2).1 hR with hz | hlt
    · exact (hall i j hij).1 hz
    · rw [(hall i j hij).2] at hlt; omega
  have n1 : (1 : Fin 4) ≠ 0 := by decide
  have n2 : (2 : Fin 4) ≠ 0 := by decide
  have n3 : (3 : Fin 4) ≠ 0 := by decide
  have n12 : (1 : Fin 4) ≠ 2 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have fin := fun (i j k : Fin 4) hi hj hk hij hik hjk h2 hy0 hy1 =>
    (lemma10_lab m h d i j k hi hj hk hij hik hjk hall h2 hy0 hy1)
  rcases z7_pair_two _ _ _ (R_ne_zero (hall 1 0 n1).1) (R_ne_zero (hall 2 0 n2).1)
      (R_ne_zero (hall 3 0 n3).1) (hdist 1 2 n1 n2 n12) (hdist 1 3 n1 n3 n13)
      (hdist 2 3 n2 n3 n23) with e | e | e | e | e | e
  · obtain ⟨σ, hσ⟩ := fin 1 2 3 n1 n2 n3 n12 n13 n23 e (hdist 3 1 n3 n1 n13.symm)
      (hdist 3 2 n3 n2 n23.symm)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩
  · obtain ⟨σ, hσ⟩ := fin 2 1 3 n2 n1 n3 n12.symm n23 n13 e (hdist 3 2 n3 n2 n23.symm)
      (hdist 3 1 n3 n1 n13.symm)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩
  · obtain ⟨σ, hσ⟩ := fin 1 3 2 n1 n3 n2 n13 n12 n23.symm e (hdist 2 1 n2 n1 n12.symm)
      (hdist 2 3 n2 n3 n23)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩
  · obtain ⟨σ, hσ⟩ := fin 3 1 2 n3 n1 n2 n13.symm n23.symm n12 e (hdist 2 3 n2 n3 n23)
      (hdist 2 1 n2 n1 n12.symm)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩
  · obtain ⟨σ, hσ⟩ := fin 2 3 1 n2 n3 n1 n23 n12.symm n13.symm e (hdist 1 2 n1 n2 n12)
      (hdist 1 3 n1 n3 n13)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩
  · obtain ⟨σ, hσ⟩ := fin 3 2 1 n3 n2 n1 n23.symm n13.symm n12.symm e (hdist 1 3 n1 n3 n13)
      (hdist 1 2 n1 n2 n12)
    exact ⟨σ, Or.inr ⟨h, hall, hσ⟩⟩

/-! ## Lemma 11 -/

theorem z7_lemma11 : ∀ x y t : ZMod 7, x ≠ 0 → y ≠ 0 → x ≠ y → t ≠ 0 →
    (x = 2 * y ∨ (x = 3 * y ∧ (y = t ∨ y = -t))) ∨
    (y = 2 * x ∨ (y = 3 * x ∧ (x = t ∨ x = -t))) ∨
    (y - x = 2 * -x ∨ (y - x = 3 * -x ∧ (-x = t ∨ -x = -t))) ∨
    (-x = 2 * (y - x) ∨ (-x = 3 * (y - x) ∧ (y - x = t ∨ y - x = -t))) ∨
    (x - y = 2 * -y ∨ (x - y = 3 * -y ∧ (-y = t ∨ -y = -t))) ∨
    (-y = 2 * (x - y) ∨ (-y = 3 * (x - y) ∧ (x - y = t ∨ x - y = -t))) := by
  decide

/-- **Lemma 11** (labeling, three elements of one class; `t` plays the role of `5s`). -/
theorem lemma11 (m : ℕ) (d : Fin 3 → ℕ) (hcl : ∀ i j, d i % 7 = d j % 7) (t : ZMod 7) (ht : t ≠ 0) :
    (∀ i j, E m (d i) (d j) = 0) ∨
    ∃ σ : Equiv.Perm (Fin 3),
      nu 7 (E m (d (σ 0)) (d (σ 2))) ≠ nu 7 (E m (d (σ 1)) (d (σ 2))) ∨
      ∃ h, (∀ i j, i ≠ j → E m (d i) (d j) ≠ 0 ∧ nu 7 (E m (d i) (d j)) = h) ∧
        (R (E m (d (σ 0)) (d (σ 2))) = 2 * R (E m (d (σ 1)) (d (σ 2))) ∨
         (R (E m (d (σ 0)) (d (σ 2))) = 3 * R (E m (d (σ 1)) (d (σ 2))) ∧
          (R (E m (d (σ 1)) (d (σ 2))) = t ∨ R (E m (d (σ 1)) (d (σ 2))) = -t))) := by
  by_cases hA : ∃ l i j : Fin 3, i ≠ l ∧ j ≠ l ∧ i ≠ j ∧
      nu 7 (E m (d i) (d l)) ≠ nu 7 (E m (d j) (d l))
  · obtain ⟨l, i, j, hil, hjl, hij, hne⟩ := hA
    obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 i j l hij hil hjl
    exact Or.inr ⟨σ, Or.inl (by rw [s0, s1, s2]; exact hne)⟩
  push Not at hA
  set h := nu 7 (E m (d 0) (d 2)) with hh
  have key2 : ∀ i : Fin 3, i ≠ 2 → nu 7 (E m (d i) (d 2)) = h := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
    · exact hA 2 i 0 hi (by decide) hi0
  have hall0 : ∀ i j, i ≠ j → nu 7 (E m (d i) (d j)) = h := by
    intro i j hij
    by_cases hj : j = 2
    · subst hj; exact key2 i hij
    by_cases hi : i = 2
    · subst hi; rw [nu_swap m (d j) (d 2)]; exact key2 j hj
    rw [hA j i 2 hij (Ne.symm hj) hi, nu_swap m (d j) (d 2)]; exact key2 j hj
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · left
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact E_self m _
    by_contra hne
    have := nu_pos_of_class m (d i) (d j) (hcl i j) hne
    rw [hall0 i j hij, h0] at this; omega
  right
  have hall : ∀ i j, i ≠ j → E m (d i) (d j) ≠ 0 ∧ nu 7 (E m (d i) (d j)) = h := by
    intro i j hij
    refine ⟨?_, hall0 i j hij⟩
    intro hz; have := hall0 i j hij; rw [hz, nu_zero] at this; omega
  have n02 : (0 : Fin 3) ≠ 2 := by decide
  have n12 : (1 : Fin 3) ≠ 2 := by decide
  have n01 : (0 : Fin 3) ≠ 1 := by decide
  have hxy : R (E m (d 0) (d 2)) ≠ R (E m (d 1) (d 2)) := by
    intro hR
    rcases (sub_rule m (d 0) (d 1) (d 2) h (hall 0 2 n02).1 (hall 1 2 n12).1 (hall 0 2 n02).2
      (hall 1 2 n12).2).1 hR with hz | hlt
    · exact (hall 0 1 n01).1 hz
    · rw [(hall 0 1 n01).2] at hlt; omega
  have S01 := ((sub_rule m (d 0) (d 1) (d 2) h (hall 0 2 n02).1 (hall 1 2 n12).1 (hall 0 2 n02).2
      (hall 1 2 n12).2).2 hxy).2.2
  have S10 := ((sub_rule m (d 1) (d 0) (d 2) h (hall 1 2 n12).1 (hall 0 2 n02).1 (hall 1 2 n12).2
      (hall 0 2 n02).2).2 (Ne.symm hxy)).2.2
  have W20 := (swap_rule m (d 0) (d 2) (hall 0 2 n02).1).2.2
  have W21 := (swap_rule m (d 1) (d 2) (hall 1 2 n12).1).2.2
  rcases z7_lemma11 _ _ t (R_ne_zero (hall 0 2 n02).1) (R_ne_zero (hall 1 2 n12).1) hxy ht with
    e | e | e | e | e | e
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 0 1 2 (by decide) (by decide) (by decide)
    exact ⟨σ, Or.inr ⟨h, hall, by rw [s0, s1, s2]; exact e⟩⟩
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 1 0 2 (by decide) (by decide) (by decide)
    exact ⟨σ, Or.inr ⟨h, hall, by rw [s0, s1, s2]; exact e⟩⟩
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 1 2 0 (by decide) (by decide) (by decide)
    refine ⟨σ, Or.inr ⟨h, hall, ?_⟩⟩
    rw [s0, s1, s2, S10, show R (E m (d 2) (d 0)) = - R (E m (d 0) (d 2)) from W20]; exact e
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 2 1 0 (by decide) (by decide) (by decide)
    refine ⟨σ, Or.inr ⟨h, hall, ?_⟩⟩
    rw [s0, s1, s2, S10, show R (E m (d 2) (d 0)) = - R (E m (d 0) (d 2)) from W20]; exact e
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 0 2 1 (by decide) (by decide) (by decide)
    refine ⟨σ, Or.inr ⟨h, hall, ?_⟩⟩
    rw [s0, s1, s2, S01, show R (E m (d 2) (d 1)) = - R (E m (d 1) (d 2)) from W21]; exact e
  · obtain ⟨σ, s0, s1, s2⟩ := mkPerm3 2 0 1 (by decide) (by decide) (by decide)
    refine ⟨σ, Or.inr ⟨h, hall, ?_⟩⟩
    rw [s0, s1, s2, S01, show R (E m (d 2) (d 1)) = - R (E m (d 1) (d 2)) from W21]; exact e

/-! ## finishing tools -/

theorem nu_zero_of_not_dvd {x : ℕ} (hx : ¬ 7 ∣ x) : nu 7 x = 0 := by
  unfold nu; exact padicValNat.eq_zero_of_not_dvd hx

theorem z7_solve : ∀ ρ K : ZMod 7, ρ ≠ 0 → ∃ c : ZMod 7, c * ρ = K := by decide

/-- The `Lambda_0` shift on classes: one `k` shifts every level-0 `x` with `r(x) = j ρ` by `j K`. -/
theorem shift_class (m : ℕ) (hm : 1 ≤ m) (ρ K : ZMod 7) (hρ : ρ ≠ 0) :
    ∃ k < 7, ∀ x, ¬ 7 ∣ x → ∀ j : ZMod 7, R x = j * ρ →
      (qq m ((1 + 7 ^ m * k) * x) : ZMod 7) = qq m x + j * K := by
  obtain ⟨c, hc⟩ := z7_solve ρ K hρ
  refine ⟨c.val, ZMod.val_lt c, ?_⟩
  intro x hx j hj
  have := qq_lam m 0 0 c.val x (by omega) le_rfl (ZMod.val_lt c) (nu_zero_of_not_dvd hx)
  simp only [Nat.sub_zero, if_true] at this
  rw [this, ZMod.natCast_zmod_val]
  have hR : ((rp 7 x : ℕ) : ZMod 7) = j * ρ := hj
  rw [hR, ← hc]; ring

theorem Lam0_coprime (m k : ℕ) (hm : 1 ≤ m) : Nat.Coprime (1 + 7 ^ m * k) 7 := by
  have : 1 + 7 ^ m * k ≡ 1 [MOD 7] := by
    have h7 : 7 ∣ 7 ^ m * k := Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) k
    obtain ⟨c, hc⟩ := h7
    unfold Nat.ModEq; rw [hc]; omega
  exact (coprime_of_modEq_one (by norm_num) this).1

theorem nat_avoid {v : ℕ} (hv : v < 7) (h0 : (v : ZMod 7) ≠ 0) (h6 : (v : ZMod 7) ≠ 6) : v ≠ 0 ∧ v ≠ 6 := by
  constructor
  · rintro rfl; exact h0 (by simp)
  · rintro rfl; exact h6 (by rfl)

theorem R_mul_unit {l x : ℕ} (hl : Nat.Coprime l 7) (hx : x ≠ 0) : R (l * x) = (l : ZMod 7) * R x := by
  unfold R; rw [rp_mul_unit (not_dvd_of_coprime hl) hx, ZMod.natCast_mod]; push_cast; ring

theorem R_of_not_dvd {x : ℕ} (hx : ¬ 7 ∣ x) : R x = ((x % 7 : ℕ) : ZMod 7) := by
  unfold R rp; rw [nu_zero_of_not_dvd hx, pow_zero, Nat.div_one]

theorem not_dvd_mul {l x : ℕ} (hl : Nat.Coprime l 7) (hx : ¬ 7 ∣ x) : ¬ 7 ∣ l * x := by
  intro h
  have hp : Nat.Prime 7 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact not_dvd_of_coprime hl h1
  · exact hx h1

/-- Bridge to the real statement: a multiplier `lam` prime to 7 that keeps every level-0 speed of
`S` off `q ∈ {0, 6}`, plus top speeds `T` (level `m`), gives a time `t = lam / 7^(m+1)`. -/
theorem witness_of_lam (m lam : ℕ) (hlam : Nat.Coprime lam 7) (S T : List ℕ)
    (hS : ∀ d ∈ S, qq m (lam * d) ≠ 0 ∧ qq m (lam * d) ≠ 6) (hT : ∀ d ∈ T, d ≠ 0 ∧ nu 7 d = m) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S ++ T, (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hl0 : lam ≠ 0 := by
    rintro rfl; simp at hlam
  refine ⟨(lam : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ), by positivity, ?_⟩
  intro d hd
  have heq : (lam : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ) * d = ((lam * d : ℕ) : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [heq]
  rcases List.mem_append.mp hd with h | h
  · obtain ⟨a, b⟩ := hS d h
    have := qarc_bridge_mid 7 m (7 ^ (m + 1)) (lam * d) (by norm_num) rfl a (by simpa using b)
    simpa using this
  · obtain ⟨a, b⟩ := hT d h
    have := qarc_bridge_top 7 m (7 ^ (m + 1)) (lam * d) (by norm_num) rfl (Nat.mul_ne_zero hl0 a)
      (by rw [nu_mul_coprime 7 lam d hlam hl0 a, b])
    simpa using this

/-- exact top-level shift: `x ≡ y + 7^m z` gives `q(μ x) = q(μ y) + μ z`. -/
theorem top_shift (m μ x y z : ℕ) (h : x ≡ y + 7 ^ m * z [MOD 7 ^ (m + 1)]) :
    (qq m (μ * x) : ZMod 7) = qq m (μ * y) + (μ : ZMod 7) * z := by
  have h1 : μ * x ≡ μ * y + 7 ^ m * (μ * z % 7) [MOD 7 ^ (m + 1)] := by
    have h2 := h.mul_left μ
    refine h2.trans ?_
    have h3 : μ * (y + 7 ^ m * z) = μ * y + 7 ^ m * (μ * z % 7) + 7 ^ (m + 1) * (μ * z / 7) := by
      have := Nat.div_add_mod (μ * z) 7
      rw [pow_succ]
      calc μ * (y + 7 ^ m * z) = μ * y + 7 ^ m * (μ * z) := by ring
        _ = μ * y + 7 ^ m * (7 * (μ * z / 7) + μ * z % 7) := by rw [this]
        _ = _ := by ring
    rw [h3]; unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
  unfold qq
  rw [qarc_congr h1, qarc_add_topmul 7 m (by norm_num) _ _ (Nat.mod_lt _ (by norm_num)),
    ZMod.natCast_mod]
  push_cast; rw [ZMod.natCast_mod]; push_cast; ring

/-- a multiplier `≡ 1 mod 7` keeps an exact top-level difference. -/
theorem top_keep {m lam x y z : ℕ} (hlam : lam ≡ 1 [MOD 7]) (h : x ≡ y + 7 ^ m * z [MOD 7 ^ (m + 1)]) :
    lam * x ≡ lam * y + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
  have h2 := h.mul_left lam
  rw [mul_add] at h2
  refine h2.trans (Nat.ModEq.add_left _ ?_)
  exact mul_modEq_self_of_dvd (v := m) (by omega) (by simpa using hlam) (dvd_mul_right _ _)

/-- **Lemma 7 (ii), extended**: `e(d, d') ≡ 7^m z` with `z < 7`, `z = 0` allowed (`m ≥ 2`). -/
theorem lemma7_ii_ext (m d d' z : ℕ) (X : Finset (ZMod 7)) (hm : 2 ≤ m) (hd : ¬ 7 ∣ d)
    (hd' : ¬ 7 ∣ d') (hr : rp 7 d' = 2 * rp 7 d % 7)
    (hz : ediff m d d' ≡ 7 ^ m * z [MOD 7 ^ (m + 1)])
    (hX : ¬ ((z : ZMod 7) ∈ X ∧ (z : ZMod 7) - 1 ∈ X)) :
    ∃ lam ∈ Lam 1 m 7, etilde m (lam * d) (lam * d') ∉ X := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero 7)
  have hd'0 : d' ≠ 0 := by rintro rfl; exact hd' (dvd_zero 7)
  have hN := N_pos m
  -- the identity e~(lam d, lam d') = z - c for lam in Lam 1
  have core : ∀ k < 7, ∀ c, qq m (2 * ((1 + 7 ^ (m - 1) * k) * d)) =
      (2 * qq m ((1 + 7 ^ (m - 1) * k) * d) + c) % 7 →
      etilde m ((1 + 7 ^ (m - 1) * k) * d) ((1 + 7 ^ (m - 1) * k) * d') = (z : ZMod 7) - c := by
    intro k hk c hq2
    set lam := 1 + 7 ^ (m - 1) * k with hlam
    have hlmem : lam ∈ Lam 1 m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    have h7 := Lam_modEq_seven (by omega) hlmem
    have hr' : rp 7 (lam * d') = 2 * rp 7 (lam * d) % 7 := by
      rw [rp_mul_of_modEq_one (by norm_num) h7 hd0, rp_mul_of_modEq_one (by norm_num) h7 hd'0]; exact hr
    rw [(ediff_branch1 m _ _ hr').2]
    have hb : 2 * d ≡ d' + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
      have := modEq_add_dsub (7 ^ (m + 1)) (2 * d) d' hN
      rw [← (ediff_branch1 m d d' hr).1] at this
      exact this.trans (hz.add_left _)
    have h2 : 2 * (lam * d) ≡ lam * d' + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
      rw [show 2 * (lam * d) = lam * (2 * d) by ring]; exact top_keep h7 hb
    have A := top_shift m 1 _ _ z h2
    simp only [one_mul, Nat.cast_one] at A
    have B : (qq m (2 * (lam * d)) : ZMod 7) = 2 * (qq m (lam * d) : ZMod 7) + c := by
      rw [hq2, ZMod.natCast_mod]; push_cast; ring
    linear_combination A - B
  by_cases hcase : (z : ZMod 7) ∉ X
  · obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := 1) (m := m) (x := 7 * d) (t := 0)
      (by norm_num) (by omega) (nu_seven_mul d hd) (by omega) (by norm_num)
    refine ⟨1 + 7 ^ (m - 1) * k, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, ?_⟩
    obtain ⟨c, hc, hq2, hc0, _⟩ := seven_carry m ((1 + 7 ^ (m - 1) * k) * d)
    have hc0' : c = 0 := hc0 (by unfold qq; rw [show 7 * ((1 + 7 ^ (m - 1) * k) * d) =
      (1 + 7 ^ (m - 1) * k) * (7 * d) by ring]; exact hkq)
    rw [core k hk c hq2, hc0']; simpa using hcase
  · have hX1 : (z : ZMod 7) - 1 ∉ X := by
      push Not at hcase; intro h; exact hX ⟨hcase, h⟩
    obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := 1) (m := m) (x := 7 * d) (t := 6)
      (by norm_num) (by omega) (nu_seven_mul d hd) (by omega) (by norm_num)
    refine ⟨1 + 7 ^ (m - 1) * k, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, ?_⟩
    obtain ⟨c, hc, hq2, _, hc6⟩ := seven_carry m ((1 + 7 ^ (m - 1) * k) * d)
    have hc1 : c = 1 := hc6 (by unfold qq; rw [show 7 * ((1 + 7 ^ (m - 1) * k) * d) =
      (1 + 7 ^ (m - 1) * k) * (7 * d) by ring]; exact hkq)
    rw [core k hk c hq2, hc1]; simpa using hX1

end LRSpectrumFull.BarajasSerra.Sec6
