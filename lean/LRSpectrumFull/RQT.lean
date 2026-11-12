/-
# RQ, module T: Theorem T (modulus `q ≥ 6`, two slow runners, two runners coprime to `q`)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem T (q >= 6)".
Structure in Lean (no measure theory):

* `q ≥ 7`, `q ≠ 8`: the pigeonhole `exists_two_good` (any two coprime runners, whatever their classes), with
  `lemSR2` for the slow runners.
* `q = 8`, different classes: Lemma C (`lemmaC_real`).
* same class (`q = 6` always, `q = 8` when `v b ≡ ± v a`): `T_same`.  Non-resonant: `QGen_core`.  Resonant
  (`u_i = |D|`): `resonant_x`, an explicit perturbation argument that replaces the paper's measure count:
  choose `z` with `‖z + σ‖ ≤ 3/10`, `‖z + φ₁‖ ≥ 3/10` (`exists_shift`), then either take the coset point
  `x = (k + z)/D` (if `D ∤ u₂`) or perturb `z` by `δ/t` with `|δ| ≤ 1/5`, `t = u₂/D`, `|t| ≥ 2`.
  The window needed is `2/5 ≤ 3/5 - 1/q`, i.e. `q ≥ 5`.
-/
import LRSpectrumFull.RQGen
import LRSpectrumFull.RQPigeon
import LRSpectrumFull.RQLemmaC

namespace LRSpectrumFull

lemma tpDist_perturb (y e : ℝ) : tpDist y ≤ tpDist (y + e) + |e| := by
  unfold tpDist
  have h := round_le y (round (y + e))
  have h2 : |y - (round (y + e) : ℝ)| ≤ |y + e - round (y + e)| + |e| := by
    rw [show y - (round (y + e) : ℝ) = (y + e - round (y + e)) + (-e) by ring]
    calc |(y + e - (round (y + e) : ℝ)) + (-e)| ≤ |y + e - round (y + e)| + |-e| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith

lemma abs_ge_of_int (c : ℝ) (hc : c = 3 / 10 ∨ c = -3 / 10) (d : ℤ) : 3 / 10 ≤ |c + d| := by
  rcases hc with rfl | rfl
  · rcases le_or_gt 0 d with h | h
    · have : (0 : ℝ) ≤ d := by exact_mod_cast h
      exact le_trans (by linarith) (le_abs_self _)
    · have : (d : ℝ) ≤ -1 := by exact_mod_cast (by omega : d ≤ -1)
      exact le_trans (by linarith) (neg_le_abs _)
  · rcases le_or_gt d 0 with h | h
    · have : (d : ℝ) ≤ 0 := by exact_mod_cast h
      exact le_trans (by linarith) (neg_le_abs _)
    · have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      exact le_trans (by linarith) (le_abs_self _)

/-- a shift of size at most `3/10` moves any `u` to distance at least `3/10` from `ℤ` -/
lemma exists_shift (u : ℝ) : ∃ r : ℝ, |r| ≤ 3 / 10 ∧ 3 / 10 ≤ tpDist (u + r) := by
  have hk : tpDist u = |u - (round u : ℤ)| := rfl
  by_cases h : 3 / 10 ≤ |u - (round u : ℤ)|
  · exact ⟨0, by norm_num, by rw [add_zero, hk]; exact h⟩
  · push Not at h
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    rcases le_or_gt 0 (u - (round u : ℤ)) with h0 | h0
    · refine ⟨3 / 10 - (u - (round u : ℤ)), abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      show 3 / 10 ≤ |_ - _|
      refine le_trans (abs_ge_of_int (3 / 10) (Or.inl rfl) (round u - round (u + (3 / 10 - (u - (round u : ℤ)))))) (le_of_eq ?_)
      congr 1
      push_cast
      ring
    · refine ⟨-3 / 10 - (u - (round u : ℤ)), abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      show 3 / 10 ≤ |_ - _|
      refine le_trans (abs_ge_of_int (-3 / 10) (Or.inr rfl) (round u - round (u + (-3 / 10 - (u - (round u : ℤ)))))) (le_of_eq ?_)
      congr 1
      push_cast
      ring

lemma resonant_x_pos (d : ℕ) (hd : 0 < d) (u₂ : ℕ) (hu2 : 0 < u₂) (hne : u₂ ≠ d) (φ₁ φ₂ σ : ℝ) :
    ∃ x : ℝ, GoodR d φ₁ x ∧ GoodR u₂ φ₂ x ∧ ∃ n : ℤ, |(d : ℝ) * x + σ - n| ≤ 2 / 5 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨r, hr1, hr2⟩ := exists_shift (φ₁ - σ)
  have hz2 : 3 / 10 ≤ tpDist ((-σ + r) + φ₁) := by
    have e : (-σ + r) + φ₁ = (φ₁ - σ) + r := by ring
    rw [e]; exact hr2
  by_cases hdvd : (d : ℤ) ∣ (u₂ : ℤ)
  · obtain ⟨t, ht⟩ := hdvd
    have ht2 : 2 ≤ t := by
      have h1 : 1 ≤ t := by
        by_contra hlt
        have : t ≤ 0 := by omega
        have : (d : ℤ) * t ≤ 0 := by nlinarith
        omega
      have h3 : t ≠ 1 := by
        rintro rfl
        apply hne
        omega
      omega
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    have htp : (0 : ℝ) < t := by linarith
    have hu2R : (u₂ : ℝ) = d * t := by exact_mod_cast ht
    obtain ⟨δ, hδ1, hδ2⟩ := exists_perturb ((t : ℝ) * (-σ + r) + φ₂)
    have hdx : (d : ℝ) * (((-σ + r) + δ / t) / d) = (-σ + r) + δ / t := mul_div_cancel₀ _ hdR.ne'
    have e1 : (t : ℝ) * (δ / t) = δ := mul_div_cancel₀ δ htp.ne'
    have hsmall : |δ / t| ≤ 1 / 10 := by
      rw [abs_div, abs_of_pos htp, div_le_iff₀ htp]
      linarith
    refine ⟨((-σ + r) + δ / t) / d, ?_, ?_, 0, ?_⟩
    · unfold GoodR
      have e : (d : ℝ) * (((-σ + r) + δ / t) / d) + φ₁ = ((-σ + r) + φ₁) + δ / t := by
        rw [hdx]; ring
      rw [e]
      have := tpDist_perturb ((-σ + r) + φ₁) (δ / t)
      linarith
    · unfold GoodR
      have e : (u₂ : ℝ) * (((-σ + r) + δ / t) / d) + φ₂ = ((t : ℝ) * (-σ + r) + φ₂) + δ := by
        rw [hu2R]
        linear_combination (t : ℝ) * hdx + e1
      rw [e]; exact hδ2
    · rw [hdx]
      have e : -σ + r + δ / t + σ - ((0 : ℤ) : ℝ) = r + δ / t := by push_cast; ring
      rw [e]
      calc |r + δ / t| ≤ |r| + |δ / t| := abs_add_le _ _
        _ ≤ 2 / 5 := by linarith
  · obtain ⟨k, hk⟩ := coset_branchR_ne (d : ℤ) (by exact_mod_cast hd.ne') u₂ hdvd (-(-σ + r)) φ₂
    have hdxk : (d : ℝ) * (((k : ℝ) + (-σ + r)) / d) = (k : ℝ) + (-σ + r) := mul_div_cancel₀ _ hdR.ne'
    refine ⟨((k : ℝ) + (-σ + r)) / d, ?_, ?_, k, ?_⟩
    · unfold GoodR
      have e : (d : ℝ) * (((k : ℝ) + (-σ + r)) / d) + φ₁ = ((-σ + r) + φ₁) + (k : ℤ) := by
        rw [hdxk]; ring
      rw [e, tpDist_add_int]
      linarith
    · unfold GoodR
      have e : ((k : ℝ) - (-(-σ + r))) / (((d : ℤ)) : ℝ) = ((k : ℝ) + (-σ + r)) / d := by
        push_cast; ring
      rw [e] at hk
      exact hk
    · rw [hdxk]
      have e : (k : ℝ) + (-σ + r) + σ - k = r := by ring
      rw [e]
      linarith

lemma resonant_x (D : ℤ) (hD : D ≠ 0) (u₂ : ℕ) (hu2 : 0 < u₂) (hne : u₂ ≠ D.natAbs) (φ₁ φ₂ σ : ℝ) :
    ∃ x : ℝ, GoodR D.natAbs φ₁ x ∧ GoodR u₂ φ₂ x ∧ ∃ n : ℤ, |(D : ℝ) * x + σ - n| ≤ 2 / 5 := by
  have pd : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  rcases Int.natAbs_eq D with hDd | hDd
  · obtain ⟨x, g1, g2, n, hn⟩ := resonant_x_pos D.natAbs pd u₂ hu2 hne φ₁ φ₂ σ
    refine ⟨x, g1, g2, n, ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = (D : ℝ) :=
      (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) hDd.symm)
    rwa [hdR] at hn
  · obtain ⟨x, g1, g2, n, hn⟩ := resonant_x_pos D.natAbs pd u₂ hu2 hne φ₁ φ₂ (-σ)
    refine ⟨x, g1, g2, -n, ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = -(D : ℝ) := by
      have : (D.natAbs : ℤ) = -D := by omega
      have h2 := (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) this)
      rw [h2, Int.cast_neg]
    rw [hdR] at hn
    have e : (D : ℝ) * x + σ - ((-n : ℤ) : ℝ) = -(-(D : ℝ) * x + -σ - n) := by push_cast; ring
    rw [e, abs_neg]
    exact hn

/-- Same-class case of `T` (`q ≥ 5`): resonant or not. -/
theorem T_same (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (q : ℕ)
    (hq : 5 ≤ q) (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (u₁ u₂ : ℕ) (hu₁ : v s₁ = q * u₁) (hu₂ : v s₂ = q * u₂)
    (ha : Nat.Coprime (v a) q) (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (v a : ℤ) - ε * v b = q * D)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  have hvab : v a ≠ v b := fun h => hab (hinj h)
  have hD0 : D ≠ 0 := D_neq q (v a) (v b) (hpos a) (hpos b) hvab ε D hε hD
  have p1 : 0 < u₁ := pos_of_mul_eq q u₁ (v s₁) (hpos s₁) hu₁
  have p2 : 0 < u₂ := pos_of_mul_eq q u₂ (v s₂) (hpos s₂) hu₂
  have u12 : u₁ ≠ u₂ := fun h => h12 (hinj (by rw [hu₁, hu₂, h]))
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have h1q : 1 / (q : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hqR
  by_cases r1 : u₁ = D.natAbs
  · have n2 : u₂ ≠ D.natAbs := fun h => u12 (r1.trans h.symm)
    obtain ⟨x, g1, g2, n, hn⟩ := resonant_x D hD0 u₂ p2 n2 (φ s₁) (φ s₂) (φ a - ε * φ b)
    rw [← r1] at g1
    exact finish_window v φ q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε hD
      x g1 g2 n (le_trans hn (by linarith))
  · by_cases r2 : u₂ = D.natAbs
    · obtain ⟨x, g2, g1, n, hn⟩ := resonant_x D hD0 u₁ p1 r1 (φ s₂) (φ s₁) (φ a - ε * φ b)
      rw [← r2] at g2
      exact finish_window v φ q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε hD
        x g1 g2 n (le_trans hn (by linarith))
    · exact QGen_core v hpos hinj q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D
        hε hD r1 r2 φ

/-- Theorem T: `q ≥ 6` divides the speeds `v s₁, v s₂`; `v a, v b` are coprime to `q`; four distinct positive
speeds, arbitrary real phases; no non-resonance hypothesis. -/
theorem T (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (q : ℕ) (hq : 6 ≤ q)
    (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (hs₁ : q ∣ v s₁) (hs₂ : q ∣ v s₂)
    (ha : Nat.Coprime (v a) q) (hb : Nat.Coprime (v b) q) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨u₁, hu₁⟩ := hs₁
  obtain ⟨u₂, hu₂⟩ := hs₂
  have p1 : 0 < u₁ := pos_of_mul_eq q u₁ (v s₁) (hpos s₁) hu₁
  have p2 : 0 < u₂ := pos_of_mul_eq q u₂ (v s₂) (hpos s₂) hu₂
  have u12 : u₁ ≠ u₂ := fun h => h12 (hinj (by rw [hu₁, hu₂, h]))
  have hq0 : 0 < q := by omega
  by_cases hbig : 7 ≤ q ∧ q ≠ 8
  · obtain ⟨x, g1, g2⟩ := lemSR2 u₁ u₂ p1 p2 u12 (φ s₁) (φ s₂)
    obtain ⟨j, ja, jb⟩ := exists_two_good q hbig.1 hbig.2 (v a) (v b) ha hb (φ a) (φ b) x
    exact assemble4 v φ q hq0 s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ x j g1 g2 ja jb
  · have hq68 : q = 6 ∨ q = 8 := by omega
    by_cases hcls : (q : ℤ) ∣ (v a : ℤ) - v b ∨ (q : ℤ) ∣ (v a : ℤ) + v b
    · obtain ⟨ε, D, hε, hD⟩ := eps_Dq q (v a) (v b) hcls
      exact T_same v hpos hinj q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε
        hD φ
    · rcases hq68 with rfl | rfl
      · exfalso
        apply hcls
        have na2 : ¬ 2 ∣ v a := fun h => absurd (Nat.Coprime.coprime_dvd_left h ha) (by decide)
        have na3 : ¬ 3 ∣ v a := fun h => absurd (Nat.Coprime.coprime_dvd_left h ha) (by decide)
        have nb2 : ¬ 2 ∣ v b := fun h => absurd (Nat.Coprime.coprime_dvd_left h hb) (by decide)
        have nb3 : ¬ 3 ∣ v b := fun h => absurd (Nat.Coprime.coprime_dvd_left h hb) (by decide)
        have ha6 : v a % 6 = 1 ∨ v a % 6 = 5 := by omega
        have hb6 : v b % 6 = 1 ∨ v b % 6 = 5 := by omega
        push_cast
        rcases ha6 with h | h <;> rcases hb6 with h' | h' <;> omega
      · have na2 : ¬ 2 ∣ v a := fun h => absurd (Nat.Coprime.coprime_dvd_left h ha) (by decide)
        have nb2 : ¬ 2 ∣ v b := fun h => absurd (Nat.Coprime.coprime_dvd_left h hb) (by decide)
        have hcls' : ¬((8 : ℤ) ∣ (v a : ℤ) - v b ∨ (8 : ℤ) ∣ (v a : ℤ) + v b) := by exact_mod_cast hcls
        have ha8 : v a % 8 = 1 ∨ v a % 8 = 3 ∨ v a % 8 = 5 ∨ v a % 8 = 7 := by omega
        have hb8 : v b % 8 = 1 ∨ v b % 8 = 3 ∨ v b % 8 = 5 ∨ v b % 8 = 7 := by omega
        have hμ : (8 : ℤ) ∣ (v b : ℤ) - 3 * v a ∨ (8 : ℤ) ∣ (v b : ℤ) - 5 * v a := by
          rcases ha8 with h | h | h | h <;> rcases hb8 with h' | h' | h' | h' <;> omega
        obtain ⟨μ, hμ35, hrel⟩ : ∃ μ : ℤ, (μ = 3 ∨ μ = 5) ∧
            (v b : ZMod 8) = (μ : ZMod 8) * (v a : ZMod 8) := by
          rcases hμ with h | h
          · refine ⟨3, Or.inl rfl, ?_⟩
            have := (ZMod.intCast_eq_intCast_iff_dvd_sub (3 * (v a : ℤ)) (v b : ℤ) 8).mpr
              (by exact_mod_cast h)
            push_cast at this ⊢
            exact this.symm
          · refine ⟨5, Or.inr rfl, ?_⟩
            have := (ZMod.intCast_eq_intCast_iff_dvd_sub (5 * (v a : ℤ)) (v b : ℤ) 8).mpr
              (by exact_mod_cast h)
            push_cast at this ⊢
            exact this.symm
        obtain ⟨x, g1, g2⟩ := lemSR2 u₁ u₂ p1 p2 u12 (φ s₁) (φ s₂)
        obtain ⟨j, ja, jb⟩ := lemmaC_real (v a) (v b) ha μ hμ35 hrel (φ a) (φ b) x
        exact assemble4 v φ 8 hq0 s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ x j g1 g2 ja jb

end LRSpectrumFull
