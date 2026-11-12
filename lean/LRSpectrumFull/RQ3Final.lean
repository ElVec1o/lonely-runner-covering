/-
# RQ3, module F: Theorem Q3 (modulus 3, two slow runners, two runners prime to 3, non-resonant), real phases

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem Q3", run exactly as `QGen` with `q = 3`:
the window `‖D x + σ‖ ≤ 3/5 - 1/3 = 4/15` replaces `3/10`; the slow-runner step is the mixed three-runner lemma
`q3Mix3` (thresholds `1/5, 1/5` for the two slow runners and `7/30` for the window runner, i.e.
`‖D x + σ + 1/2‖ ≥ 7/30`) in place of `lemSR3`.  `window_lemma`, `finish_window`, `eps_Dq`, `D_neq`,
`resonance_of` are reused from `RQGen`.

* `q3_exists_int_of_far` : `‖y + 1/2‖ ≥ 7/30` implies `y` is within `4/15` of `ℤ`.
* `q3_slow_window`       : the two slow runners good and `‖D x + σ‖ ≤ 4/15`.
* `Q3_core`              : the theorem with non-resonance as `u_i ≠ |D|`.
* `Q3`                   : the theorem; `Q3_ndvd`: the same with `¬ 3 ∣` in place of coprimality.
-/
import LRSpectrumFull.RQ3Mix
import LRSpectrumFull.RQGen

namespace LRSpectrumFull

lemma q3_exists_int_of_far (y : ℝ) (h : 7 / 30 ≤ tpDist (y + 1 / 2)) :
    ∃ n : ℤ, |y - n| ≤ 4 / 15 := by
  unfold tpDist at h
  have hle := abs_sub_round (y + 1 / 2)
  generalize round (y + 1 / 2) = r at h hle
  rcases le_or_gt 0 (y + 1 / 2 - r) with h0 | h0
  · refine ⟨r, ?_⟩
    rw [abs_of_nonneg h0] at h hle
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨r - 1, ?_⟩
    rw [abs_of_neg h0] at h hle
    push_cast
    rw [abs_le]
    constructor <;> linarith

lemma q3_slow_window (u₁ u₂ : ℕ) (D : ℤ) (p1 : 0 < u₁) (p2 : 0 < u₂) (hD0 : D ≠ 0) (u12 : u₁ ≠ u₂)
    (u1d : u₁ ≠ D.natAbs) (u2d : u₂ ≠ D.natAbs) (φ₁ φ₂ σ : ℝ) :
    ∃ x : ℝ, GoodR u₁ φ₁ x ∧ GoodR u₂ φ₂ x ∧ ∃ n : ℤ, |(D : ℝ) * x + σ - n| ≤ 4 / 15 := by
  have pd : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
  rcases Int.natAbs_eq D with hDd | hDd
  · obtain ⟨x, g1, g2, g3⟩ := q3Mix3 u₁ u₂ D.natAbs p1 p2 pd u12 u1d u2d φ₁ φ₂ (σ + 1 / 2)
    refine ⟨x, g1, g2, q3_exists_int_of_far _ ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = (D : ℝ) :=
      (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) hDd.symm)
    rw [hdR] at g3
    have e : (D : ℝ) * x + (σ + 1 / 2) = ((D : ℝ) * x + σ) + 1 / 2 := by ring
    rw [e] at g3
    exact g3
  · obtain ⟨x, g1, g2, g3⟩ := q3Mix3 u₁ u₂ D.natAbs p1 p2 pd u12 u1d u2d φ₁ φ₂ (-(σ + 1 / 2))
    refine ⟨x, g1, g2, q3_exists_int_of_far _ ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = -(D : ℝ) := by
      have : (D.natAbs : ℤ) = -D := by omega
      have h2 := (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) this)
      rw [h2, Int.cast_neg]
    rw [hdR] at g3
    have e : -(D : ℝ) * x + -(σ + 1 / 2) = -(((D : ℝ) * x + σ) + 1 / 2) := by ring
    rw [e, tpDist_neg] at g3
    exact g3

theorem Q3_core (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (u₁ u₂ : ℕ) (hu₁ : v s₁ = 3 * u₁) (hu₂ : v s₂ = 3 * u₂)
    (ha : Nat.Coprime (v a) 3) (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (v a : ℤ) - ε * v b = 3 * D)
    (n1 : u₁ ≠ D.natAbs) (n2 : u₂ ≠ D.natAbs) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  have hvab : v a ≠ v b := fun h => hab (hinj h)
  have hD' : (v a : ℤ) - ε * v b = ((3 : ℕ) : ℤ) * D := by exact_mod_cast hD
  have hD0 : D ≠ 0 := D_neq 3 (v a) (v b) (hpos a) (hpos b) hvab ε D hε hD'
  have p1 : 0 < u₁ := pos_of_mul_eq 3 u₁ (v s₁) (hpos s₁) hu₁
  have p2 : 0 < u₂ := pos_of_mul_eq 3 u₂ (v s₂) (hpos s₂) hu₂
  have u12 : u₁ ≠ u₂ := fun h => h12 (hinj (by rw [hu₁, hu₂, h]))
  obtain ⟨x, g1, g2, n, hn⟩ :=
    q3_slow_window u₁ u₂ D p1 p2 hD0 u12 n1 n2 (φ s₁) (φ s₂) (φ a - ε * φ b)
  exact finish_window v φ 3 (by norm_num) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε
    hD' x g1 g2 n (le_trans hn (by norm_num))

/-- Theorem Q3: `3` divides the speeds `v s₁, v s₂`; `v a, v b` are coprime to `3` (so congruent up to sign
mod `3`); no slow speed equals `v a + v b` or `|v a - v b|` (written without absolute value); four distinct
positive speeds, arbitrary real phases. -/
theorem Q3 (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (hs₁ : 3 ∣ v s₁) (hs₂ : 3 ∣ v s₂)
    (ha : Nat.Coprime (v a) 3) (hb : Nat.Coprime (v b) 3)
    (hr₁ : v s₁ ≠ v a + v b ∧ v a ≠ v b + v s₁ ∧ v b ≠ v a + v s₁)
    (hr₂ : v s₂ ≠ v a + v b ∧ v a ≠ v b + v s₂ ∧ v b ≠ v a + v s₂)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨u₁, hu₁⟩ := hs₁
  obtain ⟨u₂, hu₂⟩ := hs₂
  have na : ¬ 3 ∣ v a := fun h => absurd (Nat.Coprime.coprime_dvd_left h ha) (by decide)
  have nb : ¬ 3 ∣ v b := fun h => absurd (Nat.Coprime.coprime_dvd_left h hb) (by decide)
  have hcls : ((3 : ℕ) : ℤ) ∣ (v a : ℤ) - v b ∨ ((3 : ℕ) : ℤ) ∣ (v a : ℤ) + v b := by
    have ha3 : v a % 3 = 1 ∨ v a % 3 = 2 := by omega
    have hb3 : v b % 3 = 1 ∨ v b % 3 = 2 := by omega
    push_cast
    rcases ha3 with h | h <;> rcases hb3 with h' | h' <;> omega
  obtain ⟨ε, D, hε, hD⟩ := eps_Dq 3 (v a) (v b) hcls
  have hD3 : (v a : ℤ) - ε * v b = 3 * D := by exact_mod_cast hD
  refine Q3_core v hpos hinj s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε hD3 ?_ ?_ φ
  · intro h
    rcases resonance_of 3 (v a) (v b) (v s₁) u₁ ε D hε hD hu₁ h.symm with r | r | r
    · exact hr₁.1 r
    · exact hr₁.2.1 r
    · exact hr₁.2.2 r
  · intro h
    rcases resonance_of 3 (v a) (v b) (v s₂) u₂ ε D hε hD hu₂ h.symm with r | r | r
    · exact hr₂.1 r
    · exact hr₂.2.1 r
    · exact hr₂.2.2 r

/-- `Q3` with the divisibility hypotheses `¬ 3 ∣ v a`, `¬ 3 ∣ v b` in place of coprimality. -/
theorem Q3_ndvd (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (hs₁ : 3 ∣ v s₁) (hs₂ : 3 ∣ v s₂)
    (na : ¬ 3 ∣ v a) (nb : ¬ 3 ∣ v b)
    (hr₁ : v s₁ ≠ v a + v b ∧ v a ≠ v b + v s₁ ∧ v b ≠ v a + v s₁)
    (hr₂ : v s₂ ≠ v a + v b ∧ v a ≠ v b + v s₂ ∧ v b ≠ v a + v s₂)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t :=
  Q3 v hpos hinj s₁ s₂ a b h12 h1a h1b h2a h2b hab hs₁ hs₂
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr na))
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr nb)) hr₁ hr₂ φ

end LRSpectrumFull
