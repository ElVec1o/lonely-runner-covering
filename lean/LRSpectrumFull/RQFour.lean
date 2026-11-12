/-
# RQ, module F: Theorem Q4 (modulus 4, two slow runners, two odd runners, non-resonant)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem Q4".
Speeds `v s₁, v s₂ ≡ 0 (mod 4)`, `v a, v b` odd, `v a - ε v b = 4 D`.  The three runners `(v s₁/4, v s₂/4, |D|)` are
distinct and positive exactly when no slow speed equals `v a + v b` or `|v a - v b|` (non-resonance).  `lemSR3`
gives an offset `x` good for the two slow runners and for a window runner of speed `|D|` and phase `±(σ + 1/2)`;
hence `‖D x + σ‖ ≤ 3/10 ≤ 3/5 - 1/4` and `window_lemma` (q = 4) finishes.
-/
import LRSpectrumFull.RQThree

namespace LRSpectrumFull

lemma cover4 : ∀ s₁ s₂ a b i : Fin 4, s₁ ≠ s₂ → s₁ ≠ a → s₁ ≠ b → s₂ ≠ a → s₂ ≠ b → a ≠ b →
    i = s₁ ∨ i = s₂ ∨ i = a ∨ i = b := by
  decide

lemma eps_D4 (va vb : ℕ) (ha : va % 2 = 1) (hb : vb % 2 = 1) :
    ∃ ε D : ℤ, (ε = 1 ∨ ε = -1) ∧ (va : ℤ) - ε * vb = 4 * D := by
  by_cases hc : va % 4 = vb % 4
  · exact ⟨1, ((va : ℤ) - vb) / 4, Or.inl rfl, by omega⟩
  · exact ⟨-1, ((va : ℤ) + vb) / 4, Or.inr rfl, by omega⟩

lemma D_ne4 (va vb : ℕ) (pa : 0 < va) (pb : 0 < vb) (hne : va ≠ vb) (ε D : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vb = 4 * D) : D ≠ 0 := by
  intro h
  rcases hε with rfl | rfl <;> omega

lemma nonres4 (va vb vs : ℕ) (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vb = 4 * D)
    (h4 : 4 ∣ vs) (r1 : vs ≠ va + vb) (r2 : va ≠ vb + vs) (r3 : vb ≠ va + vs) :
    D.natAbs ≠ vs / 4 := by
  intro h
  rcases Int.natAbs_eq D with h' | h' <;> rcases hε with rfl | rfl <;> omega

lemma cop4 (n : ℕ) (h : n % 2 = 1) : Nat.Coprime n 4 := by
  have h2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h)
  simpa using Nat.Coprime.mul_right h2 h2

/-- Theorem Q4: `4` divides the speeds `v s₁, v s₂`; `v a, v b` are odd; no slow speed is `v a + v b` or
`|v a - v b|` (written without absolute value); four distinct positive speeds, any real phases. -/
theorem Q4 (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a) (h2b : s₂ ≠ b)
    (hab : a ≠ b) (hs₁ : 4 ∣ v s₁) (hs₂ : 4 ∣ v s₂) (ha : v a % 2 = 1) (hb : v b % 2 = 1)
    (hr₁ : v s₁ ≠ v a + v b ∧ v a ≠ v b + v s₁ ∧ v b ≠ v a + v s₁)
    (hr₂ : v s₂ ≠ v a + v b ∧ v a ≠ v b + v s₂ ∧ v b ≠ v a + v s₂)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  have hcov := cover4 s₁ s₂ a b
  obtain ⟨ε, D, hε, hD⟩ := eps_D4 (v a) (v b) ha hb
  have hvab : v a ≠ v b := fun h => hab (hinj h)
  have hD0 : D ≠ 0 := D_ne4 _ _ (hpos a) (hpos b) hvab ε D hε hD
  have pu1 : 0 < v s₁ / 4 := Nat.div_pos (Nat.le_of_dvd (hpos s₁) hs₁) (by norm_num)
  have pu2 : 0 < v s₂ / 4 := Nat.div_pos (Nat.le_of_dvd (hpos s₂) hs₂) (by norm_num)
  have pd : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
  have u12 : v s₁ / 4 ≠ v s₂ / 4 := by
    have : v s₁ ≠ v s₂ := fun h => h12 (hinj h)
    omega
  have u1d : v s₁ / 4 ≠ D.natAbs := fun h =>
    nonres4 _ _ _ ε D hε hD hs₁ hr₁.1 hr₁.2.1 hr₁.2.2 h.symm
  have u2d : v s₂ / 4 ≠ D.natAbs := fun h =>
    nonres4 _ _ _ ε D hε hD hs₂ hr₂.1 hr₂.2.1 hr₂.2.2 h.symm
  have hq4 : (0 : ℕ) < 4 := by norm_num
  have key : ∀ x : ℝ, GoodR (v s₁ / 4) (φ s₁) x → GoodR (v s₂ / 4) (φ s₂) x →
      (∃ n : ℤ, |(D : ℝ) * x + (φ a - ε * φ b) - n| ≤ 3 / 10) →
      ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
    intro x g1 g2 hwin
    obtain ⟨n, hn⟩ := hwin
    obtain ⟨j, ja, jb⟩ := window_lemma 4 (by norm_num) (v a) (v b) (cop4 _ ha) ε D hε hD
      (φ a) (φ b) x n (le_trans hn (by norm_num))
    refine ⟨((j : ℝ) + x) / ((4 : ℕ) : ℝ), fun i => ?_⟩
    rcases hcov i h12 h1a h1b h2a h2b hab with h | h | h | h
    · rw [h]
      obtain ⟨u, hu⟩ := hs₁
      rw [hu, Nat.mul_div_cancel_left u hq4] at g1
      rw [hu]
      exact (goodR_mulq 4 u hq4 _ x j).2 g1
    · rw [h]
      obtain ⟨u, hu⟩ := hs₂
      rw [hu, Nat.mul_div_cancel_left u hq4] at g2
      rw [hu]
      exact (goodR_mulq 4 u hq4 _ x j).2 g2
    · rw [h]; exact ja
    · rw [h]; exact jb
  rcases Int.natAbs_eq D with hDd | hDd
  · obtain ⟨x, g1, g2, g3⟩ := lemSR3 (v s₁ / 4) (v s₂ / 4) D.natAbs pu1 pu2 pd u12 u1d u2d
      (φ s₁) (φ s₂) ((φ a - ε * φ b) + 1 / 2)
    refine key x g1 g2 (exists_int_of_far _ ?_)
    have hdR : ((D.natAbs : ℕ) : ℝ) = (D : ℝ) :=
      (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) hDd.symm)
    unfold GoodR at g3
    rw [hdR] at g3
    have e : (D : ℝ) * x + ((φ a - ε * φ b) + 1 / 2) = ((D : ℝ) * x + (φ a - ε * φ b)) + 1 / 2 := by
      ring
    rw [e] at g3
    exact g3
  · obtain ⟨x, g1, g2, g3⟩ := lemSR3 (v s₁ / 4) (v s₂ / 4) D.natAbs pu1 pu2 pd u12 u1d u2d
      (φ s₁) (φ s₂) (-((φ a - ε * φ b) + 1 / 2))
    refine key x g1 g2 (exists_int_of_far _ ?_)
    have hdR : ((D.natAbs : ℕ) : ℝ) = -(D : ℝ) := by
      have : (D.natAbs : ℤ) = -D := by omega
      have h2 := (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) this)
      rw [h2, Int.cast_neg]
    unfold GoodR at g3
    rw [hdR] at g3
    have e : -(D : ℝ) * x + -((φ a - ε * φ b) + 1 / 2)
        = -(((D : ℝ) * x + (φ a - ε * φ b)) + 1 / 2) := by ring
    rw [e, tpDist_neg] at g3
    exact g3

end LRSpectrumFull
