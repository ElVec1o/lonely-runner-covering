/-
# RQ, module G: the general same-class lemma `QGen` (every modulus `q ≥ 4`)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, Theorem Q4, run for a general modulus `q ≥ 4`
(the block-1 seat's observation: the window threshold `3/10 ≤ 3/5 - 1/q` holds exactly for `q ≥ 4`).

`q` divides the speeds `v s₁, v s₂`; `v a, v b` are coprime to `q` and `v a ≡ ± v b (mod q)`; no slow speed is
`v a + v b` or `|v a - v b|`.  New lemmas only; `RQFour.lean` is not edited.

* `assemble4`    : slow runners good at `x`, `a`, `b` good at `(j + x)/q`  =>  a good time for all four runners.
* `finish_window`: `window_lemma` + `assemble4`.
* `slow_window`  : `lemSR3` on `(u₁, u₂, |D|)` gives `x` with both slow runners good and `‖D x + σ‖ ≤ 3/10`.
* `QGen_core`    : the theorem with the non-resonance stated as `u_i ≠ |D|`.
* `QGen`         : the theorem with the non-resonance stated on the speeds.
-/
import LRSpectrumFull.RQFour

namespace LRSpectrumFull

lemma assemble4 (v : Fin 4 → ℕ) (φ : Fin 4 → ℝ) (q : ℕ) (hq : 0 < q) (s₁ s₂ a b : Fin 4)
    (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a) (h2b : s₂ ≠ b) (hab : a ≠ b)
    (u₁ u₂ : ℕ) (hu₁ : v s₁ = q * u₁) (hu₂ : v s₂ = q * u₂) (x : ℝ) (j : ℤ)
    (g1 : GoodR u₁ (φ s₁) x) (g2 : GoodR u₂ (φ s₂) x)
    (ja : GoodR (v a) (φ a) (((j : ℝ) + x) / q)) (jb : GoodR (v b) (φ b) (((j : ℝ) + x) / q)) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  refine ⟨((j : ℝ) + x) / q, fun i => ?_⟩
  rcases cover4 s₁ s₂ a b i h12 h1a h1b h2a h2b hab with h | h | h | h
  · rw [h, hu₁]; exact (goodR_mulq q u₁ hq _ x j).2 g1
  · rw [h, hu₂]; exact (goodR_mulq q u₂ hq _ x j).2 g2
  · rw [h]; exact ja
  · rw [h]; exact jb

lemma finish_window (v : Fin 4 → ℕ) (φ : Fin 4 → ℝ) (q : ℕ) (hq : 2 ≤ q) (s₁ s₂ a b : Fin 4)
    (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a) (h2b : s₂ ≠ b) (hab : a ≠ b)
    (u₁ u₂ : ℕ) (hu₁ : v s₁ = q * u₁) (hu₂ : v s₂ = q * u₂) (ha : Nat.Coprime (v a) q)
    (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (v a : ℤ) - ε * v b = q * D) (x : ℝ)
    (g1 : GoodR u₁ (φ s₁) x) (g2 : GoodR u₂ (φ s₂) x) (n : ℤ)
    (hn : |(D : ℝ) * x + (φ a - ε * φ b) - n| ≤ 3 / 5 - 1 / q) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨j, ja, jb⟩ := window_lemma q hq (v a) (v b) ha ε D hε hD (φ a) (φ b) x n hn
  exact assemble4 v φ q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ x j g1 g2 ja jb

lemma eps_Dq (q : ℕ) (va vb : ℕ) (h : (q : ℤ) ∣ (va : ℤ) - vb ∨ (q : ℤ) ∣ (va : ℤ) + vb) :
    ∃ ε D : ℤ, (ε = 1 ∨ ε = -1) ∧ (va : ℤ) - ε * vb = q * D := by
  rcases h with ⟨D, hD⟩ | ⟨D, hD⟩
  · exact ⟨1, D, Or.inl rfl, by linear_combination hD⟩
  · exact ⟨-1, D, Or.inr rfl, by linear_combination hD⟩

lemma D_neq (q va vb : ℕ) (pa : 0 < va) (pb : 0 < vb) (hne : va ≠ vb) (ε D : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vb = q * D) : D ≠ 0 := by
  intro h
  subst h
  rcases hε with rfl | rfl <;> omega

lemma pos_of_mul_eq (q u w : ℕ) (hw : 0 < w) (h : w = q * u) : 0 < u :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)

/-- a slow speed `q u` equal to `|va - ε vb|` is a resonance `vs = va + vb` or `|va - vb|` -/
lemma resonance_of (q va vb vs u : ℕ) (ε D : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hD : (va : ℤ) - ε * vb = q * D) (hvs : vs = q * u) (h : D.natAbs = u) :
    vs = va + vb ∨ va = vb + vs ∨ vb = va + vs := by
  have hvsZ : (vs : ℤ) = (q : ℤ) * u := by exact_mod_cast hvs
  have hD2 : D = u ∨ D = -(u : ℤ) := by
    rcases Int.natAbs_eq D with h' | h'
    · left; omega
    · right; omega
  rcases hD2 with h2 | h2
  · rw [h2] at hD
    generalize (q : ℤ) * (u : ℤ) = w at hD hvsZ
    rcases hε with rfl | rfl <;> omega
  · rw [h2, mul_neg] at hD
    generalize (q : ℤ) * (u : ℤ) = w at hD hvsZ
    rcases hε with rfl | rfl <;> omega

lemma slow_window (u₁ u₂ : ℕ) (D : ℤ) (p1 : 0 < u₁) (p2 : 0 < u₂) (hD0 : D ≠ 0) (u12 : u₁ ≠ u₂)
    (u1d : u₁ ≠ D.natAbs) (u2d : u₂ ≠ D.natAbs) (φ₁ φ₂ σ : ℝ) :
    ∃ x : ℝ, GoodR u₁ φ₁ x ∧ GoodR u₂ φ₂ x ∧ ∃ n : ℤ, |(D : ℝ) * x + σ - n| ≤ 3 / 10 := by
  have pd : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
  rcases Int.natAbs_eq D with hDd | hDd
  · obtain ⟨x, g1, g2, g3⟩ := lemSR3 u₁ u₂ D.natAbs p1 p2 pd u12 u1d u2d φ₁ φ₂ (σ + 1 / 2)
    refine ⟨x, g1, g2, exists_int_of_far _ ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = (D : ℝ) :=
      (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) hDd.symm)
    unfold GoodR at g3
    rw [hdR] at g3
    have e : (D : ℝ) * x + (σ + 1 / 2) = ((D : ℝ) * x + σ) + 1 / 2 := by ring
    rw [e] at g3
    exact g3
  · obtain ⟨x, g1, g2, g3⟩ := lemSR3 u₁ u₂ D.natAbs p1 p2 pd u12 u1d u2d φ₁ φ₂ (-(σ + 1 / 2))
    refine ⟨x, g1, g2, exists_int_of_far _ ?_⟩
    have hdR : ((D.natAbs : ℕ) : ℝ) = -(D : ℝ) := by
      have : (D.natAbs : ℤ) = -D := by omega
      have h2 := (Int.cast_natCast (R := ℝ) D.natAbs).symm.trans (congrArg (Int.cast : ℤ → ℝ) this)
      rw [h2, Int.cast_neg]
    unfold GoodR at g3
    rw [hdR] at g3
    have e : -(D : ℝ) * x + -(σ + 1 / 2) = -(((D : ℝ) * x + σ) + 1 / 2) := by ring
    rw [e, tpDist_neg] at g3
    exact g3

theorem QGen_core (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (q : ℕ)
    (hq : 4 ≤ q) (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (u₁ u₂ : ℕ) (hu₁ : v s₁ = q * u₁) (hu₂ : v s₂ = q * u₂)
    (ha : Nat.Coprime (v a) q) (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (v a : ℤ) - ε * v b = q * D)
    (n1 : u₁ ≠ D.natAbs) (n2 : u₂ ≠ D.natAbs) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  have hvab : v a ≠ v b := fun h => hab (hinj h)
  have hD0 : D ≠ 0 := D_neq q (v a) (v b) (hpos a) (hpos b) hvab ε D hε hD
  have p1 : 0 < u₁ := pos_of_mul_eq q u₁ (v s₁) (hpos s₁) hu₁
  have p2 : 0 < u₂ := pos_of_mul_eq q u₂ (v s₂) (hpos s₂) hu₂
  have u12 : u₁ ≠ u₂ := fun h => h12 (hinj (by rw [hu₁, hu₂, h]))
  obtain ⟨x, g1, g2, n, hn⟩ := slow_window u₁ u₂ D p1 p2 hD0 u12 n1 n2 (φ s₁) (φ s₂) (φ a - ε * φ b)
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have h1q : 1 / (q : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hqR
  exact finish_window v φ q (by omega) s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε hD x
    g1 g2 n (le_trans hn (by linarith))

/-- `QGen`: modulus `q ≥ 4` divides the two speeds `v s₁, v s₂`; `v a, v b` are coprime to `q` and congruent
up to sign mod `q`; no slow speed equals `v a + v b` or `|v a - v b|` (written without absolute values);
four distinct positive speeds, arbitrary real phases. -/
theorem QGen (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (q : ℕ)
    (hq : 4 ≤ q) (s₁ s₂ a b : Fin 4) (h12 : s₁ ≠ s₂) (h1a : s₁ ≠ a) (h1b : s₁ ≠ b) (h2a : s₂ ≠ a)
    (h2b : s₂ ≠ b) (hab : a ≠ b) (hs₁ : q ∣ v s₁) (hs₂ : q ∣ v s₂)
    (ha : Nat.Coprime (v a) q) (hb : Nat.Coprime (v b) q)
    (hcls : (q : ℤ) ∣ (v a : ℤ) - v b ∨ (q : ℤ) ∣ (v a : ℤ) + v b)
    (hr₁ : v s₁ ≠ v a + v b ∧ v a ≠ v b + v s₁ ∧ v b ≠ v a + v s₁)
    (hr₂ : v s₂ ≠ v a + v b ∧ v a ≠ v b + v s₂ ∧ v b ≠ v a + v s₂)
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨u₁, hu₁⟩ := hs₁
  obtain ⟨u₂, hu₂⟩ := hs₂
  obtain ⟨ε, D, hε, hD⟩ := eps_Dq q (v a) (v b) hcls
  refine QGen_core v hpos hinj q hq s₁ s₂ a b h12 h1a h1b h2a h2b hab u₁ u₂ hu₁ hu₂ ha ε D hε hD ?_ ?_ φ
  · intro h
    rcases resonance_of q (v a) (v b) (v s₁) u₁ ε D hε hD hu₁ h.symm with r | r | r
    · exact hr₁.1 r
    · exact hr₁.2.1 r
    · exact hr₁.2.2 r
  · intro h
    rcases resonance_of q (v a) (v b) (v s₂) u₂ ε D hε hD hu₂ h.symm with r | r | r
    · exact hr₂.1 r
    · exact hr₂.2.1 r
    · exact hr₂.2.2 r

end LRSpectrumFull
