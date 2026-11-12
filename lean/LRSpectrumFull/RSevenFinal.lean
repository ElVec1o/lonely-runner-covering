/-
# R7-partial, module F: the theorems for four speeds, exactly one divisible by 7

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem R7-partial".
Setting: `v : Fin 4 → ℕ` pairwise distinct and positive, arbitrary real phases, indices `s, a, b, c` pairwise distinct,
`7 ∣ v s`, and `7 ∤ v a, v b, v c`.  Classes of the free speeds: `x ~ y` iff `7 ∣ x - y` or `7 ∣ x + y`.

* `R7A`        : pattern (A): `a ~ b` and `a ~ c` (all three free speeds in one class).
* `R7B`        : pattern (B): `b ~ c`, `a ≁ b`, and NOT [`v s ∈ {v b + v c, |v b - v c|}` and `v b ≡ ± 3 v a`].
* `R7_partial` : the disjunction of the two patterns.  Pattern (C) (three classes) and the excluded sub-case of (B)
                 (this is where `(1,3,4,7)` lives) are NOT covered.
-/
import LRSpectrumFull.RSevenA
import LRSpectrumFull.RSevenB

namespace LRSpectrumFull

lemma eps_D7 (x y : ℕ) (h : (7 : ℤ) ∣ (x : ℤ) - y ∨ (7 : ℤ) ∣ (x : ℤ) + y) :
    ∃ ε D : ℤ, (ε = 1 ∨ ε = -1) ∧ (x : ℤ) - ε * y = ((7 : ℕ) : ℤ) * D := by
  rcases h with ⟨D, hD⟩ | ⟨D, hD⟩
  · exact ⟨1, D, Or.inl rfl, by push_cast; linear_combination hD⟩
  · exact ⟨-1, D, Or.inr rfl, by push_cast; linear_combination hD⟩

lemma cop7 (n : ℕ) (h : ¬ 7 ∣ n) : Nat.Coprime n 7 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h)

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
lemma fin7 : ∀ μ y : ZMod 7, y ≠ 0 → μ ≠ 0 → μ ≠ 1 → μ ≠ -1 →
    ¬ (y = 3 * (μ * y) ∨ y = -3 * (μ * y)) → μ = 3 ∨ μ = -3 := by
  decide

lemma finish7 (v : Fin 4 → ℕ) (φ : Fin 4 → ℝ) (s a b c : Fin 4)
    (hall : ∀ i, i = s ∨ i = a ∨ i = b ∨ i = c) (w : ℕ) (hw : v s = 7 * w) (x : ℝ)
    (hx : 1 / 5 ≤ tpDist ((w : ℝ) * x + φ s)) (j : ℤ)
    (ga : GoodR (v a) (φ a) (((j : ℝ) + x) / ((7 : ℕ) : ℝ)))
    (gb : GoodR (v b) (φ b) (((j : ℝ) + x) / ((7 : ℕ) : ℝ)))
    (gc : GoodR (v c) (φ c) (((j : ℝ) + x) / ((7 : ℕ) : ℝ))) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  refine ⟨((j : ℝ) + x) / ((7 : ℕ) : ℝ), fun i => ?_⟩
  rcases hall i with h | h | h | h
  · rw [h, hw]
    exact (goodR_mulq 7 w (by norm_num) (φ s) x j).2 hx
  · rw [h]; exact ga
  · rw [h]; exact gb
  · rw [h]; exact gc

/-- Pattern (A): the three speeds not divisible by 7 lie pairwise in one class mod 7. -/
theorem R7A (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s a b c : Fin 4) (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hs : 7 ∣ v s) (ha : ¬ 7 ∣ v a) (hb : ¬ 7 ∣ v b) (hc : ¬ 7 ∣ v c)
    (hab7 : (7 : ℤ) ∣ (v a : ℤ) - v b ∨ (7 : ℤ) ∣ (v a : ℤ) + v b)
    (hac7 : (7 : ℤ) ∣ (v a : ℤ) - v c ∨ (7 : ℤ) ∣ (v a : ℤ) + v c) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨w, hw⟩ := hs
  have hw1 : 1 ≤ w := by have := hpos s; omega
  obtain ⟨εb, Db, hεb, hDb⟩ := eps_D7 (v a) (v b) hab7
  obtain ⟨εc, Dc, hεc, hDc⟩ := eps_D7 (v a) (v c) hac7
  have hDb0 : Db ≠ 0 :=
    D_neq 7 (v a) (v b) (hpos a) (hpos b) (fun h => hab (hinj h)) εb Db hεb hDb
  have hDc0 : Dc ≠ 0 :=
    D_neq 7 (v a) (v c) (hpos a) (hpos c) (fun h => hac (hinj h)) εc Dc hεc hDc
  have hDne : Db ≠ Dc := by
    intro h
    apply hbc
    apply hinj
    have e1 : (v a : ℤ) - εb * v b = 7 * Db := by exact_mod_cast hDb
    have e2 : (v a : ℤ) - εc * v c = 7 * Dc := by exact_mod_cast hDc
    have hb0 := hpos b
    have hc0 := hpos c
    subst h
    rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
  obtain ⟨x, hx, j, ga, gb, gc⟩ := r7CaseA 7 (by norm_num) (by norm_num) w hw1 (v a) (v b) (v c)
    (φ a) (φ b) (φ c) (φ s) εb εc hεb hεc (cop7 _ ha) (cop7 _ hb) (cop7 _ hc) Db Dc hDb hDc
    hDb0 hDc0 hDne
  exact finish7 v φ s a b c (fun i => cover4 s a b c i hsa hsb hsc hab hac hbc) w hw x hx j ga gb gc

/-- Pattern (B): `b ~ c`, `a ≁ b`, and not [`v s = v b + v c` or `|v b - v c| = v s`, together with `v b ≡ ±3 v a`]. -/
theorem R7B (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s a b c : Fin 4) (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hs : 7 ∣ v s) (ha : ¬ 7 ∣ v a) (hb : ¬ 7 ∣ v b) (hc : ¬ 7 ∣ v c)
    (hbc7 : (7 : ℤ) ∣ (v b : ℤ) - v c ∨ (7 : ℤ) ∣ (v b : ℤ) + v c)
    (hab7 : ¬ ((7 : ℤ) ∣ (v a : ℤ) - v b ∨ (7 : ℤ) ∣ (v a : ℤ) + v b))
    (hex : ¬ ((v s = v b + v c ∨ v b = v c + v s ∨ v c = v b + v s) ∧
      ((7 : ℤ) ∣ (v b : ℤ) - 3 * v a ∨ (7 : ℤ) ∣ (v b : ℤ) + 3 * v a)))
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := hs
  have hw1 : 1 ≤ w := by have := hpos s; omega
  obtain ⟨ε, D, hε, hD⟩ := eps_D7 (v b) (v c) hbc7
  have hD0 : D ≠ 0 := D_neq 7 (v b) (v c) (hpos b) (hpos c) (fun h => hbc (hinj h)) ε D hε hD
  have hb0 : (v b : ZMod 7) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff _ 7).mp h)
  obtain ⟨μ, hμdef⟩ : ∃ μ : ZMod 7, μ = (v a : ZMod 7) / (v b : ZMod 7) := ⟨_, rfl⟩
  have hμ : (v a : ZMod 7) = μ * (v b : ZMod 7) := by rw [hμdef]; field_simp
  have hμ0 : μ ≠ 0 := by
    intro h
    apply ha
    apply (ZMod.natCast_eq_zero_iff _ 7).mp
    rw [hμ, h, zero_mul]
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, one_mul] at hμ
    apply hab7
    left
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((v a : ℤ) - v b) 7).mp
      (by push_cast; rw [hμ]; ring)
    exact_mod_cast this
  have hμ2 : μ ≠ -1 := by
    intro h
    rw [h] at hμ
    apply hab7
    right
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((v a : ℤ) + v b) 7).mp
      (by push_cast; rw [hμ]; ring)
    exact_mod_cast this
  have hres : D.natAbs = w → μ = 3 ∨ μ = -3 := by
    intro hnat
    have hr := resonance_of 7 (v b) (v c) (v s) w ε D hε hD hw hnat
    have hno : ¬ ((7 : ℤ) ∣ (v b : ℤ) - 3 * v a ∨ (7 : ℤ) ∣ (v b : ℤ) + 3 * v a) :=
      fun h => hex ⟨hr, h⟩
    apply fin7 μ (v b) hb0 hμ0 hμ1 hμ2
    rintro (h | h)
    · apply hno
      left
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((v b : ℤ) - 3 * v a) 7).mp
        (by push_cast; rw [hμ]; linear_combination h)
      exact_mod_cast this
    · apply hno
      right
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((v b : ℤ) + 3 * v a) 7).mp
        (by push_cast; rw [hμ]; linear_combination h)
      exact_mod_cast this
  obtain ⟨x, hx, j, gb, gc, ga⟩ := r7CaseB 7 rfl w hw1 (v b) (v c) (v a) (φ b) (φ c) (φ a) (φ s) ε D
    hε (cop7 _ hb) hD hD0 μ hμ hμ0 hμ1 hμ2 hres
  exact finish7 v φ s a b c (fun i => cover4 s a b c i hsa hsb hsc hab hac hbc) w hw x hx j ga gb gc

/-- Theorem R7-partial: exactly one speed `v s` divisible by 7, the other three (`a, b, c`) not, in pattern (A) or (B). -/
theorem R7_partial (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (s a b c : Fin 4) (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hs : 7 ∣ v s) (ha : ¬ 7 ∣ v a) (hb : ¬ 7 ∣ v b) (hc : ¬ 7 ∣ v c)
    (hpat : (((7 : ℤ) ∣ (v a : ℤ) - v b ∨ (7 : ℤ) ∣ (v a : ℤ) + v b) ∧
        ((7 : ℤ) ∣ (v a : ℤ) - v c ∨ (7 : ℤ) ∣ (v a : ℤ) + v c)) ∨
      (((7 : ℤ) ∣ (v b : ℤ) - v c ∨ (7 : ℤ) ∣ (v b : ℤ) + v c) ∧
        ¬ ((7 : ℤ) ∣ (v a : ℤ) - v b ∨ (7 : ℤ) ∣ (v a : ℤ) + v b) ∧
        ¬ ((v s = v b + v c ∨ v b = v c + v s ∨ v c = v b + v s) ∧
          ((7 : ℤ) ∣ (v b : ℤ) - 3 * v a ∨ (7 : ℤ) ∣ (v b : ℤ) + 3 * v a))))
    (φ : Fin 4 → ℝ) : ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  rcases hpat with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact R7A v hpos hinj s a b c hsa hsb hsc hab hac hbc hs ha hb hc h1 h2 φ
  · exact R7B v hpos hinj s a b c hsa hsb hsc hab hac hbc hs ha hb hc h1 h2 h3 φ

end LRSpectrumFull
