/-
# TP'(4), module M8a: extraction of the three free runners and the dispatch Case 2+1 / Case 3

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Sections 2-4 (the split of Case H by the classes
`±1`, `±2` of the free speeds mod 5).

`Case3` is the single remaining hard configuration: the pinned case in which the three free speeds lie in one
class `{r, -r}` mod 5.  This module proves `caseH_of_case3 : Case3 → CaseH` (Case 2+1 by `case21`; the
extraction of `a, b, c` from `Fin 4 \ {z}`; the pinned runner by `good_pinned`).
-/
import LRSpectrumFull.TPFourCase21
import LRSpectrumFull.TPFourReduce

namespace LRSpectrumFull

/-- Any two nonzero residues mod 5 are in the same class (`b = ± a`) or in different classes (`b = 2 a`, `3 a`). -/
lemma ratio_class (a b : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0) :
    b = a ∨ b = -a ∨ b = 2 * a ∨ b = 3 * a := by
  revert a b; decide

/-- The pinned runner (speed `5 w`, phase `5 q / 5`) at time `(j + x) / 5` is good iff `‖w x‖ ≥ 1/5`. -/
lemma good_pinned (u : ℕ) (hu5 : 5 ∣ u) (s : ℤ) (hs : (5 : ℤ) ∣ s) (j : ℕ) (x : ℝ)
    (h : 1 / 5 ≤ tpDist (((u / 5 : ℕ) : ℝ) * x)) : Good u s (((j : ℝ) + x) / 5) := by
  obtain ⟨w, rfl⟩ := hu5
  obtain ⟨q, hq⟩ := hs
  rw [good_mul5]
  unfold Good
  have e : (w : ℝ) * x + (s : ℝ) / 5 = (w : ℝ) * x + ((q : ℤ) : ℝ) := by
    rw [hq]; push_cast; ring
  rw [e, tpDist_add_int]
  have e2 : 5 * w / 5 = w := by omega
  rw [e2] at h
  exact h

/-- The three free runners and the pinned one are all good at `(j + x) / 5`. -/
lemma finish_four (v : Fin 4 → ℕ) (s : Fin 4 → ℤ) (z a b c : Fin 4)
    (hall : ∀ i, i = z ∨ i = a ∨ i = b ∨ i = c) (hz5 : 5 ∣ v z) (hzs : (5 : ℤ) ∣ s z)
    (x : ℝ) (hx : 1 / 5 ≤ tpDist (((v z / 5 : ℕ) : ℝ) * x)) (j : ZMod 5)
    (ha : Good (v a) (s a) ((((j.val : ℕ) : ℝ) + x) / 5))
    (hb : Good (v b) (s b) ((((j.val : ℕ) : ℝ) + x) / 5))
    (hc : Good (v c) (s c) ((((j.val : ℕ) : ℝ) + x) / 5)) :
    ∃ t : ℝ, ∀ i, Good (v i) (s i) t := by
  refine ⟨(((j.val : ℕ) : ℝ) + x) / 5, fun i => ?_⟩
  rcases hall i with h | h | h | h
  · rw [h]; exact good_pinned (v z) hz5 (s z) hzs j.val x hx
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc

lemma hne_of (va vb : ℕ) (hva : 0 < va) (hvb : 0 < vb) (hne : va ≠ vb) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) : (va : ℤ) ≠ ε * vb := by
  rcases hε with rfl | rfl <;> omega

lemma exists_eps (a b : ZMod 5) (h : b = a ∨ b = -a) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ b = (ε : ZMod 5) * a := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by simp [h]⟩
  · exact ⟨-1, Or.inr rfl, by simp [h]⟩

lemma other_of_not_same (a c : ZMod 5) (a0 : a ≠ 0) (c0 : c ≠ 0) (h : ¬ (c = a ∨ c = -a)) :
    c = 2 * a ∨ c = 3 * a := by
  rcases ratio_class a c a0 c0 with h1 | h1 | h1 | h1
  · exact absurd (Or.inl h1) h
  · exact absurd (Or.inr h1) h
  · exact Or.inl h1
  · exact Or.inr h1

/-- Two residues in the other class relative to `a` are in one class relative to each other. -/
lemma other_other (a b c : ZMod 5) (hb : b = 2 * a ∨ b = 3 * a) (hc : c = 2 * a ∨ c = 3 * a) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ c = (ε : ZMod 5) * b ∧
      ∃ l : ZMod 5, (l = 2 ∨ l = 3) ∧ a = l * b := by
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp, 3, Or.inr rfl, by revert a; decide⟩
  · exact ⟨-1, Or.inr rfl, by push_cast; revert a; decide, 3, Or.inr rfl, by revert a; decide⟩
  · exact ⟨-1, Or.inr rfl, by push_cast; revert a; decide, 2, Or.inl rfl, by revert a; decide⟩
  · exact ⟨1, Or.inl rfl, by simp, 2, Or.inl rfl, by revert a; decide⟩

/-- The remaining hard case of Case H: all three free speeds in one class `{r, -r}` mod 5. -/
def Case3 : Prop :=
  ∀ (v : Fin 4 → ℕ) (s : Fin 4 → ℤ) (z a b c : Fin 4), (∀ i, 0 < v i) → Function.Injective v →
    (∀ i, i = z ∨ i = a ∨ i = b ∨ i = c) → a ≠ z → b ≠ z → c ≠ z → a ≠ b → a ≠ c → b ≠ c →
    5 ∣ v z → (5 : ℤ) ∣ s z → ¬ 5 ∣ v a → ¬ 5 ∣ v b → ¬ 5 ∣ v c →
    ((v b : ZMod 5) = v a ∨ (v b : ZMod 5) = -(v a : ZMod 5)) →
    ((v c : ZMod 5) = v a ∨ (v c : ZMod 5) = -(v a : ZMod 5)) →
    ∃ t : ℝ, ∀ i, Good (v i) (s i) t

theorem caseH_of_case3 (h3 : Case3) : CaseH := by
  intro v s z hpos hinj hz5 hzs hfree
  have hcard : (Finset.univ.erase z).card = 3 := by simp
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  have mem : ∀ i, i ∈ Finset.univ.erase z ↔ (i = a ∨ i = b ∨ i = c) := by
    intro i; rw [hset]; simp
  have hall : ∀ i, i = z ∨ i = a ∨ i = b ∨ i = c := by
    intro i
    by_cases hi : i = z
    · exact Or.inl hi
    · exact Or.inr ((mem i).mp (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩))
  have haz : a ≠ z := (Finset.mem_erase.mp ((mem a).mpr (Or.inl rfl))).1
  have hbz : b ≠ z := (Finset.mem_erase.mp ((mem b).mpr (Or.inr (Or.inl rfl)))).1
  have hcz : c ≠ z := (Finset.mem_erase.mp ((mem c).mpr (Or.inr (Or.inr rfl)))).1
  have fa := hfree a haz
  have fb := hfree b hbz
  have fc := hfree c hcz
  have a0 : (v a : ZMod 5) ≠ 0 := fun h => fa ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  have b0 : (v b : ZMod 5) ≠ 0 := fun h => fb ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  have c0 : (v c : ZMod 5) ≠ 0 := fun h => fc ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  have hw : 1 ≤ v z / 5 := by
    obtain ⟨k, hk⟩ := hz5
    have := hpos z
    omega
  have vab : v a ≠ v b := fun h => hab (hinj h)
  have vac : v a ≠ v c := fun h => hac (hinj h)
  have vbc : v b ≠ v c := fun h => hbc (hinj h)
  by_cases sb : ((v b : ZMod 5) = v a ∨ (v b : ZMod 5) = -(v a : ZMod 5)) <;>
    by_cases sc : ((v c : ZMod 5) = v a ∨ (v c : ZMod 5) = -(v a : ZMod 5))
  · exact h3 v s z a b c hpos hinj hall haz hbz hcz hab hac hbc hz5 hzs fa fb fc sb sc
  · -- b with a, c in the other class
    obtain ⟨ε, hε, hb⟩ := exists_eps _ _ sb
    have hc := other_of_not_same _ _ a0 c0 sc
    obtain ⟨x, hx, j, ja, jb, jc⟩ := case21 (v z / 5) hw (v a) (v b) (v c) (s a) (s b) (s c) ε hε
      (if (v c : ZMod 5) = 2 * v a then 2 else 3) (by split_ifs <;> simp) fa hb
      (by split_ifs with h
          · exact h
          · exact hc.resolve_left h)
      (hne_of _ _ (hpos a) (hpos b) vab ε hε)
    exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc
  · -- c with a, b in the other class
    obtain ⟨ε, hε, hc⟩ := exists_eps _ _ sc
    have hb := other_of_not_same _ _ a0 b0 sb
    obtain ⟨x, hx, j, ja, jc, jb⟩ := case21 (v z / 5) hw (v a) (v c) (v b) (s a) (s c) (s b) ε hε
      (if (v b : ZMod 5) = 2 * v a then 2 else 3) (by split_ifs <;> simp) fa hc
      (by split_ifs with h
          · exact h
          · exact hb.resolve_left h)
      (hne_of _ _ (hpos a) (hpos c) vac ε hε)
    exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc
  · -- b and c both in the other class: use b as the base runner
    have hb := other_of_not_same _ _ a0 b0 sb
    have hc := other_of_not_same _ _ a0 c0 sc
    obtain ⟨ε, hε, hcb, l, hl, hal⟩ := other_other _ _ _ hb hc
    obtain ⟨x, hx, j, jb, jc, ja⟩ := case21 (v z / 5) hw (v b) (v c) (v a) (s b) (s c) (s a) ε hε
      l hl fb hcb hal (hne_of _ _ (hpos b) (hpos c) vbc ε hε)
    exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc

end LRSpectrumFull
