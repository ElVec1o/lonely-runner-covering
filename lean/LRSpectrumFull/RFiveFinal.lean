/-
# Theorem R5 (real phases): dispatch on four runners and the theorem

Paper proof: ROOMS/OPUS_REAL_PHASES_2026_11_12.md, "Assembly"; real twins of `TPFourGlue.caseH_of_case3` and
`TPFourReduce.lemT`.  There is no induction on four runners (Lemma S handles at most three), and no divisor
fact / rigid shape / hub / step 5b.

* `caseHR`  : one slow runner `z` (any real phase) and three free runners: a good time exists.
* `R5_core` : four distinct positive speeds, some divisible by 5 and some not, any real phases.
* `R5`      : the same with the hypothesis `gcd = 1` and "some `v i` divisible by 5".

Statement chosen: `R5` is `Finset.univ.gcd v = 1` and `∃ i, 5 ∣ v i` (as proposed).  `R5_core` is the stronger
statement that is actually proved: the gcd is only used to rule out "all four speeds divisible by 5".
-/
import LRSpectrumFull.RFiveCase

namespace LRSpectrumFull

lemma good_pinnedR (u : ℕ) (hu5 : 5 ∣ u) (φ : ℝ) (j : ℕ) (x : ℝ)
    (h : 1 / 5 ≤ tpDist (((u / 5 : ℕ) : ℝ) * x + φ)) : GoodR u φ (((j : ℝ) + x) / 5) := by
  obtain ⟨w, rfl⟩ := hu5
  rw [goodR_mul5]
  have e2 : 5 * w / 5 = w := by omega
  rw [e2] at h
  exact h

lemma finish_fourR (v : Fin 4 → ℕ) (φ : Fin 4 → ℝ) (z a b c : Fin 4)
    (hall : ∀ i, i = z ∨ i = a ∨ i = b ∨ i = c) (hz5 : 5 ∣ v z)
    (x : ℝ) (hx : 1 / 5 ≤ tpDist (((v z / 5 : ℕ) : ℝ) * x + φ z)) (j : ZMod 5)
    (ha : GoodR (v a) (φ a) ((((j.val : ℕ) : ℝ) + x) / 5))
    (hb : GoodR (v b) (φ b) ((((j.val : ℕ) : ℝ) + x) / 5))
    (hc : GoodR (v c) (φ c) ((((j.val : ℕ) : ℝ) + x) / 5)) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  refine ⟨(((j.val : ℕ) : ℝ) + x) / 5, fun i => ?_⟩
  rcases hall i with h | h | h | h
  · rw [h]; exact good_pinnedR (v z) hz5 (φ z) j.val x hx
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc

/-- One slow runner (any real phase) and three free runners. -/
theorem caseHR (v : Fin 4 → ℕ) (φ : Fin 4 → ℝ) (z : Fin 4) (hpos : ∀ i, 0 < v i)
    (hinj : Function.Injective v) (hz5 : 5 ∣ v z) (hfree : ∀ i, i ≠ z → ¬ 5 ∣ v i) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
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
  have pa := hpos a
  have pb := hpos b
  have pc := hpos c
  by_cases sb : ((v b : ZMod 5) = v a ∨ (v b : ZMod 5) = -(v a : ZMod 5)) <;>
    by_cases sc : ((v c : ZMod 5) = v a ∨ (v c : ZMod 5) = -(v a : ZMod 5))
  · -- all three in one class
    obtain ⟨εb, hεb, hb⟩ := exists_eps _ _ sb
    obtain ⟨εc, hεc, hc⟩ := exists_eps _ _ sc
    have hbc'' : εb * (v b : ℤ) ≠ εc * v c := by
      rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
    obtain ⟨x, hx, j, ja, jb, jc⟩ := case3R (v z / 5) hw (v a) (v b) (v c) (φ a) (φ b) (φ c) (φ z)
      εb εc hεb hεc fa fb fc hb hc (hne_of _ _ pa pb vab εb hεb) (hne_of _ _ pa pc vac εc hεc) hbc''
    exact finish_fourR v φ z a b c hall hz5 x hx j ja jb jc
  · -- b with a, c in the other class
    obtain ⟨ε, hε, hb⟩ := exists_eps _ _ sb
    have hc := other_of_not_same _ _ a0 c0 sc
    obtain ⟨x, hx, j, ja, jb, jc⟩ := case21R (v z / 5) hw (v a) (v b) (v c) (φ a) (φ b) (φ c) (φ z)
      ε hε (if (v c : ZMod 5) = 2 * v a then 2 else 3) (by split_ifs <;> simp) fa hb
      (by split_ifs with h
          · exact h
          · exact hc.resolve_left h)
      (hne_of _ _ pa pb vab ε hε)
    exact finish_fourR v φ z a b c hall hz5 x hx j ja jb jc
  · -- c with a, b in the other class
    obtain ⟨ε, hε, hc⟩ := exists_eps _ _ sc
    have hb := other_of_not_same _ _ a0 b0 sb
    obtain ⟨x, hx, j, ja, jc, jb⟩ := case21R (v z / 5) hw (v a) (v c) (v b) (φ a) (φ c) (φ b) (φ z)
      ε hε (if (v b : ZMod 5) = 2 * v a then 2 else 3) (by split_ifs <;> simp) fa hc
      (by split_ifs with h
          · exact h
          · exact hb.resolve_left h)
      (hne_of _ _ pa pc vac ε hε)
    exact finish_fourR v φ z a b c hall hz5 x hx j ja jb jc
  · -- b and c both in the other class: use b as the base runner
    have hb := other_of_not_same _ _ a0 b0 sb
    have hc := other_of_not_same _ _ a0 c0 sc
    obtain ⟨ε, hε, hcb, l, hl, hal⟩ := other_other _ _ _ hb hc
    obtain ⟨x, hx, j, jb, jc, ja⟩ := case21R (v z / 5) hw (v b) (v c) (v a) (φ b) (φ c) (φ a) (φ z)
      ε hε l hl fb hcb hal (hne_of _ _ pb pc vbc ε hε)
    exact finish_fourR v φ z a b c hall hz5 x hx j ja jb jc

/-- Four distinct positive speeds, at least one divisible by 5 and at least one not, any real phases. -/
theorem R5_core (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hslow : ∃ i, 5 ∣ v i) (hfree : ∃ i, ¬ 5 ∣ v i) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨z, hz5⟩ := hslow
  obtain ⟨a0, ha0⟩ := hfree
  set A : Finset (Fin 4) := Finset.univ.filter (fun i => ¬ 5 ∣ v i) with hA
  have ha0A : a0 ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0⟩
  have hzA : z ∉ A := fun h => (Finset.mem_filter.mp h).2 hz5
  by_cases ha : A.card ≤ 2
  · set C : Finset (Fin 4) := Finset.univ.filter (fun i => 5 ∣ v i) with hC
    have hCcard : C.card ≤ 3 := by
      have hsub : C ⊆ Finset.univ.erase a0 := by
        intro k hk
        obtain ⟨-, hk5⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h
        exact ha0 (h ▸ hk5)
      have := Finset.card_le_card hsub
      simpa using this
    obtain ⟨x, hx⟩ := lemSR (∑ i ∈ C, v i / 5) (fun i => v i / 5) φ C
      (fun i hi => by
        obtain ⟨-, ⟨w, hw⟩⟩ := Finset.mem_filter.mp hi
        have := hpos i
        show 0 < v i / 5
        omega)
      (fun i hi k hk hik => by
        obtain ⟨-, h5i⟩ := Finset.mem_filter.mp hi
        obtain ⟨-, h5k⟩ := Finset.mem_filter.mp hk
        have hik' : v i / 5 = v k / 5 := hik
        exact hinj (by omega))
      hCcard le_rfl
    obtain ⟨t, ht⟩ := step_le2R Finset.univ v φ ha x hx
    exact ⟨t, fun i => ht i (Finset.mem_univ _)⟩
  · -- three free runners, the fourth slow
    push Not at ha
    have hAle : A.card ≤ 3 := by
      have hsub : A ⊆ Finset.univ.erase z := by
        intro k hk
        exact Finset.mem_erase.mpr ⟨fun h => hzA (h ▸ hk), Finset.mem_univ _⟩
      have := Finset.card_le_card hsub
      simpa using this
    have hz : ∀ i, i ≠ z → ¬ 5 ∣ v i := by
      intro i hiz hi5
      have hsub : A ⊆ (Finset.univ.erase i).erase z := by
        intro k hk
        obtain ⟨-, hk5⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_erase.mpr ⟨fun h => hk5 (h ▸ hz5), ?_⟩
        exact Finset.mem_erase.mpr ⟨fun h => hk5 (h ▸ hi5), Finset.mem_univ _⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simp [hiz.symm]), Finset.card_erase_of_mem (by simp)] at this
      simp at this
      omega
    exact caseHR v φ z hpos hinj hz5 hz

/-- Theorem R5: four distinct positive speeds with gcd 1, one of them divisible by 5, any real phases:
some time puts every runner at distance at least `1/5` from the integers. -/
theorem R5 (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hgcd : Finset.univ.gcd v = 1) (h5 : ∃ i, 5 ∣ v i) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ tpDist ((v i : ℝ) * t + φ i) := by
  have hfree : ∃ i, ¬ 5 ∣ v i := by
    by_contra hno
    push Not at hno
    have h : 5 ∣ Finset.univ.gcd v := Finset.dvd_gcd (fun i _ => hno i)
    rw [hgcd] at h
    omega
  obtain ⟨t, ht⟩ := R5_core v hpos hinj h5 hfree φ
  exact ⟨t, fun i => ht i⟩

end LRSpectrumFull
