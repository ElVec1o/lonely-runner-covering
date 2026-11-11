/-
# TP'(4), module M8b: closing of Case 3 (step 5b, the hub choice) and `case3 : Case3`

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, step 5b and "Closing Case 3".

* `exists_tau` : if `5 ∣ σ_ab` and `5 ∣ σ_ac` there is an integer `τ` with `5 ∣ v_i τ + s_i` for `i = a, b, c`.
* `case3`      : all three free speeds in one class.  If both `σ_ab` and `σ_ac` are divisible by 5, then step 5b
  (`shift_five`, which also covers the pinned runner).  Otherwise one of the three runners is a hub with both of
  its `σ` not divisible by 5 (the three `σ` sum to zero up to units), and `hub` applies.
-/
import LRSpectrumFull.TPFourHub
import LRSpectrumFull.TPFourGlue
import LRSpectrumFull.TPFourFive

namespace LRSpectrumFull

lemma exists_tau (va vb vc : ℕ) (sa sb sc : ℤ) (εb εc : ℤ) (hεb : εb = 1 ∨ εb = -1)
    (hεc : εc = 1 ∨ εc = -1) (ha : ¬ 5 ∣ va)
    (hb : (vb : ZMod 5) = (εb : ZMod 5) * va) (hc : (vc : ZMod 5) = (εc : ZMod 5) * va)
    (h1 : (5 : ℤ) ∣ sa - εb * sb) (h2 : (5 : ℤ) ∣ sa - εc * sc) :
    ∃ τ : ℤ, (5 : ℤ) ∣ (va : ℤ) * τ + sa ∧ (5 : ℤ) ∣ (vb : ℤ) * τ + sb ∧
      (5 : ℤ) ∣ (vc : ℤ) * τ + sc := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  have hI : (va : ZMod 5) * (va : ZMod 5)⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hS1 : (sa : ZMod 5) - (εb : ZMod 5) * sb = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (sa - εb * sb) 5).mpr (by exact_mod_cast h1)
    push_cast at this
    exact this
  have hS2 : (sa : ZMod 5) - (εc : ZMod 5) * sc = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (sa - εc * sc) 5).mpr (by exact_mod_cast h2)
    push_cast at this
    exact this
  have hE1 : (εb : ZMod 5) * εb = 1 := by rcases hεb with rfl | rfl <;> norm_num
  have hE2 : (εc : ZMod 5) * εc = 1 := by rcases hεc with rfl | rfl <;> norm_num
  obtain ⟨τ0, hτ0⟩ : ∃ t : ZMod 5, t = (-(sa : ZMod 5)) * (va : ZMod 5)⁻¹ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℤ, (τ : ZMod 5) = τ0 :=
    ⟨(τ0.val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩
  have key : ∀ n : ℤ, (n : ZMod 5) = 0 → (5 : ℤ) ∣ n := fun n hn => by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp hn
  refine ⟨τ, key _ ?_, key _ ?_, key _ ?_⟩
  · push_cast
    rw [hτ, hτ0]
    linear_combination (-(sa : ZMod 5)) * hI
  · push_cast
    rw [hb, hτ, hτ0]
    linear_combination (-(εb : ZMod 5) * sa) * hI + (-(εb : ZMod 5)) * hS1 + (-(sb : ZMod 5)) * hE1
  · push_cast
    rw [hc, hτ, hτ0]
    linear_combination (-(εc : ZMod 5) * sa) * hI + (-(εc : ZMod 5)) * hS2 + (-(sc : ZMod 5)) * hE2

lemma rel_inv (x y : ZMod 5) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (h : y = (ε : ZMod 5) * x) :
    x = (ε : ZMod 5) * y := by
  have hE : (ε : ZMod 5) * ε = 1 := by
    rcases hε with rfl | rfl <;> first | norm_num | simp | (push_cast; ring)
  linear_combination (-(ε : ZMod 5)) * h + (-x) * hE

lemma eps_mul (εb εc : ℤ) (hεb : εb = 1 ∨ εb = -1) (hεc : εc = 1 ∨ εc = -1) :
    εb * εc = 1 ∨ εb * εc = -1 := by
  rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> first | omega | simp

theorem case3 : Case3 := by
  intro v s z a b c hpos hinj hall haz hbz hcz hab hac hbc hz5 hzs fa fb fc hsb hsc
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
  obtain ⟨εb, hεb, hb⟩ := exists_eps _ _ hsb
  obtain ⟨εc, hεc, hc⟩ := exists_eps _ _ hsc
  have hεbc := eps_mul εb εc hεb hεc
  have hba : (v a : ZMod 5) = (εb : ZMod 5) * v b := rel_inv _ _ εb hεb hb
  have hca : (v a : ZMod 5) = (εc : ZMod 5) * v c := rel_inv _ _ εc hεc hc
  have hneb := hne_of (v a) (v b) (hpos a) (hpos b) vab εb hεb
  have hnec := hne_of (v a) (v c) (hpos a) (hpos c) vac εc hεc
  by_cases h1 : (5 : ℤ) ∣ s a - εb * s b
  · by_cases h2 : (5 : ℤ) ∣ s a - εc * s c
    · -- step 5b: all sigma are divisible by 5
      obtain ⟨τ, t1, t2, t3⟩ := exists_tau (v a) (v b) (v c) (s a) (s b) (s c) εb εc hεb hεc fa
        hb hc h1 h2
      refine shift_five v s hpos τ (fun i => ?_)
      rcases hall i with h | h | h | h
      · rw [h]
        have hz5' : (5 : ℤ) ∣ (v z : ℤ) := by exact_mod_cast hz5
        exact dvd_add (dvd_mul_of_dvd_left hz5' τ) hzs
      · rw [h]; exact t1
      · rw [h]; exact t2
      · rw [h]; exact t3
    · -- hub c
      have hbcl : (v b : ZMod 5) = ((εb * εc : ℤ) : ZMod 5) * v c := by
        rw [hb, hca]; push_cast; ring
      have hn1 := hne_of (v c) (v a) pc pa vac.symm εc hεc
      have hn2 := hne_of (v c) (v b) pc pb vbc.symm (εb * εc) hεbc
      have hn3 : εc * (v a : ℤ) ≠ (εb * εc) * v b := by
        rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
      have s1 : ¬ (5 : ℤ) ∣ s c - εc * s a := by
        rcases hεc with rfl | rfl <;> omega
      have s2 : ¬ (5 : ℤ) ∣ s c - (εb * εc) * s b := by
        rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
      obtain ⟨x, hx, j, jc, ja, jb⟩ := hub (v z / 5) hw (v c) (v a) (v b) (s c) (s a) (s b) εc
        (εb * εc) hεc hεbc fc fa fb hca hbcl hn1 hn2 hn3 s1 s2
      exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc
  · by_cases h2 : (5 : ℤ) ∣ s a - εc * s c
    · -- hub b
      have hcbl : (v c : ZMod 5) = ((εb * εc : ℤ) : ZMod 5) * v b := by
        rw [hc, hba]; push_cast; ring
      have hn1 := hne_of (v b) (v a) pb pa vab.symm εb hεb
      have hn2 := hne_of (v b) (v c) pb pc vbc (εb * εc) hεbc
      have hn3 : εb * (v a : ℤ) ≠ (εb * εc) * v c := by
        rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
      have s1 : ¬ (5 : ℤ) ∣ s b - εb * s a := by
        rcases hεb with rfl | rfl <;> omega
      have s2 : ¬ (5 : ℤ) ∣ s b - (εb * εc) * s c := by
        rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
      obtain ⟨x, hx, j, jb, ja, jc⟩ := hub (v z / 5) hw (v b) (v a) (v c) (s b) (s a) (s c) εb
        (εb * εc) hεb hεbc fb fa fc hba hcbl hn1 hn2 hn3 s1 s2
      exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc
    · -- hub a
      have hbc'' : εb * (v b : ℤ) ≠ εc * v c := by
        rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> omega
      obtain ⟨x, hx, j, ja, jb, jc⟩ := hub (v z / 5) hw (v a) (v b) (v c) (s a) (s b) (s c) εb εc
        hεb hεc fa fb fc hb hc hneb hnec hbc'' h1 h2
      exact finish_four v s z a b c hall hz5 hzs x hx j ja jb jc

end LRSpectrumFull
