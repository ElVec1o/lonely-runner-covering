/-
# Theorem R5 (real phases), module K: the two remaining configurations of Case H with real phases

Paper proof: ROOMS/OPUS_REAL_PHASES_2026_11_12.md, Lemma 5 (2+1) and the one-class case (Lemma 6 on each of the three
pairs, else the cluster lemma).  Hub choice, step 5b and the divisor fact of the grid proof are not needed.

Notation: free runners `a, b, c` (speeds not divisible by 5), one slow runner of speed `5 w` and phase `φ_d`;
`β_i = 5 φ_i + v_i x`.  `σ_b = φ_a - ε_b φ_b`, `5 D_b = v_a - ε_b v_b`.

* `case21R`: `b` in the class of `a`, `c` in the other class (Lemma 4R window, then `exists_good_21`).
* `case3R` : `a, b, c` in one class: exact coincidence of a pair if Lemma 6 does not fail for it
             (`exists_exactR`), else `cluster_div` and `exists_good_3`.
-/
import LRSpectrumFull.RFiveCluster
import LRSpectrumFull.RFiveLemS

namespace LRSpectrumFull

lemma case21R (w : ℕ) (hw : 1 ≤ w) (va vb vc : ℕ) (φa φb φc φd : ℝ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (lc : ZMod 5) (hlc : lc = 2 ∨ lc = 3) (ha : ¬ 5 ∣ va)
    (hb : (vb : ZMod 5) = (ε : ZMod 5) * va) (hc : (vc : ZMod 5) = lc * va)
    (hne : (va : ℤ) ≠ ε * vb) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ ∃ j : ZMod 5,
      GoodR va φa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ GoodR vb φb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        GoodR vc φc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  obtain ⟨D, hD⟩ := dvd5_class va vb ε hε hb
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply hne
    omega
  obtain ⟨x, m, h1, h2⟩ := lemma4R D hD0 w hw (φa - ε * φb) φd
  have hDR : ((va : ℤ) : ℝ) - (ε : ℝ) * (vb : ℝ) = 5 * (D : ℝ) := by exact_mod_cast hD
  have hcen : |(5 * φa + va * x) - ((ε : ℝ) * (5 * φb + vb * x) + ((5 * m : ℤ) : ℝ))| ≤ 1 := by
    have e : (5 * φa + va * x) - ((ε : ℝ) * (5 * φb + vb * x) + ((5 * m : ℤ) : ℝ))
        = 5 * ((D : ℝ) * x + (φa - ε * φb) - m) := by
      push_cast
      push_cast at hDR
      linear_combination x * hDR
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    linarith
  obtain ⟨j, hja, hjb, hjc⟩ := exists_good_21 va vb vc (5 * φa + va * x) (5 * φb + vb * x)
    (5 * φc + vc * x) ε m hε lc hlc ha0 hb hc hcen
  have hb5 : ¬ 5 ∣ vb := by
    intro h5
    have : (vb : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff vb 5).mpr h5
    rw [hb] at this
    rcases hε with rfl | rfl <;> simp at this <;> exact ha0 this
  have hc5 : ¬ 5 ∣ vc := by
    intro h5
    have : (vc : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff vc 5).mpr h5
    rw [hc] at this
    have key : ∀ (l a : ZMod 5), (l = 2 ∨ l = 3) → l * a = 0 → a = 0 := by decide
    exact ha0 (key lc _ hlc this)
  exact ⟨x, h2, j, goodR_of_not_mem_badImg ha φa x j hja, goodR_of_not_mem_badImg hb5 φb x j hjb,
    goodR_of_not_mem_badImg hc5 φc x j hjc⟩

lemma case3R (w : ℕ) (hw : 1 ≤ w) (va vb vc : ℕ) (φa φb φc φd : ℝ) (εb εc : ℤ)
    (hεb : εb = 1 ∨ εb = -1) (hεc : εc = 1 ∨ εc = -1)
    (ha : ¬ 5 ∣ va) (hb5 : ¬ 5 ∣ vb) (hc5 : ¬ 5 ∣ vc)
    (hb : (vb : ZMod 5) = (εb : ZMod 5) * va) (hc : (vc : ZMod 5) = (εc : ZMod 5) * va)
    (hneb : (va : ℤ) ≠ εb * vb) (hnec : (va : ℤ) ≠ εc * vc) (hbc : εb * (vb : ℤ) ≠ εc * vc) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ ∃ j : ZMod 5,
      GoodR va φa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ GoodR vb φb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        GoodR vc φc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  obtain ⟨Db, hDb⟩ := dvd5_class va vb εb hεb hb
  obtain ⟨Dc, hDc⟩ := dvd5_class va vc εc hεc hc
  have hDb0 : Db ≠ 0 := by
    rintro rfl
    apply hneb
    omega
  have hDc0 : Dc ≠ 0 := by
    rintro rfl
    apply hnec
    omega
  have hDne : Db ≠ Dc := by
    intro h
    apply hbc
    omega
  have hDbR : ((va : ℤ) : ℝ) - (εb : ℝ) * (vb : ℝ) = 5 * (Db : ℝ) := by exact_mod_cast hDb
  have hDcR : ((va : ℤ) : ℝ) - (εc : ℝ) * (vc : ℝ) = 5 * (Dc : ℝ) := by exact_mod_cast hDc
  -- the finishing step for any `x` with the pinned runner far and a good residue for the three bad sets
  have fin : ∀ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) →
      (∃ j : ZMod 5, j ∉ badImg va (5 * φa + va * x) ∧ j ∉ badImg vb (5 * φb + vb * x) ∧
        j ∉ badImg vc (5 * φc + vc * x)) →
      ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ ∃ j : ZMod 5,
        GoodR va φa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ GoodR vb φb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
          GoodR vc φc ((((j.val : ℕ) : ℝ) + x) / 5) := by
    intro x hx ⟨j, j1, j2, j3⟩
    exact ⟨x, hx, j, goodR_of_not_mem_badImg ha φa x j j1, goodR_of_not_mem_badImg hb5 φb x j j2,
      goodR_of_not_mem_badImg hc5 φc x j j3⟩
  by_cases f1 : L6 Db w (φa - εb * φb) φd
  · by_cases f2 : L6 Dc w (φa - εc * φc) φd
    · by_cases f3 : L6 (Db - Dc) w ((φa - εb * φb) - (φa - εc * φc)) φd
      · -- Lemma 6 fails on all three pairs: all three `D` divide `w`; cluster
        obtain ⟨t1, ht1, -⟩ := f1
        obtain ⟨t2, ht2, -⟩ := f2
        obtain ⟨t3, ht3, -⟩ := f3
        obtain ⟨x, mb, mc, hfar, r2, r3, r4⟩ := cluster_div w hw Db Dc (φa - εb * φb)
          (φa - εc * φc) φd hDb0 hDc0 hDne ⟨t1, ht1⟩ ⟨t2, ht2⟩ ⟨t3, ht3⟩
        obtain ⟨lo, l0, lb, lc, u0, ub, uc⟩ := spread3 _ _ r2 r3 r4
        have eb : (εb : ℝ) * (5 * φb + vb * x) + ((5 * mb : ℤ) : ℝ)
            = (5 * φa + va * x) - 5 * ((Db : ℝ) * x + (φa - εb * φb) - mb) := by
          push_cast
          push_cast at hDbR
          linear_combination (-x) * hDbR
        have ec : (εc : ℝ) * (5 * φc + vc * x) + ((5 * mc : ℤ) : ℝ)
            = (5 * φa + va * x) - 5 * ((Dc : ℝ) * x + (φa - εc * φc) - mc) := by
          push_cast
          push_cast at hDcR
          linear_combination (-x) * hDcR
        obtain ⟨j, hja, hjb, hjc⟩ := exists_good_3 va vb vc (5 * φa + va * x) (5 * φb + vb * x)
          (5 * φc + vc * x) εb εc mb mc hεb hεc ha0 hb hc
          ((5 * φa + va * x) - 5 * lo - 2)
          ⟨by linarith, by linarith⟩
          (by rw [eb]; constructor <;> linarith)
          (by rw [ec]; constructor <;> linarith)
        exact fin x hfar ⟨j, hja, hjb, hjc⟩
      · -- pair (b, c) coincides exactly
        obtain ⟨x, m, hx, hfar⟩ := exists_exactR (Db - Dc) (sub_ne_zero.mpr hDne) w
          ((φa - εb * φb) - (φa - εc * φc)) φd f3
        have h : (εb : ℝ) * (5 * φb + vb * x) + ((5 * m : ℤ) : ℝ)
            = (εc : ℝ) * (5 * φc + vc * x) + ((5 * 0 : ℤ) : ℝ) := by
          push_cast at hx hDbR hDcR ⊢
          linear_combination (-5) * hx - x * hDbR + x * hDcR
        have hEq : badImg vb (5 * φb + vb * x) = badImg vc (5 * φc + vc * x) := by
          ext j
          rw [mem_badImg_class va vb _ εb m hεb ha0 hb j, mem_badImg_class va vc _ εc 0 hεc ha0 hc j,
            h]
        obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := va) (βc := 5 * φa + va * x) hEq
        exact fin x hfar ⟨j, j3, j2, j1⟩
    · -- pair (a, c) coincides exactly
      obtain ⟨x, m, hx, hfar⟩ := exists_exactR Dc hDc0 w (φa - εc * φc) φd f2
      have h : (5 * φa + va * x) = (εc : ℝ) * (5 * φc + vc * x) + ((5 * m : ℤ) : ℝ) := by
        push_cast at hx hDcR ⊢
        linear_combination x * hDcR + 5 * hx
      have hEq := badImg_eq_of_class va vc _ _ εc m hεc ha0 hc h
      obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := vb) (βc := 5 * φb + vb * x) hEq
      exact fin x hfar ⟨j, j1, j3, j2⟩
  · -- pair (a, b) coincides exactly
    obtain ⟨x, m, hx, hfar⟩ := exists_exactR Db hDb0 w (φa - εb * φb) φd f1
    have h : (5 * φa + va * x) = (εb : ℝ) * (5 * φb + vb * x) + ((5 * m : ℤ) : ℝ) := by
      push_cast at hx hDbR ⊢
      linear_combination x * hDbR + 5 * hx
    have hEq := badImg_eq_of_class va vb _ _ εb m hεb ha0 hb h
    obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := vc) (βc := 5 * φc + vc * x) hEq
    exact fin x hfar ⟨j, j1, j2, j3⟩

end LRSpectrumFull
