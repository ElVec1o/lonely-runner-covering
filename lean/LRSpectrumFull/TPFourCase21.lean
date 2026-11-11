/-
# TP'(4), module M5b: Lemma 5, Case 2+1 of Case H

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Section 3 and Lemma 5.

Runner `a` is free (`5 ∤ v_a`); runner `b` has `v_b ≡ ε v_a (mod 5)` with `ε = ±1`; runner `c` has
`v_c ≡ λ v_a (mod 5)` with `λ ∈ {2, 3}`; `w ≥ 1` is the speed of the pinned runner divided by 5.  Put
`5 D = v_a - ε v_b` (so `D ≠ 0` iff `v_a ≠ ε v_b`) and `σ = s_a - ε s_b`.  The centre formula is
`β_a - ε β_b = σ + 5 D x` with `β_i = s_i + v_i x`.  Lemma 4 gives `x` with `|D x + σ/5 - m| ≤ 1/5` and the
pinned runner away from 0; `exists_good_21` then gives a residue `j` good for all three free runners.

* `case21` : the conclusion of `CaseH` for the three free runners and the pinned one, in terms of `Good`,
  with the pinned runner expressed as `1/5 ≤ tpDist (w x)`.
-/
import LRSpectrumFull.TPFourArcs
import LRSpectrumFull.TPFourCoset

namespace LRSpectrumFull

lemma case21 (w : ℕ) (hw : 1 ≤ w) (va vb vc : ℕ) (sa sb sc : ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (lc : ZMod 5) (hlc : lc = 2 ∨ lc = 3) (ha : ¬ 5 ∣ va)
    (hb : (vb : ZMod 5) = (ε : ZMod 5) * va) (hc : (vc : ZMod 5) = lc * va)
    (hne : (va : ℤ) ≠ ε * vb) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x) ∧ ∃ j : ZMod 5,
      Good va sa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ Good vb sb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        Good vc sc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  have hdvd : (5 : ℤ) ∣ (va : ℤ) - ε * vb := by
    have h0 : (((va : ℤ) - ε * vb : ℤ) : ZMod 5) = 0 := by
      push_cast
      rw [hb]
      rcases hε with rfl | rfl <;> push_cast <;> ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h0
  obtain ⟨D, hD⟩ := hdvd
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply hne
    omega
  obtain ⟨x, m, h1, h2⟩ := lemma4 D hD0 w hw (sa - ε * sb)
  have hDR : ((va : ℤ) : ℝ) - (ε : ℝ) * (vb : ℝ) = 5 * (D : ℝ) := by exact_mod_cast hD
  have hcen : |((sa : ℝ) + va * x) - ((ε : ℝ) * ((sb : ℝ) + vb * x) + ((5 * m : ℤ) : ℝ))| ≤ 1 := by
    have e : ((sa : ℝ) + va * x) - ((ε : ℝ) * ((sb : ℝ) + vb * x) + ((5 * m : ℤ) : ℝ))
        = 5 * ((D : ℝ) * x + ((sa - ε * sb : ℤ) : ℝ) / 5 - m) := by
      push_cast
      push_cast at hDR
      linear_combination x * hDR
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    linarith
  obtain ⟨j, hja, hjb, hjc⟩ := exists_good_21 va vb vc ((sa : ℝ) + va * x) ((sb : ℝ) + vb * x)
    ((sc : ℝ) + vc * x) ε m hε lc hlc ha0 hb hc hcen
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
  exact ⟨x, h2, j, good_of_not_mem_badImg ha sa x j hja, good_of_not_mem_badImg hb5 sb x j hjb,
    good_of_not_mem_badImg hc5 sc x j hjc⟩

end LRSpectrumFull
