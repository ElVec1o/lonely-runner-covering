/-
# TP'(4), module M6d: the hub step of Case 3 (Lemma 6 or Lemma 7)

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Section 4 (Lemma 6, Lemma 7, closing paragraph).

`hub`: runner `a` (the hub) and two further free runners `b`, `c` in the same class as `a`.  If `5 ∤ σ_ab` and
`5 ∤ σ_ac` (with `σ_ab = s_a - ε_b s_b`, `σ_ac = s_a - ε_c s_c`), then there is `x` with the pinned runner away
from 0 and a residue `j` good for all three free runners.  Either Lemma 6 (`case6`) applies for one of the two
pairs, or both pairs fail it; then `big_of_fail` gives `5 |D| ≤ w` (this is where `5 ∤ σ` is used: 5 is prime)
and Lemma 7 (`lemma7`) applies.
-/
import LRSpectrumFull.TPFourLemma7

namespace LRSpectrumFull

lemma five_dvd_of_mul (t σ : ℤ) (h : (5 : ℤ) ∣ t * σ) (hσ : ¬ (5 : ℤ) ∣ σ) : (5 : ℤ) ∣ t := by
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (t * σ) 5).mpr (by exact_mod_cast h)
  push_cast at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd t 5).mp h2
  · exact (hσ (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd σ 5).mp h2)).elim

/-- "Lemma 6 fails" with `5 ∤ σ` forces `5 |D| ≤ w`. -/
lemma big_of_fail (w : ℕ) (hw : 1 ≤ w) (D σ : ℤ) (hD : D ≠ 0) (hσ : ¬ (5 : ℤ) ∣ σ)
    (h : D ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / D) * σ) : 5 * |D| ≤ (w : ℤ) := by
  obtain ⟨⟨t, ht⟩, h5⟩ := h
  have hq : (w : ℤ) / D = t := by rw [ht]; exact Int.mul_ediv_cancel_left t hD
  rw [hq] at h5
  obtain ⟨t', ht'⟩ := five_dvd_of_mul t σ h5 hσ
  have ht0 : t' ≠ 0 := by
    rintro rfl
    have : (w : ℤ) = 0 := by rw [ht, ht']; ring
    omega
  have h1 : (1 : ℤ) ≤ |t'| := Int.one_le_abs ht0
  have h2 : |(w : ℤ)| = |D| * (5 * |t'|) := by
    rw [ht, ht', abs_mul, abs_mul]; norm_num
  have h3 : |(w : ℤ)| = (w : ℤ) := abs_of_nonneg (Nat.cast_nonneg w)
  nlinarith [abs_nonneg D, mul_nonneg (abs_nonneg D) (sub_nonneg.mpr h1)]

lemma dvd_five_of_class (va vx : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : (vx : ZMod 5) = (ε : ZMod 5) * va) : (5 : ℤ) ∣ (va : ℤ) - ε * vx := by
  have h0 : (((va : ℤ) - ε * vx : ℤ) : ZMod 5) = 0 := by
    push_cast
    rw [h]
    rcases hε with rfl | rfl <;> push_cast <;> ring
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h0

lemma hub (w : ℕ) (hw : 1 ≤ w) (va vb vc : ℕ) (sa sb sc : ℤ) (εb εc : ℤ)
    (hεb : εb = 1 ∨ εb = -1) (hεc : εc = 1 ∨ εc = -1)
    (ha : ¬ 5 ∣ va) (hb5 : ¬ 5 ∣ vb) (hc5 : ¬ 5 ∣ vc)
    (hb : (vb : ZMod 5) = (εb : ZMod 5) * va) (hc : (vc : ZMod 5) = (εc : ZMod 5) * va)
    (hneb : (va : ℤ) ≠ εb * vb) (hnec : (va : ℤ) ≠ εc * vc) (hbc : εb * (vb : ℤ) ≠ εc * vc)
    (σb : ¬ (5 : ℤ) ∣ sa - εb * sb) (σc : ¬ (5 : ℤ) ∣ sa - εc * sc) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x) ∧ ∃ j : ZMod 5,
      Good va sa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ Good vb sb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        Good vc sc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  obtain ⟨Db, hDb⟩ := dvd_five_of_class va vb εb hεb hb
  obtain ⟨Dc, hDc⟩ := dvd_five_of_class va vc εc hεc hc
  have hDb0 : Db ≠ 0 := by
    rintro rfl
    apply hneb
    omega
  have hDc0 : Dc ≠ 0 := by
    rintro rfl
    apply hnec
    omega
  by_cases f1 : Db ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / Db) * (sa - εb * sb)
  · by_cases f2 : Dc ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / Dc) * (sa - εc * sc)
    · exact lemma7 w hw va vb vc sa sb sc εb εc hεb hεc ha hb5 hc5 hb hc Db Dc hDb hDc hneb hnec
        hbc (big_of_fail w hw Db _ hDb0 σb f1) (big_of_fail w hw Dc _ hDc0 σc f2)
    · obtain ⟨x, hx, j, ja, jc, jb⟩ :=
        case6 w va vc vb sa sc sb εc hεc ha hb5 hc Dc hDc hnec f2
      exact ⟨x, hx, j, ja, jb, jc⟩
  · exact case6 w va vb vc sa sb sc εb hεb ha hc5 hb Db hDb hneb f1

end LRSpectrumFull
