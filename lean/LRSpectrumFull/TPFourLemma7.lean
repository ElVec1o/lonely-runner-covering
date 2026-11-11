/-
# TP'(4), module M6c: Lemma 7 (cluster) in terms of the runners

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 7.

Hub `a`, two further free runners `b`, `c` of the same class (`v_b ≡ ε_b v_a`, `v_c ≡ ε_c v_a`), pinned speed `5 w`.
With `5 D_b = v_a - ε_b v_b`, `5 D_c = v_a - ε_c v_c` and the bounds `5 |D_b|, 5 |D_c| ≤ w` (this is what
"Lemma 6 fails" gives, see `TPFourHub`), `cluster_real` yields `x` and shifts `m_b`, `m_c` with the three centres
`β_a`, `ε_b β_b + 5 m_b`, `ε_c β_c + 5 m_c` in an interval of length 2; `exists_good_3` finishes.
-/
import LRSpectrumFull.TPFourTight

namespace LRSpectrumFull

lemma lemma7 (w : ℕ) (hw : 1 ≤ w) (va vb vc : ℕ) (sa sb sc : ℤ) (εb εc : ℤ)
    (hεb : εb = 1 ∨ εb = -1) (hεc : εc = 1 ∨ εc = -1)
    (ha : ¬ 5 ∣ va) (hb5 : ¬ 5 ∣ vb) (hc5 : ¬ 5 ∣ vc)
    (hb : (vb : ZMod 5) = (εb : ZMod 5) * va) (hc : (vc : ZMod 5) = (εc : ZMod 5) * va)
    (Db Dc : ℤ) (hDb : (va : ℤ) - εb * vb = 5 * Db) (hDc : (va : ℤ) - εc * vc = 5 * Dc)
    (hneb : (va : ℤ) ≠ εb * vb) (hnec : (va : ℤ) ≠ εc * vc) (hbc : εb * (vb : ℤ) ≠ εc * vc)
    (hbb : 5 * |Db| ≤ (w : ℤ)) (hbc' : 5 * |Dc| ≤ (w : ℤ)) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x) ∧ ∃ j : ZMod 5,
      Good va sa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ Good vb sb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        Good vc sc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
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
  obtain ⟨x, mb, mc, hfar, r2, r3, r4⟩ :=
    cluster_real Db Dc (sa - εb * sb) (sa - εc * sc) w hw hDb0 hDc0 hDne hbb hbc'
  obtain ⟨lo, l0, lb, lc, u0, ub, uc⟩ := spread3 _ _ r2 r3 r4
  have hDbR : (va : ℝ) - (εb : ℝ) * (vb : ℝ) = 5 * (Db : ℝ) := by exact_mod_cast hDb
  have hDcR : (va : ℝ) - (εc : ℝ) * (vc : ℝ) = 5 * (Dc : ℝ) := by exact_mod_cast hDc
  have eb : (εb : ℝ) * ((sb : ℝ) + vb * x) + ((5 * mb : ℤ) : ℝ)
      = ((sa : ℝ) + va * x) -
        5 * ((Db : ℝ) * x + ((sa - εb * sb : ℤ) : ℝ) / 5 - mb) := by
    push_cast
    linear_combination (-x) * hDbR
  have ec : (εc : ℝ) * ((sc : ℝ) + vc * x) + ((5 * mc : ℤ) : ℝ)
      = ((sa : ℝ) + va * x) -
        5 * ((Dc : ℝ) * x + ((sa - εc * sc : ℤ) : ℝ) / 5 - mc) := by
    push_cast
    linear_combination (-x) * hDcR
  obtain ⟨j, hja, hjb, hjc⟩ := exists_good_3 va vb vc ((sa : ℝ) + va * x) ((sb : ℝ) + vb * x)
    ((sc : ℝ) + vc * x) εb εc mb mc hεb hεc ha0 hb hc
    (((sa : ℝ) + va * x) - 5 * lo - 2)
    ⟨by linarith, by linarith⟩
    (by rw [eb]; constructor <;> linarith)
    (by rw [ec]; constructor <;> linarith)
  exact ⟨x, hfar, j, good_of_not_mem_badImg ha sa x j hja, good_of_not_mem_badImg hb5 sb x j hjb,
    good_of_not_mem_badImg hc5 sc x j hjc⟩

end LRSpectrumFull
