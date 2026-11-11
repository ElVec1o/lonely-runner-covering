/-
# TP'(4), module M6b: Lemma 7(i), (ii) in real terms

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 7.

With `r_b(x) = D_b x + σ_b/5 - m_b` and `r_c(x) = D_c x + σ_c/5 - m_c` (the real numbers `(c_a - c_i)/5` after the
integer shift `m_i`; `m_i` is free):

* `tight_window` (Lemma 7(i)): for `D_b, D_c` nonzero and distinct there are `x`, `m_b`, `m_c` with
  `|r_b|, |r_c|, |r_b - r_c| ≤ 8/25` (the set `{0, r_b, r_c}` lies in an interval of length `8/25`).
  Three branches: `D_b ∤ D_c`, `D_c ∤ D_b`, and `D_c = -D_b`.
* `cluster_real` (Lemma 7(ii)): if moreover `5 |D_b|, 5 |D_c| ≤ w`, the perturbation `x ↦ x + δ/w` of
  `exists_perturb` keeps the pinned runner away from 0 and moves `r_b`, `r_c` by at most `1/25`, so all
  three pairwise distances are `≤ 2/5`.
* `spread3`: three reals with pairwise distances `≤ 2/5` lie in `[lo, lo + 2/5]` with `lo ≤ 0`.
-/
import LRSpectrumFull.TPFourWindow

namespace LRSpectrumFull

lemma tight_left (Db Dc σb σc : ℤ) (hDb : Db ≠ 0) (hnd : ¬ Db ∣ Dc) :
    ∃ x : ℝ, ∃ mb mc : ℤ, |(Db : ℝ) * x + σb / 5 - mb| ≤ 8 / 25 ∧
      |(Dc : ℝ) * x + σc / 5 - mc| ≤ 8 / 25 ∧
      |((Db : ℝ) * x + σb / 5 - mb) - ((Dc : ℝ) * x + σc / 5 - mc)| ≤ 8 / 25 := by
  have hDR : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb
  obtain ⟨k, m, hkm⟩ :=
    exists_window Db Dc hDb hnd ((σc : ℝ) / 5 - (Dc : ℝ) * ((σb : ℝ) / 5) / Db)
  have hx : (Db : ℝ) * (((k : ℝ) - σb / 5) / Db) = (k : ℝ) - σb / 5 := by field_simp
  have e0 : (Db : ℝ) * (((k : ℝ) - σb / 5) / Db) + σb / 5 - k = 0 := by linarith
  have e : (Dc : ℝ) * (((k : ℝ) - σb / 5) / Db) + σc / 5 - m
      = (σc : ℝ) / 5 - (Dc : ℝ) * ((σb : ℝ) / 5) / Db + ((Dc * k : ℤ) : ℝ) / (Db : ℝ) - m := by
    push_cast; ring
  refine ⟨((k : ℝ) - σb / 5) / Db, k, m, ?_, ?_, ?_⟩
  · rw [e0]; norm_num
  · rw [e]; exact hkm
  · rw [e0, zero_sub, abs_neg, e]; exact hkm

lemma tight_window (Db Dc σb σc : ℤ) (hDb : Db ≠ 0) (hDc : Dc ≠ 0) (hne : Db ≠ Dc) :
    ∃ x : ℝ, ∃ mb mc : ℤ, |(Db : ℝ) * x + σb / 5 - mb| ≤ 8 / 25 ∧
      |(Dc : ℝ) * x + σc / 5 - mc| ≤ 8 / 25 ∧
      |((Db : ℝ) * x + σb / 5 - mb) - ((Dc : ℝ) * x + σc / 5 - mc)| ≤ 8 / 25 := by
  by_cases h1 : Db ∣ Dc
  · by_cases h2 : Dc ∣ Db
    · -- branch 3: `D_c = -D_b`
      have hDc' : Dc = -Db := by
        have := Int.natAbs_eq_of_dvd_dvd h1 h2
        omega
      have hDR : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb
      have hDcR : (Dc : ℝ) = -(Db : ℝ) := by exact_mod_cast hDc'
      obtain ⟨n, hn⟩ : ∃ n : ℤ, |((σb : ℝ) + σc) / 5 - n| ≤ 1 / 2 := ⟨round _, abs_sub_round _⟩
      obtain ⟨hn1, hn2⟩ := abs_le.mp hn
      obtain ⟨x, hxdef⟩ : ∃ x : ℝ,
          x = (((σb : ℝ) + σc) / 10 - n / 2 - σb / 5) / Db := ⟨_, rfl⟩
      have hX : (Db : ℝ) * x = ((σb : ℝ) + σc) / 10 - n / 2 - σb / 5 := by
        rw [hxdef]; field_simp
      have hrb : (Db : ℝ) * x + σb / 5 - ((0 : ℤ) : ℝ) = ((σb : ℝ) + σc) / 10 - n / 2 := by
        push_cast; linarith
      have hrc : (Dc : ℝ) * x + σc / 5 - ((n : ℤ) : ℝ) = ((σb : ℝ) + σc) / 10 - n / 2 := by
        rw [hDcR]; linarith
      refine ⟨x, 0, n, ?_, ?_, ?_⟩
      · rw [hrb, abs_le]; constructor <;> linarith
      · rw [hrc, abs_le]; constructor <;> linarith
      · rw [hrb, hrc, sub_self, abs_zero]; norm_num
    · -- branch 2: `D_c ∤ D_b`
      obtain ⟨x, mc, mb, hc, hb, hcb⟩ := tight_left Dc Db σc σb hDc h2
      refine ⟨x, mb, mc, hb, hc, ?_⟩
      rw [abs_sub_comm]; exact hcb
  · exact tight_left Db Dc σb σc hDb h1

lemma cluster_real (Db Dc σb σc : ℤ) (w : ℕ) (hw : 1 ≤ w) (hDb : Db ≠ 0) (hDc : Dc ≠ 0)
    (hne : Db ≠ Dc) (hbb : 5 * |Db| ≤ (w : ℤ)) (hbc : 5 * |Dc| ≤ (w : ℤ)) :
    ∃ x : ℝ, ∃ mb mc : ℤ, 1 / 5 ≤ tpDist ((w : ℝ) * x) ∧
      |(Db : ℝ) * x + σb / 5 - mb| ≤ 2 / 5 ∧ |(Dc : ℝ) * x + σc / 5 - mc| ≤ 2 / 5 ∧
      |((Db : ℝ) * x + σb / 5 - mb) - ((Dc : ℝ) * x + σc / 5 - mc)| ≤ 2 / 5 := by
  obtain ⟨x0, mb, mc, h1, h2, h3⟩ := tight_window Db Dc σb σc hDb hDc hne
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  obtain ⟨δ, hδ, hfar⟩ := exists_perturb ((w : ℝ) * x0)
  have hxw : (w : ℝ) * (x0 + δ / w) = (w : ℝ) * x0 + δ := by field_simp
  have hbbR : 5 * |(Db : ℝ)| ≤ w := by exact_mod_cast hbb
  have hbcR : 5 * |(Dc : ℝ)| ≤ w := by exact_mod_cast hbc
  have eb : |(Db : ℝ) * δ / w| ≤ 1 / 25 := by
    rw [abs_div, abs_mul, abs_of_pos hwR, div_le_iff₀ hwR]
    have := mul_le_mul_of_nonneg_left hδ (abs_nonneg (Db : ℝ))
    linarith
  have ec : |(Dc : ℝ) * δ / w| ≤ 1 / 25 := by
    rw [abs_div, abs_mul, abs_of_pos hwR, div_le_iff₀ hwR]
    have := mul_le_mul_of_nonneg_left hδ (abs_nonneg (Dc : ℝ))
    linarith
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  obtain ⟨c1, c2⟩ := abs_le.mp h3
  obtain ⟨d1, d2⟩ := abs_le.mp eb
  obtain ⟨e1, e2⟩ := abs_le.mp ec
  have ebq : (Db : ℝ) * (x0 + δ / w) + σb / 5 - mb
      = ((Db : ℝ) * x0 + σb / 5 - mb) + (Db : ℝ) * δ / w := by ring
  have ecq : (Dc : ℝ) * (x0 + δ / w) + σc / 5 - mc
      = ((Dc : ℝ) * x0 + σc / 5 - mc) + (Dc : ℝ) * δ / w := by ring
  refine ⟨x0 + δ / w, mb, mc, ?_, ?_, ?_, ?_⟩
  · rw [hxw]; exact hfar
  · rw [ebq, abs_le]; constructor <;> linarith
  · rw [ecq, abs_le]; constructor <;> linarith
  · rw [ebq, ecq, abs_le]; constructor <;> linarith

lemma spread3 (a b : ℝ) (h1 : |a| ≤ 2 / 5) (h2 : |b| ≤ 2 / 5) (h3 : |a - b| ≤ 2 / 5) :
    ∃ lo : ℝ, lo ≤ 0 ∧ lo ≤ a ∧ lo ≤ b ∧ 0 ≤ lo + 2 / 5 ∧ a ≤ lo + 2 / 5 ∧ b ≤ lo + 2 / 5 := by
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have hm : min 0 (min a b) = 0 ∨ min 0 (min a b) = a ∨ min 0 (min a b) = b := by
    rcases min_choice 0 (min a b) with h | h
    · exact Or.inl h
    · rcases min_choice a b with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  refine ⟨min 0 (min a b), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_, ?_, ?_⟩
  · have : -(2 / 5) ≤ min 0 (min a b) :=
      le_min (by norm_num) (le_min (by linarith) (by linarith))
    linarith
  · rcases hm with h | h | h <;> rw [h] <;> linarith
  · rcases hm with h | h | h <;> rw [h] <;> linarith

end LRSpectrumFull
