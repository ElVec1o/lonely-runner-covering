/-
# TP'(3), Case F checker (c ≤ 15)

Generic machinery: an integer certificate `(sa, sb, sc, P, D)` means the time `t = P / D` puts the three runners
(speeds `a, b, c`, phases `sa/4, sb/4, sc/4`) at distance `≥ 1/4` from an integer.  Runner `v` with phase `s/4`
is good iff `(4 v P + s D) mod 4D ∈ [D, 3D]`.  The data are produced by
`private/INVENTION_2026_11/tp3/gen_f.c` (TPFData.lean); every check is `decide +kernel`.
-/
import LRSpectrumFull.TPThreeR

namespace LRSpectrumFull
namespace TPF

abbrev E := Int × Int × Int × Int × Int

def goodB (v P D s : Int) : Bool :=
  decide (D ≤ (4 * v * P + s * D) % (4 * D) ∧ (4 * v * P + s * D) % (4 * D) ≤ 3 * D)

def entryOK (a b c : Int) (e : E) : Bool :=
  decide (0 < e.2.2.2.2) && goodB a e.2.2.2.1 e.2.2.2.2 e.1 && goodB b e.2.2.2.1 e.2.2.2.2 e.2.1 &&
    goodB c e.2.2.2.1 e.2.2.2.2 e.2.2.1

def covers (tbl : List E) : Bool :=
  [0, 1, 2, 3].all fun sa => [0, 1, 2, 3].all fun sb => [0, 1, 2, 3].all fun sc =>
    tbl.any fun e => e.1 == sa && e.2.1 == sb && e.2.2.1 == sc

def tripleOK (x : Int × Int × Int × List E) : Bool :=
  x.2.2.2.all (entryOK x.1 x.2.1 x.2.2.1) && covers x.2.2.2

lemma tp_of_goodB (v P D s : Int) (hD : 0 < D) (h : goodB v P D s = true) :
    1 / 4 ≤ tpDist ((v : ℝ) * ((P : ℝ) / D) + (s : ℝ) / 4) := by
  unfold goodB at h
  rw [decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set N : Int := 4 * v * P + s * D with hN
  set w : Int := N / (4 * D) with hw
  set r : Int := N % (4 * D) with hr
  have hdiv : 4 * D * w + r = N := Int.mul_ediv_add_emod N (4 * D)
  have hx : (v : ℝ) * ((P : ℝ) / D) + (s : ℝ) / 4 = (w : ℝ) + (r : ℝ) / (4 * D) := by
    have h' : ((4 * D * w + r : Int) : ℝ) = (N : ℝ) := by rw [hdiv]
    rw [hN] at h'
    push_cast at h'
    field_simp
    linarith
  rw [hx]
  have e1 : (D : ℝ) ≤ r := by exact_mod_cast h1
  have e2 : (r : ℝ) ≤ 3 * D := by exact_mod_cast h2
  refine tpDist_ge_win _ _ w ?_ ?_ (by norm_num) (by norm_num)
  · have : 1 / 4 ≤ (r : ℝ) / (4 * D) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · have : (r : ℝ) / (4 * D) ≤ 3 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith

lemma goodB_mod4 (v P D s : Int) (h : goodB v P D (s % 4) = true) : goodB v P D s = true := by
  unfold goodB at h ⊢
  have : 4 * v * P + s * D = (4 * v * P + (s % 4) * D) + (s / 4) * (4 * D) := by
    have := Int.mul_ediv_add_emod s 4
    linear_combination (-D) * this
  rw [this, Int.add_mul_emod_self_right]
  exact h

/-- one triple from a verified table -/
theorem triple_spec (a b c : Int) (tbl : List E) (h : tripleOK (a, b, c, tbl) = true) (sa sb sc : Int) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4) := by
  unfold tripleOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  unfold covers at hcov
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hcov
  have hs : ∀ s : Int, s % 4 ∈ ([0, 1, 2, 3] : List Int) := by
    intro s
    have h0 : 0 ≤ s % 4 := Int.emod_nonneg _ (by norm_num)
    have h4 : s % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  obtain ⟨e, he, ⟨ea, eb⟩, ec⟩ := hcov _ (hs sa) _ (hs sb) _ (hs sc)
  simp only [List.all_eq_true] at hall
  have hE := hall e he
  unfold entryOK at hE
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hE
  obtain ⟨⟨⟨hD, g1⟩, g2⟩, g3⟩ := hE
  rw [ea] at g1; rw [eb] at g2; rw [ec] at g3
  refine ⟨(e.2.2.2.1 : ℝ) / e.2.2.2.2, ?_, ?_, ?_⟩
  · exact tp_of_goodB _ _ _ _ hD (goodB_mod4 _ _ _ _ g1)
  · exact tp_of_goodB _ _ _ _ hD (goodB_mod4 _ _ _ _ g2)
  · exact tp_of_goodB _ _ _ _ hD (goodB_mod4 _ _ _ _ g3)

end TPF
end LRSpectrumFull
