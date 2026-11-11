/-
# TP'(3) reduced to Case A

`TPp_three_of_caseA`: if Case A holds (primitive sorted triples with `c ≥ 16`, `c ≠ a + b`), then `TPp 3`.
Cases R (`c = a + b`) and F (`c ≤ 15`) are the verified `caseR`, `TPF.caseF`.  Steps: sorted primitive triple
(case split), rescaling by the gcd, ordering (six permutations), `N = 4`.
-/
import LRSpectrumFull.TPFMain

namespace LRSpectrumFull

/-- Case A: sorted primitive triples with `c ≥ 16` and `c ≠ a + b`. -/
def CaseA : Prop :=
  ∀ a b c : ℕ, 0 < a → a < b → b < c → 16 ≤ c → c ≠ a + b →
    Nat.gcd (Nat.gcd a b) c = 1 → ∀ sa sb sc : ℤ,
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4)

lemma three_primitive (hA : CaseA) (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (sa sb sc : ℤ) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4) := by
  by_cases hc15 : c ≤ 15
  · exact TPF.caseF a b c ha hab hbc hc15 hg sa sb sc
  by_cases hR : c = a + b
  · subst hR
    have hcop : Nat.Coprime a b := by
      have h1 : Nat.gcd a b ∣ a + b := Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
      have : Nat.gcd a b ∣ Nat.gcd (Nat.gcd a b) (a + b) := Nat.dvd_gcd (dvd_refl _) h1
      rw [hg] at this
      exact Nat.dvd_one.mp this
    exact caseR a b ha (by omega) hcop (by omega) sa sb sc
  · exact hA a b c ha hab hbc (by omega) hR hg sa sb sc

lemma split3 (a b c : ℕ) (ha : 0 < a) :
    ∃ g a' b' c' : ℕ, 0 < g ∧ Nat.gcd (Nat.gcd a' b') c' = 1 ∧ a = g * a' ∧ b = g * b' ∧ c = g * c' := by
  have hgpos : 0 < Nat.gcd (Nat.gcd a b) c := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ ha)
  have hgab : Nat.gcd (Nat.gcd a b) c ∣ Nat.gcd a b := Nat.gcd_dvd_left _ _
  have hga : Nat.gcd (Nat.gcd a b) c ∣ a := hgab.trans (Nat.gcd_dvd_left _ _)
  have hgb : Nat.gcd (Nat.gcd a b) c ∣ b := hgab.trans (Nat.gcd_dvd_right _ _)
  have hgc : Nat.gcd (Nat.gcd a b) c ∣ c := Nat.gcd_dvd_right _ _
  refine ⟨Nat.gcd (Nat.gcd a b) c, a / Nat.gcd (Nat.gcd a b) c, b / Nat.gcd (Nat.gcd a b) c,
    c / Nat.gcd (Nat.gcd a b) c, hgpos, ?_, ?_, ?_, ?_⟩
  · rw [Nat.gcd_div hga hgb, Nat.gcd_div hgab hgc]
    exact Nat.div_self hgpos
  · exact (Nat.mul_div_cancel' hga).symm
  · exact (Nat.mul_div_cancel' hgb).symm
  · exact (Nat.mul_div_cancel' hgc).symm

lemma three_sorted (hA : CaseA) (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (sa sb sc : ℤ) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4) := by
  obtain ⟨g, a', b', c', hgpos, hprim, rfl, rfl, rfl⟩ := split3 a b c ha
  have ha' : 0 < a' := Nat.pos_of_mul_pos_left ha
  have hab' : a' < b' := Nat.lt_of_mul_lt_mul_left hab
  have hbc' : b' < c' := Nat.lt_of_mul_lt_mul_left hbc
  obtain ⟨t, h1, h2, h3⟩ := three_primitive hA a' b' c' ha' hab' hbc' hprim sa sb sc
  have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  refine ⟨t / g, ?_, ?_, ?_⟩
  · have : ((g * a' : ℕ) : ℝ) * (t / g) = (a' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h1
  · have : ((g * b' : ℕ) : ℝ) * (t / g) = (b' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h2
  · have : ((g * c' : ℕ) : ℝ) * (t / g) = (c' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h3

lemma three_any (hA : CaseA) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (sa sb sc : ℤ) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4) := by
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3
  · exact three_sorted hA a b c ha h1 h3 sa sb sc
  · -- a<b, a<c, c<b : a<c<b
    obtain ⟨t, x, y, z⟩ := three_sorted hA a c b ha h2 h3 sa sc sb
    exact ⟨t, x, z, y⟩
  · omega
  · -- a<b, c<a : c<a<b
    obtain ⟨t, x, y, z⟩ := three_sorted hA c a b hc h2 h1 sc sa sb
    exact ⟨t, y, z, x⟩
  · -- b<a, a<c : b<a<c
    obtain ⟨t, x, y, z⟩ := three_sorted hA b a c hb h1 h2 sb sa sc
    exact ⟨t, y, x, z⟩
  · omega
  · -- b<a, c<a, b<c : b<c<a
    obtain ⟨t, x, y, z⟩ := three_sorted hA b c a hb h3 h2 sb sc sa
    exact ⟨t, z, x, y⟩
  · -- c<b<a
    obtain ⟨t, x, y, z⟩ := three_sorted hA c b a hc h3 h1 sc sb sa
    exact ⟨t, z, y, x⟩

theorem TPp_three_of_caseA (hA : CaseA) : TPp 3 := by
  intro v hv hinj s
  have h01 : v 0 ≠ v 1 := fun h => absurd (hinj h) (by decide)
  have h02 : v 0 ≠ v 2 := fun h => absurd (hinj h) (by decide)
  have h12 : v 1 ≠ v 2 := fun h => absurd (hinj h) (by decide)
  obtain ⟨t, x, y, z⟩ := three_any hA (v 0) (v 1) (v 2) (hv 0) (hv 1) (hv 2) h01 h02 h12 (s 0) (s 1) (s 2)
  refine ⟨t, ?_⟩
  have e : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  intro i
  rw [e]
  fin_cases i
  · simpa using x
  · simpa using y
  · simpa using z

end LRSpectrumFull
