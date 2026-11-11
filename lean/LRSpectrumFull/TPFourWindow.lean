/-
# TP'(4), module M6a: windows, perturbation and three arcs (tools for Lemma 7)

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 7 (i), (ii), (iii).

* `exists_coset_window` / `exists_window` : the coset claim of Lemma 7(i) (Bezout once): for `p ≥ 2` coprime to `q`
  the values `q k / p` meet every closed window of length `16/25 ≥ 1/2` modulo 1.
* `exists_perturb`   : the perturbation of Lemma 4 / Lemma 7(ii): some `δ`, `|δ| ≤ 1/5`, with `‖y + δ‖ ≥ 1/5`.
* `three_arcs`       : Lemma 7(iii): three arcs whose centres lie in an interval of length 2 miss a residue.
* `exists_good_3`    : the same for `badImg` of three free runners of one class.
-/
import LRSpectrumFull.TPFourCoset
import LRSpectrumFull.TPFourCoincide

namespace LRSpectrumFull

lemma exists_coset_window (p q : ℤ) (hp : 2 ≤ p) (hc : IsCoprime p q) (y : ℝ) :
    ∃ k m : ℤ, |y + ((q * k : ℤ) : ℝ) / (p : ℝ) - m| ≤ 8 / 25 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  set r : ℤ := ⌈(-(8 / 25) - y) * p⌉ with hr
  obtain ⟨k, b, hkb⟩ := bezout_solve p q hc r
  refine ⟨k, b, ?_⟩
  have hz : ((q * k : ℤ) : ℝ) = (r : ℝ) + (p : ℝ) * b := by exact_mod_cast hkb
  have e : y + ((q * k : ℤ) : ℝ) / (p : ℝ) - b = y + (r : ℝ) / p := by
    rw [hz]; field_simp; ring
  rw [e]
  have r1 : (-(8 / 25) - y) * p ≤ r := Int.le_ceil _
  have r2 : (r : ℝ) < (-(8 / 25) - y) * p + 1 := Int.ceil_lt_add_one _
  rw [abs_le]
  constructor
  · have : -(8 / 25) - y ≤ (r : ℝ) / p := by rw [le_div_iff₀ hpos]; exact r1
    linarith
  · have : (r : ℝ) / p < 8 / 25 - y := by
      rw [div_lt_iff₀ hpos]; nlinarith
    linarith

lemma exists_window_pos (D E : ℤ) (hD : 0 < D) (hnd : ¬ D ∣ E) (y : ℝ) :
    ∃ k m : ℤ, |y + ((E * k : ℤ) : ℝ) / (D : ℝ) - m| ≤ 8 / 25 := by
  obtain ⟨g, D', E', hg, hgcd, hD', hE'⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left E hD.ne')
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hD'pos : 0 < D' := by
    by_contra hle
    push Not at hle
    nlinarith
  have hcop : IsCoprime D' E' := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hD'2 : 2 ≤ D' := by
    by_contra hlt
    have h1 : D' = 1 := by omega
    apply hnd
    exact ⟨E', by rw [hE', hD', h1]; ring⟩
  obtain ⟨k, m, hkm⟩ := exists_coset_window D' E' hD'2 hcop y
  refine ⟨k, m, ?_⟩
  have hD'R : (D' : ℝ) ≠ 0 := by exact_mod_cast hD'pos.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDe : (D : ℝ) = D' * g := by exact_mod_cast hD'
  have hEe : (E : ℝ) = E' * g := by exact_mod_cast hE'
  have e : ((E * k : ℤ) : ℝ) / (D : ℝ) = ((E' * k : ℤ) : ℝ) / (D' : ℝ) := by
    rw [div_eq_div_iff hDR hD'R]
    push_cast
    rw [hDe, hEe]
    ring
  rw [e]
  exact hkm

lemma exists_window (D E : ℤ) (hD : D ≠ 0) (hnd : ¬ D ∣ E) (y : ℝ) :
    ∃ k m : ℤ, |y + ((E * k : ℤ) : ℝ) / (D : ℝ) - m| ≤ 8 / 25 := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨k, m, hk⟩ := exists_window_pos (-D) (-E) (by omega)
      (fun hd => hnd (dvd_neg.mp (neg_dvd.mp hd))) y
    refine ⟨k, m, ?_⟩
    have e : ((-E * k : ℤ) : ℝ) / ((-D : ℤ) : ℝ) = ((E * k : ℤ) : ℝ) / (D : ℝ) := by
      push_cast
      rw [neg_mul, neg_div_neg_eq]
    rw [e] at hk
    exact hk
  · exact exists_window_pos D E h hnd y

/-- A shift `δ` with `|δ| ≤ 1/5` that moves `y` to distance at least `1/5` from the integers. -/
lemma exists_perturb (y : ℝ) : ∃ δ : ℝ, |δ| ≤ 1 / 5 ∧ 1 / 5 ≤ tpDist (y + δ) := by
  by_cases hfar : 1 / 5 ≤ tpDist y
  · exact ⟨0, by norm_num, by simpa using hfar⟩
  · push Not at hfar
    set c0 : ℝ := y - round y with hc0
    have hc0abs : |c0| < 1 / 5 := hfar
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hc0abs
    set δ : ℝ := (if 0 ≤ c0 then 1 / 5 else -(1 / 5)) - c0 with hδ
    have hδb : |δ| ≤ 1 / 5 := by
      rw [hδ]; split_ifs with h
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
    refine ⟨δ, hδb, ?_⟩
    rw [hδ]
    split_ifs with h
    · refine far_of_between _ (round y) ?_ ?_ <;> linarith
    · refine far_of_between _ (round y - 1) ?_ ?_ <;> push_cast <;> linarith

/-- Lemma 7(iii): three arcs with centres in `[L, L+2]` miss the residue `⌊L⌋ + 4`. -/
lemma three_arcs (L g1 g2 g3 : ℝ) (h1 : L ≤ g1 ∧ g1 ≤ L + 2) (h2 : L ≤ g2 ∧ g2 ≤ L + 2)
    (h3 : L ≤ g3 ∧ g3 ≤ L + 2) :
    ∃ z : ZMod 5, z ∉ arc g1 ∧ z ∉ arc g2 ∧ z ∉ arc g3 := by
  have key : ∀ g : ℝ, L ≤ g → g ≤ L + 2 → ((⌊L⌋ + 4 : ℤ) : ZMod 5) ∉ arc g := by
    intro g hl hu hmem
    unfold arc at hmem
    simp only [Finset.mem_image, Finset.mem_Icc] at hmem
    obtain ⟨k, ⟨k1, k2⟩, hk⟩ := hmem
    have f1 : ⌊L⌋ ≤ ⌊g⌋ := Int.floor_mono hl
    have c1 : ⌈g⌉ ≤ ⌈L + ((2 : ℤ) : ℝ)⌉ := Int.ceil_mono (by push_cast; linarith)
    rw [Int.ceil_add_intCast] at c1
    have c2 : ⌈L⌉ ≤ ⌊L⌋ + 1 := Int.ceil_le_floor_add_one L
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub k (⌊L⌋ + 4) 5).mp hk
    have hd' : (5 : ℤ) ∣ (⌊L⌋ + 4) - k := by exact_mod_cast hd
    omega
  exact ⟨_, key g1 h1.1 h1.2, key g2 h2.1 h2.2, key g3 h3.1 h3.2⟩

lemma mem_badImg_class (va vb : ℕ) (βb : ℝ) (ε m : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ha : (va : ZMod 5) ≠ 0) (hb : (vb : ZMod 5) = (ε : ZMod 5) * va) (j : ZMod 5) :
    j ∈ badImg vb βb ↔ -((va : ZMod 5) * j) ∈ arc ((ε : ℝ) * βb + ((5 * m : ℤ) : ℝ)) := by
  have hb0 : (vb : ZMod 5) ≠ 0 := by
    intro h0
    rw [hb] at h0
    rcases hε with rfl | rfl <;> simp at h0 <;> exact ha h0
  rw [mem_badImg_iff hb0, hb, ← mem_arc_eps ε m hε]
  have : -((ε : ZMod 5) * va * j) = (ε : ZMod 5) * -((va : ZMod 5) * j) := by ring
  rw [this]

lemma exists_good_3 (va vb vc : ℕ) (βa βb βc : ℝ) (εb εc mb mc : ℤ) (hεb : εb = 1 ∨ εb = -1)
    (hεc : εc = 1 ∨ εc = -1) (ha : (va : ZMod 5) ≠ 0)
    (hb : (vb : ZMod 5) = (εb : ZMod 5) * va) (hc : (vc : ZMod 5) = (εc : ZMod 5) * va)
    (L : ℝ) (h1 : L ≤ βa ∧ βa ≤ L + 2)
    (h2 : L ≤ (εb : ℝ) * βb + ((5 * mb : ℤ) : ℝ) ∧ (εb : ℝ) * βb + ((5 * mb : ℤ) : ℝ) ≤ L + 2)
    (h3 : L ≤ (εc : ℝ) * βc + ((5 * mc : ℤ) : ℝ) ∧ (εc : ℝ) * βc + ((5 * mc : ℤ) : ℝ) ≤ L + 2) :
    ∃ j : ZMod 5, j ∉ badImg va βa ∧ j ∉ badImg vb βb ∧ j ∉ badImg vc βc := by
  obtain ⟨z, hz1, hz2, hz3⟩ := three_arcs L _ _ _ h1 h2 h3
  have hj : -((va : ZMod 5) * (-((va : ZMod 5)⁻¹ * z))) = z := by
    rw [mul_neg, neg_neg, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨-((va : ZMod 5)⁻¹ * z), ?_, ?_, ?_⟩
  · rw [mem_badImg_iff ha, hj]; exact hz1
  · rw [mem_badImg_class va vb βb εb mb hεb ha hb, hj]; exact hz2
  · rw [mem_badImg_class va vc βc εc mc hεc ha hc, hj]; exact hz3

end LRSpectrumFull
