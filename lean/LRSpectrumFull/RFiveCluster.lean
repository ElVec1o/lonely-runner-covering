/-
# Theorem R5 (real phases), module C: the cluster lemma (paper Lemma 7', with the rigid shape R* absorbed)

Paper proof: ROOMS/OPUS_REAL_PHASES_2026_11_12.md, Lemma 7'(i)-(iii), divisor fact, Lemma R*; the unified version
proved here is written out in ROOMS/R5_LEAN_BLOCK1_2026_11_12.md (section "cluster_div").

Statement `cluster_div`: if `D_b, D_c, D_b - D_c` are nonzero (the first two, and `D_b ≠ D_c`) divisors of `w`,
there is `x` with the slow runner far from 0 and the three pairwise differences of `r_b, r_c, 0` all `≤ 2/5`
(`r_i = D_i x + σ_i - m_i`).  No divisor fact and no separate rigid-shape case: whichever of the three
coincidence/window branches fires, the pair that is bunched exactly is the one whose `|D|` may equal `w`, and the
other two pairs have `2|D| ≤ w` because their `D` divides `w` without being `± w`.

* `exists_coset_window4` : the constant `1/4` window (the paper's true constant; the old `8/25` is not enough here).
* `tight_left4`          : `D_b ∤ D_c`: exact zero of `r_b` and `|r_c| ≤ 1/4`.
* `cluster_perturb`      : Lemma 7'(ii): the perturbation `x ↦ x + δ/w`.
* `cluster_div`          : the unified lemma.
-/
import LRSpectrumFull.RFiveWindow
import LRSpectrumFull.TPFourTight

namespace LRSpectrumFull

lemma exists_coset_window4 (p q : ℤ) (hp : 2 ≤ p) (hc : IsCoprime p q) (y : ℝ) :
    ∃ k m : ℤ, |y + ((q * k : ℤ) : ℝ) / (p : ℝ) - m| ≤ 1 / 4 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  set r : ℤ := ⌈(-(1 / 4) - y) * p⌉ with hr
  obtain ⟨k, b, hkb⟩ := bezout_solve p q hc r
  refine ⟨k, b, ?_⟩
  have hz : ((q * k : ℤ) : ℝ) = (r : ℝ) + (p : ℝ) * b := by exact_mod_cast hkb
  have e : y + ((q * k : ℤ) : ℝ) / (p : ℝ) - b = y + (r : ℝ) / p := by
    rw [hz]; field_simp; ring
  rw [e]
  have r1 : (-(1 / 4) - y) * p ≤ r := Int.le_ceil _
  have r2 : (r : ℝ) < (-(1 / 4) - y) * p + 1 := Int.ceil_lt_add_one _
  rw [abs_le]
  constructor
  · have : -(1 / 4) - y ≤ (r : ℝ) / p := by rw [le_div_iff₀ hpos]; exact r1
    linarith
  · have : (r : ℝ) / p < 1 / 4 - y := by
      rw [div_lt_iff₀ hpos]; nlinarith
    linarith

lemma exists_window4_pos (D E : ℤ) (hD : 0 < D) (hnd : ¬ D ∣ E) (y : ℝ) :
    ∃ k m : ℤ, |y + ((E * k : ℤ) : ℝ) / (D : ℝ) - m| ≤ 1 / 4 := by
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
  obtain ⟨k, m, hkm⟩ := exists_coset_window4 D' E' hD'2 hcop y
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

lemma exists_window4 (D E : ℤ) (hD : D ≠ 0) (hnd : ¬ D ∣ E) (y : ℝ) :
    ∃ k m : ℤ, |y + ((E * k : ℤ) : ℝ) / (D : ℝ) - m| ≤ 1 / 4 := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨k, m, hk⟩ := exists_window4_pos (-D) (-E) (by omega)
      (fun hd => hnd (dvd_neg.mp (neg_dvd.mp hd))) y
    refine ⟨k, m, ?_⟩
    have e : ((-E * k : ℤ) : ℝ) / ((-D : ℤ) : ℝ) = ((E * k : ℤ) : ℝ) / (D : ℝ) := by
      push_cast
      rw [neg_mul, neg_div_neg_eq]
    rw [e] at hk
    exact hk
  · exact exists_window4_pos D E h hnd y

lemma tight_left4 (Db Dc : ℤ) (σb σc : ℝ) (hDb : Db ≠ 0) (hnd : ¬ Db ∣ Dc) :
    ∃ x : ℝ, ∃ mb mc : ℤ, (Db : ℝ) * x + σb - mb = 0 ∧ |(Dc : ℝ) * x + σc - mc| ≤ 1 / 4 := by
  have hDR : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb
  obtain ⟨k, m, hkm⟩ := exists_window4 Db Dc hDb hnd (σc - (Dc : ℝ) * σb / Db)
  have hx : (Db : ℝ) * (((k : ℝ) - σb) / Db) = (k : ℝ) - σb := mul_div_cancel₀ _ hDR
  refine ⟨((k : ℝ) - σb) / Db, k, m, by linarith, ?_⟩
  have e : (Dc : ℝ) * (((k : ℝ) - σb) / Db) + σc - m
      = σc - (Dc : ℝ) * σb / Db + ((Dc * k : ℤ) : ℝ) / (Db : ℝ) - m := by
    push_cast; ring
  rw [e]; exact hkm

lemma pert_le (E : ℝ) (w : ℕ) (hw : 1 ≤ w) (c : ℝ) (hc : 0 ≤ c) (hE : |E| ≤ c * w) (δ : ℝ)
    (hδ : |δ| ≤ 1 / 5) : |E * δ / w| ≤ c / 5 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  rw [abs_div, abs_mul, abs_of_pos hwR, div_le_iff₀ hwR]
  have := mul_le_mul hE hδ (abs_nonneg δ) (mul_nonneg hc hwR.le)
  nlinarith

/-- Lemma 7'(ii): a perturbation `x0 ↦ x0 + δ/w` keeps the slow runner away from 0 and moves the three
pairwise differences by at most `eb/5`, `ec/5`, `ed/5`. -/
lemma cluster_perturb (w : ℕ) (hw : 1 ≤ w) (Db Dc : ℤ) (σb σc φd : ℝ) (x0 : ℝ) (mb mc : ℤ)
    (b0 c0 d0 eb ec ed : ℝ) (heb : 0 ≤ eb) (hec : 0 ≤ ec) (hed : 0 ≤ ed)
    (h1 : |(Db : ℝ) * x0 + σb - mb| ≤ b0) (h2 : |(Dc : ℝ) * x0 + σc - mc| ≤ c0)
    (h3 : |((Db : ℝ) * x0 + σb - mb) - ((Dc : ℝ) * x0 + σc - mc)| ≤ d0)
    (p1 : |(Db : ℝ)| ≤ eb * w) (p2 : |(Dc : ℝ)| ≤ ec * w) (p3 : |(Db : ℝ) - Dc| ≤ ed * w)
    (k1 : b0 + eb / 5 ≤ 2 / 5) (k2 : c0 + ec / 5 ≤ 2 / 5) (k3 : d0 + ed / 5 ≤ 2 / 5) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ |(Db : ℝ) * x + σb - mb| ≤ 2 / 5 ∧
      |(Dc : ℝ) * x + σc - mc| ≤ 2 / 5 ∧
      |((Db : ℝ) * x + σb - mb) - ((Dc : ℝ) * x + σc - mc)| ≤ 2 / 5 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwne : (w : ℝ) ≠ 0 := hwR.ne'
  obtain ⟨δ, hδ, hfar⟩ := exists_perturb ((w : ℝ) * x0 + φd)
  have hwd : (w : ℝ) * (δ / w) = δ := mul_div_cancel₀ _ hwne
  have hxw : (w : ℝ) * (x0 + δ / w) + φd = ((w : ℝ) * x0 + φd) + δ := by
    rw [mul_add, hwd]; ring
  have q1 := pert_le (Db : ℝ) w hw eb heb p1 δ hδ
  have q2 := pert_le (Dc : ℝ) w hw ec hec p2 δ hδ
  have q3 := pert_le ((Db : ℝ) - Dc) w hw ed hed p3 δ hδ
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  obtain ⟨c1, c2⟩ := abs_le.mp h3
  obtain ⟨d1, d2⟩ := abs_le.mp q1
  obtain ⟨e1, e2⟩ := abs_le.mp q2
  obtain ⟨f1, f2⟩ := abs_le.mp q3
  have ebq : (Db : ℝ) * (x0 + δ / w) + σb - mb
      = ((Db : ℝ) * x0 + σb - mb) + (Db : ℝ) * δ / w := by ring
  have ecq : (Dc : ℝ) * (x0 + δ / w) + σc - mc
      = ((Dc : ℝ) * x0 + σc - mc) + (Dc : ℝ) * δ / w := by ring
  have ebcq : ((Db : ℝ) * (x0 + δ / w) + σb - mb) - ((Dc : ℝ) * (x0 + δ / w) + σc - mc)
      = (((Db : ℝ) * x0 + σb - mb) - ((Dc : ℝ) * x0 + σc - mc)) + ((Db : ℝ) - Dc) * δ / w := by ring
  refine ⟨x0 + δ / w, ?_, ?_, ?_, ?_⟩
  · rw [hxw]; exact hfar
  · rw [ebq, abs_le]; constructor <;> linarith
  · rw [ecq, abs_le]; constructor <;> linarith
  · rw [ebcq, abs_le]; constructor <;> linarith

lemma abs_le_of_dvd' (d w : ℤ) (hw : 1 ≤ w) (hd : d ∣ w) : |d| ≤ w :=
  Int.le_of_dvd (by omega) ((abs_dvd d w).mpr hd)

lemma two_abs_le (d w : ℤ) (hw : 1 ≤ w) (hd : d ∣ w) (hne : |d| ≠ w) : 2 * |d| ≤ w := by
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by
    rintro rfl
    omega
  have h1 : 1 ≤ |e| := Int.one_le_abs he0
  have h2 : |w| = |d| * |e| := by rw [he, abs_mul]
  have h3 : |w| = w := abs_of_nonneg (by omega)
  have h4 : |e| ≠ 1 := by
    intro h
    apply hne
    rw [h] at h2
    omega
  have h5 : 2 ≤ |e| := by omega
  nlinarith [mul_nonneg (abs_nonneg d) (sub_nonneg.mpr h5)]

lemma abs_ne_of_not_dvd (a d w : ℤ) (ha : a ∣ w) (hnd : ¬ a ∣ d) : |d| ≠ w := by
  intro h
  apply hnd
  rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at h
    rw [h]
    exact ha
  · rw [h1] at h
    have : d = -w := by omega
    rw [this]
    exact dvd_neg.mpr ha

lemma abs_sub_ne_of_not_dvd (a d w : ℤ) (ha : a ∣ w) (hnd : ¬ a ∣ d) : |a - d| ≠ w := by
  intro h
  apply hnd
  rcases abs_cases (a - d) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at h
    have : d = a - w := by omega
    rw [this]
    exact dvd_sub dvd_rfl ha
  · rw [h1] at h
    have : d = a + w := by omega
    rw [this]
    exact dvd_add dvd_rfl ha

/-- The cluster lemma: all three differences `D_b, D_c, D_b - D_c` divide `w`. -/
lemma cluster_div (w : ℕ) (hw : 1 ≤ w) (Db Dc : ℤ) (σb σc φd : ℝ) (hDb : Db ≠ 0) (hDc : Dc ≠ 0)
    (hne : Db ≠ Dc) (h1 : Db ∣ (w : ℤ)) (h2 : Dc ∣ (w : ℤ)) (h3 : (Db - Dc) ∣ (w : ℤ)) :
    ∃ x : ℝ, ∃ mb mc : ℤ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧
      |(Db : ℝ) * x + σb - mb| ≤ 2 / 5 ∧ |(Dc : ℝ) * x + σc - mc| ≤ 2 / 5 ∧
      |((Db : ℝ) * x + σb - mb) - ((Dc : ℝ) * x + σc - mc)| ≤ 2 / 5 := by
  have hwZ : (1 : ℤ) ≤ w := by exact_mod_cast hw
  have hle : ∀ d : ℤ, d ∣ (w : ℤ) → |(d : ℝ)| ≤ 1 * w := by
    intro d hd
    have h := abs_le_of_dvd' d w hwZ hd
    have h' : |(d : ℝ)| ≤ (w : ℝ) := by exact_mod_cast h
    linarith
  have hhalf : ∀ d : ℤ, d ∣ (w : ℤ) → |d| ≠ (w : ℤ) → |(d : ℝ)| ≤ (1 / 2) * w := by
    intro d hd hne'
    have h := two_abs_le d w hwZ hd hne'
    have h' : 2 * |(d : ℝ)| ≤ (w : ℝ) := by exact_mod_cast h
    linarith
  have hleD3 : |(Db : ℝ) - Dc| ≤ 1 * w := by
    have := hle (Db - Dc) h3
    push_cast at this
    linarith
  by_cases hb : Db ∣ Dc
  · by_cases hc : Dc ∣ Db
    · -- branch 3: `D_c = -D_b`, the pair (b, c) is bunched exactly
      have hDc' : Dc = -Db := by
        have := Int.natAbs_eq_of_dvd_dvd hb hc
        omega
      have hDR : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb
      have hDcR : (Dc : ℝ) = -(Db : ℝ) := by exact_mod_cast hDc'
      obtain ⟨n, hn⟩ : ∃ n : ℤ, |σb + σc - n| ≤ 1 / 2 := ⟨round _, abs_sub_round _⟩
      obtain ⟨hn1, hn2⟩ := abs_le.mp hn
      obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, x0 = ((σb + σc) / 2 - n / 2 - σb) / Db := ⟨_, rfl⟩
      have hX : (Db : ℝ) * x0 = (σb + σc) / 2 - n / 2 - σb := by
        rw [hx0]; exact mul_div_cancel₀ _ hDR
      have hDx : (Dc : ℝ) * x0 = -((σb + σc) / 2 - n / 2 - σb) := by
        rw [hDcR, neg_mul, hX]
      have r1 : (Db : ℝ) * x0 + σb - ((0 : ℤ) : ℝ) = (σb + σc) / 2 - n / 2 := by
        push_cast; linarith
      have r2 : (Dc : ℝ) * x0 + σc - ((n : ℤ) : ℝ) = (σb + σc) / 2 - n / 2 := by
        linarith
      have hhalfb : |(Db : ℝ)| ≤ (1 / 2) * w := by
        have e : |(Db : ℝ) - Dc| = 2 * |(Db : ℝ)| := by
          rw [hDcR, sub_neg_eq_add, ← two_mul, abs_mul]; norm_num
        linarith
      have hhalfc : |(Dc : ℝ)| ≤ (1 / 2) * w := by rw [hDcR, abs_neg]; exact hhalfb
      obtain ⟨x, hfar, c1, c2, c3⟩ := cluster_perturb w hw Db Dc σb σc φd x0 0 n (1 / 4) (1 / 4) 0
        (1 / 2) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
        (by rw [r1, abs_le]; constructor <;> linarith)
        (by rw [r2, abs_le]; constructor <;> linarith)
        (by rw [r1, r2, sub_self]; simp)
        hhalfb hhalfc hleD3 (by norm_num) (by norm_num) (by norm_num)
      exact ⟨x, 0, n, hfar, c1, c2, c3⟩
    · -- branch 2: `D_c ∤ D_b`, `r_c` is bunched exactly at zero
      obtain ⟨x0, mc, mb, hz, hb4⟩ := tight_left4 Dc Db σc σb hDc hc
      have p1 : |(Db : ℝ)| ≤ (1 / 2) * w := hhalf Db h1 (abs_ne_of_not_dvd Dc Db w h2 hc)
      have p3 : |(Db : ℝ) - Dc| ≤ (1 / 2) * w := by
        have hne3 : |Db - Dc| ≠ (w : ℤ) := by
          rw [abs_sub_comm]; exact abs_sub_ne_of_not_dvd Dc Db w h2 hc
        have := hhalf (Db - Dc) h3 hne3
        push_cast at this
        linarith
      obtain ⟨x, hfar, c1, c2, c3⟩ := cluster_perturb w hw Db Dc σb σc φd x0 mb mc (1 / 4) 0 (1 / 4)
        (1 / 2) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) hb4
        (by rw [hz]; simp)
        (by
          obtain ⟨u1, u2⟩ := abs_le.mp hb4
          rw [abs_le]; constructor <;> linarith)
        p1 (hle Dc h2) p3 (by norm_num) (by norm_num) (by norm_num)
      exact ⟨x, mb, mc, hfar, c1, c2, c3⟩
  · -- branch 1: `D_b ∤ D_c`, `r_b` is bunched exactly at zero
    obtain ⟨x0, mb, mc, hz, hc4⟩ := tight_left4 Db Dc σb σc hDb hb
    have p2 : |(Dc : ℝ)| ≤ (1 / 2) * w := hhalf Dc h2 (abs_ne_of_not_dvd Db Dc w h1 hb)
    have p3 : |(Db : ℝ) - Dc| ≤ (1 / 2) * w := by
      have hne3 : |Db - Dc| ≠ (w : ℤ) := abs_sub_ne_of_not_dvd Db Dc w h1 hb
      have := hhalf (Db - Dc) h3 hne3
      push_cast at this
      linarith
    obtain ⟨x, hfar, c1, c2, c3⟩ := cluster_perturb w hw Db Dc σb σc φd x0 mb mc 0 (1 / 4) (1 / 4)
      1 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hz]; simp) hc4
      (by
        obtain ⟨u1, u2⟩ := abs_le.mp hc4
        rw [abs_le]; constructor <;> linarith)
      (hle Db h1) p2 p3 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨x, mb, mc, hfar, c1, c2, c3⟩

end LRSpectrumFull
