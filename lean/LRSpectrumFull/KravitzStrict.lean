/-
# Strict bound: `ML > 2/7` (hence `D < 3/14`) for large coordinates

The strict analogue of the `≥`-chain, built on the *interior*-band covering
`double_band_cover_strict` (every residue gives `‖·‖ > 2/7` strictly). This removes the
boundary caveat: for `r > 30`, `D(p,q,r) < 3/14` *strictly*, so `D = 3/14` forces `r ≤ 30`,
and the classification `D ≥ 3/14 ⟺ L₃` becomes exact. No `sorry`.
-/

import LRSpectrumFull.KravitzCovering
import LRSpectrumFull.KravitzHookup

namespace LRSpectrumFull

variable {k : ℕ}

/-- Strict lower bound for the gap: if every runner is `> c` from the integers, the gap `> c`. -/
theorem lt_gap (v : Fin (k + 1) → ℤ) (t : ℝ) (c : ℝ)
    (h : ∀ i, c < nearestIntDist ((v i : ℝ) * t)) : c < gap v t := by
  simp only [gap, Finset.lt_inf'_iff]
  intro i _; exact h i

/-- A real strictly inside the middle band `(2/7, 5/7)` is strictly `> 2/7` from the integers. -/
theorem nid_gt_two_sevenths (y : ℝ) (h1 : 2 / 7 < y) (h2 : y < 5 / 7) :
    2 / 7 < nearestIntDist y := by
  rcases le_or_gt y (1 / 2) with h | h
  · rw [nearestIntDist_eq_self_of_le_half y (by linarith) h]; linarith
  · have e : nearestIntDist y = nearestIntDist (1 - y) := by
      rw [show (1 : ℝ) - y = -y + ((1 : ℤ) : ℝ) by push_cast; ring,
        nearestIntDist_add_int, nearestIntDist_neg]
    rw [e, nearestIntDist_eq_self_of_le_half (1 - y) (by linarith) (by linarith)]; linarith

/-- Strict integer band ⟹ `nid > 2/7`. If `2m < 7N < 5m` then `‖N/m‖ > 2/7`. -/
theorem nid_gt_of_band (N m : ℤ) (hm : 0 < m) (hlo : 2 * m < 7 * N) (hhi : 7 * N < 5 * m) :
    2 / 7 < nearestIntDist ((N : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply nid_gt_two_sevenths
  · rw [lt_div_iff₀ hmR]
    have h : (2 : ℝ) * m < 7 * N := by exact_mod_cast hlo
    linarith
  · rw [div_lt_iff₀ hmR]
    have h : (7 : ℝ) * N < 5 * m := by exact_mod_cast hhi
    linarith

/-- Strict runner band ⟹ `nid > 2/7`. -/
theorem nid_runner_gt (a k m c : ℤ) (hm : 0 < m)
    (hlo : 2 * m < 7 * (a * k - c * m)) (hhi : 7 * (a * k - c * m) < 5 * m) :
    2 / 7 < nearestIntDist ((a : ℝ) * ((k : ℝ) / (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))
  have e : (a : ℝ) * ((k : ℝ) / (m : ℝ))
      = ((a * k - c * m : ℤ) : ℝ) / (m : ℝ) + ((c : ℤ) : ℝ) := by
    field_simp; push_cast; ring
  rw [e, nearestIntDist_add_int]
  exact nid_gt_of_band (a * k - c * m) m hm hlo hhi

/-- Strict pair-sum construction. -/
theorem ML_gt_at_pairsum (p q r k : ℤ) (c : ℝ) (hpr : ((p + r : ℤ) : ℝ) ≠ 0)
    (hp : c < nearestIntDist ((p : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ))))
    (hq : c < nearestIntDist ((q : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))) :
    c < ML ![p, q, r] := by
  refine lt_of_lt_of_le ?_ (gap_le_ML ![p, q, r] ((k : ℝ) / ((p + r : ℤ) : ℝ)))
  apply lt_gap
  intro i
  fin_cases i
  · show c < nearestIntDist ((![p, q, r] 0 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    simpa using hp
  · show c < nearestIntDist ((![p, q, r] 1 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    simpa using hq
  · show c < nearestIntDist ((![p, q, r] 2 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    rw [show ((![p, q, r] 2 : ℤ) : ℝ) = (r : ℝ) by simp, nid_runner_swap p r k hpr]
    exact hp

/-- Strict full-band tile: both runners strictly in the band ⟹ `ML > 2/7`. -/
theorem ML_gt_fullband_k (p q r k cp cq : ℤ) (hm : 0 < p + r)
    (hp1 : 2 * (p + r) < 7 * (p * k - cp * (p + r)))
    (hp2 : 7 * (p * k - cp * (p + r)) < 5 * (p + r))
    (hq1 : 2 * (p + r) < 7 * (q * k - cq * (p + r)))
    (hq2 : 7 * (q * k - cq * (p + r)) < 5 * (p + r)) :
    2 / 7 < ML ![p, q, r] := by
  have hpr : ((p + r : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < ((p + r : ℤ) : ℝ))
  exact ML_gt_at_pairsum p q r k (2 / 7) hpr
    (nid_runner_gt p k (p + r) cp hm hp1 hp2) (nid_runner_gt q k (p + r) cq hm hq1 hq2)

/-- Strict unconditional inverse sweep, via the interior-band covering. -/
theorem ML_gt_sweep_cover (p q r a b : ℤ) (_hp : 0 < p) (hm : 33 ≤ p + r)
    (hbez : p * a + (p + r) * b = 1)
    (hs0 : 0 < (q * a) % (p + r)) (hs2 : 2 * ((q * a) % (p + r)) ≠ p + r) :
    2 / 7 < ML ![p, q, r] := by
  set s := (q * a) % (p + r) with hs
  set dd := (q * a) / (p + r) with hdd
  have hqa : q * a = s + (p + r) * dd := (Int.emod_add_mul_ediv (q * a) (p + r)).symm
  have hsM : s < p + r := Int.emod_lt_of_pos _ (by omega)
  obtain ⟨ℓ, hℓlo, hℓhi, c, hclo, hchi⟩ := double_band_cover_strict (p + r) s hm hs0 hsM hs2
  refine ML_gt_fullband_k p q r (a * ℓ) (-b * ℓ) (c + dd * ℓ) (by omega) ?_ ?_ ?_ ?_
  · have hidp : p * (a * ℓ) - (-b * ℓ) * (p + r) = ℓ := by linear_combination ℓ * hbez
    rw [hidp]; omega
  · have hidp : p * (a * ℓ) - (-b * ℓ) * (p + r) = ℓ := by linear_combination ℓ * hbez
    rw [hidp]; omega
  · have hidq : q * (a * ℓ) - (c + dd * ℓ) * (p + r) = ℓ * s - c * (p + r) := by
      linear_combination ℓ * hqa
    rw [hidq]; omega
  · have hidq : q * (a * ℓ) - (c + dd * ℓ) * (p + r) = ℓ * s - c * (p + r) := by
      linear_combination ℓ * hqa
    rw [hidq]; omega

/-- Strict sweep through the `(q,r)` pairing. -/
theorem ML_gt_sweep_cover_qr (p q r a b : ℤ) (hq : 0 < q) (hm : 33 ≤ q + r)
    (hbez : q * a + (q + r) * b = 1)
    (hs0 : 0 < (p * a) % (q + r)) (hs2 : 2 * ((p * a) % (q + r)) ≠ q + r) :
    2 / 7 < ML ![p, q, r] := by
  rw [← ML_swap01 p q r]; exact ML_gt_sweep_cover q p r a b hq hm hbez hs0 hs2

/-- Strict comparable closure via the coprime `(q,r)` pairing (`q+r ≥ 33`). -/
theorem ML_gt_of_coprime_qr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hm : 33 ≤ q + r) (hcop : IsCoprime q (q + r)) : 2 / 7 < ML ![p, q, r] := by
  obtain ⟨a, b, hab⟩ := hcop
  have hca : IsCoprime (q + r) a := ⟨b, q, by linear_combination hab⟩
  set s := (p * a) % (q + r) with hsdef
  set quot := (p * a) / (q + r) with hqdef
  have hemod : s + (q + r) * quot = p * a := by rw [hsdef, hqdef]; exact Int.emod_add_mul_ediv _ _
  have hs0 : 0 < s := by
    have hge : 0 ≤ s := hsdef ▸ Int.emod_nonneg (p * a) (by omega)
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have hdvd : (q + r) ∣ p * a := by rw [hsdef] at h; exact Int.dvd_of_emod_eq_zero h.symm
      have hdq : (q + r) ∣ p := hca.dvd_of_dvd_mul_right hdvd
      have := Int.le_of_dvd hp hdq; omega
  have hs2 : 2 * s ≠ q + r := by
    intro he
    have h2 : (q + r) ∣ 2 * p * a := ⟨1 + 2 * quot, by linear_combination -2 * hemod + he⟩
    have h2' : (q + r) ∣ (2 * p) * a := by rw [show (2 * p) * a = 2 * p * a by ring]; exact h2
    have hdp : (q + r) ∣ 2 * p := hca.dvd_of_dvd_mul_right h2'
    have := Int.le_of_dvd (by omega) hdp; omega
  exact ML_gt_sweep_cover_qr p q r a b (by omega) hm (by linear_combination hab) hs0 hs2

/-- Strict comparable closure via the coprime `(p,r)` pairing (`p+r ≥ 33`, `p+r ≠ 2q`). -/
theorem ML_gt_of_coprime_pr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hm : 33 ≤ p + r) (hne : p + r ≠ 2 * q) (hcop : IsCoprime p (p + r)) :
    2 / 7 < ML ![p, q, r] := by
  obtain ⟨a, b, hab⟩ := hcop
  have hca : IsCoprime (p + r) a := ⟨b, p, by linear_combination hab⟩
  set s := (q * a) % (p + r) with hsdef
  set quot := (q * a) / (p + r) with hqdef
  have hemod : s + (p + r) * quot = q * a := by rw [hsdef, hqdef]; exact Int.emod_add_mul_ediv _ _
  have hs0 : 0 < s := by
    have hge : 0 ≤ s := hsdef ▸ Int.emod_nonneg (q * a) (by omega)
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have hdvd : (p + r) ∣ q * a := by rw [hsdef] at h; exact Int.dvd_of_emod_eq_zero h.symm
      have hdq : (p + r) ∣ q := hca.dvd_of_dvd_mul_right hdvd
      have := Int.le_of_dvd (by omega) hdq; omega
  have hs2 : 2 * s ≠ p + r := by
    intro he
    have h2 : (p + r) ∣ 2 * q * a := ⟨1 + 2 * quot, by linear_combination -2 * hemod + he⟩
    have h2' : (p + r) ∣ (2 * q) * a := by rw [show (2 * q) * a = 2 * q * a by ring]; exact h2
    have hdq : (p + r) ∣ 2 * q := hca.dvd_of_dvd_mul_right h2'
    obtain ⟨m, hm2⟩ := hdq
    have hmpos : 0 < m := by nlinarith [hm2, hp, hpq, hqr]
    have hmlt : m < 2 := by nlinarith [hm2, hpq, hqr, hp]
    have hm1 : m = 1 := by omega
    rw [hm1, mul_one] at hm2; omega
  exact ML_gt_sweep_cover p q r a b hp hm (by linear_combination hab) hs0 hs2

/-- Strict Case A via `(q,r)`: shared factor `≥3` gives `ML ≥ 1/3 > 2/7`. -/
theorem ML_gt_caseA_qr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hg : 3 ≤ (Int.gcd q r : ℤ)) (hcop : IsCoprime p (Int.gcd q r : ℤ)) :
    2 / 7 < ML ![p, q, r] := by
  have h := ML_ge_caseA_qr p q r hp hpq hqr hg hcop
  -- ML_ge_caseA_qr weakened to 2/7; recover strict via the underlying 1/3 bound
  set g : ℤ := (Int.gcd q r : ℤ) with hgdef
  obtain ⟨w₁, hw₁⟩ := Int.gcd_dvd_left (a := q) (b := r)
  obtain ⟨w₂, hw₂⟩ := Int.gcd_dvd_right (a := q) (b := r)
  rw [← hgdef] at hw₁ hw₂
  have hgpos : 0 < g := by omega
  have hw1pos : 0 < w₁ := by
    rcases lt_or_ge w₁ 1 with h' | h'
    · nlinarith [hw₁, hgpos, hpq, hp]
    · omega
  have hw12 : w₁ < w₂ := by nlinarith [hw₁, hw₂, hqr, hgpos]
  have hN : 3 ≤ w₁ + w₂ := by omega
  have hcopw : IsCoprime w₁ (w₁ + w₂) := by
    have hco : Int.gcd (q / g) (r / g) = 1 := Int.gcd_div_gcd_div_gcd (by omega : 0 < Int.gcd q r)
    have e1 : q / g = w₁ := by rw [hw₁]; exact Int.mul_ediv_cancel_left _ (by omega)
    have e2 : r / g = w₂ := by rw [hw₂]; exact Int.mul_ediv_cancel_left _ (by omega)
    rw [e1, e2] at hco
    have hcw : IsCoprime w₁ w₂ := Int.isCoprime_iff_gcd_eq_one.mpr hco
    rw [add_comm]; simpa using hcw.add_mul_left_right 1
  have hcaseA : 1 / 3 ≤ ML ![q, r, p] :=
    ML_ge_third_caseA q r p g w₁ w₂ (w₁ + w₂) (by omega) hN hw₁ hw₂ rfl hcopw hcop
  rw [ML_swap12 q p r, ML_swap01 p q r] at hcaseA; linarith

/-- Strict Case A via `(p,r)`. -/
theorem ML_gt_caseA_pr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hg : 3 ≤ (Int.gcd p r : ℤ)) (hcop : IsCoprime q (Int.gcd p r : ℤ)) :
    2 / 7 < ML ![p, q, r] := by
  set g : ℤ := (Int.gcd p r : ℤ) with hgdef
  obtain ⟨w₁, hw₁⟩ := Int.gcd_dvd_left (a := p) (b := r)
  obtain ⟨w₂, hw₂⟩ := Int.gcd_dvd_right (a := p) (b := r)
  rw [← hgdef] at hw₁ hw₂
  have hgpos : 0 < g := by omega
  have hw1pos : 0 < w₁ := by
    rcases lt_or_ge w₁ 1 with h' | h'
    · nlinarith [hw₁, hgpos, hp]
    · omega
  have hw12 : w₁ < w₂ := by nlinarith [hw₁, hw₂, hpq, hqr, hgpos]
  have hN : 3 ≤ w₁ + w₂ := by omega
  have hcopw : IsCoprime w₁ (w₁ + w₂) := by
    have hco : Int.gcd (p / g) (r / g) = 1 := Int.gcd_div_gcd_div_gcd (by omega : 0 < Int.gcd p r)
    have e1 : p / g = w₁ := by rw [hw₁]; exact Int.mul_ediv_cancel_left _ (by omega)
    have e2 : r / g = w₂ := by rw [hw₂]; exact Int.mul_ediv_cancel_left _ (by omega)
    rw [e1, e2] at hco
    have hcw : IsCoprime w₁ w₂ := Int.isCoprime_iff_gcd_eq_one.mpr hco
    rw [add_comm]; simpa using hcw.add_mul_left_right 1
  have hcaseA : 1 / 3 ≤ ML ![p, r, q] :=
    ML_ge_third_caseA p r q g w₁ w₂ (w₁ + w₂) (by omega) hN hw₁ hw₂ rfl hcopw hcop
  rw [ML_swap12 p q r] at hcaseA; linarith

/-- **STRICT large-coordinate bound.** Sorted primitive `0<p<q<r` with `r > 30` ⟹
`ML(p,q,r) > 2/7` *strictly*, i.e. `D(p,q,r) < 3/14`. -/
theorem ML_gt_of_large (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : 30 < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ)) :
    2 / 7 < ML ![p, q, r] := by
  have hg1 : 1 ≤ (Int.gcd q r : ℤ) := by
    have : 0 < Int.gcd q r := Int.gcd_pos_of_ne_zero_right q (by omega); omega
  rcases lt_trichotomy (Int.gcd q r : ℤ) 2 with hlt | heq | hgt
  · have hcop : IsCoprime q r := Int.isCoprime_iff_gcd_eq_one.mpr (by omega)
    have hcqr : IsCoprime q (q + r) := by rw [add_comm]; simpa using hcop.add_mul_left_right 1
    exact ML_gt_of_coprime_qr p q r hp hpq hqr (by omega) hcqr
  · have h2q : (2 : ℤ) ∣ q := heq ▸ Int.gcd_dvd_left (a := q) (b := r)
    have h2r : (2 : ℤ) ∣ r := heq ▸ Int.gcd_dvd_right (a := q) (b := r)
    have hgp1 : 1 ≤ (Int.gcd p r : ℤ) := by
      have : 0 < Int.gcd p r := Int.gcd_pos_of_ne_zero_right p (by omega); omega
    rcases lt_trichotomy (Int.gcd p r : ℤ) 2 with hlt2 | heq2 | hgt2
    · have hcoppr : IsCoprime p r := Int.isCoprime_iff_gcd_eq_one.mpr (by omega)
      have hcpr : IsCoprime p (p + r) := by rw [add_comm]; simpa using hcoppr.add_mul_left_right 1
      have h2np : ¬ (2 : ℤ) ∣ p := by
        intro hd
        have hu := hcoppr.isUnit_of_dvd' hd h2r
        rw [Int.isUnit_iff] at hu; omega
      have hne : p + r ≠ 2 * q := by
        obtain ⟨rr, hrr⟩ := h2r
        rcases Int.even_or_odd p with ⟨pp, hpp⟩ | ⟨pp, hpp⟩
        · exact absurd ⟨pp, by omega⟩ h2np
        · omega
      exact ML_gt_of_coprime_pr p q r hp hpq hqr (by omega) hne hcpr
    · exfalso
      have h2p : (2 : ℤ) ∣ p := heq2 ▸ Int.gcd_dvd_left (a := p) (b := r)
      obtain ⟨u, v, huv⟩ := hcop_p
      obtain ⟨pp, hpp⟩ := h2p
      obtain ⟨gg, hgg⟩ : (2 : ℤ) ∣ (Int.gcd q r : ℤ) := ⟨1, by rw [heq]; ring⟩
      have : (2 : ℤ) ∣ 1 := ⟨u * pp + v * gg, by rw [← huv, hpp, hgg]; ring⟩
      norm_num at this
    · exact ML_gt_caseA_pr p q r hp hpq hqr (by omega) hcop_q
  · exact ML_gt_caseA_qr p q r hp hpq hqr (by omega) hcop_p

/-- **STRICT `D`-bound:** sorted primitive with `r > 30` ⟹ `D(p,q,r) < 3/14`. -/
theorem D_lt_of_large (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : 30 < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ)) :
    D ![p, q, r] < 3 / 14 := by
  have h := ML_gt_of_large p q r hp hpq hqr hr hcop_p hcop_q
  simp only [D]; linarith

end LRSpectrumFull
