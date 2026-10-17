/-
# Hooking the complete covering (`double_band_cover`) into the ML engine

`ML_ge_sweep_cover` is the modular-inverse sweep with the range/span hypotheses of
`ML_ge_sweep_inverse` *replaced* by the unconditional `double_band_cover` (Kravitz Lemma 7.1).
For a coprime comb `p·a + (p+r)·b = 1` with pair-sum `p+r ≥ 12` and inverse step
`s = q·a mod (p+r)` satisfying `0 < s` and `2s ≠ p+r` (both automatic when `gcd(s, p+r)=1`),
we get `ML(p,q,r) ≥ 2/7` — *with no resonance escape hatch*. This is the genuine
comparable-regime closure: the covering `ℓ` lands both the `p`-runner (`ℓ ∈ band`) and the
`q`-runner (`ℓ·s − c·M ∈ band`) in the `2/7`-band of the pair-sum modulus simultaneously,
which is exactly what `ML_ge_fullband_k` consumes. No `sorry`.
-/

import LRSpectrumFull.KravitzCovering
import LRSpectrumFull.KravitzCaseA
import LRSpectrumFull.KravitzBandGe
import LRSpectrumFull.Sweep
import LRSpectrumFull.PermInvariance

namespace LRSpectrumFull

/-- `ML` is invariant under swapping the last two coordinates (from `D_swap12`). -/
theorem ML_swap12 (p q r : ℤ) : ML ![p, r, q] = ML ![p, q, r] := by
  have h := D_swap12 p q r; simp only [D] at h; linarith

/-- `ML` is invariant under swapping the first two coordinates (from `D_swap01`). -/
theorem ML_swap01 (p q r : ℤ) : ML ![q, p, r] = ML ![p, q, r] := by
  have h := D_swap01 p q r; simp only [D] at h; linarith

/-- `ML` is invariant under swapping the outer two coordinates (from `D_swap02`). -/
theorem ML_swap02 (p q r : ℤ) : ML ![r, q, p] = ML ![p, q, r] := by
  have h := D_swap02 p q r; simp only [D] at h; linarith

/-- **The unconditional inverse sweep (via the complete covering).** -/
theorem ML_ge_sweep_cover (p q r a b : ℤ) (hp : 0 < p) (hm : 12 ≤ p + r)
    (hbez : p * a + (p + r) * b = 1)
    (hs0 : 0 < (q * a) % (p + r))
    (hs2 : 2 * ((q * a) % (p + r)) ≠ p + r) :
    2 / 7 ≤ ML ![p, q, r] := by
  set s := (q * a) % (p + r) with hs
  set dd := (q * a) / (p + r) with hdd
  have hqa : q * a = s + (p + r) * dd := (Int.emod_add_mul_ediv (q * a) (p + r)).symm
  have hsM : s < p + r := Int.emod_lt_of_pos _ (by omega)
  obtain ⟨ℓ, hℓlo, hℓhi, c, hclo, hchi⟩ :=
    double_band_cover (p + r) s hm hs0 hsM hs2
  refine ML_ge_fullband_k p q r (a * ℓ) (-b * ℓ) (c + dd * ℓ) (by omega) ?_ ?_ ?_ ?_
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

/-- **Covering sweep via the `(q,r)` pairing.** Same as `ML_ge_sweep_cover` but using the
pair `(q,r)` (largest pair-sum `q+r`) with the third runner `p`. Routes through `ML_swap01`. -/
theorem ML_ge_sweep_cover_qr (p q r a b : ℤ) (hq : 0 < q) (hm : 12 ≤ q + r)
    (hbez : q * a + (q + r) * b = 1)
    (hs0 : 0 < (p * a) % (q + r)) (hs2 : 2 * ((p * a) % (q + r)) ≠ q + r) :
    2 / 7 ≤ ML ![p, q, r] := by
  rw [← ML_swap01 p q r]
  exact ML_ge_sweep_cover q p r a b hq hm hbez hs0 hs2

/-- **Broad comparable closure.** Any *sorted* triple `0 < p < q < r` with `q+r ≥ 12` and a
coprime `(q, r)` pairing (`gcd(q, q+r) = gcd(q,r) = 1`) has `ML(p,q,r) ≥ 2/7`. The inverse-step
conditions of `ML_ge_sweep_cover_qr` are derived: `s = p·a mod (q+r) > 0` because `q+r ∤ p`
(as `0 < p < q+r`), and `2s ≠ q+r` because `2s = q+r ⟹ (q+r) ∣ 2p ⟹ q+r ≤ 2p`, contradicting
`2p < q+r` (which holds for sorted triples). Covers every comparable triple with a coprime
top pair — no further hypotheses. -/
theorem ML_ge_of_coprime_qr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hm : 12 ≤ q + r) (hcop : IsCoprime q (q + r)) :
    2 / 7 ≤ ML ![p, q, r] := by
  obtain ⟨a, b, hab⟩ := hcop
  have hca : IsCoprime (q + r) a := ⟨b, q, by linear_combination hab⟩
  set s := (p * a) % (q + r) with hsdef
  set quot := (p * a) / (q + r) with hqdef
  have hemod : s + (q + r) * quot = p * a := by
    rw [hsdef, hqdef]; exact Int.emod_add_mul_ediv _ _
  have hs0 : 0 < s := by
    have hge : 0 ≤ s := hsdef ▸ Int.emod_nonneg (p * a) (by omega)
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have hdvd : (q + r) ∣ p * a := by rw [hsdef] at h; exact Int.dvd_of_emod_eq_zero h.symm
      have hdp : (q + r) ∣ p := hca.dvd_of_dvd_mul_right hdvd
      have := Int.le_of_dvd hp hdp; omega
  have hs2 : 2 * s ≠ q + r := by
    intro he
    have h2 : (q + r) ∣ 2 * p * a := ⟨1 + 2 * quot, by linear_combination -2 * hemod + he⟩
    have h2' : (q + r) ∣ (2 * p) * a := by rw [show (2 * p) * a = 2 * p * a by ring]; exact h2
    have hdp : (q + r) ∣ 2 * p := hca.dvd_of_dvd_mul_right h2'
    have := Int.le_of_dvd (by omega) hdp; omega
  exact ML_ge_sweep_cover_qr p q r a b (by omega) hm (by linear_combination hab) hs0 hs2

/-- **Comparable closure via the `(p,r)` pairing.** Sorted `0<p<q<r`, `p+r ≥ 12`,
`p+r ≠ 2q`, coprime `(p,r)` ⟹ `ML ≥ 2/7`. (Used in the `gcd(q,r)=2` branch, where `p` is
odd so `p+r ≠ 2q` holds by parity.) Inverse step `s=q·a mod (p+r)`; `2s≠p+r` since
`2s=p+r ⟹ (p+r)∣2q ⟹ 2q=p+r` (as `p+r ≤ 2q < 2(p+r)`), contradicting `p+r≠2q`. -/
theorem ML_ge_of_coprime_pr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hm : 12 ≤ p + r) (hne : p + r ≠ 2 * q) (hcop : IsCoprime p (p + r)) :
    2 / 7 ≤ ML ![p, q, r] := by
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
  exact ML_ge_sweep_cover p q r a b hp hm (by linear_combination hab) hs0 hs2

/-- **Case A via the `(p,r)` pairing.** Shared factor `g=gcd(p,r) ≥ 3`, `p` coprime... wait
this is `q` coprime to `g`. Used when `gcd(p,r) ≥ 3`. -/
theorem ML_ge_caseA_pr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hg : 3 ≤ (Int.gcd p r : ℤ)) (hcop : IsCoprime q (Int.gcd p r : ℤ)) :
    2 / 7 ≤ ML ![p, q, r] := by
  set g : ℤ := (Int.gcd p r : ℤ) with hgdef
  have hgpos : 0 < g := by omega
  obtain ⟨w₁, hw₁⟩ := Int.gcd_dvd_left (a := p) (b := r)
  obtain ⟨w₂, hw₂⟩ := Int.gcd_dvd_right (a := p) (b := r)
  rw [← hgdef] at hw₁ hw₂
  have hw1pos : 0 < w₁ := by
    rcases lt_or_ge w₁ 1 with h | h
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

/-- **Case A via the `(q,r)` pairing.** If the top pair shares a factor `g = gcd(q,r) ≥ 3`
and `p` is coprime to `g` (from primitivity), then `ML(p,q,r) ≥ 1/3 ≥ 2/7`. -/
theorem ML_ge_caseA_qr (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hg : 3 ≤ (Int.gcd q r : ℤ)) (hcop : IsCoprime p (Int.gcd q r : ℤ)) :
    2 / 7 ≤ ML ![p, q, r] := by
  set g : ℤ := (Int.gcd q r : ℤ) with hgdef
  have hgpos : 0 < g := by omega
  obtain ⟨w₁, hw₁⟩ := Int.gcd_dvd_left (a := q) (b := r)
  obtain ⟨w₂, hw₂⟩ := Int.gcd_dvd_right (a := q) (b := r)
  rw [← hgdef] at hw₁ hw₂
  have hw1pos : 0 < w₁ := by
    rcases lt_or_ge w₁ 1 with h | h
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
  have hperm : ML ![q, r, p] = ML ![p, q, r] := by
    rw [ML_swap12 q p r, ML_swap01 p q r]
  rw [hperm] at hcaseA; linarith

/-- **TOP-LEVEL: the large-coordinate bound (Kravitz Theorem 7.2, lower direction).**
For a sorted triple `0 < p < q < r` with `r > 30` and primitivity in the usable form
`IsCoprime p (gcd q r)` and `IsCoprime q (gcd p r)`, we have `ML(p,q,r) ≥ 2/7`, i.e.
`D(p,q,r) ≤ 3/14`. Since every triple in `L₃` has `q+r ≤ 11 < 12 ≤ p+r`, `r > 30` already
guarantees non-`L₃`. The dispatch is on `g = gcd(q,r)`: `g=1` → `(q,r)` sweep; `g≥3` →
Case A on `(q,r)`; `g=2` (so `q,r` even, `p` odd) → on `gcd(p,r)`: `=1` → `(p,r)` sweep
(`p+r≠2q` by parity), `≥3` → Case A on `(p,r)` (`gcd(p,r)=2` is impossible, else `gcd(p,q,r)≥2`). -/
theorem ML_ge_of_large (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : 30 < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ)) :
    2 / 7 ≤ ML ![p, q, r] := by
  have hg1 : 1 ≤ (Int.gcd q r : ℤ) := by
    have : 0 < Int.gcd q r := Int.gcd_pos_of_ne_zero_right q (by omega); omega
  rcases lt_trichotomy (Int.gcd q r : ℤ) 2 with hlt | heq | hgt
  · -- gcd(q,r) = 1
    have hcop : IsCoprime q r := Int.isCoprime_iff_gcd_eq_one.mpr (by omega)
    have hcqr : IsCoprime q (q + r) := by rw [add_comm]; simpa using hcop.add_mul_left_right 1
    exact ML_ge_of_coprime_qr p q r hp hpq hqr (by omega) hcqr
  · -- gcd(q,r) = 2
    have h2q : (2 : ℤ) ∣ q := heq ▸ Int.gcd_dvd_left (a := q) (b := r)
    have h2r : (2 : ℤ) ∣ r := heq ▸ Int.gcd_dvd_right (a := q) (b := r)
    have hgp1 : 1 ≤ (Int.gcd p r : ℤ) := by
      have : 0 < Int.gcd p r := Int.gcd_pos_of_ne_zero_right p (by omega); omega
    rcases lt_trichotomy (Int.gcd p r : ℤ) 2 with hlt2 | heq2 | hgt2
    · -- gcd(p,r) = 1
      have hcoppr : IsCoprime p r := Int.isCoprime_iff_gcd_eq_one.mpr (by omega)
      have hcpr : IsCoprime p (p + r) := by rw [add_comm]; simpa using hcoppr.add_mul_left_right 1
      have h2np : ¬ (2 : ℤ) ∣ p := by
        intro hd
        have hu := hcoppr.isUnit_of_dvd' hd h2r
        rw [Int.isUnit_iff] at hu; omega
      have hne : p + r ≠ 2 * q := by
        obtain ⟨rr, hrr⟩ := h2r; obtain ⟨qq, hqq⟩ := h2q
        rcases Int.even_or_odd p with ⟨pp, hpp⟩ | ⟨pp, hpp⟩
        · exact absurd ⟨pp, by omega⟩ h2np
        · omega
      exact ML_ge_of_coprime_pr p q r hp hpq hqr (by omega) hne hcpr
    · -- gcd(p,r) = 2 : impossible (2 ∣ p,q,r contradicts primitivity)
      exfalso
      have h2p : (2 : ℤ) ∣ p := heq2 ▸ Int.gcd_dvd_left (a := p) (b := r)
      obtain ⟨u, v, huv⟩ := hcop_p
      obtain ⟨pp, hpp⟩ := h2p
      obtain ⟨gg, hgg⟩ : (2 : ℤ) ∣ (Int.gcd q r : ℤ) := ⟨1, by rw [heq]; ring⟩
      have : (2 : ℤ) ∣ 1 := ⟨u * pp + v * gg, by rw [← huv, hpp, hgg]; ring⟩
      norm_num at this
    · -- gcd(p,r) ≥ 3 : Case A on (p,r)
      exact ML_ge_caseA_pr p q r hp hpq hqr (by omega) hcop_q
  · -- gcd(q,r) ≥ 3 : Case A on (q,r)
    exact ML_ge_caseA_qr p q r hp hpq hqr (by omega) hcop_p

/-- **The large-coordinate bound, as a `D`-statement.** Sorted primitive `0<p<q<r` with
`r > 30` ⟹ `D(p,q,r) ≤ 3/14`. Equivalently (contrapositive): `D(p,q,r) ≥ 3/14 ⟹ r ≤ 30`,
the coordinate bound behind Proposition 2.2 — the small remainder `r ≤ 30` being the finite
`native_decide` enumeration (`D3Classify`). -/
theorem D_le_of_large (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : 30 < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ)) :
    D ![p, q, r] ≤ 3 / 14 :=
  D_le_threshold_of_ML p q r (ML_ge_of_large p q r hp hpq hqr hr hcop_p hcop_q)

/-- **End-to-end demonstration.** The triple `(25,29,54)` (with `r = p+q`, the kind that
originally needed the three-gap machinery and was a `small-modulus` miss) is closed
unconditionally by the covering sweep: comb `25·19 + 79·(−6) = 1`, inverse step
`s = 29·19 mod 79 = 77`. The machine proves `ML(25,29,54) ≥ 2/7`. -/
example : 2 / 7 ≤ ML ![25, 29, 54] :=
  ML_ge_sweep_cover 25 29 54 19 (-6) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide)

end LRSpectrumFull

