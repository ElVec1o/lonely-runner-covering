import LRSpectrumFull.CoordConstruction
import LRSpectrumFull.Confinement

/-!
# Non-strict band lemmas at the `2/7` threshold

`KravitzStrict.lean` develops the strict chain

  `nid_gt_two_sevenths` → `nid_gt_of_band` → `nid_runner_gt` → `ML_gt_fullband_k`,

which proves `2/7 < ML ![p,q,r]` from a strict residue band. The covering lemma
`double_band_cover` (as opposed to `double_band_cover_strict`) delivers a *closed* band, so the
hookups need the non-strict chain ending in `ML_ge_fullband_k`. This file supplies it, mirroring the
strict proofs line for line with `<` replaced by `≤`, and adds the translation of the `2/7`
threshold on `ML` into the `3/14` threshold on `D`.

Nothing here is new mathematics: it is the closed-band form of statements already present, and the
`D` lemma is `D = 1/2 - ML` read backwards.
-/

namespace LRSpectrumFull

/-- A real in the closed middle band `[2/7, 5/7]` is at least `2/7` from the integers. -/
theorem nid_ge_two_sevenths (y : ℝ) (h1 : 2 / 7 ≤ y) (h2 : y ≤ 5 / 7) :
    2 / 7 ≤ nearestIntDist y := by
  rcases le_or_gt y (1 / 2) with h | h
  · rw [nearestIntDist_eq_self_of_le_half y (by linarith) h]; linarith
  · have e : nearestIntDist y = nearestIntDist (1 - y) := by
      rw [show (1 : ℝ) - y = -y + ((1 : ℤ) : ℝ) by push_cast; ring,
        nearestIntDist_add_int, nearestIntDist_neg]
    rw [e, nearestIntDist_eq_self_of_le_half (1 - y) (by linarith) (by linarith)]; linarith

/-- Closed integer band ⟹ `nid ≥ 2/7`.  If `2m ≤ 7N ≤ 5m` then `‖N/m‖ ≥ 2/7`. -/
theorem nid_ge_of_band (N m : ℤ) (hm : 0 < m) (hlo : 2 * m ≤ 7 * N) (hhi : 7 * N ≤ 5 * m) :
    2 / 7 ≤ nearestIntDist ((N : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply nid_ge_two_sevenths
  · rw [le_div_iff₀ hmR]
    have h : (2 : ℝ) * m ≤ 7 * N := by exact_mod_cast hlo
    linarith
  · rw [div_le_iff₀ hmR]
    have h : (7 : ℝ) * N ≤ 5 * m := by exact_mod_cast hhi
    linarith

/-- Closed runner band ⟹ `nid ≥ 2/7`, accounting for the integer part `c`. -/
theorem nid_runner_ge (a k m c : ℤ) (hm : 0 < m)
    (hlo : 2 * m ≤ 7 * (a * k - c * m)) (hhi : 7 * (a * k - c * m) ≤ 5 * m) :
    2 / 7 ≤ nearestIntDist ((a : ℝ) * ((k : ℝ) / (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))
  have e : (a : ℝ) * ((k : ℝ) / (m : ℝ))
      = ((a * k - c * m : ℤ) : ℝ) / (m : ℝ) + ((c : ℤ) : ℝ) := by
    field_simp; push_cast; ring
  rw [e, nearestIntDist_add_int]
  exact nid_ge_of_band (a * k - c * m) m hm hlo hhi

/-- Non-strict full-band construction at the pair sum.  The closed-band counterpart of
`ML_gt_fullband_k`. -/
theorem ML_ge_fullband_k (p q r k cp cq : ℤ) (hm : 0 < p + r)
    (hp1 : 2 * (p + r) ≤ 7 * (p * k - cp * (p + r)))
    (hp2 : 7 * (p * k - cp * (p + r)) ≤ 5 * (p + r))
    (hq1 : 2 * (p + r) ≤ 7 * (q * k - cq * (p + r)))
    (hq2 : 7 * (q * k - cq * (p + r)) ≤ 5 * (p + r)) :
    2 / 7 ≤ ML ![p, q, r] := by
  have hpr : ((p + r : ℤ) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < ((p + r : ℤ) : ℝ))
  exact ML_ge_at_pairsum p q r k (2 / 7) hpr
    (nid_runner_ge p k (p + r) cp hm hp1 hp2) (nid_runner_ge q k (p + r) cq hm hq1 hq2)

/-- `D = 1/2 - ML`, so the `2/7` threshold on `ML` is exactly the `3/14` threshold on `D`. -/
theorem D_le_threshold_of_ML (p q r : ℤ) (h : 2 / 7 ≤ ML ![p, q, r]) :
    D ![p, q, r] ≤ 3 / 14 := by
  simp only [D]
  linarith

/-- **Small-modulus arm.**  If all three runners land in the closed band `[2/7, 5/7]` at the
explicit time `k/N`, then `ML ≥ 2/7`.  Unlike `ML_ge_fullband_k` this makes no use of the pair-sum
identity, so the third residue must be supplied. -/
theorem ML_ge_smallmod (p q r N k cp cq cr : ℤ) (hN : 0 < N)
    (hp1 : 2 * N ≤ 7 * (p * k - cp * N)) (hp2 : 7 * (p * k - cp * N) ≤ 5 * N)
    (hq1 : 2 * N ≤ 7 * (q * k - cq * N)) (hq2 : 7 * (q * k - cq * N) ≤ 5 * N)
    (hr1 : 2 * N ≤ 7 * (r * k - cr * N)) (hr2 : 7 * (r * k - cr * N) ≤ 5 * N) :
    2 / 7 ≤ ML ![p, q, r] := by
  refine le_trans ?_ (gap_le_ML ![p, q, r] ((k : ℝ) / (N : ℝ)))
  apply le_gap
  intro i
  fin_cases i
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((![p, q, r] 0 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge p k N cp hN hp1 hp2
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((![p, q, r] 1 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge q k N cq hN hq1 hq2
  · show (2 / 7 : ℝ) ≤ nearestIntDist ((![p, q, r] 2 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge r k N cr hN hr1 hr2

/-- **Mod-3 arm.**  If none of the three speeds is divisible by `3`, then at `t = 1/3` every runner
sits at distance exactly `1/3` from the integers, and `1/3 ≥ 2/7`. -/
theorem ML_ge_mod3 (p q r : ℤ) (hp : ¬ (3 ∣ p)) (hq : ¬ (3 ∣ q)) (hr : ¬ (3 ∣ r)) :
    2 / 7 ≤ ML ![p, q, r] := by
  have band : ∀ a : ℤ, ¬ (3 ∣ a) →
      2 * 3 ≤ 7 * (a * 1 - (a / 3) * 3) ∧ 7 * (a * 1 - (a / 3) * 3) ≤ 5 * 3 := by
    intro a ha
    have hmod : a % 3 ≠ 0 := fun h => ha (Int.dvd_of_emod_eq_zero h)
    have h0 : 0 ≤ a % 3 := Int.emod_nonneg a (by norm_num)
    have h1 : a % 3 < 3 := Int.emod_lt_of_pos a (by norm_num)
    have hid : a * 1 - (a / 3) * 3 = a % 3 := by
      have := Int.emod_add_ediv a 3; omega
    rw [hid]; omega
  exact ML_ge_smallmod p q r 3 1 (p / 3) (q / 3) (r / 3) (by norm_num)
    (band p hp).1 (band p hp).2 (band q hq).1 (band q hq).2 (band r hr).1 (band r hr).2

end LRSpectrumFull
