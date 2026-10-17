import LRSpectrumFull.EightMSS
import LRSpectrumFull.Delta2Boundary
import LRSpectrumFull.BarajasSerraLRC6Plan
import LRSpectrumFull.EightCert27

/-!
# E5 without the MSS axiom: the two-dimensional rounding step

`EightMSS.e5b_staircase` (VERIFIED) turns `∑ v > 28^6` into an integer vector `z`, not parallel to
`v`, with `|28 z_i - σ v_i| ≤ 1`. `EightMSS.MSSGap7` asks to turn such a `z` into a witness time
for `v` at level `1/8`, given LRC for six speeds. We prove `MSSGap7` by the planar-subtorus
argument (Giri and Kravitz, "The structure of Lonely Runner spectra", §7; also the case `r = 1`
of Proposition 3.4 in "Fourteen lonely runners", arXiv:2609.02604):

1. Choose `i, j` with `z_i/v_i < z_j/v_j` adjacent among the slopes `z_k/v_k`. The integer vector
   `c = (z_i+z_j) v - (v_i+v_j) z` has no zero coordinate (the mediant slope is taken by no `k`)
   and `c_j = -c_i`, so `|c|` has at most six distinct entries.
2. LRC6 applied to `|c|` with coordinate `j` deleted gives `τ` with `‖c_k τ‖ ≥ 1/7` for all `k`.
3. Round the `z`-coefficient `-(v_i+v_j) τ` to an integer; with `s = σ/28`, `d = z - s v`,
   `t = (z_i+z_j) τ + r s` satisfies `t v_k ≡ c_k τ - r d_k (mod 1)`, `|r| ≤ 1/2`, `|d_k| ≤ 1/28`,
   so `‖t v_k‖ ≥ 1/7 - 1/56 = 1/8`.

This replaces the axiom `EightMSSImport.mss_theorem_A_n7`.
-/

namespace LRSpectrumFull.EightE5

open LRSpectrumFull

/-- Adjacent slope pair: `z_i/v_i < z_j/v_j` and no `k` has the mediant slope. -/
theorem exists_adjacent_pair (v z : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hnp : ∃ a b, z a * v b ≠ z b * v a) :
    ∃ i j, z i * v j < z j * v i ∧ ∀ k, (z i + z j) * v k ≠ (v i + v j) * z k := by
  classical
  set P : Finset (Fin 7 × Fin 7) :=
    Finset.univ.filter (fun p => z p.1 * v p.2 < z p.2 * v p.1) with hP
  have hPne : P.Nonempty := by
    obtain ⟨a, b, hab⟩ := hnp
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨(a, b), by simp [hP, h]⟩
    · exact ⟨(b, a), by simp [hP]; linarith⟩
  set r : Fin 7 → ℚ := fun k => (z k : ℚ) / v k with hr
  obtain ⟨⟨i, j⟩, hmem, hmin⟩ := P.exists_min_image (fun p => r p.2 - r p.1) hPne
  have hij : z i * v j < z j * v i := by simpa [hP] using hmem
  refine ⟨i, j, hij, fun k hk => ?_⟩
  have hvi : (0 : ℚ) < v i := by exact_mod_cast hv i
  have hvj : (0 : ℚ) < v j := by exact_mod_cast hv j
  have hvk : (0 : ℚ) < v k := by exact_mod_cast hv k
  have hijq : (z i : ℚ) * v j < z j * v i := by exact_mod_cast hij
  have hkq : ((z i : ℚ) + z j) * v k = (v i + v j) * z k := by exact_mod_cast hk
  -- slope of k is strictly between: z_i v_k < z_k v_i
  have h1 : z i * v k < z k * v i := by
    have : (z i : ℚ) * v k < z k * v i := by nlinarith
    exact_mod_cast this
  have hmemk : (i, k) ∈ P := by simp [hP, h1]
  have hle := hmin (i, k) hmemk
  simp only [hr] at hle
  -- r k < r j
  have hkj : (z k : ℚ) * v j < z j * v k := by nlinarith
  have : (z k : ℚ) / v k < z j / v j := by
    rw [div_lt_div_iff₀ hvk hvj]; exact hkj
  linarith

/-- `MSSGap7` holds. -/
theorem mssGap7_holds : EightMSS.MSSGap7 := by
  intro h6 v hv hg hz
  obtain ⟨z, σ, hnp, hzb⟩ := hz
  obtain ⟨i, j, hij, hmed⟩ := exists_adjacent_pair v z hv hnp
  have hij' : i ≠ j := by
    rintro rfl; exact lt_irrefl _ hij
  set c : Fin 7 → ℤ := fun k => (z i + z j) * v k - (v i + v j) * z k with hc
  have hc0 : ∀ k, c k ≠ 0 := fun k h => hmed k (by simp only [hc] at h; linarith)
  have hcj : c j = - c i := by simp only [hc]; ring
  set u : Fin (5 + 1) → ℤ := fun m => |c (j.succAbove m)| with hu
  have hupos : ∀ m, 0 < u m := fun m => abs_pos.mpr (hc0 _)
  obtain ⟨τ, hτ⟩ := (le_ML_iff_exists_far u _).mp (h6 u hupos)
  have habs : ∀ k, nearestIntDist ((|c k| : ℤ) * τ : ℝ) = nearestIntDist ((c k : ℝ) * τ) := by
    intro k
    rcases abs_choice (c k) with h | h <;> rw [h]
    push_cast; rw [neg_mul, nearestIntDist_neg]
  have hsucc : ∀ k, k ≠ j → 1 / ((5 : ℝ) + 2) ≤ nearestIntDist ((c k : ℝ) * τ) := by
    intro k hk
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hk
    have := hτ m
    simp only [hu] at this
    rwa [habs] at this
  have hall : ∀ k, 1 / ((5 : ℝ) + 2) ≤ nearestIntDist ((c k : ℝ) * τ) := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [hcj]; push_cast; rw [neg_mul, nearestIntDist_neg]
      exact hsucc i hij'
    · exact hsucc k hk
  -- rounding
  set a1 : ℝ := -((v i : ℝ) + v j) * τ with ha1
  set k1 : ℤ := round a1 with hk1
  set r : ℝ := a1 - k1 with hr
  have hr2 : |r| ≤ 1 / 2 := abs_sub_round a1
  set s : ℝ := (σ : ℝ) / 28 with hs
  set t : ℝ := ((z i : ℝ) + z j) * τ + r * s with ht
  refine (le_ML_iff_exists_far v (1 / 8)).mpr ⟨t, fun k => ?_⟩
  have hd : |(z k : ℝ) - s * v k| ≤ 1 / 28 := by
    have h := hzb k
    have h' : |(28 : ℝ) * z k - (σ : ℝ) * v k| ≤ 1 := by exact_mod_cast h
    have : (z k : ℝ) - s * v k = ((28 : ℝ) * z k - (σ : ℝ) * v k) / 28 := by
      rw [hs]; ring
    rw [this, abs_div]; norm_num; linarith
  have hid : (v k : ℝ) * t = ((c k : ℝ) * τ - r * ((z k : ℝ) - s * v k)) + ((-(k1 * z k) : ℤ) : ℝ) := by
    simp only [ht, hc, hr, ha1]; push_cast; ring
  rw [hid, nearestIntDist_add_int]
  have hL := nearestIntDist_lipschitz ((c k : ℝ) * τ - r * ((z k : ℝ) - s * v k)) ((c k : ℝ) * τ)
  have hsmall : |r * ((z k : ℝ) - s * v k)| ≤ 1 / 56 := by
    rw [abs_mul]
    calc |r| * |(z k : ℝ) - s * v k| ≤ (1 / 2) * (1 / 28) :=
          mul_le_mul hr2 hd (abs_nonneg _) (by norm_num)
      _ = 1 / 56 := by norm_num
  have hk := hall k
  have heq : (c k : ℝ) * τ - r * ((z k : ℝ) - s * v k) - (c k : ℝ) * τ
      = -(r * ((z k : ℝ) - s * v k)) := by ring
  rw [heq, abs_neg] at hL
  have := (abs_le.mp hL).1
  norm_num at hk ⊢
  linarith

/-- **E5-sum, unconditional given LRC6.** Same statement as `EightPlan.e5_sum_STUB_SUPERSEDED`. -/
theorem e5_sum (h6 : EightPlan.LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hsum : (28 : ℤ) ^ 6 < ∑ i, v i) : 1 / 8 ≤ ML v :=
  EightMSS.e5_sum_of_gap mssGap7_holds h6 v hv hg hsum

/-- **E5 (product form).** -/
theorem e5_prod (h6 : EightPlan.LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, v i) : 1 / 8 ≤ ML v :=
  e5_sum h6 v hv hg (EightPlan.e5_amgm v hv hprod)

/-- `eight_runners` from the contracts, E5 supplied by `e5_prod` above. -/
theorem eight_runners_of (h6 : EightPlan.LRC6)
    (hchk : ∀ p ∈ EightPlan.rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v := by
  refine EightPlan.e0_primitive (fun w hw hg => ?_) v hv
  by_contra hlt
  push Not at hlt
  have hce : EightPlan.IsCE w := ⟨hw, hg, hlt⟩
  have hpar := EightPlan.e4_parity h6 w hce
  have hS : ∀ p ∈ EightPlan.rosenfeldS, ∃ i, (p : ℤ) ∣ w i := fun p hp =>
    EightPlan.e2_prime_dvd p (EightPlan.rosenfeldS_primes p hp).1
      (EightPlan.rosenfeldS_primes p hp).2 (hchk p hp) w hw hpar hlt
  have hdvd := EightPlan.e3_lcm_dvd w hw hlt hS
  have hpos : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hle := Int.le_of_dvd hpos hdvd
  have hnum : ((28 : ℕ) ^ 42 : ℤ) < ((7 ^ 7 * (840 * ∏ p ∈ EightPlan.rosenfeldS, p) : ℕ) : ℤ) := by
    exact_mod_cast EightPlan.numeric
  have hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, w i := by
    push_cast at hnum hle
    nlinarith
  exact absurd (e5_prod h6 w hw hg hprod) (not_le.mpr hlt)

/-- **LRC for eight runners.** No MSS axiom: LRC6 from `BarajasSerra.LRC6_barajasSerra`, the
27 per-prime checks from `EightCert27.hchk_all`, E5 from `mssGap7_holds`. -/
theorem eight_runners_unconditional (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  eight_runners_of BarajasSerra.LRC6_barajasSerra EightCert27.hchk_all v hv

end LRSpectrumFull.EightE5
