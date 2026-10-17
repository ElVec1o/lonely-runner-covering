import LRSpectrumFull.BarajasSerraSec6G4
import LRSpectrumFull.BarajasSerraLRC6M1

/-!
# E6 session 20: LRC6 case (a) assembled

Five speeds at the minimal 7-level `g`, one speed at a strictly higher level `g + m`, `m ≥ 1`.
`m = 1`: `lrc6_m1_scaled` (session 15). `m ≥ 2`: divide by `7^g` and apply `Sec6.case_a_ge2`
(Section 6 via G4). Scaling as in `lrc6_m1_scaled` / `card4_hard_scaled`.
-/

namespace LRSpectrumFull.BarajasSerra

open LRSpectrumFull

/-- **LRC6 case (a)**: five speeds with `nu_7 = g`, one with `nu_7 > g`. -/
theorem case_a (y : Fin 5 → ℕ) (d g : ℕ) (hy0 : ∀ i, y i ≠ 0) (hd : d ≠ 0)
    (hyv : ∀ i, nu 7 (y i) = g) (hdv : g < nu 7 d) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 7 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 7 : ℝ) ≤ nearestIntDist (t * d) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases h1 : nu 7 d = g + 1
  · exact lrc6_m1_scaled y d g hy0 hd hyv h1
  have hM : 2 ≤ nu 7 d - g := by omega
  have hdvy : ∀ i, 7 ^ g ∣ y i := fun i => by rw [← hyv i]; exact pow_padicValNat_dvd
  have hdvd : 7 ^ g ∣ d := (pow_dvd_pow 7 hdv.le).trans (by exact pow_padicValNat_dvd)
  have hpg : 0 < 7 ^ g := by positivity
  set y' : Fin 5 → ℕ := fun i => y i / 7 ^ g
  set d' := d / 7 ^ g
  have hyeq : ∀ i, y i = 7 ^ g * y' i := fun i => (Nat.mul_div_cancel' (hdvy i)).symm
  have hdeq : d = 7 ^ g * d' := (Nat.mul_div_cancel' hdvd).symm
  have hy'7 : ∀ i, ¬ 7 ∣ y' i := by
    intro i h
    have h1 : 7 ^ g * 7 ∣ y i := by rw [hyeq i]; exact Nat.mul_dvd_mul_left _ h
    rw [← pow_succ, ← hyv i] at h1
    exact pow_succ_padicValNat_not_dvd (hy0 i) h1
  have hd'0 : d' ≠ 0 := by intro h; apply hd; rw [hdeq, h, mul_zero]
  have hnu : nu 7 d' = nu 7 d - g := by unfold nu; exact padicValNat.div_pow hdvd
  obtain ⟨t, ht, hb, hbd⟩ := Sec6.case_a_ge2 (nu 7 d - g) hM y' hy'7 d' hd'0 hnu
  refine ⟨t / (7 ^ g : ℝ), by positivity, fun i => ?_, ?_⟩
  · have : t / (7 ^ g : ℝ) * (y i : ℝ) = t * (y' i : ℝ) := by
      rw [hyeq i]; push_cast; field_simp
    rw [this]; simpa using hb i
  · have : t / (7 ^ g : ℝ) * (d : ℝ) = t * (d' : ℝ) := by
      rw [hdeq]; push_cast; field_simp
    rw [this]; simpa using hbd

end LRSpectrumFull.BarajasSerra
