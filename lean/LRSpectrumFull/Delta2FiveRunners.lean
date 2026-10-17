/-
# The five runners: the Lonely Runner Conjecture for four moving runners

`five_runners` — for any four positive integer speeds there is a time at
which all four runners are at distance `≥ 1/5` from the origin: the
Barajas–Serra Prime Filtering argument at `p = 5`, fully machine-checked.
The time is `t = μ / 5^{m+1+g}` where `g` is the common `5`-valuation,
`m` the reduced top level, and `μ` the multiplier produced by
`pfl_master`; the single contact between the `ℤ/5^{m+1}` digit world and
`ℝ` is the grid bridge `nid_natCast_div`.
-/
import LRSpectrumFull.Delta2PFLMaster
import LRSpectrumFull.Delta2GridBridge
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- **The real bridge.**  A safe element of `ℤ/5^{M+1}` yields distance
`≥ 1/5` at time `μ / 5^{M+1+g}`, after unscaling the common valuation
`5^g`. -/
theorem bridge_real (M g l s μ : ℕ) (hμ : ¬ 5 ∣ μ) (hgl : g ≤ l)
    (hsafe : 5 ^ M ≤ cdist (5 * 5 ^ M) (μ * (5 ^ (l - g) * s))) :
    (1 : ℝ) / 5 ≤ nearestIntDist
      (((5 ^ l * s : ℕ) : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))) := by
  have hN : 0 < 5 * 5 ^ M := by positivity
  have hx : ((5 ^ l * s : ℕ) : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))
      = ((μ * (5 ^ (l - g) * s) : ℕ) : ℝ) / ((5 * 5 ^ M : ℕ) : ℝ) := by
    obtain ⟨w, hw⟩ : ∃ w, l - g = w := ⟨l - g, rfl⟩
    push_cast
    rw [hw, show l = w + g from by omega, pow_add (5 : ℝ) w g,
      pow_add (5 : ℝ) (M + 1) g, pow_succ (5 : ℝ) M]
    field_simp
  rw [hx, nid_natCast_div (5 * 5 ^ M) (μ * (5 ^ (l - g) * s)) hN]
  have hcd : 5 ^ M ≤ min ((μ * (5 ^ (l - g) * s)) % (5 * 5 ^ M))
      (5 * 5 ^ M - (μ * (5 ^ (l - g) * s)) % (5 * 5 ^ M)) := hsafe
  have h15 : (1 : ℝ) / 5 = ((5 ^ M : ℕ) : ℝ) / ((5 * 5 ^ M : ℕ) : ℝ) := by
    push_cast
    rw [div_eq_div_iff (by norm_num) (by positivity)]
    ring
  rw [h15]
  gcongr

/-- **The Lonely Runner Conjecture for four moving runners** (`n = 4`,
five runners with the stationary one): for any four positive integer
speeds there is a positive time at which every runner is at distance at
least `1/5` around the circle.  Proof: Barajas–Serra Prime Filtering at
`p = 5` — common `5`-valuation unscaled, then the level dichotomy
(`pfl_master`): at most two elements per level (multiplier composition)
or the `3+1` shape (the decided digit chase). -/
theorem five_runners (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 : ℝ) / 5 ≤ nearestIntDist ((d i : ℝ) * t) := by
  obtain ⟨l₀, s₀, he₀, hs₀⟩ := exists_level (d 0) (hd 0)
  obtain ⟨l₁, s₁, he₁, hs₁⟩ := exists_level (d 1) (hd 1)
  obtain ⟨l₂, s₂, he₂, hs₂⟩ := exists_level (d 2) (hd 2)
  obtain ⟨l₃, s₃, he₃, hs₃⟩ := exists_level (d 3) (hd 3)
  set g := min (min l₀ l₁) (min l₂ l₃) with hg
  set M := max (max (l₀ - g) (l₁ - g)) (max (l₂ - g) (l₃ - g)) with hM
  obtain ⟨μ, hμ, H0, H1, H2, H3⟩ :=
    pfl_master (l₀ - g) (l₁ - g) (l₂ - g) (l₃ - g) s₀ s₁ s₂ s₃ M
      hs₀ hs₁ hs₂ hs₃ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hμ0 : 0 < μ := Nat.pos_of_ne_zero (fun h => hμ (h ▸ dvd_zero 5))
  refine ⟨(μ : ℝ) / (5 : ℝ) ^ (M + 1 + g),
    div_pos (by exact_mod_cast hμ0) (by positivity), ?_⟩
  have B0 : (1 : ℝ) / 5 ≤ nearestIntDist
      ((d 0 : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))) := by
    rw [he₀]
    exact bridge_real M g l₀ s₀ μ hμ (by omega) H0
  have B1 : (1 : ℝ) / 5 ≤ nearestIntDist
      ((d 1 : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))) := by
    rw [he₁]
    exact bridge_real M g l₁ s₁ μ hμ (by omega) H1
  have B2 : (1 : ℝ) / 5 ≤ nearestIntDist
      ((d 2 : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))) := by
    rw [he₂]
    exact bridge_real M g l₂ s₂ μ hμ (by omega) H2
  have B3 : (1 : ℝ) / 5 ≤ nearestIntDist
      ((d 3 : ℝ) * ((μ : ℝ) / (5 : ℝ) ^ (M + 1 + g))) := by
    rw [he₃]
    exact bridge_real M g l₃ s₃ μ hμ (by omega) H3
  intro i
  fin_cases i
  · exact B0
  · exact B1
  · exact B2
  · exact B3


/-- **Five runners for nonzero integer speeds.**  `five_runners` is stated for positive naturals,
which is the form the digit argument produces.  Passing to nonzero integers is the reduction
`nearestIntDist (-x) = nearestIntDist x`. -/
theorem five_runners_int (d : Fin 4 → ℤ) (hd : ∀ i, d i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 : ℝ) / 5 ≤ nearestIntDist ((d i : ℝ) * t) := by
  obtain ⟨t, ht0, ht⟩ := five_runners (fun i => (d i).natAbs)
    (fun i => Int.natAbs_pos.mpr (hd i))
  refine ⟨t, ht0, fun i => ?_⟩
  have h := ht i
  have habs : ((d i).natAbs : ℝ) = |(d i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs] at h
  rcases abs_cases ((d i : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩
  · rwa [he] at h
  · rw [he] at h
    rwa [show -(d i : ℝ) * t = -((d i : ℝ) * t) by ring, nearestIntDist_neg] at h

end LRSpectrumFull
