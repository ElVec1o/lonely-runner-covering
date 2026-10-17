import Mathlib
import LRSpectrumFull.MaxLoneliness
import LRSpectrumFull.NearestIntCont
import LRSpectrumFull.RoomA4_rosenfeld

/-!
# ROOM A4, compression round: one soundness lemma for every certificate of chain C1

Chain C1 carries several certificates for the floor `δ ≤ ML v` (`δ = 1/(k+2)`):
`rieszSharpFiresQ` (R₁), the degree-2 test R₂, Hilbert's exact union bound U₁ < 1, GL5 and the
residue witnesses.  Each is a first-moment (union-bound) argument for a nonnegative measure `ν`
on the time line: if `Σᵢ ν(Bᵢ) < ν(ℝ)`, with `Bᵢ = {t : ‖vᵢ t‖ < δ}`, some time avoids every
`Bᵢ`.  The cases differ only in the choice of `ν`:

* `ν = P^D · Lebesgue` on `[0,1]` (`P = ∏ (1 - cos 2π vᵢ t)`): U_D, and after a per-runner Markov
  step, R_D;
* `ν` = counting measure on a coset `t₀ + (1/q)ℤ`: GL5 and Rosenfeld's Lemma 5;
* `ν` = a Dirac mass at `p/q`: the witness branch and Rosenfeld's Lemma 4.

This file proves that single lemma (`floor_of_measure_certificate`), its Markov form
(`floor_of_test_certificate`), and the integral form used by U_D for every continuous
nonnegative weight (`floor_of_integral_unionBound`, `floor_of_UD`).  The Fourier evaluation of
`∫_{Bᵢ} P^D` (Hilbert's kernel formula) and the relaxation R_D ⇒ U_D < 1 are NOT formalized here.
-/

namespace LRSpectrumFull.RoomA4Compress

open LRSpectrumFull MeasureTheory Real

variable {k : ℕ}

/-- The bad set of runner `i` at level `δ`: times where runner `i` is closer than `δ` to the
origin. -/
def badSet (v : Fin (k + 1) → ℤ) (δ : ℝ) (i : Fin (k + 1)) : Set ℝ :=
  {t | nearestIntDist ((v i : ℝ) * t) < δ}

theorem measurableSet_badSet (v : Fin (k + 1) → ℤ) (δ : ℝ) (i : Fin (k + 1)) :
    MeasurableSet (badSet v δ i) := by
  have hc : Continuous fun t : ℝ => nearestIntDist ((v i : ℝ) * t) :=
    continuous_nearestIntDist.comp (continuous_const.mul continuous_id)
  exact (isOpen_lt hc continuous_const).measurableSet

/-- A time outside every bad set gives the floor. -/
theorem le_ML_of_good (v : Fin (k + 1) → ℤ) (δ t : ℝ)
    (h : ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * t)) : δ ≤ ML v :=
  (le_gap v t δ h).trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-- If the floor fails, the bad sets cover the line. -/
theorem cover_of_lt_ML (v : Fin (k + 1) → ℤ) (δ : ℝ) (hlt : ML v < δ) :
    ∀ t : ℝ, ∃ i, t ∈ badSet v δ i := by
  intro t
  by_contra hn
  push Not at hn
  exact absurd (le_ML_of_good v δ t (fun i => not_lt.mp (hn i))) (not_le.mpr hlt)

/-- **The single soundness lemma.**  For any measure `ν` on `ℝ` (no finiteness or measurability
hypothesis is needed), `Σᵢ ν(Bᵢ) < ν(ℝ)` forces the floor `δ ≤ ML v`. -/
theorem floor_of_measure_certificate (v : Fin (k + 1) → ℤ) (δ : ℝ) (ν : Measure ℝ)
    (h : ∑ i, ν (badSet v δ i) < ν Set.univ) : δ ≤ ML v := by
  by_contra hlt
  have hcov : (Set.univ : Set ℝ) ⊆ ⋃ i, badSet v δ i := by
    intro t _
    obtain ⟨i, hi⟩ := cover_of_lt_ML v δ (not_le.mp hlt) t
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hle : ν Set.univ ≤ ∑ i, ν (badSet v δ i) :=
    (measure_mono hcov).trans (measure_iUnion_fintype_le ν _)
  exact absurd h (not_lt.mpr hle)

/-- **Markov form.**  Any test `g ≥ 1` on the union of the bad sets with `∫⁻ g dν < ν(ℝ)` forces
the floor.  (R_D is this with `ν = P^D` and `g = (π²/K²)(1 + Σᵢ cot²(π vᵢ t))`.) -/
theorem floor_of_test_certificate (v : Fin (k + 1) → ℤ) (δ : ℝ) (ν : Measure ℝ)
    (g : ℝ → ENNReal) (hg : ∀ t, (∃ i, t ∈ badSet v δ i) → 1 ≤ g t)
    (h : ∫⁻ t, g t ∂ν < ν Set.univ) : δ ≤ ML v := by
  by_contra hlt
  have hcov := cover_of_lt_ML v δ (not_le.mp hlt)
  have hle : ν Set.univ ≤ ∫⁻ t, g t ∂ν := by
    calc ν Set.univ = ∫⁻ _t, (1 : ENNReal) ∂ν := by simp
      _ ≤ ∫⁻ t, g t ∂ν := lintegral_mono fun t => hg t (hcov t)
  exact absurd h (not_lt.mpr hle)

/-- The witness branch is the Dirac instance: a time `t₀` with every runner at distance `≥ δ`
makes `Σᵢ δ_{t₀}(Bᵢ) = 0 < 1`. -/
theorem measure_certificate_of_good (v : Fin (k + 1) → ℤ) (δ t₀ : ℝ)
    (h : ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * t₀)) :
    ∑ i, (Measure.dirac t₀) (badSet v δ i) < (Measure.dirac t₀) Set.univ := by
  have h0 : ∀ i, (Measure.dirac t₀) (badSet v δ i) = 0 := by
    intro i
    rw [Measure.dirac_apply' _ (measurableSet_badSet v δ i)]
    have : t₀ ∉ badSet v δ i := by
      simp only [badSet, Set.mem_setOf_eq, not_lt]; exact h i
    simp [this]
  simp [h0]

/-- **Integral form (U_D for every continuous nonnegative weight).**  If
`Σᵢ ∫_{[0,1] ∩ Bᵢ} F < ∫_{[0,1]} F` for a continuous `F ≥ 0`, the floor holds. -/
theorem floor_of_integral_unionBound (v : Fin (k + 1) → ℤ) (δ : ℝ) (F : ℝ → ℝ)
    (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    (h : ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v δ i, F t < ∫ t in Set.Icc (0 : ℝ) 1, F t) :
    δ ≤ ML v := by
  by_contra hlt
  have hcov := cover_of_lt_ML v δ (not_le.mp hlt)
  have hint : IntegrableOn F (Set.Icc (0 : ℝ) 1) := hF.integrableOn_Icc
  have hind : ∀ i, Integrable ((badSet v δ i).indicator F) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun i => hint.integrable.indicator (measurableSet_badSet v δ i)
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≤ ∑ i, (badSet v δ i).indicator F t := by
    intro t _
    obtain ⟨i0, hi0⟩ := hcov t
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (badSet v δ i).indicator F t :=
      fun i _ => Set.indicator_nonneg (fun s _ => hF0 s) t
    calc F t = (badSet v δ i0).indicator F t := (Set.indicator_of_mem hi0 F).symm
      _ ≤ ∑ i, (badSet v δ i).indicator F t :=
        Finset.single_le_sum (f := fun i => (badSet v δ i).indicator F t) hnn
          (Finset.mem_univ i0)
  have hsumint : IntegrableOn (fun t => ∑ i, (badSet v δ i).indicator F t)
      (Set.Icc (0 : ℝ) 1) := by
    have := integrable_finsetSum (Finset.univ) (fun i _ => hind i)
    simpa [IntegrableOn, Finset.sum_apply] using this
  have hmono : ∫ t in Set.Icc (0 : ℝ) 1, F t
      ≤ ∫ t in Set.Icc (0 : ℝ) 1, ∑ i, (badSet v δ i).indicator F t :=
    setIntegral_mono_on hint hsumint measurableSet_Icc hpt
  have hsplit : ∫ t in Set.Icc (0 : ℝ) 1, ∑ i, (badSet v δ i).indicator F t
      = ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v δ i, F t := by
    rw [integral_finsetSum Finset.univ (fun i _ => hind i)]
    exact Finset.sum_congr rfl (fun i _ => setIntegral_indicator (measurableSet_badSet v δ i))
  rw [hsplit] at hmono
  exact absurd h (not_lt.mpr hmono)

/-- The Riesz product weight `P(t)^D = ∏ᵢ (1 - cos 2π vᵢ t)^D`. -/
noncomputable def rieszWeight (v : Fin (k + 1) → ℤ) (D : ℕ) (t : ℝ) : ℝ :=
  (∏ i, (1 - Real.cos (2 * π * (v i : ℝ) * t))) ^ D

theorem continuous_rieszWeight (v : Fin (k + 1) → ℤ) (D : ℕ) :
    Continuous (rieszWeight v D) := by
  unfold rieszWeight
  fun_prop

theorem rieszWeight_nonneg (v : Fin (k + 1) → ℤ) (D : ℕ) (t : ℝ) : 0 ≤ rieszWeight v D t := by
  unfold rieszWeight
  refine pow_nonneg (Finset.prod_nonneg fun i _ => ?_) D
  have := Real.cos_le_one (2 * π * (v i : ℝ) * t); linarith

/-- **U_D < 1 ⇒ floor** (Hilbert S5 for `D = 1`; the `D = 2` case covers every family on which
Grothendieck's R₂ fires, by the Markov relaxation).  Stated with the exact integrals; the
per-family numerical value of the left side is a separate computation. -/
theorem floor_of_UD (v : Fin (k + 1) → ℤ) (D : ℕ)
    (h : ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v (1 / ((k : ℝ) + 2)) i, rieszWeight v D t
        < ∫ t in Set.Icc (0 : ℝ) 1, rieszWeight v D t) :
    1 / ((k : ℝ) + 2) ≤ ML v :=
  floor_of_integral_unionBound v _ (rieszWeight v D) (continuous_rieszWeight v D)
    (rieszWeight_nonneg v D) h

/-! ### The compressed crux: the floor on the stratum where no Riesz-product weight certifies

`BridgeDisjunctionQPrimInd2` (Rosenfeld seat) asks for `rieszSharpFiresQ ∨ witness` on the
inductive, leave-one-out-primitive, divisor-complete class.  Both disjuncts are certificates for
the floor, and `rieszSharpFiresQ` is dominated by the exact union bound U₁ (PROVED, not formalized
here).  The compressed crux asks directly for the floor, and only on families where no weight
`P^D` gives a union bound below `1`.  It is implied by Ind2 and still suffices, with A1–A3, for
`UniversalFloor`.  R₂ and GL5 do not appear. -/

/-- U_D fires: the exact union bound under the weight `P^D` is below `1`, at `δ = 1/(k+2)`. -/
def UDFires (v : Fin (k + 1) → ℤ) (D : ℕ) : Prop :=
  ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v (1 / ((k : ℝ) + 2)) i, rieszWeight v D t
    < ∫ t in Set.Icc (0 : ℝ) 1, rieszWeight v D t

/-- **Compressed crux.**  The floor for every family of the Ind2 class on which no `U_D` fires. -/
def FloorCruxU : Prop :=
  ∀ k : ℕ, 11 ≤ k →
    (∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u) →
    ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 →
    (∀ l : Fin (k + 1), Finset.univ.gcd (fun j : Fin k => v (l.succAbove j)) = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ k + 2 → ∃ i, (j : ℤ) ∣ v i) →
    ¬ StrongFree v →
    (∀ D : ℕ, ¬ UDFires v D) →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- The compressed crux is implied by Ind2 (it is the weaker statement). -/
theorem floorCruxU_of_ind2 (h : RoomA4Rosenfeld.BridgeDisjunctionQPrimInd2) : FloorCruxU := by
  intro k hk ih v hv hprim hl1o hdiv hSF _
  rcases h k hk ih v hv hprim hl1o hdiv hSF with hr | ⟨p, q, hq, hwit⟩
  · exact floor_of_rieszSharpFiresQ v hr
  · exact cube_floor_of_witness v hv p q hq hwit

/-- One inductive step from the compressed crux: Lemma 5, Lemma 4, `U_D`, then the crux. -/
theorem floor_step_U (hc : FloorCruxU) (k : ℕ) (hk : 11 ≤ k)
    (ih : ∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hprim : Finset.univ.gcd v = 1)
    (hSF : ¬ StrongFree v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  by_cases hall : ∀ l : Fin (k₀ + 1 + 1),
      Finset.univ.gcd (fun j : Fin (k₀ + 1) => v (l.succAbove j)) = 1
  · by_cases hdiv : ∀ j : ℕ, 2 ≤ j → j ≤ k₀ + 1 + 2 → ∃ i, (j : ℤ) ∣ v i
    · by_cases hU : ∃ D : ℕ, UDFires v D
      · obtain ⟨D, hD⟩ := hU
        exact floor_of_UD v D hD
      · push Not at hU
        exact hc (k₀ + 1) hk ih v hv hprim hall hdiv hSF hU
    · push Not at hdiv
      obtain ⟨j, hj2, hjk, hnd⟩ := hdiv
      exact cube_floor_of_witness v hv 1 j (by omega)
        (RoomA4Rosenfeld.witness_of_missing_divisor v hv j hj2 hjk hnd)
  · push Not at hall
    obtain ⟨l, hl⟩ := hall
    have := RoomA4Rosenfeld.floor_of_leaveOneOut_imprimitive k₀ (by omega) (ih k₀ (by omega))
      v hv hprim l hl
    exact_mod_cast this

/-- **Four-atom theorem with the compressed crux.**  A1, A2, A3 and `FloorCruxU` give the
universal floor. -/
theorem universalFloor_of_four_atoms_U
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hc : FloorCruxU) : UniversalFloor := by
  have hsep := separationSF_of_tiny_and_residual h1 (eightDoubledResidual_of_witness h2)
  have key : ∀ n : ℕ, ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → 1 / ((n : ℝ) + 2) ≤ ML v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hSF : StrongFree v
      · exact le_trans (hsep n) (ladderSF_le v hv hSF)
      · by_cases hk : n ≤ 10
        · exact hwinB n hk v hv hSF
        · refine floor_of_primitive_floor_pred (fun u => ¬ StrongFree u) ?_ ?_ v hv hSF
          · intro g hg w hgw hsfw
            exact hgw ((strongFree_smul g hg.ne' w).mpr hsfw)
          · intro u hu hprim hsfu
            exact floor_step_U hc n (by omega) ih u hu hprim hsfu
  intro n _ v hv
  exact key n v hv

end LRSpectrumFull.RoomA4Compress
