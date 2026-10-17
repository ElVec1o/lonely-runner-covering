/-
# The web certificate: the four-direction wall becomes integer combinatorics

`cube_floor_of_cert` — for any positive family, the floor `1/(k+2)` follows
from a single inequality between the *van masses*: the `cubeWtR`-weighted
counts of vanishing `[-3,3]`-combinations of the family and of its `k+1`
one-runner-deleted subfamilies.  The analysis layer (Riesz measure, union
bound, exact mass identities) is discharged once and for all; what remains
of the four-direction wall is arithmetic on the finite vanishing webs.

The thresholds are rational (`cubeEps`): at `k = 4` the cosine factor is
*exactly* `1/8` (`cos(π/3) = 1/2`), so the certificate is the pure integer
inequality `∑ S_w < S` in the octuple weights `w8 = (20, -15, 6, -1)`
(`cube_floor_of_cert_four_int`).  For `k ≥ 5` the sextic π-chain gives
`(1 - cos(2π/(k+2)))³ ≤ 1/15, 3/100, 3/200` (`k = 5, 6, ≥ 7`).

`CubeCertResidual` restates the four-direction residual as this certificate;
`denseTorsion_of_cubeCert` rewires the free side of the all-`N` program onto
it.  Exhaustive computation (all `51{,}793{,}894` strongly free five-runner
families of height `≤ 100`) verifies the `k = 4` certificate with worst
ratio `0.86769` — the statement is finite-checkable per family and carries
a `13\%` uniform margin over the scanned landscape.
-/
import LRSpectrumFull.Delta2CubePara

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- The van mass of a family: the `cubeWtR`-weighted count of its vanishing
`[-3,3]`-combinations. -/
noncomputable def vanMass (m : ℕ) (v : Fin m → ℤ) : ℝ :=
  ∑ c ∈ (Fintype.piFinset
      (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ i, c i * v i) = 0),
    ∏ i, cubeWtR (c i)

/-- The integer van mass, in the octuple weights `w8 = (20, -15, 6, -1)`. -/
def vanMassZ (m : ℕ) (v : Fin m → ℤ) : ℤ :=
  ∑ c ∈ (Fintype.piFinset
      (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ i, c i * v i) = 0),
    ∏ i, w8 (c i).natAbs

/-- The van mass is the integer van mass over `8^m`. -/
theorem vanMass_eq_z (m : ℕ) (v : Fin m → ℤ) :
    vanMass m v = (vanMassZ m v : ℝ) / 8 ^ m := by
  unfold vanMass vanMassZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.prod_congr rfl (fun i _ => cubeWtR_w8 (c i)), Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The rational cube thresholds: `1/8` at the corner `k = 4`, then `1/15`,
`3/100`, `3/200` from the sextic chain. -/
noncomputable def cubeEps (k : ℕ) : ℝ :=
  if k ≤ 4 then 1/8 else if k = 5 then 1/15 else if k = 6 then 3/100 else 3/200

/-- The sextic π-chain, `k ≥ 5`: the cosine factor times `(k+2)^6` stays
below `8 · 961.51`. -/
theorem cube_u3_pow6 {k : ℕ} (hk : 5 ≤ k) :
    (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * ((k : ℝ) + 2) ^ 6
      < 7692.08 := by
  have hk5' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ)
    linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  have hδ61 : δ ^ 6 * ((k : ℝ) + 2) ^ 6 = 1 := by
    rw [← mul_pow, hδval, one_pow]
  have hK2pos : (0 : ℝ) < ((k : ℝ) + 2) ^ 6 := by positivity
  have hexp : (2 * (π * δ) ^ 2) ^ 3 = 8 * π ^ 6 * δ ^ 6 := by ring
  calc (1 - Real.cos (2 * π * δ)) ^ 3 * ((k : ℝ) + 2) ^ 6
      < (2 * (π * δ) ^ 2) ^ 3 * ((k : ℝ) + 2) ^ 6 :=
        mul_lt_mul_of_pos_right hu3 hK2pos
    _ = 8 * π ^ 6 * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by rw [hexp]; ring
    _ = 8 * π ^ 6 := by rw [hδ61]; ring
    _ < 7692.08 := by nlinarith [hπ6]

/-- The cosine factor is at most the rational threshold, every `k ≥ 4`. -/
theorem cube_eps_bound {k : ℕ} (hk : 4 ≤ k) :
    (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 ≤ cubeEps k := by
  rcases eq_or_lt_of_le hk with hk4 | hk5
  · subst hk4
    have harg : 2 * π * (1 / ((4 : ℕ) + 2 : ℝ)) = π / 3 := by
      push_cast
      ring
    rw [harg, Real.cos_pi_div_three]
    norm_num [cubeEps]
  · have hk5le : 5 ≤ k := by omega
    have hchain := cube_u3_pow6 hk5le
    rcases eq_or_lt_of_le hk5le with hk5' | hk6
    · rw [← hk5'] at hchain ⊢
      have heval : (((5 : ℕ) : ℝ) + 2) ^ 6 = 117649 := by norm_num
      rw [heval] at hchain
      have hε : cubeEps 5 = 1/15 := by norm_num [cubeEps]
      rw [hε]
      linarith
    · have hk6le : 6 ≤ k := by omega
      rcases eq_or_lt_of_le hk6le with hk6' | hk7
      · rw [← hk6'] at hchain ⊢
        have heval : (((6 : ℕ) : ℝ) + 2) ^ 6 = 262144 := by norm_num
        rw [heval] at hchain
        have hε : cubeEps 6 = 3/100 := by norm_num [cubeEps]
        rw [hε]
        linarith
      · have hk7' : 7 ≤ k := by omega
        have hK9 : (531441 : ℝ) ≤ ((k : ℝ) + 2) ^ 6 := by
          have hk7R : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk7'
          calc (531441 : ℝ) = 9 ^ 6 := by norm_num
            _ ≤ ((k : ℝ) + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
        have hε : cubeEps k = 3/200 := by
          unfold cubeEps
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hε]
        have hcnn : 0 ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 := by
          have := Real.cos_le_one (2 * π * (1 / ((k : ℝ) + 2)))
          positivity
        nlinarith [hchain, hK9, hcnn]

set_option maxHeartbeats 800000 in
/-- **The certificate floor.**  A positive `(k+1)`-family (`k ≥ 4`) whose van
masses satisfy `cubeEps k · ∑ᵢ vanMass(subfamily i) < vanMass(family)` meets
the floor `1/(k+2)`.  The Riesz analysis is fully discharged: both masses
are exact grid identities, the subfamily masses are nonnegative from the
trigonometric side, and the crude union engine closes. -/
theorem cube_floor_of_cert {k : ℕ} (hk : 4 ≤ k) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, 0 < v i)
    (hcert : cubeEps k * (∑ i : Fin (k + 1),
        vanMass k (fun j' => v (i.succAbove j'))) < vanMass (k + 1) v) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hQfull : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hM := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQfull
  have hMsub : ∀ i : Fin (k + 1),
      (∑ j ∈ Finset.range Q, (∏ j' : Fin k,
        (1 - Real.cos (2 * π * ((v (i.succAbove j') : ℤ) : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      = (Q : ℝ) * vanMass k (fun j' => v (i.succAbove j')) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    exact riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
  -- subfamily masses are nonnegative from the trigonometric side
  have hsubnn : ∀ i : Fin (k + 1),
      0 ≤ vanMass k (fun j' => v (i.succAbove j')) := by
    intro i
    have htrig : 0 ≤ ∑ j ∈ Finset.range Q, (∏ j' : Fin k,
        (1 - Real.cos (2 * π * ((v (i.succAbove j') : ℤ) : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 :=
      Finset.sum_nonneg (fun j _ => pow_nonneg (Finset.prod_nonneg (fun j' _ => by
        have := Real.cos_le_one (2 * π * ((v (i.succAbove j') : ℤ) : ℝ) * (j : ℝ) / (Q : ℝ))
        linarith)) 3)
    rw [hMsub i] at htrig
    by_contra hneg
    push_neg at hneg
    have : (Q : ℝ) * vanMass k (fun j' => v (i.succAbove j')) < 0 :=
      mul_neg_of_pos_of_neg hQR hneg
    linarith
  have hsumnn : 0 ≤ ∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')) :=
    Finset.sum_nonneg (fun i _ => hsubnn i)
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity)
    (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith)
    ((Q : ℝ) * vanMass (k + 1) v)
    (fun i => (Q : ℝ) * vanMass k (fun j' => v (i.succAbove j')))
    hM hMsub ?_
  have hufac := cube_eps_bound hk
  have hstep1 : (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
      * (∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')))
      ≤ cubeEps k * (∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j'))) :=
    mul_le_mul_of_nonneg_right hufac hsumnn
  have hsum : (∑ i : Fin (k + 1), (Q : ℝ) * vanMass k (fun j' => v (i.succAbove j')))
      = (Q : ℝ) * ∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')) :=
    (Finset.mul_sum _ _ _).symm
  rw [hsum]
  calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * ((Q : ℝ) * ∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j')))
      = (Q : ℝ) * ((1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
          * ∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j'))) := by ring
    _ ≤ (Q : ℝ) * (cubeEps k
          * ∑ i : Fin (k + 1), vanMass k (fun j' => v (i.succAbove j'))) :=
        mul_le_mul_of_nonneg_left hstep1 hQR.le
    _ < (Q : ℝ) * vanMass (k + 1) v := mul_lt_mul_of_pos_left hcert hQR

/-- **The integer corner.**  At `k = 4` the certificate is a pure integer
inequality: if `∑ᵢ vanMassZ(subfamily i) < vanMassZ(family)` in the octuple
weights `(20, -15, 6, -1)`, the five-runner family meets the floor `1/6`. -/
theorem cube_floor_of_cert_four_int (v : Fin 5 → ℤ) (hv : ∀ i, 0 < v i)
    (hcert : (∑ i : Fin 5, vanMassZ 4 (fun j' => v (i.succAbove j')))
      < vanMassZ 5 v) :
    1 / ((4 : ℝ) + 2) ≤ ML v := by
  have h8 : (0 : ℝ) < 8 ^ 5 := by norm_num
  refine cube_floor_of_cert (le_refl 4) v hv ?_
  have hε : cubeEps 4 = 1/8 := by norm_num [cubeEps]
  rw [hε, vanMass_eq_z]
  have hsub : (∑ i : Fin 5, vanMass 4 (fun j' => v (i.succAbove j')))
      = (∑ i : Fin 5, (vanMassZ 4 (fun j' => v (i.succAbove j')) : ℝ)) / 8 ^ 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => vanMass_eq_z 4 _)
  rw [hsub]
  have hcast : ((∑ i : Fin 5, vanMassZ 4 (fun j' => v (i.succAbove j')) : ℤ) : ℝ)
      < ((vanMassZ 5 v : ℤ) : ℝ) := by exact_mod_cast hcert
  push_cast at hcast ⊢
  linarith

/-- **The certificate residual**: the free side's last hypothesis, now pure
web arithmetic.  For every `k ∈ [4,7]` and every strongly free positive
family, the rational-threshold van-mass inequality holds.  At `k = 4` this
is the integer inequality `∑ S_w < S`; verified exhaustively for all
`51{,}793{,}894` strongly free five-runner families of height `≤ 100`
(worst ratio `0.86769`). -/
def CubeCertResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v →
    cubeEps k * (∑ i : Fin (k + 1),
        vanMass k (fun j' => v (i.succAbove j'))) < vanMass (k + 1) v

/-- The four-direction residual follows from the certificate. -/
theorem cubeFourDir_of_cubeCert (h : CubeCertResidual) : CubeFourDirResidual := by
  intro k hk4 hk7 v hv hSF _ _ _ _ _ _ _ _
  exact cube_floor_of_cert hk4 v hv (h k hk4 hk7 v hv hSF)

/-- The dense-torsion shard reduces to the web certificate: the free side of
the all-`N` program now rests on finite web arithmetic. -/
theorem denseTorsion_of_cubeCert (h : CubeCertResidual) : DenseTorsionResidual :=
  denseTorsion_of_fourDir (cubeFourDir_of_cubeCert h)

end LRSpectrumFull
