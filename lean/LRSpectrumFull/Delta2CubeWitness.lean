/-
# The rational-witness pillar and the hybrid residual

`cube_floor_of_witness` — a purely integer certificate for the floor: if
some rational `p/q` puts every runner at distance `≥ 1/(k+2)` — the integer
conditions `q ≤ (k+2)·min(v_i p mod q, q − v_i p mod q)` — then
`1/(k+2) ≤ ML v`.  Decidable per family.

`CubeHybridResidual` — the free side's residual, weakened to an OR: every
strongly free positive family satisfies **either** the van-mass certificate
**or** a bounded rational witness (`q ≤ 2·∑ v_i`; the max of the piecewise
linear loneliness sits at a kink, whose reduced denominator divides `2v_i`
or `v_i ± v_j`).  The two branches have complementary strengths: the mass
certificate handles sparse webs, witnesses handle the radix-tower families
where the mass margin is thin — the certificate-worst family `(1,3,9,14,40)`
has `ML = 7/27 = 0.259` at `t = 13/27` (`27 ∣ v₄+v₅`), far above the `1/6`
it needs.  `denseTorsion_of_cubeHybrid` rewires the program onto the weaker
Prop; `cubeHybrid_of_cubeCert` records that it is implied by the pure
mass-certificate residual.
-/
import LRSpectrumFull.Delta2CubeDecouple
import LRSpectrumFull.Delta2GridBridge
import LRSpectrumFull.CoveringWitness

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- **The rational-witness floor.**  Integer conditions
`q ≤ (k+2)·min(v_i p mod q, q − v_i p mod q)` for all `i` put every runner
at distance `≥ 1/(k+2)` at time `p/q`, so the floor holds. -/
theorem cube_floor_of_witness {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (p q : ℕ) (hq : 0 < q)
    (hwit : ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  refine ML_ge_of_witness v ((p : ℝ) / (q : ℝ)) (1 / ((k : ℝ) + 2)) (fun i => ?_)
  have hcast : ((v i : ℤ) : ℝ) = (((v i).toNat : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (hv i).le).symm
  have harg : (v i : ℝ) * ((p : ℝ) / (q : ℝ))
      = (((v i).toNat * p : ℕ) : ℝ) / (q : ℝ) := by
    rw [hcast]
    push_cast
    ring
  rw [harg, nid_natCast_div q _ hq]
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [div_le_div_iff₀ hk2 hq']
  have hm := hwit i
  have hmR : (q : ℝ) ≤ ((k : ℝ) + 2)
      * ((min ((v i).toNat * p % q) (q - (v i).toNat * p % q) : ℕ) : ℝ) := by
    exact_mod_cast hm
  linarith

/-- **The hybrid residual**: every strongly free positive family (`k = 4..7`)
satisfies the van-mass certificate or carries a bounded rational witness.
Strictly weaker than `CubeCertResidual`; per family both branches are
finitely checkable. -/
def CubeHybridResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v →
    (cubeEps k * (∑ i : Fin (k + 1),
        vanMass k (fun j' => v (i.succAbove j'))) < vanMass (k + 1) v)
    ∨ (∃ p q : ℕ, 0 < q ∧ q ≤ 2 * (∑ i, (v i).toNat) ∧
        ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q))

/-- The four-direction residual follows from the hybrid: each family closes
by whichever branch it satisfies. -/
theorem cubeFourDir_of_cubeHybrid (h : CubeHybridResidual) : CubeFourDirResidual := by
  intro k hk4 hk7 v hv hSF _ _ _ _ _ _ _ _
  rcases h k hk4 hk7 v hv hSF with hcert | ⟨p, q, hq, _, hwit⟩
  · exact cube_floor_of_cert hk4 v hv hcert
  · exact cube_floor_of_witness v hv p q hq hwit

/-- The free side of the all-`N` program rests on the hybrid residual. -/
theorem denseTorsion_of_cubeHybrid (h : CubeHybridResidual) : DenseTorsionResidual :=
  denseTorsion_of_fourDir (cubeFourDir_of_cubeHybrid h)

/-- The hybrid is implied by the pure mass-certificate residual: the
weakening is genuine. -/
theorem cubeHybrid_of_cubeCert (h : CubeCertResidual) : CubeHybridResidual :=
  fun k hk4 hk7 v hv hSF => Or.inl (h k hk4 hk7 v hv hSF)

end LRSpectrumFull
