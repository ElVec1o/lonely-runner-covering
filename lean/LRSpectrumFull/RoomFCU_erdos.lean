/-
Room FCU, Erdos seat (the right question).  Pricing statements for `FloorCruxU`.

* `floorCruxU_of_universalFloor` : the universal floor (LRC for every number of runners)
  implies `FloorCruxU`.  With `universalFloor_of_four_atoms_U` this says: given A1-A3,
  `FloorCruxU` is EQUIVALENT to LRC.  The crux has the full price of LRC.
* `universalFloor_iff_divisible` : LRC is equivalent to the floor on the sub-class
  `D` of families in which `n+2` (the number of runners) divides some speed.  The
  complement of `D` is closed by the time `1/(n+2)` (Lemma 4).
* `universalFloor_of_strictD` : a strict floor on `D` (the strong form of CONJECTURE (T):
  "no family in D is tight") implies LRC.  So (T) in its strong form costs at least LRC.
-/
import Mathlib
import LRSpectrumFull.MaxLoneliness
import LRSpectrumFull.Delta2CubeWitness
import LRSpectrumFull.Delta2GrandReduction
import LRSpectrumFull.RoomA4_rosenfeld
import LRSpectrumFull.RoomA4_compress

namespace LRSpectrumFull.RoomFCUErdos

open LRSpectrumFull

/-- LRC implies the compressed crux (trivially: its conclusion is LRC for one family). -/
theorem floorCruxU_of_universalFloor (h : UniversalFloor) : RoomA4Compress.FloorCruxU := by
  intro k hk _ v hv _ _ _ _ _
  exact h k (by omega) v hv

/-- Floor on the sub-class `D` (runner count divides some speed). -/
def FloorD : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) →
    (∃ i, ((n + 2 : ℕ) : ℤ) ∣ v i) → 1 / ((n : ℝ) + 2) ≤ ML v

/-- Strict floor on `D`: strong form of CONJECTURE (T). -/
def StrictFloorD : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) →
    (∃ i, ((n + 2 : ℕ) : ℤ) ∣ v i) → 1 / ((n : ℝ) + 2) < ML v

/-- Outside `D` the floor holds by the time `1/(n+2)`. -/
theorem floor_of_not_D {n : ℕ} (v : Fin (n + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hnd : ∀ i, ¬ (((n + 2 : ℕ) : ℤ) ∣ v i)) : 1 / ((n : ℝ) + 2) ≤ ML v :=
  cube_floor_of_witness v hv 1 (n + 2) (by omega)
    (RoomA4Rosenfeld.witness_of_missing_divisor v hv (n + 2) (by omega) le_rfl hnd)

theorem universalFloor_iff_divisible : UniversalFloor ↔ FloorD := by
  constructor
  · intro h n hn v hv _
    exact h n hn v hv
  · intro h n hn v hv
    by_cases hD : ∃ i, ((n + 2 : ℕ) : ℤ) ∣ v i
    · exact h n hn v hv hD
    · push Not at hD
      exact floor_of_not_D v hv hD

theorem universalFloor_of_strictD (h : StrictFloorD) : UniversalFloor :=
  universalFloor_iff_divisible.mpr (fun n hn v hv hD => (h n hn v hv hD).le)

/-- Equivalence of the compressed crux with LRC, given the three other atoms. -/
theorem floorCruxU_iff_universalFloor
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
        ¬ StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v) :
    RoomA4Compress.FloorCruxU ↔ UniversalFloor :=
  ⟨RoomA4Compress.universalFloor_of_four_atoms_U h1 h2 hwinB, floorCruxU_of_universalFloor⟩

/-- Statement only (no proof yet; `def`, so no `sorry` enters the module).  Lemma P, the
one-sided perturbation of the time `a/(k+2)`: if exactly one speed `v i0` is divisible by
`q = k+2`, it is the strictly largest speed, and some unit `u` mod `q` is the residue of no
speed, then the floor holds STRICTLY.  Proof (PROVED on paper, report_erdos.md): take
`a = u⁻¹ mod q`, `t = a/q - c/(q v_{i0})`, `c = min 2 ((1 + v_{i0}/V)/2)`, `V` the largest
other speed. -/
def LemmaP_statement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ∀ i0 : Fin (k + 1),
    ((k + 2 : ℕ) : ℤ) ∣ v i0 →
    (∀ i, i ≠ i0 → ¬ (((k + 2 : ℕ) : ℤ) ∣ v i) ∧ v i < v i0) →
    (∃ u : ℕ, Nat.Coprime u (k + 2) ∧ ∀ i, ¬ (v i ≡ (u : ℤ) [ZMOD ((k + 2 : ℕ) : ℤ)])) →
    1 / ((k : ℝ) + 2) < ML v

end LRSpectrumFull.RoomFCUErdos
