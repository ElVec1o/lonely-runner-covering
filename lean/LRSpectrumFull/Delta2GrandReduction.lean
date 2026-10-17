/-
# The grand reduction: the Lonely Runner Conjecture from three named atoms

This file assembles the verified machinery of the programme into a single machine-checked
reduction.  **`universalQED_of_three_atoms`**: the Lonely Runner Conjecture for every number
of runners follows from

1. `hwinSF` — the StrongFree window: dissociated families of `2..8` velocities clear the
   floor (`k = 1..7`; the tail `k ≥ 8` is the *verified* `riesz_clears_floor_sharp`);
2. `hwinB`  — the Bridge window: relation-carrying families of `1..11` velocities clear
   the floor (`k ≤ 10`);
3. `hdisj`  — the analytic Bridge disjunction: every relation-carrying family with at least
   twelve velocities satisfies the sharp web-Riesz condition at the canonical modulus, or
   admits a residue witness (uncapped).

All glue is proved here from built modules only.  Note the previous top assembly
(`Delta2SeparationSummit`) had never compiled; this file inlines its argument from
`ladderSF_le` and is the first verified end-to-end assembly.

The disjunction consumers are exact: the sharp condition feeds `riesz_union_markov` with the
canonical masses *definitionally* (`rfl`), and the residue side feeds `cube_floor_of_witness`.
-/
import LRSpectrumFull.Delta2SeparationWindow
import LRSpectrumFull.Delta2WebRieszSharp
import LRSpectrumFull.Delta2CubeWitness
import LRSpectrumFull.Delta2BridgeDisjunction

namespace LRSpectrumFull

open Real

/-- The canonical modulus: one more than the total absolute height. -/
def canonicalQ {m : ℕ} (v : Fin m → ℤ) : ℕ := (∑ i, (v i).natAbs) + 1

/-- The Riesz mass of a family on the `Q`-point grid, as a raw sum. -/
noncomputable def rieszMassSum {m : ℕ} (v : Fin m → ℤ) (Q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range Q, ∏ i, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))

/-- **The analytic sharp web-Riesz condition** at the canonical modulus and `δ = 1/(k+2)`:
the Markov-sharpened budget `(∑ᵢ(2Mᵢ − M))·(1−c) < M·(1+c)` with the masses given by the raw
grid sums. -/
def rieszSharpCondition {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  (∑ i : Fin (k + 1), (2 * rieszMassSum (fun j' : Fin k => v (i.succAbove j')) (canonicalQ v)
      - rieszMassSum v (canonicalQ v)))
      * (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2))))
    < rieszMassSum v (canonicalQ v) * (1 + Real.cos (2 * π * (1 / ((k : ℝ) + 2))))

set_option maxHeartbeats 800000 in
/-- The sharp condition clears the floor: pure assembly — the mass hypotheses of
`riesz_union_markov` hold by `rfl` at the canonical modulus. -/
theorem floor_of_rieszSharpCondition {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : rieszSharpCondition v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  have hQ0 : 0 < canonicalQ v := Nat.succ_pos _
  have hδ0 : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  have hδ2 : (1 : ℝ) / ((k : ℝ) + 2) ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine riesz_union_markov v (canonicalQ v) hQ0 (1 / ((k : ℝ) + 2)) hδ0 hδ2
    (rieszMassSum v (canonicalQ v)) rfl
    (fun i => rieszMassSum (fun j' : Fin k => v (i.succAbove j')) (canonicalQ v))
    (fun i => rfl) ?_
  exact h

/-- **The Bridge disjunction, analytic form** (open).  Every relation-carrying family of at
least twelve velocities satisfies the sharp web-Riesz condition, or admits a residue witness
`t = p/q` — no cap on `q`.  The capped, computable `BridgeDisjunction` implies this form. -/
def BridgeDisjunctionA : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
    rieszSharpCondition v ∨
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- **The Bridge from its window and the disjunction.**  `RelationBridgeSF` — the full
non-StrongFree half of the programme — follows from the finite window `k ≤ 10` plus the
analytic disjunction. -/
theorem relationBridgeSF_of_window_and_disjunction
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionA) : RelationBridgeSF := by
  intro k v hv hSF
  by_cases hk : k ≤ 10
  · exact hwinB k hk v hv hSF
  · rcases hdisj k (by omega) v hv hSF with h | ⟨p, q, hq, hwit⟩
    · exact floor_of_rieszSharpCondition v h
    · exact cube_floor_of_witness v hv p q hq hwit

/-- **The seven-rung Separation window.**  The StrongFree ladder clears the floor at every
level, given only the rungs `1 ≤ k ≤ 7`: the base and nonemptiness are the verified
`ladderSF_base` and `freeSpectrumSF_nonempty`, and the tail `k ≥ 8` is the verified
`riesz_clears_floor_sharp`. -/
theorem separationSF_of_window7
    (hwin : ∀ k : ℕ, 1 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
        StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n := by
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simpa using ladderSF_base
  · apply le_csInf (freeSpectrumSF_nonempty n)
    rintro x ⟨v, hv, hSF, rfl⟩
    by_cases hle : n ≤ 7
    · exact hwin n h0 hle v hv hSF
    · exact riesz_clears_floor_sharp (by omega : 8 ≤ n) v hSF

/-- `UniversalFloor` is `UniversalQED` with `LRC` unfolded (`Delta2GlobalPartition.LRC n` is
definitionally `∀ v, pos → 1/(n+2) ≤ ML v`).  Stated locally because the keystone's import
cone contains the multi-hour seam modules; a keystone-importing one-line bridge can convert
`UniversalFloor → UniversalQED` by `exact` whenever that cone is built. -/
def UniversalFloor : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → 1 / ((n : ℝ) + 2) ≤ ML v

/-- The summit assembly, from built modules only (the module previously carrying this
statement had never compiled; the argument is `ladderSF_le` plus a case split). -/
theorem universalFloor_assembly
    (hsep : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n)
    (hB : RelationBridgeSF) : UniversalFloor := by
  intro n hn v hv
  by_contra h
  push_neg at h
  by_cases hSF : StrongFree v
  · have h1 := ladderSF_le v hv hSF
    have h2 := hsep n
    linarith
  · have := hB n v hv hSF
    linarith

/-- **THE GRAND REDUCTION.**  The Lonely Runner Conjecture, for every number of runners,
follows from exactly three named atoms:

* `hwinSF` — the StrongFree window `k = 1..7` (dissociated families of at most eight
  velocities);
* `hwinB` — the Bridge window `k ≤ 10` (relation-carrying families of at most eleven
  velocities);
* `hdisj` — the analytic Bridge disjunction for twelve velocities and beyond.

Everything else — the Riesz tail on the free side, the Markov web-Riesz consumer and the
residue consumer of the disjunction, and the summit case split — is machine-checked. -/
theorem universalFloor_of_three_atoms
    (hwinSF : ∀ k : ℕ, 1 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
        StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionA) : UniversalFloor :=
  universalFloor_assembly (separationSF_of_window7 hwinSF)
    (relationBridgeSF_of_window_and_disjunction hwinB hdisj)

/-- **THE GRAND REDUCTION, sharpest form.**  The free side enters through the strongest
in-repo reduction (`separationSF_of_tiny_and_residual`): the StrongFree window shrinks to
`k = 3..6` in full plus only the `±2`-relation carriers at `k = 7`.  The Lonely Runner
Conjecture for every number of runners from **four** named atoms:

* `h1` — `StrongFreeWindowTiny`: dissociated families, `4..7` velocities;
* `h2` — `EightDoubledResidual`: dissociated `8`-velocity families carrying a `±2`-relation;
* `hwinB` — the Bridge window `k ≤ 10`;
* `hdisj` — the analytic Bridge disjunction for `k ≥ 11`. -/
theorem universalFloor_of_four_atoms
    (h1 : StrongFreeWindowTiny) (h2 : EightDoubledResidual)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionA) : UniversalFloor :=
  universalFloor_assembly (separationSF_of_tiny_and_residual h1 h2)
    (relationBridgeSF_of_window_and_disjunction hwinB hdisj)

/-- The computable, capped disjunction (`BridgeDisjunction`, the form the adversarial hunt
attacks) delivers the analytic form, **modulo the single connecting lemma**
`rieszSharpFiresQ → rieszSharpCondition` (the rational-web-mass bridge, stated here as the
explicit hypothesis `hcrit`).  The residue side is monotone: a capped witness is a witness. -/
theorem bridgeDisjunctionA_of_computable
    (hcrit : ∀ {k : ℕ} (v : Fin (k + 1) → ℤ), rieszSharpFiresQ v → rieszSharpCondition v)
    (h : BridgeDisjunction) : BridgeDisjunctionA := by
  intro k hk v hv hSF
  rcases h k hk v hv hSF with hq | ⟨p, q, hq0, _, hwit⟩
  · exact Or.inl (hcrit v hq)
  · exact Or.inr ⟨p, q, hq0, hwit⟩

end LRSpectrumFull
