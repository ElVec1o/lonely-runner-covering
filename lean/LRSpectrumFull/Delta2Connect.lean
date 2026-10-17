/-
# The connecting lemma: rational web masses ⟹ the floor

`rieszSharpFiresQ` (computable, rational web masses, the form the adversarial hunt attacks) is
bridged to the analytic floor.  The arithmetic half is *exactly* `absorption` with `S = univ`
and `B = ∑ᵢ(2Mᵢ − M)`: then `hpads` is vacuous, `hcoreB` is `le_refl`, and `absorption`'s
threshold `9.9225·(B + ((k+2) − |S|)·M) ≤ (k+2)²·M` becomes `9.9225·(B + M) ≤ (k+2)²·M`, which
is `rieszSharpFiresQ`'s budget verbatim (`99225/10000 = 9.9225`).

What remains is the **mass correspondence**: that the rational `webMassQ`/`webMassDelQ` equal
the real grid masses divided by `Q`.  Both are stated as explicit named hypotheses here rather
than assumed silently — they are the honest remaining gap, and they are *facts about the
`riesz_mass_web_real` bookkeeping*, not new mathematics: `webSections` is the ternary encoding
of the web, `sgn3` is the same `0 ↦ 0, 1 ↦ 1, 2 ↦ −1` decoding used inside `Delta2RieszMass`,
and the subfamily statement is the same identity after `succAbove` reindexing.

`floor_of_rieszSharpFiresQ_of_masses` is therefore the connecting lemma modulo exactly those
two bookkeeping facts, with every analytic step machine-checked.
-/
import LRSpectrumFull.Delta2GrandReduction
import LRSpectrumFull.Delta2MassCorrespond
import LRSpectrumFull.Delta2Scaling

namespace LRSpectrumFull

open Real

set_option maxHeartbeats 800000 in
/-- **The connecting lemma, modulo the mass correspondence.**  Given that the rational web
masses agree with the real grid masses at the canonical modulus (`hM`, `hMi`), the computable
criterion `rieszSharpFiresQ` implies the Lonely-Runner floor.  The analytic content is
`absorption` at `S = univ`; nothing else is assumed. -/
theorem floor_of_rieszSharpFiresQ_of_masses {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hM : rieszMassSum v (canonicalQ v) = (canonicalQ v : ℝ) * (webMassQ v : ℝ))
    (hMi : ∀ i : Fin (k + 1),
      rieszMassSum (fun j' : Fin k => v (i.succAbove j')) (canonicalQ v)
        = (canonicalQ v : ℝ) * (webMassDelQ v i : ℝ))
    (h : rieszSharpFiresQ v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  obtain ⟨hpos, hbudget⟩ := h
  have hQ0 : 0 < canonicalQ v := Nat.succ_pos _
  have hQR : (0 : ℝ) < ((canonicalQ v : ℕ) : ℝ) := by exact_mod_cast hQ0
  have hposR : (0 : ℝ) < (webMassQ v : ℝ) := by exact_mod_cast hpos
  have hM0 : 0 < ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ) := mul_pos hQR hposR
  -- the rational budget, cast to `ℝ`
  have hbudgetR : (99225 : ℝ) * ((∑ i, (2 * (webMassDelQ v i : ℝ) - (webMassQ v : ℝ)))
      + (webMassQ v : ℝ)) ≤ 10000 * ((k : ℝ) + 2) ^ 2 * (webMassQ v : ℝ) := by
    have hcast : ((99225 * ((∑ i, (2 * webMassDelQ v i - webMassQ v)) + webMassQ v) : ℚ) : ℝ)
        ≤ ((10000 * ((k : ℚ) + 2) ^ 2 * webMassQ v : ℚ) : ℝ) := by exact_mod_cast hbudget
    push_cast at hcast
    exact hcast
  -- the grid masses, definitionally the raw sums
  have hmassM : ∑ j ∈ Finset.range (canonicalQ v), ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))
      = ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ) := by rw [← hM]; rfl
  have hmassMi : ∀ i : Fin (k + 1),
      ∑ j ∈ Finset.range (canonicalQ v), ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))
      = ((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ) := by
    intro i; rw [← hMi i]; rfl
  -- `M ≤ 2Mᵢ`: the difference is `∑ⱼ (1 + cos θᵢ)·Pᵢ`, termwise nonnegative
  have h2Mi : ∀ i : Fin (k + 1),
      ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ)
        ≤ 2 * (((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ)) := by
    intro i
    have hsubnn : ∀ j : ℕ, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ)
          / ((canonicalQ v : ℕ) : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ)
          / ((canonicalQ v : ℕ) : ℝ)); linarith
    have hsplit : ∀ j : ℕ,
        (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ)
            / ((canonicalQ v : ℕ) : ℝ))))
          = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))
            * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ)
                / ((canonicalQ v : ℕ) : ℝ))) := fun j => by
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))) i]
    have hkey : 2 * (((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ))
        - ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ)
        = ∑ j ∈ Finset.range (canonicalQ v),
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ)
                  / ((canonicalQ v : ℕ) : ℝ))) := by
      rw [← hmassM, ← hmassMi i, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hsplit j]; ring
    have hnn : 0 ≤ ∑ j ∈ Finset.range (canonicalQ v),
        (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / ((canonicalQ v : ℕ) : ℝ)))
          * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ)
              / ((canonicalQ v : ℕ) : ℝ))) := by
      refine Finset.sum_nonneg (fun j _ => ?_)
      have h1 : (0 : ℝ) ≤ 1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ)
          / ((canonicalQ v : ℕ) : ℝ)) := by
        have := Real.neg_one_le_cos (2 * π * (v i : ℝ) * (j : ℝ)
          / ((canonicalQ v : ℕ) : ℝ)); linarith
      exact mul_nonneg h1 (hsubnn j)
    linarith [hkey ▸ hnn]
  -- apply `absorption` with `S = univ`
  refine absorption v (canonicalQ v) hQ0 (((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ)) hM0
    hmassM (fun i => ((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ)) hmassMi
    Finset.univ
    (∑ i, (2 * (((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ))
      - ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ)))
    (Finset.sum_nonneg (fun i _ => by linarith [h2Mi i]))
    (fun i hi => absurd (Finset.mem_univ i) hi) (le_refl _) ?_
  -- the threshold: `absorption`'s budget at `|S| = k+1` is exactly the rational one, scaled by `Q`
  have hcard : ((Finset.univ : Finset (Fin (k + 1))).card : ℝ) = (k : ℝ) + 1 := by
    simp [Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ i, (2 * (((canonicalQ v : ℕ) : ℝ) * (webMassDelQ v i : ℝ))
        - ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ)))
      = ((canonicalQ v : ℕ) : ℝ)
        * (∑ i, (2 * (webMassDelQ v i : ℝ) - (webMassQ v : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hcard, hsum]
  have hscaled : ((canonicalQ v : ℕ) : ℝ) * ((99225 : ℝ)
        * ((∑ i, (2 * (webMassDelQ v i : ℝ) - (webMassQ v : ℝ))) + (webMassQ v : ℝ)))
      ≤ ((canonicalQ v : ℕ) : ℝ)
        * (10000 * ((k : ℝ) + 2) ^ 2 * (webMassQ v : ℝ)) :=
    mul_le_mul_of_nonneg_left hbudgetR hQR.le
  nlinarith [hscaled, hQR]

/-- **The connecting lemma, unconditional.**  The mass hypotheses of
`floor_of_rieszSharpFiresQ_of_masses` are now *discharged* by the verified mass correspondence:
`rieszMassSum_eq_webMassQ` for the whole family, and `rieszMassSum_eq_webMassQ_of` composed with
the subfamily bijection `webMassQ_succAbove_eq_webMassDelQ` for each deleted index.  So the
computable criterion `rieszSharpFiresQ` implies the Lonely-Runner floor with **no** side
hypotheses — every step is machine-checked. -/
theorem floor_of_rieszSharpFiresQ {k : ℕ} (v : Fin (k + 1) → ℤ)
    (h : rieszSharpFiresQ v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  refine floor_of_rieszSharpFiresQ_of_masses v (rieszMassSum_eq_webMassQ v) ?_ h
  intro i
  have hsum : (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < canonicalQ v := by
    have hsplit := Fin.sum_univ_succAbove (fun j => (v j).natAbs) i
    simp only [canonicalQ]
    omega
  rw [rieszMassSum_eq_webMassQ_of (fun j' : Fin k => v (i.succAbove j')) (canonicalQ v)
        (Nat.succ_pos _) hsum, webMassQ_succAbove_eq_webMassDelQ v i]

/-- **The computable Bridge disjunction.**  Identical to `BridgeDisjunctionA` except the analytic
`rieszSharpCondition` is replaced by the *computable, rational* `rieszSharpFiresQ` — the exact
predicate the adversarial hunt evaluates.  The residue-witness side is verbatim. -/
def BridgeDisjunctionQ : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
    rieszSharpFiresQ v ∨
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- **The Bridge from its window and the computable disjunction.**  The full non-StrongFree half
follows from the finite window `k ≤ 10` plus `BridgeDisjunctionQ`, whose sharp branch is now
discharged by the *unconditional* `floor_of_rieszSharpFiresQ` (no `hcrit` hypothesis remains). -/
theorem relationBridgeSF_of_window_and_disjunctionQ
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQ) : RelationBridgeSF := by
  intro k v hv hSF
  by_cases hk : k ≤ 10
  · exact hwinB k hk v hv hSF
  · rcases hdisj k (by omega) v hv hSF with h | ⟨p, q, hq, hwit⟩
    · exact floor_of_rieszSharpFiresQ v h
    · exact cube_floor_of_witness v hv p q hq hwit

/-- **THE GRAND REDUCTION, computable-disjunction form.**  The Lonely Runner Conjecture for every
number of runners from the four named atoms, with the analytic Bridge disjunction replaced by its
**computable** counterpart `BridgeDisjunctionQ`.  The sharp branch's connecting lemma — previously
an open hypothesis — is now the verified `floor_of_rieszSharpFiresQ`.  Everything else is
machine-checked. -/
theorem universalFloor_of_four_atoms_Q
    (h1 : StrongFreeWindowTiny) (h2 : EightDoubledResidual)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQ) : UniversalFloor :=
  universalFloor_assembly (separationSF_of_tiny_and_residual h1 h2)
    (relationBridgeSF_of_window_and_disjunctionQ hwinB hdisj)

/-- **The dissociated-octet witness atom** (non-Riesz).  Every strongly-free eight-runner family
carrying a `±2`-relation admits a residue witness `t = p/q` — the pure covering condition
`cube_floor_of_witness` consumes at `k = 7` (`k + 2 = 9`).  This *bypasses* the falsified `±2`-web
mass correction entirely (the residue route, not the Riesz route).

Empirical status: **true with `q ≤ 31`** for every family produced by a 70-restart adversarial
hill-climb (random sampling: `q ≤ 22`).  The proof path is a Fourier main term
`q·(7/9)^8 ≈ 0.13 q` (positive already at small `q`) dominating the mod-`q` resonance count
`#{h : ∑ hₖvₖ ≡ 0}` that dissociation is exactly built to control — stated here as a named atom,
not proved. -/
def DissociatedOctetWitness : Prop :=
  ∀ v : Fin 8 → ℤ, (∀ i, 0 < v i) → StrongFree v → ¬ TwoFree v →
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ 9 * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- The witness atom discharges `EightDoubledResidual` outright — one application of
`cube_floor_of_witness` at `k = 7`.  No Riesz mass enters. -/
theorem eightDoubledResidual_of_witness (h : DissociatedOctetWitness) : EightDoubledResidual := by
  intro v hv hSF hTF
  obtain ⟨p, q, hq, hwit⟩ := h v hv hSF hTF
  simpa using cube_floor_of_witness (k := 7) v hv p q hq hwit

/-- **THE GRAND REDUCTION, fully covering/computable form.**  The Lonely Runner Conjecture for
every number of runners from four atoms, each now either a finite window or a pure
covering/criterion condition: the tiny StrongFree window `k = 3..6`, the **witness** atom
`DissociatedOctetWitness` for the `±2`-carriers, the Bridge window `k ≤ 10`, and the **computable**
disjunction `BridgeDisjunctionQ` for `k ≥ 11`.  Both formerly Riesz-flavored atoms (`±2` residual,
sharp branch) are discharged through `cube_floor_of_witness` / `floor_of_rieszSharpFiresQ`. -/
theorem universalFloor_of_four_atoms_QW
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQ) : UniversalFloor :=
  universalFloor_of_four_atoms_Q h1 (eightDoubledResidual_of_witness h2) hwinB hdisj

/-- **The floor for primitive families suffices** (`gcd = 1`).  By scale invariance
(`floor_of_primitive_floor`), `UniversalFloor` follows from its restriction to primitive families.
This shrinks the whole programme's remaining burden — including the crux Bridge disjunction — to
`gcd = 1` families, the class on which the disjunction erosion is measured to be far milder (the
non-primitive champions are scaled copies whose witnesses fall past the height-relative cap). -/
def UniversalFloorPrim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) →
    Finset.univ.gcd v = 1 → 1 / ((n : ℝ) + 2) ≤ ML v

theorem universalFloor_of_primitive (hp : UniversalFloorPrim) : UniversalFloor :=
  fun n hn v hv => floor_of_primitive_floor (fun w hw hpr => hp n hn w hw hpr) v hv

/-- Scale invariance of `StrongFree`: a common nonzero factor `g` neither creates nor destroys a
`{−1,0,1}`-relation, since `∑ cᵢ (g·vᵢ) = g · ∑ cᵢ vᵢ`. -/
theorem strongFree_smul {j : ℕ} (g : ℤ) (hg : g ≠ 0) (v : Fin j → ℤ) :
    StrongFree (fun i => g * v i) ↔ StrongFree v := by
  have key : ∀ c : Fin j → ℤ, ∑ i, c i * (g * v i) = g * ∑ i, c i * v i := fun c => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  constructor
  · intro h c hc hsum
    exact h c hc (by rw [key c, hsum, mul_zero])
  · intro h c hc hsum
    refine h c hc ?_
    have hk := key c; rw [hsum] at hk
    exact (mul_eq_zero.mp hk.symm).resolve_left hg

/-- **The computable Bridge disjunction, primitive form.**  Required only on `gcd = 1` families;
the general disjunction follows by scale invariance.  This is the class on which the erosion is
measured to be far milder (the non-primitive champions are scaled copies whose residue witnesses
fall past the height-relative cap). -/
def BridgeDisjunctionQPrim : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 →
    ¬ StrongFree v →
    rieszSharpFiresQ v ∨
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- The full non-StrongFree half from the window plus the **primitive** disjunction: a
relation-carrying family reduces to its primitive part (still relation-carrying, by
`strongFree_smul`), on which the primitive disjunction applies. -/
theorem relationBridgeSF_of_window_and_disjunctionQPrim
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQPrim) : RelationBridgeSF := by
  intro k v hv hSF
  by_cases hk : k ≤ 10
  · exact hwinB k hk v hv hSF
  · refine floor_of_primitive_floor_pred (fun u => ¬ StrongFree u) ?_ ?_ v hv hSF
    · intro g hg w hgw hsfw
      exact hgw ((strongFree_smul g hg.ne' w).mpr hsfw)
    · intro u hu hprim hsfu
      rcases hdisj k (by omega) u hu hprim hsfu with h | ⟨p, q, hq, hwit⟩
      · exact floor_of_rieszSharpFiresQ u h
      · exact cube_floor_of_witness u hu p q hq hwit

/-- **A verified slice of the crux disjunction: the Riesz branch fires for even-support-dominated
families.**  Whenever the subfamily masses satisfy `∑ᵢ webMassDelQ_i ≤ (k+1)·webMassQ` — equivalently
`W₁ = ∑_σ |supp σ|·(−½)^{|supp σ|} ≥ 0`, i.e. the web's even-support (positive) relations outweigh
its odd-support ones — the computable sharp criterion `rieszSharpFiresQ` holds outright (for `k ≥ 8`).
So the *open* part of `BridgeDisjunctionQPrim` shrinks to families with `W₁ < 0`
(support-3-heavy webs), the class where the residue witness is actually needed. -/
theorem rieszSharpFiresQ_of_subfamilySum_le {k : ℕ} (hk : 8 ≤ k) (v : Fin (k + 1) → ℤ)
    (hM : 0 < webMassQ v)
    (hsum : (∑ i, webMassDelQ v i) ≤ ((k : ℚ) + 1) * webMassQ v) :
    rieszSharpFiresQ v := by
  refine ⟨hM, ?_⟩
  have h1 : (∑ i, (2 * webMassDelQ v i - webMassQ v))
      = 2 * (∑ i, webMassDelQ v i) - ((k : ℚ) + 1) * webMassQ v := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hX : (∑ i, (2 * webMassDelQ v i - webMassQ v)) + webMassQ v ≤ ((k : ℚ) + 2) * webMassQ v := by
    rw [h1]; nlinarith [hsum]
  have hk10 : (10 : ℚ) ≤ (k : ℚ) + 2 := by
    have : (10 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hpos : (0 : ℚ) < ((k : ℚ) + 2) * webMassQ v := by positivity
  calc 99225 * ((∑ i, (2 * webMassDelQ v i - webMassQ v)) + webMassQ v)
      ≤ 99225 * (((k : ℚ) + 2) * webMassQ v) := by nlinarith [hX]
    _ ≤ 10000 * ((k : ℚ) + 2) ^ 2 * webMassQ v := by nlinarith [hM, hk10, hpos]

/-- **The extremal-witness slice of the crux.**  If no velocity is divisible by `k+2`, the single
witness `t = 1/(k+2)` clears the floor (each `‖v_i/(k+2)‖ ≥ 1/(k+2)`).  This is the extremal family's
own witness — it handles `(1,2,…,k+1)` itself and, empirically, ~42% of the families on which the
Riesz criterion fails.  Together with `rieszSharpFiresQ_of_subfamilySum_le`, the *open* part of the
crux disjunction shrinks to families that simultaneously have `W₁ < 0` **and** carry a velocity
`≡ 0 (mod k+2)` — the genuine near-tight core. -/
theorem floor_of_not_dvd_succ {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (h : ∀ i, ¬ ((k + 2 : ℕ) ∣ (v i).toNat)) : 1 / ((k : ℝ) + 2) ≤ ML v :=
  cube_floor_of_witness v hv 1 (k + 2) (by omega) (fun i => by
    have hr : (v i).toNat * 1 % (k + 2) ≠ 0 := by
      rw [mul_one]; exact fun h0 => h i (Nat.dvd_of_mod_eq_zero h0)
    have hlt : (v i).toNat * 1 % (k + 2) < k + 2 := Nat.mod_lt _ (by omega)
    have hpos : 0 < min ((v i).toNat * 1 % (k + 2)) ((k + 2) - (v i).toNat * 1 % (k + 2)) := by omega
    exact Nat.le_mul_of_pos_right (k + 2) hpos)

/-- **THE GRAND REDUCTION, primitive computable form.**  As `universalFloor_of_four_atoms_QW`, but
the crux disjunction `BridgeDisjunctionQPrim` is required only on `gcd = 1` families. -/
theorem universalFloor_of_four_atoms_QWprim
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQPrim) : UniversalFloor :=
  universalFloor_assembly (separationSF_of_tiny_and_residual h1 (eightDoubledResidual_of_witness h2))
    (relationBridgeSF_of_window_and_disjunctionQPrim hwinB hdisj)

end LRSpectrumFull
