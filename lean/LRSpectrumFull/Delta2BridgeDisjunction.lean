/-
# The pad lemma and the Bridge disjunction, pinned

Two pieces toward instantiating `absorption` and closing the Bridge:

* `web_coeff_zero_of_big` — a velocity exceeding the sum of all the others has coefficient `0`
  in every `{−1,0,1}` relation.  Iterated over super-increasing pads, this is what makes
  `web(core ∪ pads) = web(core)`: the structural half of every concrete `absorption` instance.

* `BridgeDisjunction` — the open glue statement, pinned as a `Prop` with a *computable*
  criterion side (`rieszSharpFiresQ`, rational web masses; `99225/10000` majorizes `π²`), per
  the formalize-the-statement-first discipline.  No proof is claimed here; the hunt attacks it
  computationally, and `riesz_union_markov` + `riesz_mass_web_real` are the intended consumers
  once a connecting lemma `rieszSharpFiresQ v → 1/(k+2) ≤ ML v` is built.
-/
import LRSpectrumFull.Delta2WebAbsorb

namespace LRSpectrumFull

/-- **The pad lemma.**  A velocity strictly larger than the sum of the absolute values of all
the others cannot participate in any `{−1,0,1}` relation: its coefficient vanishes in every
vanishing combination.  Iterating this over super-increasing pads shows that padding a core
with fast free runners adjoins no relations. -/
theorem web_coeff_zero_of_big {m : ℕ} (v : Fin m → ℤ) (p : Fin m)
    (hbig : (∑ i ∈ Finset.univ.erase p, (v i).natAbs) < (v p).natAbs)
    (c : Fin m → ℤ) (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hrel : (∑ i, c i * v i) = 0) : c p = 0 := by
  by_contra hcp
  have hsplit : c p * v p + ∑ i ∈ Finset.univ.erase p, c i * v i = 0 := by
    rw [Finset.add_sum_erase _ (fun i => c i * v i) (Finset.mem_univ p)]
    exact hrel
  have hneg : c p * v p = -(∑ i ∈ Finset.univ.erase p, c i * v i) := by linarith
  have habs : (c p * v p).natAbs ≤ ∑ i ∈ Finset.univ.erase p, (c i * v i).natAbs := by
    rw [hneg, Int.natAbs_neg]
    exact Int.natAbs_sum_le _ _
  have hcp1 : (c p).natAbs = 1 := by
    rcases hc p with h | h | h
    · simp [h]
    · exact absurd h hcp
    · simp [h]
  have hlhs : (c p * v p).natAbs = (v p).natAbs := by
    rw [Int.natAbs_mul, hcp1, one_mul]
  have hrhs : (∑ i ∈ Finset.univ.erase p, (c i * v i).natAbs)
      ≤ ∑ i ∈ Finset.univ.erase p, (v i).natAbs := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Int.natAbs_mul]
    have h1 : (c i).natAbs ≤ 1 := by rcases hc i with h | h | h <;> simp [h]
    calc (c i).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
      _ = (v i).natAbs := one_mul _
  omega

/-! ## The computable criterion and the pinned disjunction -/

/-- Ternary coefficient decoding: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ −1`. -/
def sgn3 : Fin 3 → ℤ := fun t => if t = 1 then 1 else if t = 2 then -1 else 0

/-- The `{−1,0,1}` web of a family, as ternary sections — computable. -/
def webSections {m : ℕ} (v : Fin m → ℤ) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter (fun σ => (∑ i, sgn3 (σ i) * v i) = 0 ∧ σ ≠ (fun _ => 0))

/-- The web mass `M/Q` as a rational: `1 + Σ_{ε∈web} (−1/2)^{|supp ε|}`. -/
def webMassQ {m : ℕ} (v : Fin m → ℤ) : ℚ :=
  1 + ∑ σ ∈ webSections v, (-1 / 2 : ℚ) ^ (Finset.univ.filter (fun i => σ i ≠ 0)).card

/-- The subfamily web mass `Mᵢ/Q` as a rational: the relations avoiding `p`. -/
def webMassDelQ {m : ℕ} (v : Fin m → ℤ) (p : Fin m) : ℚ :=
  1 + ∑ σ ∈ (webSections v).filter (fun σ => σ p = 0),
    (-1 / 2 : ℚ) ^ (Finset.univ.filter (fun i => σ i ≠ 0)).card

/-- The computable sharp web-Riesz criterion: positive mass, and the `π²`-majorized budget
`9.9225·(Σ(2Mᵢ − M) + M) ≤ (k+2)²·M`, in exact rationals (`99225/10000 > π²`).  By
`absorption`-style arithmetic this implies the Markov condition of `riesz_union_markov` at
`δ = 1/(k+2)`; the connecting lemma is future work and is *not* claimed here. -/
def rieszSharpFiresQ {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  0 < webMassQ v ∧
  99225 * ((∑ i, (2 * webMassDelQ v i - webMassQ v)) + webMassQ v)
    ≤ 10000 * ((k : ℚ) + 2) ^ 2 * webMassQ v

/-- **The Bridge disjunction, v1.1** (open; the glue statement of the reduction).  Every
non-StrongFree positive family with at least twelve velocities either satisfies the computable
sharp web-Riesz criterion or admits a residue witness `t = p/q` with the *height-relative* cap
`q ≤ 8·log₂(Σ|vᵢ| + 2)`.

Version note (I10).  v1.0 used the fixed cap `q ≤ 60` and was WRONG BY DESIGN: witness
denominators grow like `6·log H` (the bounded-witness refutation, Update 70), so at any fixed
cap the adversary simply raises the height until the smallest witness crosses it.  The hunt
found exactly this — a height-5000 family whose smallest witness is `q = 59` against the cap
`60`, with 366 witnesses below 500.  Nothing cited v1.0. -/
def BridgeDisjunction : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
    rieszSharpFiresQ v ∨
    ∃ p q : ℕ, 0 < q ∧ q ≤ 8 * Nat.log2 ((∑ i, (v i).natAbs) + 2) ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

end LRSpectrumFull
