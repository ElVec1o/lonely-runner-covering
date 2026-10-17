/-
# Explicit Riesz lower bound for dissociated families (first-moment)

Building on `riesz_mass` (the mean-value identity `∑_{j<Q} ∏_i (1 − cos 2πv_i j/Q) = Q`),
this file extracts an **explicit** Lonely-Runner lower bound for a `StrongFree` (dissociated)
family via the first-moment (union) bound over the Riesz weight:

  `2(m) · sin²(πδ) < 1  ⟹  δ ≤ ML v`,

hence `ML(v) ≥ 1/(π√(2m))` for every dissociated `m`-family — the explicit form of Bedert's
`ML ≫ 1/√m` (Lemma 4.1), with constant `1/(π√2) ≈ 0.2251`.

**Scope (honest):** the union bound gives constant `1/(π√2) ≈ 0.225 < 1/4`. `riesz_clears_floor`
turns this into the Separation floor `1/(k+2) ≤ ML v` for every dissociated family of `≥ 18`
runners, unconditionally. The finite residue — dissociated families of `m = 14,15,16,17`
runners, where `2m sin²(π/(m+1))` sits just above `1` — needs the second-moment overlap
correction (sharpen the union constant `0.225 → ≥ 1/4`), which is not formalized here.
-/
import LRSpectrumFull.Delta2RieszMass
import LRSpectrumFull.MaxLoneliness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

open Complex Real

namespace LRSpectrumFull

/-- **Real form of the Riesz mass identity.**  The `Complex.cos` identity `riesz_mass`
descends to `Real.cos` since every term is a real cast. -/
theorem riesz_mass_real (m : ℕ) (v : Fin m → ℤ) (hv : StrongFree v) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) := by
  have h := riesz_mass m v hv Q hQ0 hQ
  have hcs :
      ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have cast_eq :
      ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ) = ((Q : ℕ) : ℂ) := by
    rw [hcs, h]
  exact_mod_cast cast_eq


/-- Real form of `riesz_mass_single_relation`. -/
theorem riesz_mass_single_relation_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) (r : Fin m → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * v i) = 0)
    (hchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c = r ∨ c = -r) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * (1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) := by
  have h := riesz_mass_single_relation m v Q hQ0 hQ r hr0 hrmem hrel hchar
  have hcs : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have cast_eq : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ((Q : ℝ) * (1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) : ℝ) := by
    rw [hcs, h]; push_cast [apply_ite Complex.ofReal]; ring
  exact_mod_cast cast_eq

/-- `cos(2πθ)` depends only on the distance from `θ` to `ℤ`. -/
theorem cos_two_pi_nid (θ : ℝ) :
    Real.cos (2 * π * θ) = Real.cos (2 * π * nearestIntDist θ) := by
  have hfract : Real.cos (2 * π * θ) = Real.cos (2 * π * Int.fract θ) := by
    have hEq : 2 * π * θ = 2 * π * Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [Int.fract]; push_cast; ring
    rw [hEq, Real.cos_add_int_mul_two_pi]
  rw [hfract]
  unfold nearestIntDist
  rcases le_total (Int.fract θ) (1 - Int.fract θ) with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge,
        show 2 * π * (1 - Int.fract θ) = -(2 * π * Int.fract θ) + 2 * π by ring,
        Real.cos_add_two_pi, Real.cos_neg]

/-- Dissociativity (`StrongFree`) passes to any sub-family. -/
theorem strongFree_succAbove {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : StrongFree v)
    (i : Fin (k + 1)) : StrongFree (fun j => v (i.succAbove j)) := by
  intro c hc hsum j
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc j'
  have hsum' : (∑ w, d w * v w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum
  have hz := hv d hmem hsum' (i.succAbove j)
  rwa [hd_succ] at hz


/-- Removing a runner **in** the relation's support leaves a dissociated sub-family. -/
theorem subfamily_strongFree {k : ℕ} (u : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (i : Fin (k + 1)) (hri : r i ≠ 0) :
    StrongFree (fun j' => u (i.succAbove j')) := by
  intro c' hc' hsum' j'
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c'
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  have hd0 : d = 0 := by
    rcases hchar d hmem hsumd with h | h | h
    · exact h
    · exact absurd (h ▸ hd_same) hri
    · exact absurd (by have h2 := h ▸ hd_same; simp only [Pi.neg_apply, neg_eq_zero] at h2; exact h2) hri
  have := congrFun hd0 (i.succAbove j')
  rwa [hd_succ] at this

/-- Removing a runner **outside** the relation's support keeps a single-relation sub-family. -/
theorem subfamily_hchar {k : ℕ} (u : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (i : Fin (k + 1)) (hri : r i = 0) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i.succAbove j')) = 0 →
      c' = 0 ∨ c' = (fun j' => r (i.succAbove j')) ∨ c' = -(fun j' => r (i.succAbove j')) := by
  intro c' hc' hsum'
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c'
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  rcases hchar d hmem hsumd with h | h | h
  · left; funext j'; rw [← hd_succ j', h]; rfl
  · right; left; funext j'; rw [← hd_succ j', h]
  · right; right; funext j'; rw [← hd_succ j', h]; rfl

/-- Real form of the two-relation mass identity. -/
theorem riesz_mass_two_relations_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (r s : Fin m → ℤ) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1)
    (hsmem : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hrel_r : (∑ i, r i * v i) = 0) (hrel_s : (∑ i, s i * v i) = 0)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * ((1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
                 * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))) := by
  have h := riesz_mass_two_relations m v Q hQ0 hQ r s hr0 hs0 hrmem hsmem hrel_r hrel_s hdisj hchar2
  have hcs : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have cast_eq : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ((Q : ℝ) * ((1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
                  * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))) : ℝ) := by
    rw [hcs, h]; push_cast [apply_ite Complex.ofReal]; ring
  exact_mod_cast cast_eq

/-- Removing a runner in `supp r` from a two-relation family leaves the single relation `s|`. -/
theorem subfamily2_single_r {k : ℕ} (u r s : Fin (k + 1) → ℤ)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i)
    (i : Fin (k + 1)) (hri : r i ≠ 0) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i.succAbove j')) = 0 →
      c' = 0 ∨ c' = (fun j' => s (i.succAbove j')) ∨ c' = -(fun j' => s (i.succAbove j')) := by
  intro c' hc' hsum'
  have hsi : s i = 0 := (hdisj i).resolve_left hri
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c'
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  obtain ⟨α, β, hα, hβ, hd⟩ := hchar2 d hmem hsumd
  have hα0 : α = 0 := by
    have hdi := congrFun hd i
    rw [hd_same] at hdi
    rw [hsi, mul_zero, add_zero] at hdi
    rcases mul_eq_zero.mp hdi.symm with h | h
    · exact h
    · exact absurd h hri
  have hdβs : d = fun w => β * s w := by rw [hd, hα0]; funext w; ring
  have hc'βs : c' = fun j' => β * s (i.succAbove j') := by
    funext j'; rw [← hd_succ j', hdβs]
  rcases hβ with h | h | h
  · right; right; funext j'; simp [hc'βs, h]
  · left; funext j'; simp [hc'βs, h]
  · right; left; funext j'; simp [hc'βs, h]

/-- Removing a runner in `supp s` from a two-relation family leaves the single relation `r|`. -/
theorem subfamily2_single_s {k : ℕ} (u r s : Fin (k + 1) → ℤ)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i)
    (i : Fin (k + 1)) (hsi : s i ≠ 0) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i.succAbove j')) = 0 →
      c' = 0 ∨ c' = (fun j' => r (i.succAbove j')) ∨ c' = -(fun j' => r (i.succAbove j')) := by
  intro c' hc' hsum'
  have hri : r i = 0 := (hdisj i).resolve_right hsi
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c'
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  obtain ⟨α, β, hα, hβ, hd⟩ := hchar2 d hmem hsumd
  have hβ0 : β = 0 := by
    have hdi := congrFun hd i
    rw [hd_same] at hdi
    rw [hri, mul_zero, zero_add] at hdi
    rcases mul_eq_zero.mp hdi.symm with h | h
    · exact h
    · exact absurd h hsi
  have hdαr : d = fun w => α * r w := by rw [hd, hβ0]; funext w; ring
  have hc'αr : c' = fun j' => α * r (i.succAbove j') := by
    funext j'; rw [← hd_succ j', hdαr]
  rcases hα with h | h | h
  · right; right; funext j'; simp [hc'αr, h]
  · left; funext j'; simp [hc'αr, h]
  · right; left; funext j'; simp [hc'αr, h]

/-- Removing a runner outside both supports keeps the two-relation structure `(r|, s|)`. -/
theorem subfamily2_two {k : ℕ} (u r s : Fin (k + 1) → ℤ)
    (hchar2 : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i)
    (i : Fin (k + 1)) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i.succAbove j')) = 0 →
      ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
        c' = fun j' => α * r (i.succAbove j') + β * s (i.succAbove j') := by
  intro c' hc' hsum'
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c'
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  obtain ⟨α, β, hα, hβ, hd⟩ := hchar2 d hmem hsumd
  refine ⟨α, β, hα, hβ, ?_⟩
  funext j'
  rw [← hd_succ j', hd]

/-- **First-moment Riesz lower bound.**  For a dissociated `(k+1)`-family, if `δ ≤ 1/2` and the
union-bound budget `(k+1)(1 − cos 2πδ) < 1` holds, then `ML(v) ≥ δ`.  The weight `R` is the
Riesz product; on the bad set for runner `i` its `i`-factor is at most `1 − cos 2πδ`, and the
subfamily mass caps the rest at `Q`, so the bad grid points carry `< Q` of the total weight `Q`
— some grid point escapes every runner. -/
theorem riesz_lower_bound {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : StrongFree v)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hcond : ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) < 1) :
    δ ≤ ML v := by
  set Q : ℕ := (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (v i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hmass : ∑ j ∈ Finset.range Q, R j = (Q : ℝ) := riesz_mass_real (k + 1) v hv Q hQ0 hQsum
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  -- per-runner bound
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * (Q : ℝ) := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hv'sum : (∑ j', (v' j').natAbs) < Q := by
      have hle : (∑ j', (v' j').natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    have hsubmass : ∑ j ∈ Finset.range Q,
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
      riesz_mass_real k v' (strongFree_succAbove v hv i) Q hQ0 hv'sum
    have hsubnn : ∀ j, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        = ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          Finset.sum_congr rfl (fun j _ => hRsplit j)
      _ ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * δ))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
          rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
              = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
          have hcosle : Real.cos (2 * π * δ)
              ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
            Real.cos_le_cos_of_nonneg_of_le_pi
              (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
              (by nlinarith [Real.pi_pos, hδ2])
              (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
          linarith
      _ = (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ Finset.range Q,
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcosδ
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hsubnn j)
      _ = (1 - Real.cos (2 * π * δ)) * (Q : ℝ) := by rw [hsubmass]
  -- a good grid point exists
  have hgood : ∃ j ∈ Finset.range Q, ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hcover : ∑ j ∈ Finset.range Q, R j
        ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := by
      have hrw : (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          = ∑ j ∈ Finset.range Q, ∑ i : Fin (k + 1),
              (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
        simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      rw [hrw]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨i, hi⟩ := hcon j hj
      calc R j = (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
              rw [if_pos hi]
        _ ≤ ∑ i' : Fin (k + 1),
              (if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
            refine Finset.single_le_sum
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : (Q : ℝ) ≤ ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) * (Q : ℝ) := by
      calc (Q : ℝ) = ∑ j ∈ Finset.range Q, R j := hmass.symm
        _ ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := hcover
        _ ≤ ∑ _i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * (Q : ℝ) :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) * (Q : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
    nlinarith [hfinal, mul_lt_mul_of_pos_right hcond hQR]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

/-- **Explicit Riesz lower bound, closed form.**  Every dissociated `(k+1)`-family satisfies
`ML(v) ≥ 1/(π√(2(k+1)))` — Bedert's `ML ≫ 1/√m` (Lemma 4.1) with the explicit constant
`1/(π√2) ≈ 0.2251`, obtained by optimizing `δ` in `riesz_lower_bound` and bounding
`1 − cos 2πδ = 2sin²(πδ) < 2(πδ)²`. -/
theorem riesz_ML_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : StrongFree v) :
    1 / (π * Real.sqrt (2 * ((k : ℝ) + 1))) ≤ ML v := by
  have hkR : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * ((k : ℝ) + 1)) := Real.sqrt_pos.mpr hkR
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (2 * ((k : ℝ) + 1)) := by
    have h12 : (1 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (2 * ((k : ℝ) + 1)) := Real.sqrt_le_sqrt h12
  have hprod : (2 : ℝ) ≤ π * Real.sqrt (2 * ((k : ℝ) + 1)) := by
    nlinarith [Real.two_le_pi, hsqrt1]
  set δ : ℝ := 1 / (π * Real.sqrt (2 * ((k : ℝ) + 1))) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos one_pos (mul_pos Real.pi_pos hsqrt)
  have hπδeq : π * δ = 1 / Real.sqrt (2 * ((k : ℝ) + 1)) := by
    rw [hδdef]; field_simp
  have hδsq : (π * δ) ^ 2 = 1 / (2 * ((k : ℝ) + 1)) := by
    rw [hπδeq, div_pow, one_pow, Real.sq_sqrt hkR.le]
  have hπδpos : 0 < π * δ := by rw [hπδeq]; exact div_pos one_pos hsqrt
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) hprod
  refine riesz_lower_bound v hv δ hδ0 hδ2 ?_
  have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by
    rw [hπδeq]
    calc (1 : ℝ) / Real.sqrt (2 * ((k : ℝ) + 1))
        ≤ 1 / 1 := one_div_le_one_div_of_le one_pos hsqrt1
      _ = 1 := by norm_num
      _ < π := by linarith [Real.two_le_pi]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
  rw [h1mc]
  have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
  calc ((k : ℝ) + 1) * (2 * Real.sin (π * δ) ^ 2)
      < ((k : ℝ) + 1) * (2 * (π * δ) ^ 2) := by
        apply mul_lt_mul_of_pos_left _ (by positivity); linarith [hsq]
    _ = 1 := by rw [hδsq]; field_simp

/-- **Separation floor cleared for large dissociated families.**  For `k ≥ 17` (i.e. `≥ 18`
runners), every dissociated `(k+1)`-family clears the Lonely-Runner floor: `ML(v) ≥ 1/(k+2)`.
This is the concrete payoff of `riesz_ML_lower` — `1/(π√(2(k+1))) ≥ 1/(k+2)` exactly when
`2π²(k+1) ≤ (k+2)²`, which holds for `k ≥ 17` since `π < 3.15`.  So the free half of the summit
is machine-checked, unconditionally, for all but finitely many sizes. -/
theorem riesz_clears_floor {k : ℕ} (hk : 17 ≤ k) (v : Fin (k + 1) → ℤ) (hv : StrongFree v) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  refine le_trans ?_ (riesz_ML_lower v hv)
  have hkR : (17 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hπpos : 0 < π := Real.pi_pos
  have hle : π * Real.sqrt (2 * ((k : ℝ) + 1)) ≤ (k : ℝ) + 2 := by
    have hπ2 : π ^ 2 < 9.9225 := by nlinarith [hπ, hπpos]
    have hsq : (π * Real.sqrt (2 * ((k : ℝ) + 1))) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith [hπ2, hkR,
        mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 17 by linarith) (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
    calc π * Real.sqrt (2 * ((k : ℝ) + 1))
        = Real.sqrt ((π * Real.sqrt (2 * ((k : ℝ) + 1))) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (((k : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (k : ℝ) + 2 := Real.sqrt_sq (by positivity)
  exact one_div_le_one_div_of_le (by positivity) hle

/-- **Generalized first-moment Riesz bound.**  The union bound over the Riesz weight with the
total mass `M = ∑_j R(j)` and sub-family masses `Mᵢ = ∑_j ∏_{w≠i}(…)` supplied as data: if
`(∑ Mᵢ)(1 − cos 2πδ) < M` and `δ ≤ 1/2`, then `ML v ≥ δ`.  This is `riesz_lower_bound` with the
dissociated masses `M = Mᵢ = Q` replaced by arbitrary (relation-carrying) masses — the engine
for the Bridge, where `M = 3Q/4` for a single sum-relation. -/
theorem riesz_union_general {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℝ)
    (hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = M)
    (Mi : Fin (k + 1) → ℝ)
    (hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i)
    (hcond : (∑ i, Mi i) * (1 - Real.cos (2 * π * δ)) < M) :
    δ ≤ ML v := by
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * Mi i := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hsubnn : ∀ j, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        = ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          Finset.sum_congr rfl (fun j _ => hRsplit j)
      _ ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * δ))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
          rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
              = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
          have hcosle : Real.cos (2 * π * δ)
              ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
            Real.cos_le_cos_of_nonneg_of_le_pi
              (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
              (by nlinarith [Real.pi_pos, hδ2])
              (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
          linarith
      _ = (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ Finset.range Q,
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcosδ
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hsubnn j)
      _ = (1 - Real.cos (2 * π * δ)) * Mi i := by rw [hsubmass i]
  have hgood : ∃ j ∈ Finset.range Q, ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hcover : ∑ j ∈ Finset.range Q, R j
        ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := by
      have hrw : (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          = ∑ j ∈ Finset.range Q, ∑ i : Fin (k + 1),
              (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
        simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      rw [hrw]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨i, hi⟩ := hcon j hj
      calc R j = (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
              rw [if_pos hi]
        _ ≤ ∑ i' : Fin (k + 1),
              (if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
            refine Finset.single_le_sum
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : M ≤ (∑ i, Mi i) * (1 - Real.cos (2 * π * δ)) := by
      calc M = ∑ j ∈ Finset.range Q, R j := hmass.symm
        _ ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := hcover
        _ ≤ ∑ i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * Mi i :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = (∑ i, Mi i) * (1 - Real.cos (2 * π * δ)) := by
            rw [← Finset.mul_sum]; ring
    linarith [hfinal, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i


set_option maxHeartbeats 1000000 in
/-- **The Bridge, single-relation slice** (any odd support).  A `(k+1)`-runner tuple whose only
vanishing `{−1,0,1}`-combinations are `{0, ±r}` with `r` a relation of **odd** support `s ≥ 3`
(the support-`3` case `u_a + u_b = u_c` and every longer odd `±1` relation) satisfies the
Lonely-Runner bound `ML u ≥ 1/(k+2)` for every `k ≥ 18`.  The relation-carrying analogue of
`riesz_clears_floor`: the Riesz weight survives one relation (mass `M = Q(1 + 2(−½)^s) > 0`), and
the sub-family masses satisfy `∑ Mᵢ ≤ (k+2)·M` — the key inequality being `2(s+1) ≤ 2^s`, so
`s·Q ≤ (s+1)·M` — hence the first-moment bound clears the floor with the same arithmetic as the
support-`3` case.  This greens the **entire** large-`dim₂` (single-relation) side of the Bridge. -/
theorem bridge_single_relation {k s : ℕ} (hk : 18 ≤ k) (hs : 3 ≤ s) (hodd : Odd s)
    (u : Fin (k + 1) → ℤ)
    (r : Fin (k + 1) → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * u i) = 0)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (hsupp : (Finset.univ.filter (fun i => r i ≠ 0)).card = s) :
    1 / ((k : ℝ) + 2) ≤ ML u := by
  set Q : ℕ := (∑ i, (u i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (u i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the mass product and total mass
  have hP : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) = (-1 / 2 : ℝ) ^ s := by
    have hthis : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => r i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _; by_cases h : r i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp]
  set M : ℝ := (Q : ℝ) * (1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) with hMdef
  -- odd support ⇒ `(−1/2)^s = −(1/2)^s`, bounded in `[−1/8, 0)`, so `M ≥ 3Q/4 > 0`
  have hpowbnd : (-1 / 4 : ℝ) ≤ 2 * (-1 / 2 : ℝ) ^ s := by
    have habs : |(-1 / 2 : ℝ) ^ s| ≤ (1 / 2) ^ 3 := by
      rw [abs_pow, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    have h8 : ((1 : ℝ) / 2) ^ 3 = 1 / 8 := by norm_num
    rw [h8] at habs
    have := (abs_le.mp habs).1
    linarith
  have hM0 : 0 < M := by
    rw [hMdef, hP]
    have h34 : (3 : ℝ) / 4 ≤ 1 + 2 * (-1 / 2 : ℝ) ^ s := by linarith [hpowbnd]
    nlinarith [hQR, h34]
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_single_relation_real (k + 1) u Q hQ0 hQsum r hr0 hrmem hrel hchar
  -- sub-family masses:  Mᵢ = M if r_i = 0, else Q
  set Mi : Fin (k + 1) → ℝ := fun i => if r i = 0 then M else (Q : ℝ) with hMidef
  have hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (u (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i := by
    intro i
    have hv'sum : (∑ j', (u (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (u (i.succAbove j')).natAbs) ≤ ∑ w, (u w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (u w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    simp only [hMidef]
    by_cases hri : r i = 0
    · rw [if_pos hri]
      have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
        intro hr'
        apply hr0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hri
        · exact congrFun hr' j'
      have hrel' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
        rw [hri, zero_mul, zero_add] at h
        rw [← h]; exact hrel
      rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrel'
        (subfamily_hchar u r hchar i hri)]
      rw [hMdef]
      congr 2
      rw [Fin.prod_univ_succAbove (fun w => (if r w = 0 then (1 : ℝ) else -1 / 2)) i, if_pos hri,
        one_mul]
    · rw [if_neg hri]
      exact riesz_mass_real k (fun j' => u (i.succAbove j'))
        (subfamily_strongFree u r hchar i hri) Q hQ0 hv'sum
  -- key exponential lever:  `2(n+1) ≤ 2ⁿ` for `n ≥ 3`
  have hnat : ∀ n, 3 ≤ n → 2 * (n + 1) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega
  -- `s·Q ≤ (s+1)·M`, the single-relation budget identity generalized to odd support `s`
  have hsQM : (s : ℝ) * (Q : ℝ) ≤ ((s : ℝ) + 1) * M := by
    rw [hMdef, hP]
    have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow hodd _
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have hnatR : (2 : ℝ) * ((s : ℝ) + 1) ≤ (2 : ℝ) ^ s := by exact_mod_cast hnat s hs
    have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by rw [div_pow, one_pow]
    have hfrac : ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s)) ≤ 1 := by
      rw [show ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s)) = (2 * ((s : ℝ) + 1)) / (2 : ℝ) ^ s by ring,
        div_le_one hpos]
      exact hnatR
    rw [hop, hhalf]
    nlinarith [hfrac, hQR]
  -- ∑ Mᵢ = ↑(k+1−s)·M + ↑s·Q ≤ (k+2)·M
  have hsumMi : (∑ i, Mi i) ≤ ((k : ℝ) + 2) * M := by
    have hcard2 : (Finset.univ.filter (fun i => r i = 0)).card = k + 1 - s := by
      have hc := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hss : (Finset.univ.filter (fun i => ¬ r i = 0)).card = s := hsupp
      omega
    simp only [hMidef]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [hcard2, show (Finset.univ.filter (fun i => ¬ r i = 0)).card = s from hsupp]
    have hsk1 : s ≤ k + 1 := by
      rw [← hsupp]
      calc (Finset.univ.filter (fun i => r i ≠ 0)).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k + 1 := by simp [Finset.card_univ]
    have hks : ((k + 1 - s : ℕ) : ℝ) = (k : ℝ) + 1 - (s : ℝ) := by
      rw [Nat.cast_sub hsk1]; push_cast; ring
    rw [hks]
    nlinarith [hsQM, hM0]
  -- the escape parameter δ = 1/(π√(2(k+2)))
  have hkR2 : (0 : ℝ) < 2 * ((k : ℝ) + 2) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * ((k : ℝ) + 2)) := Real.sqrt_pos.mpr hkR2
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (2 * ((k : ℝ) + 2)) := by
    have h12 : (1 : ℝ) ≤ 2 * ((k : ℝ) + 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (2 * ((k : ℝ) + 2)) := Real.sqrt_le_sqrt h12
  set δ : ℝ := 1 / (π * Real.sqrt (2 * ((k : ℝ) + 2))) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos one_pos (mul_pos Real.pi_pos hsqrt)
  have hπδeq : π * δ = 1 / Real.sqrt (2 * ((k : ℝ) + 2)) := by rw [hδdef]; field_simp
  have hδsq : (π * δ) ^ 2 = 1 / (2 * ((k : ℝ) + 2)) := by
    rw [hπδeq, div_pow, one_pow, Real.sq_sqrt hkR2.le]
  have hπδpos : 0 < π * δ := by rw [hπδeq]; exact div_pos one_pos hsqrt
  have hkRb : (18 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [Real.two_le_pi, hsqrt1])
  -- the budget (k+2)(1 − cos 2πδ) < 1
  have hkey : ((k : ℝ) + 2) * (1 - Real.cos (2 * π * δ)) < 1 := by
    have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
    have hπδltpi : π * δ < π := by
      rw [hπδeq]
      calc (1 : ℝ) / Real.sqrt (2 * ((k : ℝ) + 2)) ≤ 1 / 1 :=
            one_div_le_one_div_of_le one_pos hsqrt1
        _ = 1 := by norm_num
        _ < π := by linarith [Real.two_le_pi]
    have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
    have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
      have hpy := Real.sin_sq_add_cos_sq (π * δ)
      rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
    calc ((k : ℝ) + 2) * (2 * Real.sin (π * δ) ^ 2)
        < ((k : ℝ) + 2) * (2 * (π * δ) ^ 2) := by
          apply mul_lt_mul_of_pos_left _ (by positivity); linarith [hsq]
      _ = 1 := by rw [hδsq]; field_simp
  have hcond : (∑ i, Mi i) * (1 - Real.cos (2 * π * δ)) < M := by
    have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
      have := Real.cos_le_one (2 * π * δ); linarith
    calc (∑ i, Mi i) * (1 - Real.cos (2 * π * δ))
        ≤ ((k : ℝ) + 2) * M * (1 - Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right hsumMi hcosnn
      _ < M := by nlinarith [mul_lt_mul_of_pos_left hkey hM0]
  -- clear the floor
  refine le_trans ?_ (riesz_union_general u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass hcond)
  rw [hδdef]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsq : (π * Real.sqrt (2 * ((k : ℝ) + 2))) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hπ2, hkRb]
  calc π * Real.sqrt (2 * ((k : ℝ) + 2))
      = Real.sqrt ((π * Real.sqrt (2 * ((k : ℝ) + 2))) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (((k : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (k : ℝ) + 2 := Real.sqrt_sq (by positivity)

set_option maxHeartbeats 1000000 in
/-- **The Bridge, two-relation slice** (`dim₂ = m − 2`).  A `(k+1)`-runner tuple carrying **two
disjoint-support** support-`3` relations `r, s` — whose only vanishing `{−1,0,1}`-combinations are
the nine `α r + β s` (`α,β ∈ {−1,0,1}`) — satisfies `ML u ≥ 1/(k+2)` for `k ≥ 19`.  The Riesz mass
is `M = 9Q/16` (`riesz_mass_two_relations_real`); removing a runner leaves a single relation
(mass `3Q/4`) inside either support, or the full two-relation family (mass `M`) outside both, so
`∑ Mᵢ = (k+3)·M` and the first-moment bound clears the floor.  This greens the small-`dim₂`
frontier one rung below the single-relation slice. -/
theorem bridge_two_relations {k : ℕ} (hk : 19 ≤ k) (u : Fin (k + 1) → ℤ)
    (r s : Fin (k + 1) → ℤ) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1)
    (hsmem : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hrel_r : (∑ i, r i * u i) = 0) (hrel_s : (∑ i, s i * u i) = 0)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i)
    (hsupp_r : (Finset.univ.filter (fun i => r i ≠ 0)).card = 3)
    (hsupp_s : (Finset.univ.filter (fun i => s i ≠ 0)).card = 3) :
    1 / ((k : ℝ) + 2) ≤ ML u := by
  set Q : ℕ := (∑ i, (u i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (u i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the two mass products are each `-1/8` (support `3`), so the mass is `9Q/16`
  have hPr : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) = -1 / 8 := by
    have hthis : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => r i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]; apply Finset.prod_congr rfl
      intro i _; by_cases h : r i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp_r]; norm_num
  have hPs : (∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2)) = -1 / 8 := by
    have hthis : (∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => s i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]; apply Finset.prod_congr rfl
      intro i _; by_cases h : s i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp_s]; norm_num
  set M : ℝ := (Q : ℝ) * ((1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
                        * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))) with hMdef
  have hMval : M = (Q : ℝ) * 9 / 16 := by rw [hMdef, hPr, hPs]; ring
  have hM0 : 0 < M := by rw [hMval]; positivity
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_two_relations_real (k + 1) u Q hQ0 hQsum r s hr0 hs0 hrmem hsmem hrel_r hrel_s
      hdisj hchar2
  -- Mᵢ = M outside both supports, else 3Q/4
  set Mi : Fin (k + 1) → ℝ := fun i => if r i = 0 ∧ s i = 0 then M else (Q : ℝ) * 3 / 4 with hMidef
  have hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (u (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i := by
    intro i
    have hv'sum : (∑ j', (u (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (u (i.succAbove j')).natAbs) ≤ ∑ w, (u w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (u w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    simp only [hMidef]
    by_cases hboth : r i = 0 ∧ s i = 0
    · rw [if_pos hboth]
      obtain ⟨hri, hsi⟩ := hboth
      have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
        intro hcon; apply hr0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hri
        · exact congrFun hcon j'
      have hs'0 : (fun j' => s (i.succAbove j')) ≠ 0 := by
        intro hcon; apply hs0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hsi
        · exact congrFun hcon j'
      have hrelr' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
        rw [hri, zero_mul, zero_add] at h; rw [← h]; exact hrel_r
      have hrels' : (∑ j', s (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => s w * u w) i
        rw [hsi, zero_mul, zero_add] at h; rw [← h]; exact hrel_s
      rw [riesz_mass_two_relations_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) (fun j' => s (i.succAbove j')) hr'0 hs'0
        (fun j' => hrmem _) (fun j' => hsmem _) hrelr' hrels' (fun j' => hdisj _)
        (subfamily2_two u r s hchar2 i)]
      have hPr_sub : (∏ j', (if r (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
          = ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) := by
        rw [Fin.prod_univ_succAbove (fun w => if r w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hri,
          one_mul]
      have hPs_sub : (∏ j', (if s (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
          = ∏ w, (if s w = 0 then (1 : ℝ) else -1 / 2) := by
        rw [Fin.prod_univ_succAbove (fun w => if s w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hsi,
          one_mul]
      rw [hMdef, hPr_sub, hPs_sub]
    · rw [if_neg hboth]
      by_cases hri : r i = 0
      · -- r_i = 0 and ¬both ⟹ s_i ≠ 0: single relation r|
        have hsi : s i ≠ 0 := fun h => hboth ⟨hri, h⟩
        have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
          intro hcon; apply hr0; funext w
          refine Fin.succAboveCases i ?_ (fun j' => ?_) w
          · exact hri
          · exact congrFun hcon j'
        have hrelr' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
          have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
          rw [hri, zero_mul, zero_add] at h; rw [← h]; exact hrel_r
        rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
          (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrelr'
          (subfamily2_single_s u r s hdisj hchar2 i hsi)]
        have hPr_sub : (∏ j', (if r (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
            = ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) := by
          rw [Fin.prod_univ_succAbove (fun w => if r w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hri,
            one_mul]
        rw [hPr_sub, hPr]; ring
      · -- r_i ≠ 0 (⟹ s_i = 0): single relation s|
        have hsi : s i = 0 := (hdisj i).resolve_left hri
        have hs'0 : (fun j' => s (i.succAbove j')) ≠ 0 := by
          intro hcon; apply hs0; funext w
          refine Fin.succAboveCases i ?_ (fun j' => ?_) w
          · exact hsi
          · exact congrFun hcon j'
        have hrels' : (∑ j', s (i.succAbove j') * u (i.succAbove j')) = 0 := by
          have h := Fin.sum_univ_succAbove (fun w => s w * u w) i
          rw [hsi, zero_mul, zero_add] at h; rw [← h]; exact hrel_s
        rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
          (fun j' => s (i.succAbove j')) hs'0 (fun j' => hsmem _) hrels'
          (subfamily2_single_r u r s hdisj hchar2 i hri)]
        have hPs_sub : (∏ j', (if s (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
            = ∏ w, (if s w = 0 then (1 : ℝ) else -1 / 2) := by
          rw [Fin.prod_univ_succAbove (fun w => if s w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hsi,
            one_mul]
        rw [hPs_sub, hPs]; ring
  -- ∑ Mᵢ = (k+3)·M:  6 support runners at 3Q/4, the rest at M = 9Q/16
  have hcard_np : (Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0))).card = 6 := by
    have heq : (Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0)))
        = (Finset.univ.filter (fun i => r i ≠ 0)) ∪ (Finset.univ.filter (fun i => s i ≠ 0)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_and_or]
    rw [heq, Finset.card_union_of_disjoint, hsupp_r, hsupp_s]
    rw [Finset.disjoint_left]
    intro i hir his
    rw [Finset.mem_filter] at hir his
    rcases hdisj i with h | h
    · exact hir.2 h
    · exact his.2 h
  have hcard_p : (Finset.univ.filter (fun i => r i = 0 ∧ s i = 0)).card = k - 5 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0 ∧ s i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hsumMi : (∑ i, Mi i) = ((k : ℝ) + 3) * M := by
    simp only [hMidef]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard_p, hcard_np]
    have hk5 : ((k - 5 : ℕ) : ℝ) = (k : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hk5, hMval]; push_cast; ring
  -- escape parameter δ = 1/(π√(2(k+3)))
  have hkR2 : (0 : ℝ) < 2 * ((k : ℝ) + 3) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * ((k : ℝ) + 3)) := Real.sqrt_pos.mpr hkR2
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (2 * ((k : ℝ) + 3)) := by
    have h12 : (1 : ℝ) ≤ 2 * ((k : ℝ) + 3) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (2 * ((k : ℝ) + 3)) := Real.sqrt_le_sqrt h12
  set δ : ℝ := 1 / (π * Real.sqrt (2 * ((k : ℝ) + 3))) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos one_pos (mul_pos Real.pi_pos hsqrt)
  have hπδeq : π * δ = 1 / Real.sqrt (2 * ((k : ℝ) + 3)) := by rw [hδdef]; field_simp
  have hδsq : (π * δ) ^ 2 = 1 / (2 * ((k : ℝ) + 3)) := by
    rw [hπδeq, div_pow, one_pow, Real.sq_sqrt hkR2.le]
  have hπδpos : 0 < π * δ := by rw [hπδeq]; exact div_pos one_pos hsqrt
  have hkRb : (19 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [Real.two_le_pi, hsqrt1])
  have hkey : ((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ)) < 1 := by
    have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
    have hπδltpi : π * δ < π := by
      rw [hπδeq]
      calc (1 : ℝ) / Real.sqrt (2 * ((k : ℝ) + 3)) ≤ 1 / 1 :=
            one_div_le_one_div_of_le one_pos hsqrt1
        _ = 1 := by norm_num
        _ < π := by linarith [Real.two_le_pi]
    have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
    have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
      have hpy := Real.sin_sq_add_cos_sq (π * δ)
      rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
    calc ((k : ℝ) + 3) * (2 * Real.sin (π * δ) ^ 2)
        < ((k : ℝ) + 3) * (2 * (π * δ) ^ 2) := by
          apply mul_lt_mul_of_pos_left _ (by positivity); linarith [hsq]
      _ = 1 := by rw [hδsq]; field_simp
  have hcond : (∑ i, Mi i) * (1 - Real.cos (2 * π * δ)) < M := by
    have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
      have := Real.cos_le_one (2 * π * δ); linarith
    calc (∑ i, Mi i) * (1 - Real.cos (2 * π * δ))
        ≤ ((k : ℝ) + 3) * M * (1 - Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right hsumMi.le hcosnn
      _ < M := by nlinarith [mul_lt_mul_of_pos_left hkey hM0]
  refine le_trans ?_ (riesz_union_general u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass hcond)
  rw [hδdef]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsq : (π * Real.sqrt (2 * ((k : ℝ) + 3))) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hπ2, hkRb]
  calc π * Real.sqrt (2 * ((k : ℝ) + 3))
      = Real.sqrt ((π * Real.sqrt (2 * ((k : ℝ) + 3))) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (((k : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (k : ℝ) + 2 := Real.sqrt_sq (by positivity)

end LRSpectrumFull

-- axiom audit
#print axioms LRSpectrumFull.riesz_mass_real
#print axioms LRSpectrumFull.cos_two_pi_nid
#print axioms LRSpectrumFull.strongFree_succAbove
#print axioms LRSpectrumFull.riesz_lower_bound
#print axioms LRSpectrumFull.riesz_ML_lower
#print axioms LRSpectrumFull.riesz_clears_floor
#print axioms LRSpectrumFull.riesz_union_general
#print axioms LRSpectrumFull.riesz_mass_single_relation_real
#print axioms LRSpectrumFull.subfamily_strongFree
#print axioms LRSpectrumFull.subfamily_hchar
#print axioms LRSpectrumFull.bridge_single_relation
#print axioms LRSpectrumFull.bridge_two_relations
#print axioms LRSpectrumFull.riesz_mass_two_relations_real
