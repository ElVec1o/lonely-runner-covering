/-
# NF-existence: the elementary reduction to the JK24 normal form

The keystone of the CASE route (JK24 §3.3). Every 4×2 integer runner matrix `M`
whose first two runners have a nonzero `2×2` minor is `mD`-equal to an explicit
`jkForm a b c d e f`. The reduction is the elementary integer basis change of
JK24 (line 850 of arXiv:2411.12684):

    u' = (v₁−v₀)u + (u₀−u₁)v,   v' = (−v₁−v₀)u + (u₀+u₁)v

which makes `u'₀ = u'₁` and `v'₀ = −v'₁` (the `(a,a,·)/(d,−d,·)` shape), with
change-of-basis determinant `2·m₀₁ ≠ 0`. Since the basis change is a real
reparametrization of the rank-2 torus parameter, `mD` is invariant under it
(`mD_reparam`). No covering, no over-determination: this is pure linear algebra.

This replaces the WALL-route assumption `allShapedMinorBound` on the critical
path with an elementary, sorry-free lemma. No `sorry`.
-/
import LRSpectrumFull.Subtorus
import LRSpectrumFull.SubtorusMono
import LRSpectrumFull.NormalForm

namespace LRSpectrumFull
open Finset

/-- A `2×2` integer basis change applied to the two columns of a `4×2` runner
matrix: `(colMul M g) i c = ∑ₛ M i s · g s c`. -/
def colMul (M : Fin 4 → Fin 2 → ℤ) (g : Fin 2 → Fin 2 → ℤ) : Fin 4 → Fin 2 → ℤ :=
  fun i c => M i 0 * g 0 c + M i 1 * g 1 c

/-- Forward map `t ↦ g·t` of the reparametrization. -/
def colMap (g : Fin 2 → Fin 2 → ℝ) (t : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![g 0 0 * t 0 + g 0 1 * t 1, g 1 0 * t 0 + g 1 1 * t 1]

/-- Inverse map of the reparametrization (the `2×2` Cramer inverse). -/
noncomputable def colMapInv (g : Fin 2 → Fin 2 → ℝ) (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(g 1 1 * s 0 - g 0 1 * s 1) / (g 0 0 * g 1 1 - g 0 1 * g 1 0),
    (-(g 1 0) * s 0 + g 0 0 * s 1) / (g 0 0 * g 1 1 - g 0 1 * g 1 0)]

/-- The real reparametrization `t ↦ g·t` as an equivalence, when `det g ≠ 0`. -/
noncomputable def colEquiv (g : Fin 2 → Fin 2 → ℝ)
    (hΔ : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0) : (Fin 2 → ℝ) ≃ (Fin 2 → ℝ) where
  toFun := colMap g
  invFun := colMapInv g
  left_inv t := by
    funext i
    fin_cases i <;>
      simp only [colMap, colMapInv, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] <;>
      rw [div_eq_iff hΔ] <;> ring
  right_inv s := by
    funext i
    fin_cases i <;>
      simp only [colMap, colMapInv, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, ← mul_div_assoc] <;>
      rw [← add_div, div_eq_iff hΔ] <;> ring

/-- The reparametrization identity: the gap of the basis-changed matrix at `t`
equals the gap of the original matrix at `g·t`. -/
theorem mgap_colMul (M : Fin 4 → Fin 2 → ℤ) (g : Fin 2 → Fin 2 → ℤ)
    (hΔ : (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 ≠ 0) (t : Fin 2 → ℝ) :
    mgap (colMul M g) t = mgap M (colEquiv (fun s c => (g s c : ℝ)) hΔ t) := by
  unfold mgap
  congr 1
  funext i
  congr 1
  simp only [Fin.sum_univ_two, colMul, colEquiv, colMap, Equiv.coe_fn_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

/-- `mD` is invariant under an integer basis change of the rank-2 columns with
nonzero determinant (the real plane — hence the subtorus — is unchanged). -/
theorem mD_colMul (M : Fin 4 → Fin 2 → ℤ) (g : Fin 2 → Fin 2 → ℤ)
    (hΔ : (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 ≠ 0) :
    mD (colMul M g) = mD M :=
  mD_reparam M (colMul M g) (colEquiv (fun s c => (g s c : ℝ)) hΔ)
    (fun t => mgap_colMul M g hΔ t)

/-- The explicit JK24 normal-form basis change for the `(0,1)` runner pair. -/
def gNF (M : Fin 4 → Fin 2 → ℤ) : Fin 2 → Fin 2 → ℤ :=
  ![![M 1 1 - M 0 1, -M 1 1 - M 0 1], ![M 0 0 - M 1 0, M 0 0 + M 1 0]]

/-- The basis change lands exactly in `jkForm`, with `a = m₀₁`, `d = −m₀₁`. -/
theorem colMul_gNF_eq_jkForm (M : Fin 4 → Fin 2 → ℤ) :
    colMul M (gNF M) =
      jkForm (M 0 0 * M 1 1 - M 1 0 * M 0 1)
        (M 2 0 * (M 1 1 - M 0 1) + M 2 1 * (M 0 0 - M 1 0))
        (M 3 0 * (M 1 1 - M 0 1) + M 3 1 * (M 0 0 - M 1 0))
        (-(M 0 0 * M 1 1 - M 1 0 * M 0 1))
        (M 2 0 * (-M 1 1 - M 0 1) + M 2 1 * (M 0 0 + M 1 0))
        (M 3 0 * (-M 1 1 - M 0 1) + M 3 1 * (M 0 0 + M 1 0)) := by
  funext i c
  have e0 : (⟨0, by omega⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨1, by omega⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨2, by omega⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨3, by omega⟩ : Fin 4) = 3 := by decide
  have c0 : (⟨0, by omega⟩ : Fin 2) = 0 := by decide
  have c1 : (⟨1, by omega⟩ : Fin 2) = 1 := by decide
  fin_cases i <;> fin_cases c <;>
    simp only [colMul, gNF, jkForm, e0, e1, e2, e3, c0, c1, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;>
    ring

/-- **NF-existence (keystone).** If the first two runners of `M` have a nonzero
`2×2` minor, then `M` is `mD`-equal to an explicit `jkForm`. Elementary: the
JK24 basis change + `mD_reparam`. -/
theorem nf_exists (M : Fin 4 → Fin 2 → ℤ)
    (hm : M 0 0 * M 1 1 - M 1 0 * M 0 1 ≠ 0) :
    ∃ a b c d e f : ℤ, a ≠ 0 ∧ d ≠ 0 ∧ mD M = mD (jkForm a b c d e f) := by
  have hΔ : ((gNF M) 0 0 : ℝ) * (gNF M) 1 1 - (gNF M) 0 1 * (gNF M) 1 0 ≠ 0 := by
    have hd : ((gNF M) 0 0 : ℝ) * (gNF M) 1 1 - (gNF M) 0 1 * (gNF M) 1 0
        = 2 * ((M 0 0 * M 1 1 - M 1 0 * M 0 1 : ℤ) : ℝ) := by
      simp only [gNF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      push_cast; ring
    rw [hd]
    have hm' : ((M 0 0 * M 1 1 - M 1 0 * M 0 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm
    exact mul_ne_zero two_ne_zero hm'
  have key : mD M = mD (jkForm (M 0 0 * M 1 1 - M 1 0 * M 0 1)
      (M 2 0 * (M 1 1 - M 0 1) + M 2 1 * (M 0 0 - M 1 0))
      (M 3 0 * (M 1 1 - M 0 1) + M 3 1 * (M 0 0 - M 1 0))
      (-(M 0 0 * M 1 1 - M 1 0 * M 0 1))
      (M 2 0 * (-M 1 1 - M 0 1) + M 2 1 * (M 0 0 + M 1 0))
      (M 3 0 * (-M 1 1 - M 0 1) + M 3 1 * (M 0 0 + M 1 0))) := by
    rw [← mD_colMul M (gNF M) hΔ, colMul_gNF_eq_jkForm M]
  exact ⟨_, _, _, _, _, _, hm, neg_ne_zero.mpr hm, key⟩

/-- A permutation of `Fin 4` sending `0 ↦ i` and `1 ↦ j`, for distinct `i, j`. -/
theorem exists_perm_01 (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  by_cases hi1 : i = 1
  · subst hi1
    refine ⟨(Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap 0 j), ?_, ?_⟩
    · rw [Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by decide) hij]
    · rw [Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  · refine ⟨(Equiv.swap (0 : Fin 4) i).trans (Equiv.swap 1 j), ?_, ?_⟩
    · rw [Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hi1 hij]
    · rw [Equiv.trans_apply,
        Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hi1),
        Equiv.swap_apply_left]

/-- **NF-existence for any active pair.** If runners `i ≠ j` have a nonzero `2×2`
minor, `M` is `mD`-equal to an explicit `jkForm` (permute `(i,j)` to the `(0,1)`
slot via `mD_perm`, then `nf_exists`). -/
theorem nf_exists_pair (M : Fin 4 → Fin 2 → ℤ) (i j : Fin 4)
    (hm : M i 0 * M j 1 - M j 0 * M i 1 ≠ 0) :
    ∃ a b c d e f : ℤ, a ≠ 0 ∧ d ≠ 0 ∧ mD M = mD (jkForm a b c d e f) := by
  have hij : i ≠ j := by rintro rfl; exact hm (by ring)
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_01 i j hij
  obtain ⟨a, b, c, d, e, f, ha, hd, h⟩ := nf_exists (M ∘ σ) (by
    simp only [Function.comp_apply, hσ0, hσ1]; exact hm)
  exact ⟨a, b, c, d, e, f, ha, hd, (mD_perm M σ).symm.trans h⟩

/-- **NF-existence for any saturated band (general keystone).** A saturated `2`-dim
runner matrix is `mD`-equal to an explicit `jkForm`. Saturation (`gcd` of all minors
`= 1`) forces a nonzero minor; the rest is `nf_exists_pair`. No hyperplane case is
needed — the chosen nonzero minor becomes `a = ±m ≠ 0` in the `jkForm`. -/
theorem nf_exists_sat (M : Fin 4 → Fin 2 → ℤ) (hM : Saturated2 M) :
    ∃ a b c d e f : ℤ, a ≠ 0 ∧ d ≠ 0 ∧ mD M = mD (jkForm a b c d e f) := by
  have hne : ∃ p : Fin 4 × Fin 4, M p.1 0 * M p.2 1 - M p.1 1 * M p.2 0 ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : Finset.gcd (Finset.univ : Finset (Fin 4 × Fin 4))
        (fun p => M p.1 0 * M p.2 1 - M p.1 1 * M p.2 0) = 0 :=
      Finset.gcd_eq_zero_iff.mpr (fun p _ => h p)
    have hM' : Finset.gcd (Finset.univ : Finset (Fin 4 × Fin 4))
        (fun p => M p.1 0 * M p.2 1 - M p.1 1 * M p.2 0) = 1 := hM
    rw [hz] at hM'
    exact one_ne_zero hM'.symm
  obtain ⟨⟨i, j⟩, hp⟩ := hne
  refine nf_exists_pair M i j ?_
  rw [show M i 0 * M j 1 - M j 0 * M i 1 = M i 0 * M j 1 - M i 1 * M j 0 from by ring]
  exact hp

-- axiom audit
#print axioms nf_exists
#print axioms nf_exists_sat
