/-
# Milestone 54: permutation invariance of the D-value

`D` depends only on the multiset of speeds, not their order: `D(v ∘ σ) = D v`
for any permutation `σ`. (Immediate from `mD_col` + `mD_perm`: permuting the
runners is a runner-permutation of the rank-1 subtorus.) This lets the
pair-sum construction (`D_lt_band`) and the relative bound be applied through
*any* of the three pairings of a triple, by reordering — the missing
ingredient for covering `q` above the midpoint. No `sorry`.
-/

import LRSpectrumFull.Coherence
import LRSpectrumFull.SubtorusMono
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull

variable {k : ℕ}

/-- **Permutation invariance.** `D` is unchanged by permuting the speeds. -/
theorem D_perm (v : Fin (k + 1) → ℤ) (σ : Equiv.Perm (Fin (k + 1))) :
    D (v ∘ ⇑σ) = D v := by
  rw [← mD_col (v ∘ ⇑σ), ← mD_col v]
  have h : col (v ∘ ⇑σ) = (col v) ∘ ⇑σ := by funext i; rfl
  rw [h, mD_perm]

/-- Reordering a triple `(p,q,r) ↦ (p,r,q)` preserves `D`. -/
theorem D_swap12 (p q r : ℤ) : D ![p, r, q] = D ![p, q, r] := by
  have : (![p, q, r] : Fin 3 → ℤ) ∘ ⇑(Equiv.swap (1 : Fin 3) 2) = ![p, r, q] := by
    funext i; fin_cases i <;> rfl
  rw [← this, D_perm]

/-- Reordering a triple `(p,q,r) ↦ (q,p,r)` preserves `D`. -/
theorem D_swap01 (p q r : ℤ) : D ![q, p, r] = D ![p, q, r] := by
  have : (![p, q, r] : Fin 3 → ℤ) ∘ ⇑(Equiv.swap (0 : Fin 3) 1) = ![q, p, r] := by
    funext i; fin_cases i <;> rfl
  rw [← this, D_perm]

/-- Reordering a triple `(p,q,r) ↦ (r,q,p)` preserves `D`. -/
theorem D_swap02 (p q r : ℤ) : D ![r, q, p] = D ![p, q, r] := by
  have : (![p, q, r] : Fin 3 → ℤ) ∘ ⇑(Equiv.swap (0 : Fin 3) 2) = ![r, q, p] := by
    funext i; fin_cases i <;> rfl
  rw [← this, D_perm]

end LRSpectrumFull
