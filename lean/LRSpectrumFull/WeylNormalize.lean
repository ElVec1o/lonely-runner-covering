/-
# W(B₄) normalization via the dominant Weyl chamber (toward F.3.2 / the kernel bound)

CROSS-FIELD KEY (Lie theory): the row symmetry of the JK24 reduction is the Weyl
group W(B_n) of the B_n root system. Every W(B_n)-orbit has a UNIQUE representative
in the *dominant Weyl chamber* `x₁ ≥ x₂ ≥ … ≥ xₙ ≥ 0` — i.e. "sort by absolute
value, make non-negative". This is a solved problem in Lie theory; concretely it is
the sign+sort normalization that drops `jkForm_bounded`'s hypotheses.

This file does the sign half: `D` is invariant under componentwise absolute value
(the `(ℤ/2)ⁿ` part of W(B_n)). No `sorry`.
-/
import LRSpectrumFull.DSignFlip
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull

theorem D_flip0 (a b c : ℤ) : D ![-a, b, c] = D ![a, b, c] := by
  have h := D_sign_flip ![a, b, c] 0; simpa using h

theorem D_flip1 (a b c : ℤ) : D ![a, -b, c] = D ![a, b, c] := by
  have h := D_sign_flip ![a, b, c] 1; simpa using h

theorem D_flip2 (a b c : ℤ) : D ![a, b, -c] = D ![a, b, c] := by
  have h := D_sign_flip ![a, b, c] 2; simpa using h

/-- **Sign normalization (the `(ℤ/2)³` part of W(B₃)).** `D` is invariant under
componentwise absolute value. -/
theorem D_abs3 (a b c : ℤ) : D ![|a|, |b|, |c|] = D ![a, b, c] := by
  rcases abs_choice a with ha | ha <;> rcases abs_choice b with hb | hb <;>
    rcases abs_choice c with hc | hc <;> rw [ha, hb, hc] <;>
    simp only [D_flip0, D_flip1, D_flip2]

end LRSpectrumFull
