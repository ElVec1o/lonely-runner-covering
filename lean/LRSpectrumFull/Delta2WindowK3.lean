/-
# The `k = 3` rung of the StrongFree window is a theorem

The Lonely Runner Conjecture for five runners (four positive velocities, floor `1/5`) is a classical
result (1984), and it is *fully formalized* in this project as `ML_ge_fifth_four` (the machine-checked
Barajas–Serra Prime Filtering argument at `p = 5`, `five_runners` → `ML` form, axiom-clean,
`0 sorry`). It holds for *every* positive four-velocity family, with no freeness, distinctness, or
relation hypothesis.

Consequently the `k = 3` rung of the atom `StrongFreeWindowTiny` is not a hypothesis but a theorem,
and the atom's remaining content is only `k = 4, 5, 6`. This file records that reduction.
-/
import LRSpectrumFull.Delta2WindowClosed
import LRSpectrumFull.Delta2SeparationWindow

namespace LRSpectrumFull

/-- The StrongFree window with the (now-discharged) `k = 3` rung removed: only `k = 4, 5, 6`. -/
def StrongFreeWindow456 : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 6 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- **The `k = 3` rung of `StrongFreeWindowTiny` is unconditional.**  It follows from the verified
five-runner theorem `ML_ge_fifth_four`; the atom `StrongFreeWindowTiny` therefore reduces to its
`k = 4, 5, 6` part (`StrongFreeWindow456`). -/
theorem strongFreeWindowTiny_of_456 (h : StrongFreeWindow456) : StrongFreeWindowTiny := by
  intro k hk3 hk6 v hv hSF
  interval_cases k
  · exact le_of_eq_of_le (by norm_num) (ML_ge_fifth_four v hv)
  · exact h 4 (by norm_num) (by norm_num) v hv hSF
  · exact h 5 (by norm_num) (by norm_num) v hv hSF
  · exact h 6 (by norm_num) (by norm_num) v hv hSF

end LRSpectrumFull
