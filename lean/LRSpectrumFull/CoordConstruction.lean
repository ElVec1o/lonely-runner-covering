/-
# Milestone 52: the pair-sum construction (toward proving the ML inequality)

The breakthrough reduction of Piece A (M51) leaves one inequality to prove:
`ML(p,q,r) ≥ 1/3 − 3/(4·sum)`. The constructive lead, verified for all 997
triples checked: **at the parameter `t = k/(p+r)`, runners `p` and `r` have
equal distance** to the integers, because

    r·t = k − p·t   (since r = (p+r) − p, so r·k/(p+r) = k − p·k/(p+r)),

and `‖k − x‖ = ‖x‖`. This collapses the 3-runner gap to a **2-runner**
quantity (the pair `(p,q)` at modulus `p+r`), the engine of the eventual
proof.

This file formalizes that tool: `nid_runner_swap` (the runner coincidence)
and `ML_ge_at_pairsum` — if at some pair-sum point both the `p`- and
`q`-runners are `≥ c`, then `ML ≥ c`. Supplying a good `k` (so both are near
`1/3`) is the remaining step. No `sorry`.
-/

import LRSpectrumFull.DValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- **Runner coincidence at the pair-sum point.** At `t = k/(p+r)`, the
`r`-runner and the `p`-runner are equidistant from the integers. -/
theorem nid_runner_swap (p r k : ℤ) (hpr : ((p + r : ℤ) : ℝ) ≠ 0) :
    nearestIntDist ((r : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
      = nearestIntDist ((p : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ))) := by
  have e : (r : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ))
      = -((p : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ))) + ((k : ℤ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [e, nearestIntDist_add_int, nearestIntDist_neg]

/-- **The pair-sum construction.** If at the parameter `t = k/(p+r)` both the
`p`-runner and the `q`-runner are at distance `≥ c` from the integers, then
`ML(p,q,r) ≥ c`. (The `r`-runner is automatically `≥ c` by `nid_runner_swap`,
so all three runners clear `c` and the gap — hence `ML` — does too.) -/
theorem ML_ge_at_pairsum (p q r k : ℤ) (c : ℝ) (hpr : ((p + r : ℤ) : ℝ) ≠ 0)
    (hp : c ≤ nearestIntDist ((p : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ))))
    (hq : c ≤ nearestIntDist ((q : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))) :
    c ≤ ML ![p, q, r] := by
  refine le_trans ?_ (gap_le_ML ![p, q, r] ((k : ℝ) / ((p + r : ℤ) : ℝ)))
  apply le_gap
  intro i
  fin_cases i
  · show c ≤ nearestIntDist ((![p, q, r] 0 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    simpa using hp
  · show c ≤ nearestIntDist ((![p, q, r] 1 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    simpa using hq
  · show c ≤ nearestIntDist ((![p, q, r] 2 : ℝ) * ((k : ℝ) / ((p + r : ℤ) : ℝ)))
    rw [show ((![p, q, r] 2 : ℤ) : ℝ) = (r : ℝ) by simp, nid_runner_swap p r k hpr]
    exact hp

end LRSpectrumFull
