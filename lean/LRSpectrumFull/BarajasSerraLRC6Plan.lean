import LRSpectrumFull.BarajasSerraLRC6
import LRSpectrumFull.EightPlan

/-!
# E6 session 20: the `EightPlan.LRC6` hypothesis discharged by `Sec5.lrc6`

Only the definition `EightPlan.LRC6` is used; nothing else of `EightPlan` enters the proof.
-/

namespace LRSpectrumFull.BarajasSerra

/-- **E6 discharged.** -/
theorem LRC6_barajasSerra : EightPlan.LRC6 := by
  intro u hu
  have h := Sec5.lrc6 u hu
  have e : (1 : ℝ) / ((5 : ℝ) + 2) = 1 / 7 := by norm_num
  rw [e]; exact h

end LRSpectrumFull.BarajasSerra
