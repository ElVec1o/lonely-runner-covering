import LRSpectrumFull.EightE5

/-!
# The lonely runner conjecture for eight runners

Main theorem of `paper/eight/main.tex`. The proof is `EightE5.eight_runners_unconditional`:
Rosenfeld's reduction (`EightPlan`), LRC for seven runners after Barajas and Serra
(`BarajasSerra.LRC6_barajasSerra`), the 27 per-prime checks (`EightCert27.hchk_all`), and the
height bound E5 (`EightE5.mssGap7_holds` with `EightMSS.e5b_staircase`).

Axioms: `propext`, `Classical.choice`, `Quot.sound`, and the 27 compacted certificate axioms
`EightCert27.lemma7Check_seven_p<p>_verified`. This module does not import `EightMSSImport`
or `Chen7RunnerImport`; `EightRunnersFinal` is superseded by this module.
-/

namespace LRSpectrumFull.EightRunners

open LRSpectrumFull

/-- LRC for eight runners: seven positive integer speeds have maximal loneliness at least 1/8. -/
theorem eight_runners_unconditional (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  EightE5.eight_runners_unconditional v hv

end LRSpectrumFull.EightRunners
