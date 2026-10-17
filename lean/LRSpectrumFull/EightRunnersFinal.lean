import LRSpectrumFull.EightMSSImport
import LRSpectrumFull.EightCert27
import LRSpectrumFull.BarajasSerraLRC6Plan
import LRSpectrumFull.EightE5

/-!
# Eight runners: assembled chain with LRC6 proved in-project

SUPERSEDED (2026-09-27) by `LRSpectrumFull.EightRunners.eight_runners_unconditional`
(module `EightRunners`, which does not import `EightMSSImport` or `Chen7RunnerImport`).
Kept as a record; `eight_runners` below still uses the MSS axiom.

`LRC6` (seven runners) is supplied by `BarajasSerra.LRC6_barajasSerra`, a kernel-checked
formalization of Barajas-Serra (2008); the external axiom `Chen7RunnerImport.chen_lrc7_int`
is no longer used. The per-prime Lemma 7 checks come from `EightCert27.hchk_all`
(27 axioms, each a compaction of a kernel check we ran, with SHA256-recorded certificates).
The remaining external input is `EightMSSImport.mss_theorem_A_n7` (Malikiosis-Santos-Schymura,
Theorem A'), used for the height bound (E5).
-/

namespace LRSpectrumFull.EightRunnersFinal

open LRSpectrumFull

/-- LRC for eight runners (seven positive integer speeds, target gap 1/8). -/
theorem eight_runners (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  EightMSSImport.eight_runners_mss BarajasSerra.LRC6_barajasSerra EightCert27.hchk_all v hv

/-- LRC for eight runners without the MSS axiom: E5 is `EightE5.mssGap7_holds` (planar rounding
step, Giri-Kravitz section 7) composed with the VERIFIED staircase `EightMSS.e5b_staircase`.
Axioms: standard plus the 27 `EightCert27` compacted kernel checks. -/
theorem eight_runners_unconditional (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  EightE5.eight_runners_unconditional v hv

end LRSpectrumFull.EightRunnersFinal
