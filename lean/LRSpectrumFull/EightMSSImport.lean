/-
# E5: import of the MSS numerical consequence used by `e5_sum`, as an explicit axiom

Same pattern as `Chen7RunnerImport.lean`'s treatment of E6: the paper's result is declared as a
fully cited, standalone AXIOM in exactly the shape our proof needs (not a paraphrase), rather
than vendored or reproved. `bridge31`/`MSSGap7` in `EightMSS.lean` (the from-scratch attempt to
derive this fact inside our scalar-time formalism via zonotopes and successive minima) is
UNTOUCHED by this file and remains its own open item, costed separately in
(development file, not part of this archive) (15-24 sessions) — this file does not attack that route, it
axiomatizes the paper's theorem directly instead, per the task's explicit scope.

EXTERNAL SOURCE (trusted, not re-verified by our kernel):

  Paper    : "The lonely runner conjecture and geometry of numbers" (working/preprint title as
             carried by this project's earlier reading notes; see `EightMSS.lean`'s docstrings
             for the session-by-session reading log of the actual PDF).
  Authors  : Rustam Malikiosis, Francisco Santos, Matthias Schymura.
  arXiv id : 2411.06903 (v2, the version read in this project, per `EightMSS.lean:259-266`).
  Theorem  : **Theorem A'**, their main induction, proved in Section 3 (proof of Theorem 3.1 via
             Prop 3.3/3.4 and Remark 3.5, then Theorem A' itself via Lemma 3.6), as identified and
             read in full in `EightMSS.lean`'s "CHECKED 2026-09-25" docstring (lines 259-274 of
             that file). Theorem A' is the induction step that, given LRC for `n-1` runners,
             proves LRC for `n` runners under a point-count hypothesis on the lonely-runner
             zonotope (`|Z_v ∩ ℤ^{n-1}| > C(n+1,2)^{n-1}`); Rosenfeld's paper (arXiv:2509.14111,
             this project's own Corollary-3 citation for E5, see `EightPlan.lean` line 20/408)
             cites the resulting bound as "MSS Theorem A" applied at `n = 7`. The two names refer
             to the same underlying numerical fact at `n = 7`: Theorem A' is the inductive
             machinery: MSS then also state the un-primed "Theorem A" as its corollary for actual
             LRC (their intro); the induction step at `n = 7` (using `n = 6` LRC as the inductive
             hypothesis, i.e. our `LRC6`) is what supplies exactly the numerical consequence
             `EightPlan.e5_sum_STUB_SUPERSEDED` needs. We cite Theorem A' by name because that is the precise
             component read and pinned down (Section 3 in full, per `EightMSS.lean`'s docstring),
             not the paper's summary Theorem A statement, which is not itself directly usable
             (it is stated for general `n` without our project's explicit `28^6`/`k=7`
             instantiation).

Precision claim (per the task): the axiom below states the *exact* fact `EightPlan.e5_sum_STUB_SUPERSEDED` needs,
transcribed from a full reading of the paper's Section 3 as recorded in `EightMSS.lean`'s
docstrings (not a paraphrase, not a re-derivation). It matches the modulus `l = 28 = C(8,2)`
and the pigeonhole threshold `28^6` used throughout `EightMSS.lean` (`e5b_staircase`,
`MSSGap7`, `e5_sum_of_gap`), themselves already checked there against the paper's
`C(n+1,2)^{n-1}` at `n = 7`.

## Route taken: axiom, not vendoring or from-scratch proof

Formalizing MSS's zonotope/successive-minima apparatus (Def 1.4, Prop 1.5, successive minima,
the projection `T`, Lemma 3.6's pullback) does not exist anywhere in Mathlib
((development file, not part of this archive)'s exhaustion sweep: zero hits for `zonotope` or
`SuccessiveMin` in this project's actual Mathlib checkout) and is estimated at 1450-2650 lines /
15-24 sessions of new machinery (B1-B9 in that plan). That is out of scope for this task, which is
explicitly to package the current result honestly, not to close the gap. We therefore take exactly
the route `Chen7RunnerImport.lean` took for E6: an explicit, cited AXIOM stating the needed
numerical fact, plus a genuinely PROVED (here, essentially immediate) bridge to our own
`EightPlan.e5_sum_STUB_SUPERSEDED` shape.

Honesty (Rule 0): `mss_theorem_A_n7` below is an AXIOM. Nothing in this file's Lean kernel check
verifies the MSS proof; it verifies only that IF the stated consequence of their Theorem A' holds
(as the paper, per the reading recorded in `EightMSS.lean`, establishes) THEN `EightPlan.e5_sum_STUB_SUPERSEDED`'s
exact statement holds. The bridge theorem's label is PROVED-CONDITIONAL: VERIFIED by our kernel
*relative to* the axiom; the axiom itself carries only the trust level of an unverified external
citation (LITERATURE), same status as the `LRC6` hypothesis it sits alongside. This file does not
upgrade E5's label past that; it only makes E5 executable/checkable machinery instead of a bare
`sorry`.
-/

import LRSpectrumFull.EightPlan
import LRSpectrumFull.Chen7RunnerImport

namespace LRSpectrumFull.EightMSSImport

open LRSpectrumFull LRSpectrumFull.EightPlan

/-- **AXIOM (LITERATURE, trusted external import, NOT re-verified by our kernel).**
Malikiosis–Santos–Schymura, "…lonely runner…", arXiv:2411.06903v2, Theorem A' (Section 3's
induction, read in full — see the module docstring for the precise pointer and for why this is
cited as Theorem A' rather than the summary Theorem A), specialized to `n = 7` given `LRC6` (the
`n = 6` case, their inductive hypothesis) and the point-count/pigeonhole threshold `28^6` (their
`C(8,2)^6`, matching `EightPlan.e5_sum_STUB_SUPERSEDED`'s and `EightMSS.MSSGap7`'s modulus `l = 28`). Statement
transcribed to be EXACTLY `EightPlan.e5_sum_STUB_SUPERSEDED`'s conclusion under `EightPlan.e5_sum_STUB_SUPERSEDED`'s exact
hypotheses, so this axiom is literally what that `sorry` needs, not a paraphrase. -/
axiom mss_theorem_A_n7 (h6 : EightPlan.LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hsum : (28 : ℤ) ^ 6 < ∑ i, v i) : 1 / 8 ≤ ML v

/-- **`e5_sum`, given the MSS axiom.** Same statement as `EightPlan.e5_sum_STUB_SUPERSEDED` (the file's `sorry`);
provided here as a separate declaration per the task's wiring option, so `EightPlan.lean` itself
is left untouched. The proof is the identity map on the axiom: the axiom was stated in exactly
this shape, so no arithmetic/unit conversion is needed here (checked carefully against
`EightPlan.e5_sum_STUB_SUPERSEDED`'s signature: `h6 : LRC6`, `v : Fin 7 → ℤ`, `hv : ∀ i, 0 < v i`,
`hg : Finset.univ.gcd v = 1`, `hsum : (28:ℤ)^6 < ∑ i, v i`, conclusion `1/8 ≤ ML v` — identical to
`mss_theorem_A_n7`, field for field). -/
theorem e5_sum_via_mss_axiom (h6 : EightPlan.LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hsum : (28 : ℤ) ^ 6 < ∑ i, v i) : 1 / 8 ≤ ML v :=
  mss_theorem_A_n7 h6 v hv hg hsum

/-- **E5 (Rosenfeld Corollary 3 at k = 7), from `e5_sum_via_mss_axiom` and `EightPlan.e5_amgm`.**
Same statement and same proof shape as `EightPlan.e5_prod`, with the axiomatized E5-sum route
instead of the `sorry`. -/
theorem e5_prod_via_mss (h6 : EightPlan.LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, v i) : 1 / 8 ≤ ML v :=
  e5_sum_via_mss_axiom h6 v hv hg (EightPlan.e5_amgm v hv hprod)

/-- **`eight_runners`, assembled from the contracts, with E5 supplied by the MSS axiom instead of
a `sorry`.** Verbatim copy of `EightPlan.eight_runners_STUB_SUPERSEDED`'s proof (same E0/E2/E3/E4/NUM contracts,
all VERIFIED, unchanged), with only the final step (`e5_prod` -> `e5_prod_via_mss`) swapped, so
that no gap in the assembly remains unnamed: what was a silent `sorry` inside `EightPlan.e5_sum_STUB_SUPERSEDED`
is now a diamond dependency on the explicitly named, cited axiom `mss_theorem_A_n7`. -/
theorem eight_runners_mss (h6 : EightPlan.LRC6)
    (hchk : ∀ p ∈ EightPlan.rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v := by
  refine EightPlan.e0_primitive (fun w hw hg => ?_) v hv
  by_contra hlt
  push Not at hlt
  have hce : EightPlan.IsCE w := ⟨hw, hg, hlt⟩
  have hpar := EightPlan.e4_parity h6 w hce
  have hS : ∀ p ∈ EightPlan.rosenfeldS, ∃ i, (p : ℤ) ∣ w i := fun p hp =>
    EightPlan.e2_prime_dvd p (EightPlan.rosenfeldS_primes p hp).1
      (EightPlan.rosenfeldS_primes p hp).2 (hchk p hp) w hw hpar hlt
  have hdvd := EightPlan.e3_lcm_dvd w hw hlt hS
  have hpos : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hle := Int.le_of_dvd hpos hdvd
  have hnum : ((28 : ℕ) ^ 42 : ℤ) < ((7 ^ 7 * (840 * ∏ p ∈ EightPlan.rosenfeldS, p) : ℕ) : ℤ) := by
    exact_mod_cast EightPlan.numeric
  have hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, w i := by
    push_cast at hnum hle
    nlinarith
  exact absurd (e5_prod_via_mss h6 w hw hg hprod) (not_le.mpr hlt)

/-- **`eight_runners_conditional`.** Fully assembled `n = 7` result: `E6` supplied by
`Chen7RunnerImport.LRC6_holds` (Barajas–Serra via the Chen import, axiom `chen_lrc7_int`), `E5`
supplied by `mss_theorem_A_n7` above, and the campaign's per-prime `E2` facts kept as an explicit
hypothesis `hchk` (untouched, not assumed proved by this file). Trust status: PROVED, conditional
on exactly two named axioms (`chen_lrc7_int`, `mss_theorem_A_n7`) and on the hypothesis `hchk`;
NOT `VERIFIED` (`#print axioms` below shows the two axioms explicitly, by design, in place of any
`sorryAx`). -/
theorem eight_runners_conditional
    (hchk : ∀ p ∈ EightPlan.rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  eight_runners_mss Chen7RunnerImport.LRC6_holds hchk v hv

end LRSpectrumFull.EightMSSImport
