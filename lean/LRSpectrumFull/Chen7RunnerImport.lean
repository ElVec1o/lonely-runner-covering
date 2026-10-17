/-
# E6: import of LRC for 7 runners (6 speeds) from Honglu Chen's `lean4-lonely-runner`

EXTERNAL SOURCE (trusted, not re-verified by our kernel — see the module docstring below for why):

  Repository : https://github.com/chlciallo/lean4-lonely-runner
  Author     : Honglu Chen, Nanjing University
  Commit     : e790d70d2fac2fa2a92d5624091f01fdbd231a0a (main, 2026-09-20T02:51:18Z; fetched
               2026-09-25 via `gh api repos/chlciallo/lean4-lonely-runner/commits/main`)
  File       : Research07/LRC7/Main.lean, theorem `lrc7_int`
  License    : Apache License, Version 2.0 (LICENSE file in that repository,
               `Copyright 2026 Honglu Chen, Nanjing University`; confirmed via
               `gh api repos/chlciallo/lean4-lonely-runner --jq '.license'` -> spdx_id NOASSERTION
               with key "other", and the LICENSE blob itself is the unmodified Apache-2.0 text).
               Apache 2.0 permits redistribution and reuse with attribution (retained copyright
               and license notices); this file supplies that attribution.
  Zenodo DOI : 10.5281/zenodo.22851977 (archived release cited in their README/CITATION.cff).

Their exact statement (copied here for the record, from `Research07/LRC7/Main.lean`):

```
/-- **Lonely Runner Conjecture, integer speeds, `n = 7`** (Barajas–Serra). -/
theorem lrc7_int (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hcard : D.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧
      ∀ d ∈ D, (1 / 7 : ℝ) ≤ circ (t * d) :=
  lrc7_int_of_leaves lrc7_case4 lrc7_hc6 D hpos hcard
```

where `circ x := ‖(x : UnitAddCircle)‖`, proved equal to `|x - round x|` in their
`Research07/LRC3/Circ.lean` (`circ_eq`). Their README states the proof is Barajas–Serra (2008,
EJC 15(1) R48): the `n = 7` integer case via a 7-adic valuation decomposition and explicit finite
certificates for the `|D₇(0)| = 4` and `|D₇(0)| = 5` cases, mirroring the same literature result
our own `EightPlan.lean` cites for `E6`. Their README/Audit.lean claims `#print axioms lrc7_int`
shows only the standard axioms (`propext, Classical.choice, Quot.sound`); this claim was NOT
independently re-checked by our kernel (see "Route taken" below), so it is reported as their claim,
not ours.

## Route taken: axiom + proven bridge, not vendoring

Their `lean-toolchain` pins `leanprover/lean4:v4.34.0` and `lakefile.toml` pins
`mathlib rev = v4.34.0`; our project's `lean-mathlib/lean-toolchain` pins `v4.30.0` with
mathlib `v4.30.0`. Vendoring their `Research07/LRC7/*.lean` (which imports their whole
`LRC6/`, `M3/`, `LRC3/` closure — ~40 files) would require either a second Lean/Mathlib
toolchain inside this project (a second `lake build` closure, a second multi-GB `.lake/packages`
download, and its own compile time) or forward/back-porting their proofs to `v4.30.0` by hand,
neither of which fits the stated budget, and both carry real risk to the background campaign's
disk/CPU headroom (rule: never push free disk below 1.8 GB; the campaign needs its own room).

We therefore import their theorem as a **local axiom**, stated in the exact shape of `lrc7_int`
above (so the axiom is a literal transcription, not a paraphrase), and separately give a FULLY
PROVED, kernel-checked bridge from that shape to our own `LRC6` hypothesis (`EightPlan.lean`).
The bridge is genuine Lean work, not itself axiomatized: it uses `Finset.image`, `le_gap`,
`gap_le_ML`, and the Mathlib identity `abs_sub_round_eq_min` (`|x - round x| = min (fract x)
(1 - fract x)`), which is exactly the fact that their `circ` and our `nearestIntDist` are the same
function.

Honesty (Rule 0): `chen_lrc7_int` below is an AXIOM. Nothing in this file's Lean kernel check
verifies Barajas–Serra's proof; it verifies only that IF `lrc7_int` holds (as Chen's repository,
under an Apache-2.0-licensed, claimed-zero-`sorry` build, asserts) THEN our `LRC6` holds. The
label on `LRC6_of_chen` is PROVED-CONDITIONAL: VERIFIED by our kernel *relative to* the axiom;
the axiom itself carries only the trust level of an unverified external citation (LITERATURE,
same as the `LRC6` hypothesis it replaces — this file does not upgrade E6's label, it only makes
E6 executable/checkable machinery instead of a bare `def LRC6 : Prop := ...` hypothesis).
-/

import Mathlib.Algebra.Order.Round
import LRSpectrumFull.MaxLoneliness
import LRSpectrumFull.DValue
import LRSpectrumFull.EightPlan

namespace LRSpectrumFull.Chen7RunnerImport

open LRSpectrumFull

/-- Chen's `circ`, transcribed: distance from `x` to the nearest integer, in the exact form
`|x - round x|` used by their `Research07/LRC3/Circ.lean` (`circ_eq`). We do not import their
file; this is our own copy of the *definition*, stated so the axiom below is a literal
transcription of their theorem's signature. -/
noncomputable def circ (x : ℝ) : ℝ := |x - round x|

/-- **PROVED (Mathlib, not Chen's).** Chen's `circ` and our `nearestIntDist` are the same
function. This is the fact `Research07/LRC3/Circ.lean`'s `circ_eq` establishes on their side
(`circ x = |x - round x|`, via `UnitAddCircle.norm_eq`); on our side it follows directly from
the Mathlib identity `abs_sub_round_eq_min`. Neither direction depends on anything from Chen's
repository. -/
theorem circ_eq_nearestIntDist (x : ℝ) : circ x = nearestIntDist x := by
  unfold circ nearestIntDist
  exact abs_sub_round_eq_min x

/-- **AXIOM (LITERATURE, trusted external import, NOT re-verified by our kernel).**
Transcription of `Research07/LRC7/Main.lean`'s `lrc7_int` from
https://github.com/chlciallo/lean4-lonely-runner, commit `e790d70d2fac2fa2a92d5624091f01fdbd231a0a`,
Apache 2.0, © 2026 Honglu Chen, Nanjing University. See the module docstring for the full
citation and for why this is an axiom rather than a vendored/rebuilt proof. -/
axiom chen_lrc7_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 7 : ℝ) ≤ circ (t * d)

/-- **PROVED, given `chen_lrc7_int`.** Bridge from Chen's `Finset ℕ`/`circ` shape to our
`LRC6` hypothesis's `Fin 6 → ℤ`/`ML` shape. No injectivity is needed on either side: Chen's
`D : Finset ℕ` already dedups repeated speeds (matching our own note in `EightPlan.lean` that
"repeated speeds reduce to at most five distinct ones"), and the `Finset.image` here performs
exactly that reduction from `u`. -/
theorem lrc6_of_chen (u : Fin (5 + 1) → ℤ) (hu : ∀ i, 0 < u i) :
    (1 : ℝ) / ((5 : ℝ) + 2) ≤ ML u := by
  classical
  set D : Finset ℕ := Finset.univ.image (fun i => (u i).toNat) with hDdef
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hDdef, Finset.mem_image] at hd
    obtain ⟨i, -, rfl⟩ := hd
    have hi := hu i
    have h := Int.toNat_of_nonneg hi.le
    omega
  have hDcard : D.card ≤ 6 := by
    have h1 : D.card ≤ Finset.univ.card := Finset.card_image_le
    simpa using h1
  obtain ⟨t, ht, hDt⟩ := chen_lrc7_int D hDpos hDcard
  have hbound : ∀ i, (1 : ℝ) / 7 ≤ nearestIntDist ((u i : ℝ) * t) := by
    intro i
    have hmem : (u i).toNat ∈ D := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hc := hDt _ hmem
    rw [circ_eq_nearestIntDist] at hc
    have hcast : (((u i).toNat : ℕ) : ℝ) = (u i : ℝ) := by
      have hz : ((u i).toNat : ℤ) = u i := Int.toNat_of_nonneg (hu i).le
      exact_mod_cast hz
    rw [hcast, mul_comm] at hc
    exact hc
  have h7 : (1 : ℝ) / ((5 : ℝ) + 2) = 1 / 7 := by norm_num
  rw [h7]
  exact (le_gap u t (1 / 7) hbound).trans (gap_le_ML u t)

/-- **SUPERSEDED (2026-09-26).** Use `BarajasSerra.LRC6_barajasSerra`
(`BarajasSerraLRC6Plan.lean`), which proves the same statement `EightPlan.LRC6` from standard
axioms only; `EightRunnersFinal.eight_runners` no longer depends on `chen_lrc7_int`. This
declaration is kept as a record of the interim route.

**E6, instantiated.** `LRC6` (the hypothesis `EightPlan.lean` carries as literature) holds
given the Chen import axiom. Route: PROVED bridge (`lrc6_of_chen`) applied to an AXIOM
(`chen_lrc7_int`). Do not call this `VERIFIED`: the axiom is unverified by our kernel. -/
theorem LRC6_holds : EightPlan.LRC6 := lrc6_of_chen

/-- **SUPERSEDED (2026-09-26).** Use `EightRunnersFinal.eight_runners`, which needs neither
`chen_lrc7_int` nor the hypothesis `hchk` nor the `sorry` in `EightPlan.e5_sum_STUB_SUPERSEDED`. Kept as a
record of the interim route.

**`eight_runners`, wired to the Chen import.** Still requires the per-prime campaign
hypothesis `hchk` (the 27-prime `lemma7Check 7 p = true` facts from (development file, not part of this archive));
this file only discharges the `LRC6`/E6 leg. Trust status: PROVED modulo the axiom
`chen_lrc7_int` and modulo `hchk`; not VERIFIED end-to-end (E5's `MSSGap7` gap is also still
open in the development record (not in this archive), upstream of `e5_prod`/`e5_sum` which this theorem calls
through `EightPlan.eight_runners_STUB_SUPERSEDED`). -/
theorem eight_runners_via_chen (hchk : ∀ p ∈ EightPlan.rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  EightPlan.eight_runners_STUB_SUPERSEDED LRC6_holds hchk v hv

end LRSpectrumFull.Chen7RunnerImport
