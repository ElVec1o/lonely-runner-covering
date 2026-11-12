# LEAN_MAP: paper/shifted-real-four/NOTE.md

Lean project: `lean/` (Lean 4.30.0, Mathlib as pinned in `lean/lake-manifest.json`).
Modules are `LRSpectrumFull.<Module>` in `lean/LRSpectrumFull/<Module>.lean`. Names below omit the prefix `LRSpectrumFull.`.
None of the modules `RFiveBase`, `RFiveWindow`, `RFiveCluster`, `RFiveLemS`, `RFiveCase`, `RFiveFinal`, `RFiveCor` is imported by the
root file `lean/LRSpectrumFull.lean`. No Lean build was run for this archive. The builds and axiom prints are those of the
development repository, made on 2026-11-12; the observations of the axioms of the four main declarations were made by a fresh
review session, those of the intermediate declarations by the session that built the modules.

Warning on building: do not build `RFiveCor` or `RFiveFinal` by a single call from a fresh checkout. A named target builds its whole
import closure (20 modules for `RFiveCor`), possibly with several Lean workers at once, and one worker can need several GB. Build the
closure modules one at a time, in dependency order, by giving them to `code/lean_build/gbound_build.sh` as arguments in this order
(it builds its arguments one after the other):
`TPSmall`, `TPThreeR`, `TPPrime`, `TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourArcs`, `TPFourCoset`, `TPFourCoincide`,
`TPFourWindow`, `RFiveBase`, `RFiveWindow`, `TPFourTight`, `RFiveCluster`, `TPFourCase21`, `TPFourGlue`, `RFiveLemS`, `RFiveCase`,
`RFiveFinal`, `RFiveCor`.

## Main theorems

Definitions: `tpDist` in `TPSmall.lean`; `GoodR` in `RFiveBase.lean`.

    noncomputable def tpDist (x : R) : R := |x - round x|
    def GoodR (v : N) (phi : R) (t : R) : Prop := 1 / 5 <= tpDist ((v : R) * t + phi)

Statements (ASCII transcription of the `#check` output of the review session; the inequality is non-strict, the phases are
arbitrary reals, `Fin 4` indexing with `Function.Injective v` gives four distinct speeds, `Finset.univ.gcd v` is the gcd in N):

    R5      : forall (v : Fin 4 -> N), (forall i, 0 < v i) -> Function.Injective v -> Finset.univ.gcd v = 1 ->
                (exists i, 5 dvd v i) -> forall (phi : Fin 4 -> R), exists t, forall i, 1 / 5 <= tpDist ((v i : R) * t + phi i)
    R5_core : forall (v : Fin 4 -> N), (forall i, 0 < v i) -> Function.Injective v ->
                (exists i, 5 dvd v i) -> (exists i, not (5 dvd v i)) -> forall (phi : Fin 4 -> R),
                exists t, forall i, GoodR (v i) (phi i) t
    R5_tp   : the statement of R5_core with the conclusion 1 / 5 <= tpDist ((v i : R) * t + phi i)
    R5_gcd  : forall (v : Fin 4 -> N), (forall i, 0 < v i) -> Function.Injective v ->
                (exists i, 5 dvd v i / Finset.univ.gcd v) -> forall (phi : Fin 4 -> R),
                exists t, forall i, 1 / 5 <= tpDist ((v i : R) * t + phi i)

`R5` is in `RFiveFinal.lean` (as is `R5_core`); `R5_tp` and `R5_gcd` are in `RFiveCor.lean`. `R5_core` is stronger than `R5`; `R5`
follows from it because gcd 1 forces a speed not divisible by 5. In `R5_gcd` the division `v i / gcd` is exact and the gcd is
positive (positivity of the speeds), so the hypothesis is not trivialised. The hypotheses of `R5` are satisfiable (the review session
compiled the instance `v = (1,2,3,5)`; for `R5_gcd`, `v = (2,4,6,10)`), and the review session closed unfolded restatements of
`R5` and `R5_gcd` (explicit `|x - round x|`, explicit gcd) by `exact`.

Axioms, observed by a fresh review session on 2026-11-12 (`#print axioms`, text of the session):

    'LRSpectrumFull.R5' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LRSpectrumFull.R5_core' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LRSpectrumFull.R5_tp' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LRSpectrumFull.R5_gcd' depends on axioms: [propext, Classical.choice, Quot.sound]

The building session printed the same list for `caseHR`, `lemSR`, `cluster_div`, `case3R`, `case21R`, `lemma4R`, `exists_exactR`,
`three_free`, `exists_coincide`, `goodR_of_not_mem_badImg`, `step_le2R`. Review verdict: SOUND-WITH-CAVEATS (the caveats concern wording,
scope, the constant 1/5 and the process of the builder; see `NOTE.md`). The same session re-elaborated each of the seven `RFive*`
sources against the built object files with `lake env lean` (exit 0, no output for each), and found no `.lean` modification time
later than the corresponding build.

Not used: `five_runners` and `Delta2FiveRunners` (a text search over the 20-module closure finds no occurrence of `five_runners`,
`Delta2FiveRunners` or `FiveRunners`; the modules `TPFourFive`, `TPFourCase3` and `TPFourHub` are not in the closure).

## Import closure of `RFiveCor` inside the project (20 modules)

"In 1.2.0" means the file was already in the archive, byte-identical to the development file (SHA-256 compared for this release);
"added in 1.3.0" means it is new in this release. The hashes of all files are in `MANIFEST.tsv`.

| Module | Role | State in this archive |
|---|---|---|
| `TPSmall` | `tpDist`, `TPp` | in 1.2.0 |
| `TPThreeR`, `TPPrime` | imported through `TPFourBridge` (`TPThreeR`: case lemma for three speeds; `TPPrime`: pigeonhole lemma) | in 1.2.0 |
| `TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourArcs`, `TPFourCoset`, `TPFourCoincide`, `TPFourWindow`, `TPFourTight`, `TPFourCase21`, `TPFourGlue` | declarations of the grid proof reused unchanged (`badImg`, `arc`, `core5`, `exists_good_21`, `exists_good_3`, `three_arcs`, `exists_perturb`, `exists_coset_far`, `bezout_solve`, `spread3`, `hne_of`, `exists_eps`, `other_of_not_same`, `other_other`, `sum_div5_lt`, `tpDist_add_int`, `exists_near_of_not_good`, `badImg_eq_of_class`, `mem_badImg_class`) | in 1.2.0 |
| `RFiveBase` | `GoodR`, Lemma 1 (real phases), union bound, `exists_coincide` | added in 1.3.0 |
| `RFiveWindow` | window and exact-coincidence lemmas (`lemma4R`, `L6`, `exists_exactR`) | added in 1.3.0 |
| `RFiveCluster` | constant-1/4 window, perturbation, `cluster_div` | added in 1.3.0 |
| `RFiveLemS` | `three_free`, `lemSR` (at most three runners) | added in 1.3.0 |
| `RFiveCase` | `case21R`, `case3R` | added in 1.3.0 |
| `RFiveFinal` | `caseHR`, `R5_core`, `R5` | added in 1.3.0 |
| `RFiveCor` | `R5_tp`, `R5_gcd` | added in 1.3.0 |

Outside the project the closure imports only `Mathlib` (`import Mathlib` in `TPSmall.lean`). A text search of the 20 modules by the review
session, for `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque`,
`set_option`, `local instance`, `local notation`, `open`, `scoped`, `attribute`, `macro`, `notation`, `syntax`, `elab`, `initialize`
and `#eval`, found only: `set_option linter.unusedSimpArgs false` (`TPSmall`, `TPThreeR`); the word "admits" in a docstring of
`TPThreeR` and the word "Notation:" in a comment of `RFiveCase`; the declaration `instance fact_prime_five_tp4 : Fact (Nat.Prime 5)`
in `TPFourLocal`; and `decide` on statements over `ZMod 5` (kernel evaluation, not native). No theorem has the statement `True`.
The `RFive*` modules are not imported by `lean/LRSpectrumFull.lean`.
