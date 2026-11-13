# LEAN_MAP: paper/shifted-real-four-classes/NOTE.md

This file has two parts. One part (everything before the heading "Release 1.5.0: R7 and Q3") is the map of version 1.4.0 (the eight modules `RQ*` and the five theorems `P3`, `Q4`, `QGen`, `T`, `G24`) and is unchanged. The part from that heading on is new in version 1.5.0 (seven modules `RSevenCore`, `RSevenA`, `RSevenB`, `RSevenFinal`, `RQ3Sweep`, `RQ3Mix`, `RQ3Final`; theorems `R7A`, `R7B`, `R7_partial`, `Q3`, `Q3_ndvd`, `Q3_core`).

Lean project: `lean/` (Lean 4.30.0, Mathlib as pinned in `lean/lake-manifest.json`).
Modules are `LRSpectrumFull.<Module>` in `lean/LRSpectrumFull/<Module>.lean`. Names below omit the prefix `LRSpectrumFull.`.
None of the modules `RQWindow`, `RQThree`, `RQFour`, `RQLemmaC`, `RQGen`, `RQPigeon`, `RQT`, `RQG24` is imported by the
root file `lean/LRSpectrumFull.lean`. No Lean build was run for this archive. The builds and axiom prints are those of the
development repository, made on 2026-11-12; the axioms of the declarations listed below were printed by a fresh review session
(52 declarations: the exported theorems and lemmas of the eight modules, and `lemSR`, `coset_branchR`, `exists_perturb` from earlier modules) and, for the
declarations of the eight modules, also by the sessions that built them.

Warning on building: do not build `RQT` or `RQG24` by a single call from a fresh checkout. A named target builds its whole
import closure (23 modules for the pair `RQT`, `RQG24`), possibly with several Lean workers at once, and one worker can need several GB
(the builds of the eight `RQ*` modules in the development repository peaked at about 6 GB of resident memory). Build the
closure modules one at a time, in dependency order, by giving them to `code/lean_build/gbound_build.sh` as arguments in this order
(it builds its arguments one after the other):
`TPSmall`, `TPThreeR`, `TPPrime`, `TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourCoset`, `TPFourArcs`, `TPFourCoincide`,
`TPFourWindow`, `RFiveBase`, `RFiveWindow`, `RQWindow`, `TPFourCase21`, `TPFourGlue`, `RFiveLemS`, `RQThree`, `RQFour`, `RQGen`,
`RQPigeon`, `RQLemmaC`, `RQT`, `RQG24`.
(This is a post-order of the import lines of the files in `lean/LRSpectrumFull/`, checked to list every module of the closure once,
after all of its imports.)

## Main theorems

Definitions: `tpDist` in `TPSmall.lean`; `GoodR` in `RFiveBase.lean`.

    noncomputable def tpDist (x : R) : R := |x - round x|
    def GoodR (v : N) (phi : R) (t : R) : Prop := 1 / 5 <= tpDist ((v : R) * t + phi)

Common to the five theorems: `v : Fin 4 -> N`, `forall i, 0 < v i`, `Function.Injective v`, `phi : Fin 4 -> R` arbitrary, conclusion
`exists t : R, forall i, GoodR (v i) (phi i) t`. The inequality is non-strict, t is chosen after phi. In Q4, QGen and T the indices
`s1 s2 a b : Fin 4` carry all six pairwise inequalities (so they are four distinct indices and cover `Fin 4`, `cover4`); in G24 the
indices `a b e s` carry the six pairwise inequalities. Non-resonance for a slow speed s is written with additions only,
`v s != v a + v b /\ v a != v b + v s /\ v b != v a + v s`, which says that `v s` is neither `v a + v b` nor `|v a - v b|` (positivity).

    P3    : q >= 2; z : Fin 4; not (q dvd v z); forall i, i != z -> q dvd v i
            (RQThree.lean)
    Q4    : 4 dvd v s1; 4 dvd v s2; v a % 2 = 1; v b % 2 = 1; non-resonance for s1; non-resonance for s2
            (RQFour.lean)
    QGen  : 4 <= q; q dvd v s1; q dvd v s2; Nat.Coprime (v a) q; Nat.Coprime (v b) q;
            (q : Z) dvd (v a : Z) - v b  \/  (q : Z) dvd (v a : Z) + v b; non-resonance for s1; non-resonance for s2
            (RQGen.lean; the hypothesis on v b is carried but unused)
    T     : 6 <= q; q dvd v s1; q dvd v s2; Nat.Coprime (v a) q; Nat.Coprime (v b) q   (no class and no non-resonance hypothesis)
            (RQT.lean)
    G24   : v a % 2 = 1; v b % 2 = 1; v e % 4 = 2; v s % 4 = 0; non-resonance for s   (RQG24.lean)

Supporting statements (same file as the note's section):

    window_lemma (RQWindow.lean) : forall q, 2 <= q -> forall va vb, Nat.Coprime va q -> forall eps D : Z,
        (eps = 1 \/ eps = -1) -> (va : Z) - eps * vb = q * D -> forall phia phib x n,
        |D * x + (phia - eps * phib) - n| <= 3 / 5 - 1 / q ->
        exists j : Z, GoodR va phia ((j + x) / q) /\ GoodR vb phib ((j + x) / q)
    lemmaC_real  (RQLemmaC.lean)  : forall va vb, Nat.Coprime va 8 -> forall mu : Z, (mu = 3 \/ mu = 5) ->
        (vb : ZMod 8) = mu * va -> forall phia phib x, exists j : Z, GoodR va phia ((j + x) / 8) /\ GoodR vb phib ((j + x) / 8)

The statements were read from the source by a fresh review session. The hypotheses of each theorem are satisfiable: the review
session instantiated each in Lean with arbitrary phases (P3 on speeds (2,4,6,1) with q = 2; Q4 on (8,12,1,3); QGen on (10,15,1,4) with
q = 5; T on (6,12,1,5) with q = 6, on (8,16,1,3) with q = 8 and on (7,14,1,2) with q = 7; G24 on (1,3,2,8)), and compiled unfolded
restatements of `window_lemma`, `P3`, `Q4`, `QGen`, `T`, `G24` (explicit `|x - round x|`, explicit absolute values in the
non-resonance clause or `Int.ModEq` for the class) that close by `exact` from the theorems. For each of the three tight vectors
(1,2,3,4), (1,3,4,6), (1,3,4,7), no assignment of roles and no q satisfies the hypotheses of any of the five theorems (checked by
the review session by exact enumeration and, up to q = 8, by kernel `decide`).

Axioms, as printed by a fresh review session on 2026-11-12 (`#print axioms`; the same lists were printed by the building sessions):

    P3, Q4, QGen, T, G24, window_lemma, lemmaC_real, exists_two_good, card_bad_le, T_same, QGen_core, lemSR3, lemSR2, and all
    other exported theorems and lemmas of the eight modules except those below: [propext, Classical.choice, Quot.sound]
    cover4                                        : no axioms
    eps_D4, D_ne4, nonres4, D_neq, pos_of_mul_eq, blk8 : [propext, Quot.sound]

Review verdict: SOUND-WITH-CAVEATS (the caveats concern the wording of the prior-art statements, three redundant or unused
hypotheses, the unreviewed trust base, and the coverage figures; see `NOTE.md`). The same session re-elaborated each of the eight
sources with `lake env lean` (exit 0; the only warning of the eight sources is the unused variable `hb` in `QGen`).

## Import closure of `RQT` and `RQG24` inside the project (23 modules)

"In 1.2.0" and "added in 1.3.0" mean the file was already in the archive, byte-identical to the development file (SHA-256 compared for
this release); "added in 1.4.0" means it is added in this release. The hashes of all files are in `MANIFEST.tsv`.

| Module | Role | State in this archive |
|---|---|---|
| `TPSmall` | `tpDist`, `TPp` | in 1.2.0 |
| `TPThreeR`, `TPPrime` | imported through `TPFourBridge` | in 1.2.0 |
| `TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourCoset`, `TPFourArcs`, `TPFourCoincide`, `TPFourWindow`, `TPFourCase21`, `TPFourGlue` | declarations of the grid proof reused unchanged (`tpDist_add_int`, `exists_near_of_not_good`, `exists_perturb`, and others used by `RFive*`) | in 1.2.0 |
| `RFiveBase` | `GoodR`, Lemma 1 of the note on a speed divisible by 5 | in 1.3.0 |
| `RFiveWindow` | `coset_branchR`, `coset_branchR_ne` | in 1.3.0 |
| `RFiveLemS` | `lemSR` (at most three runners) | in 1.3.0 |
| `RQWindow` | `goodR_mulq`, `near_to_int`, `window_gap`, `window_lemma`, `exists_free_j`, `tpDist_neg`, `exists_int_of_far` | added in 1.4.0 |
| `RQThree` | `lemSR3`, `P3` | added in 1.4.0 |
| `RQFour` | `cover4`, `eps_D4`, `D_ne4`, `nonres4`, `cop4`, `Q4` | added in 1.4.0 |
| `RQLemmaC` | `blk8`, `lemmaC3`, `lemmaC5`, `lemmaC1_covers`, `lemmaC7_covers`, `mem_blk8_of_near`, `lemmaC_real` | added in 1.4.0 |
| `RQGen` | `assemble4`, `finish_window`, `eps_Dq`, `D_neq`, `pos_of_mul_eq`, `resonance_of`, `slow_window`, `QGen_core`, `QGen` | added in 1.4.0 |
| `RQPigeon` | `lemSR2`, `badSet`, `mem_badSet`, `card_bad_le`, `exists_two_good` | added in 1.4.0 |
| `RQT` | `tpDist_perturb`, `abs_ge_of_int`, `exists_shift`, `resonant_x_pos`, `resonant_x`, `T_same`, `T` | added in 1.4.0 |
| `RQG24` | `window_gap4`, `e_val`, `not_both_near`, `parity_ok`, `lemma4R_tight_pos`, `lemma4R_tight`, `g24_core`, `G24` | added in 1.4.0 |

Imports inside the eight modules: `RQWindow` imports `RFiveWindow`; `RQThree` imports `RQWindow`, `RFiveLemS`; `RQFour` imports `RQThree`;
`RQLemmaC` imports `RQWindow`; `RQGen` imports `RQFour`; `RQPigeon` imports `RQThree`; `RQT` imports `RQGen`, `RQPigeon`, `RQLemmaC`;
`RQG24` imports `RQGen`. Outside the project the closure imports only `Mathlib` (`import Mathlib` in `TPSmall.lean`).
The closure does not contain `RFiveCluster`, `RFiveCase`, `RFiveFinal`, `RFiveCor`, `TPFourTight`, `five_runners` or `Delta2FiveRunners`.

A text search of the 23 modules by the review session, for `sorry`, `admit`, `native`, `ofReduceBool`, `trustCompiler`, `#eval`, `#exit`,
`decide +`, `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque`, `@[simp`, `axiom`, found only the word "admits" in a docstring of
`TPThreeR`. `set_option`: only `linter.unusedSimpArgs false` (`TPSmall`, `TPThreeR`). `instance`: only `fact_prime_five_tp4 : Fact (Nat.Prime 5)`
(`TPFourLocal`). `open`: only `open Classical in` (`RQPigeon`, for `badSet` and `mem_badSet`: decidability). No local notation, attribute, macro,
syntax, elab, universe or variable declaration. The only `def`s of the closure are `GoodR`, `tpDist`, `badSet`, `blk8`, `arc`, `badImg`, `L6`, `TPp`,
`Good`, `Case3`, `CaseH`; nothing redefines divisibility, `%`, `/`, `gcd`, `round` or the absolute value. `decide` appears only as kernel
`decide` on small finite statements: `cover4` (1024 cases, a statement about four-element index sets), the four statements of `RQLemmaC` over
`ZMod 8` (64 cases each, two of them negations) and the fact `(8 : ZMod 8) = 0`, a few facts of the form `not Nat.Coprime 2 6` in `RQT`, and older small facts in the `TPFour*` and `RFive*`
modules. No `native_decide`, no `decide +kernel`, no `decide +native`. The `exfalso` in `T` (the case q = 6, see `NOTE.md`, Section 8) proves the class disjunction from coprimality; it is not a proof from inconsistent hypotheses.

## Release 1.5.0: R7 and Q3

All declarations are in namespace `LRSpectrumFull`; files are in `lean/LRSpectrumFull/`. None of the seven new modules is imported by the root file `lean/LRSpectrumFull.lean`, which is not updated. No Lean build was run for this archive. The builds, the axiom prints and the review are those of the development repository, made on 2026-11-12: the seven modules were built one at a time under a memory watchdog over the process tree (peaks of the process tree between about 5.6 and 6.1 GB), six of the seven at one attempt, and `RSevenB` at the third attempt after two failed builds (see the process note in `RELEASE_CHECK.md`); a fresh review session re-elaborated each of the seven sources (exit status 0; the only message is the unused variable `hc` in `R7B`), printed `#print axioms` for every constant declared by the seven modules (51 constants on the R7 side, 44 on the Q3 side; the union of the printed axioms is `propext`, `Classical.choice`, `Quot.sound`; `ofReduceBool` occurs in none), and compiled restatements of `R7_partial` and `Q3_ndvd` with the distance and the resonance clause written out (`|x - round x|`, an honest absolute value), each closed by `refine` or `exact` from the theorem. Review verdict: SOUND-WITH-CAVEATS. The only serious finding of the review was a packaging defect (two duplicate lemma names, see below), not an error of mathematics.

Renaming after the review. The review was made on the files with the lemma names `caseA` and `caseB`. These clash with `TPThreeA.caseA` and `NormalForm.caseB`, so the `RSeven*` modules could not be imported together with `TPThreeA` (hence not with `RQ3Final`) or with `NormalForm`. The two lemmas were renamed `r7CaseA` and `r7CaseB` in `RSevenA`, `RSevenB`, `RSevenFinal` (the definitions, the two uses, one comment line; nothing else changed; `RSevenCore` was not touched). After the renaming `RSevenA`, `RSevenB` and `RSevenFinal` were rebuilt one at a time (success) and a file importing `RSevenFinal`, `RQ3Final`, `RQT`, `RQG24`, `RFiveCor` and `NormalForm` elaborated without error and printed the axioms `propext`, `Classical.choice`, `Quot.sound` for `R7_partial`, `R7A`, `R7B`, `Q3`, `T`, `G24`, `QGen`, `P3`, `Q4`, `R5`, `R5_core`, `R5_gcd`. The renamed files were not reviewed again.

Known packaging limitation. The name `LRSpectrumFull.badSet` is declared in `RQPigeon` (archived since 1.4.0) and also in the development modules `BadTripleFamilies` and `PerturbStrip` (not in this archive). Hence `RQPigeon`, and with it every module of the `RQ*`, `RSeven*` and `RQ3*` family, cannot be imported in one file together with either of those two. The library root file was not extended and was already not buildable as a whole.

### Statements

Common to the theorems: `v : Fin 4 -> N`, `forall i, 0 < v i`, `Function.Injective v`, `phi : Fin 4 -> R` arbitrary, conclusion `exists t : R, forall i, GoodR (v i) (phi i) t` (`GoodR` and `tpDist` as above).

    R7_partial  (RSevenFinal.lean) : s a b c : Fin 4 with the six pairwise inequalities (so all four indices);
            7 dvd v s; not (7 dvd v a); not (7 dvd v b); not (7 dvd v c);
            hpat :  ( (7 : Z) dvd v a - v b  \/  7 dvd v a + v b ) /\ ( 7 dvd v a - v c  \/  7 dvd v a + v c )              -- (A)
               \/   ( ( 7 dvd v b - v c  \/  7 dvd v b + v c )                                                                 -- (B)
                      /\ not ( 7 dvd v a - v b  \/  7 dvd v a + v b )
                      /\ not ( ( v s = v b + v c  \/  v b = v c + v s  \/  v c = v b + v s )
                               /\ ( 7 dvd v b - 3 * v a  \/  7 dvd v b + 3 * v a ) ) )
            (the divisibilities of differences and sums are on the integer casts of the speeds)
    R7A         (RSevenFinal.lean) : the same hypotheses with hpat replaced by the two disjunctions of (A)
    R7B         (RSevenFinal.lean) : the same hypotheses with hpat replaced by the three conjuncts of (B)
                                     (the hypothesis `not (7 dvd v c)` is carried and is not used in the proof)
    Q3          (RQ3Final.lean)    : s1 s2 a b : Fin 4 with the six pairwise inequalities; 3 dvd v s1; 3 dvd v s2;
            Nat.Coprime (v a) 3; Nat.Coprime (v b) 3;
            v s1 != v a + v b /\ v a != v b + v s1 /\ v b != v a + v s1;      (non-resonance for s1)
            v s2 != v a + v b /\ v a != v b + v s2 /\ v b != v a + v s2       (non-resonance for s2)
    Q3_ndvd     (RQ3Final.lean)    : Q3 with `not (3 dvd v a)`, `not (3 dvd v b)` in place of coprimality
    Q3_core     (RQ3Final.lean)    : the core of Q3 with u1, u2 given by v s1 = 3 u1, v s2 = 3 u2, eps and D given by
            v a - eps * v b = 3 * D, and the non-resonance written as u1 != |D| and u2 != |D|

Supporting statements:

    r7CaseA (RSevenA.lean)  : q with 2 * ((2q - 1) / 5 + 1) < q and 5 <= q; w >= 1; va vb vc coprime to q; eps_b, eps_c = +-1;
            va - eps_b vb = q D_b and va - eps_c vc = q D_c with D_b, D_c nonzero and different; phases arbitrary. Then
            there is a real x with 1/5 <= tpDist (w x + phi_d) and an integer j such that the runners a, b, c are good at (j + x)/q.
    r7CaseB (RSevenB.lean)  : q = 7; w >= 1; vb coprime to 7; eps = +-1; vb - eps vc = 7 D, D nonzero; mu : ZMod 7 with
            (va : ZMod 7) = mu * vb, mu not 0, 1, -1; and (|D| = w -> mu = 3 or mu = -3). Then there is a real x with
            1/5 <= tpDist (w x + phi_d) and an integer j such that b, c, a are good at (j + x)/7.
    q3Mix3  (RQ3Mix.lean)   : p q d : N positive and pairwise different, alpha beta gamma : R arbitrary. Then there is a real x with
            1/5 <= tpDist (p x + alpha), 1/5 <= tpDist (q x + beta), 7/30 <= tpDist (d x + gamma).

### Satisfiability and the tight vectors

The review session instantiated the hypotheses in Lean with arbitrary phases by `decide`: `R7_partial` pattern (A) on the speeds (1,6,8,7), pattern (B) non-resonant on (1,3,4,14), pattern (B) resonant and not excluded on (3,1,6,7), and (3,4,7,11); `Q3` on (1,3,5,9) and (1,5,3,9). The building sessions did the same for (3,4,7,11), (1,3,4,14), (3,1,6,7) and, for `Q3`, (1,2,6,9), (1,3,5,9), (1,3,6,8), (1,3,6,10). For each of the three tight vectors (1,2,3,4), (1,3,4,6), (1,3,4,7), no assignment of roles satisfies the hypotheses of `R7_partial` or of `Q3` (kernel `decide`, all 24 role assignments in the review). Where they fail: for `R7_partial`, (1,2,3,4) and (1,3,4,6) have no speed divisible by 7; (1,3,4,7) fails only the last clause of pattern (B) (the exclusion clause: 7 = 3 + 4, and the 3-relation holds), in exactly the two assignments that exchange b and c, and with the clause removed (Lean: `HR7 false ![1,3,4,7]` by `decide`) it would satisfy the hypotheses; for `Q3`, (1,2,3,4) and (1,3,4,7) have only one speed divisible by 3, and (1,3,4,6) fails only non-resonance (3 = |1 - 4|). The exclusion clause is therefore doing real work at (1,3,4,7), whose value is exactly 1/5; the same holds for the non-resonance clause of `Q3` at (1,3,4,6). The statements were read from the source by the review session, and the review checked that the two pattern clauses are stated for all permutations of the roles (the indices are universally quantified).

### Import closure of `RSevenFinal` and `RQ3Final` inside the project (36 modules)

Outside the project the closure imports only `Mathlib` (`import Mathlib` in `TPSmall.lean`). The closure of `RSevenFinal` has 28 modules, that of `RQ3Final` has 27, and 19 are common. "In 1.2.0", "in 1.3.0", "in 1.4.0" mean the file was already in the archive, byte-identical to the development file (SHA-256 compared for this release); "added in 1.5.0" means it is added in this release. The hashes of all files are in `MANIFEST.tsv`.

| Module | Role | State in this archive |
|---|---|---|
| `TPSmall`, `TPThreeR`, `TPPrime` | `tpDist`, three-runner definitions, primes | in 1.2.0 |
| `TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourCoset`, `TPFourArcs`, `TPFourCoincide`, `TPFourWindow`, `TPFourCase21`, `TPFourGlue`, `TPFourTight` | declarations of the grid proof reused unchanged | in 1.2.0 |
| `TPThreeRed`, `TPThreeA` | three runners, real-phase building blocks `split3`, `pairBox`, `sweepCase`, `shiftCase`, `ineqL4`, `GoodQ` | in 1.2.0 |
| `TPFMain`, `TPFData`, `TPFCheck` | generated data modules (kernel `decide +kernel`; generator not archived), imported by `TPThreeRed`; not used by the lemmas of this release | in 1.2.0 |
| `RFiveBase`, `RFiveWindow`, `RFiveLemS`, `RFiveCluster`, `RFiveCase` | `GoodR`; `lemma4R`, `L6`, `exists_exactR`; `lemSR`; `cluster_div`, `two_abs_le`; `case3R` and its helpers | in 1.3.0 |
| `RQWindow`, `RQThree`, `RQFour`, `RQGen`, `RQPigeon`, `RQG24` | window lemma, `QGen` pieces, `badSet`, `card_bad_le`, `lemma4R_tight` | in 1.4.0 |
| `RSevenCore` | `not_good_of_near`, `centre_diff`, `good_of_win`, `win_ne_dvd`, `window_gap3`, `bad_transfer`, `exact_pair` | added in 1.5.0 |
| `RSevenA` | `r7CaseA` | added in 1.5.0 |
| `RSevenB` | `ap3`, `ap2`, `bc_window`, `bc_good`, `a_good`, `r7CaseB` | added in 1.5.0 |
| `RSevenFinal` | `eps_D7`, `cop7`, `fin7`, `finish7`, `R7A`, `R7B`, `R7_partial` | added in 1.5.0 |
| `RQ3Sweep` | `Q3GoodT`, `Q3Pat`, `q3Pat_perm`, `q3Pat_le`, `q3_tpDist_of_goodT`, `q3_goodT_of_goodQ`, `q3PairBox`, `q3CSweep`, `q3Sweep`, `q3Sweep123` | added in 1.5.0 |
| `RQ3Mix` | `q3MixPrim`, `q3MixSorted`, `q3MixAny`, `q3Mix3` | added in 1.5.0 |
| `RQ3Final` | `q3_exists_int_of_far`, `q3_slow_window`, `Q3_core`, `Q3`, `Q3_ndvd` | added in 1.5.0 |

(Counts: 18 modules from 1.2.0, 5 from 1.3.0, 6 from 1.4.0, 7 added in 1.5.0: 36.) Direct imports of the new modules: `RSevenCore` imports `RQG24`, `RQPigeon`; `RSevenA` imports `RSevenCore`, `RFiveCase`; `RSevenB` imports `RSevenCore`, `RFiveCluster`; `RSevenFinal` imports `RSevenA`, `RSevenB`; `RQ3Sweep` imports `TPThreeA`; `RQ3Mix` imports `RQ3Sweep`; `RQ3Final` imports `RQ3Mix`, `RQGen`. The closure contains neither `RQLemmaC`, `RQT`, `RFiveFinal`, `RFiveCor`, `five_runners` nor `Delta2FiveRunners`.

Build order. Do not build `RSevenFinal` or `RQ3Final` by a single call from a fresh checkout: a named target builds the whole import closure, possibly with several Lean workers at once, and one worker needed between about 5.6 and 6.1 GB in the builds of this release. Build the 36 modules one at a time, in this order, by giving them to `code/lean_build/gbound_build.sh` as arguments (it builds its arguments one after the other):
`TPSmall`, `TPThreeR`, `TPFCheck`, `TPPrime`, `TPFData`, `TPFourBridge`, `TPFMain`, `TPFourCoset`, `TPFourLocal`, `TPFourArcs`, `TPThreeRed`, `TPFourReduce`, `TPFourCase21`, `TPFourCoincide`, `TPThreeA`, `TPFourGlue`, `TPFourWindow`, `RQ3Sweep`, `TPFourTight`, `RFiveBase`, `RQ3Mix`, `RFiveLemS`, `RFiveWindow`, `RQWindow`, `RFiveCluster`, `RQThree`, `RQFour`, `RFiveCase`, `RQPigeon`, `RQGen`, `RQ3Final`, `RQG24`, `RSevenCore`, `RSevenA`, `RSevenB`, `RSevenFinal`.
(This order was computed by repeatedly taking the modules all of whose imports are already listed, from the import lines of the files in `lean/LRSpectrumFull/`; a script then checked that it lists 36 distinct modules, that they are exactly the union of the two closures, and that every module comes after all the modules it imports.) The modules `RQLemmaC` and `RQT` of the closure of version 1.4.0 are not needed by `R7_partial` or `Q3`.

### Text search

A text search of the seven new files (`sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, whole-word match, comments included): no hit. `set_option`: `RSevenB.lean` (4 lines: `synthInstance.maxSize 4096` and `maxRecDepth 100000`, on the lemmas `ap3` and `ap2`) and `RSevenFinal.lean` (2 lines, the same two options on `fin7`); none in `RSevenCore`, `RSevenA`, `RQ3Sweep`, `RQ3Mix`, `RQ3Final`. The three lemmas `ap3`, `ap2`, `fin7` are kernel `decide` statements over `ZMod 7` (343, 343 and 49 cases). A text search of the other 29 modules of the closure for the same words: no hit; `set_option` occurs only in `TPSmall` and `TPThreeR` (`linter.unusedSimpArgs false`) and `TPFMain` and `TPFData` (`maxRecDepth 100000`); `decide +kernel` occurs 28 times, in `TPFCheck`, `TPFMain` and `TPFData` only; no `decide +native`; `open Classical in` only in `RQPigeon`; the only `instance` is `fact_prime_five_tp4`. The new modules define `Q3GoodT` and `Q3Pat`; nothing in the closure redefines divisibility, `%`, `/`, `gcd`, `round` or the absolute value.

## Release 1.6.0: pointer to `paper/shifted-four-sum195`

Version 1.6.0 uses all seven class theorems of this note (`R5_core`, `P3`, `QGen` with `Q4`, `T`, `G24`, `R7_partial`, `Q3_ndvd`) as imported theorems in a Lean proof of the statement for speed sum at most 195 (`sLRC4_le195`, `lean/LRSpectrumFull/S4Final.lean`); see `paper/shifted-four-sum195/NOTE.md` and its `LEAN_MAP.md`. No file of this note and no module of the seven classes was changed. Build warning, repeated from there: the import closure of `S4Final` has 293 modules; do not call `lake build` on `S4Final` from a clean tree (a parallel rebuild was sampled at 29.6 GB on a 24 GB machine); build the closure one module at a time in the order of `lean/S4_BUILD_ORDER.txt`.
