# LEAN_MAP: paper/shifted-real-four-classes/NOTE.md

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
