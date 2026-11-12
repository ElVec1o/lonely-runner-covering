# Four moving runners with real phases: seven divisibility classes and a residue argument, with their Lean version

Version 1.5.0 (12 November 2026). Version 1.4.0 of this note (12 November 2026) treated five classes (P3, Q4, QGen, T, G24); version 1.5.0 adds two more (R7, Q3) in Sections 12 and 13 and updates the status, the caveats and the census. Sections 0 to 11 are unchanged except for the additions listed in Section 10 and Section 11.

Vico Bonfioli. Version of 12 November 2026 (release 1.5.0 of this archive). Preprint note, not peer reviewed.

## Status

* **Setting of every statement.** Four pairwise distinct positive integer speeds v_1, ..., v_4, arbitrary real phases phi_1, ..., phi_4, and the conclusion: some real t has ||v_i t + phi_i|| >= 1/5 for i = 1, ..., 4 (non-strict inequality), where ||y|| = |y - round(y)| is the distance from y to the nearest integer. In Lean the speeds are `v : Fin 4 -> N` with `forall i, 0 < v i` and `Function.Injective v`, the phases are `phi : Fin 4 -> R`, and the conclusion is `exists t, forall i, GoodR (v i) (phi i) t`.
* **P3** (`P3`, `RQThree.lean`). Some q >= 2 divides exactly three of the four speeds.
* **Q4** (`Q4`, `RQFour.lean`). The speeds v_a and v_b are odd, 4 divides v_s1 and v_s2 (four distinct indices s1, s2, a, b), and for s = s1 and s = s2: v_s is different from v_a + v_b and from |v_a - v_b|.
* **QGen** (`QGen`, `RQGen.lean`). The same with 4 replaced by any q >= 4: q divides v_s1 and v_s2, v_a and v_b are coprime to q, q divides v_a - v_b or v_a + v_b, and v_s is different from v_a + v_b and from |v_a - v_b| for s = s1 and s = s2.
* **T** (`T`, `RQT.lean`). Some q >= 6 divides two speeds v_s1, v_s2 and the other two speeds v_a, v_b are coprime to q. No further hypothesis.
* **G24** (`G24`, `RQG24.lean`). Four distinct indices a, b, e, s: v_a and v_b are odd, v_e is 2 mod 4, v_s is 0 mod 4, and v_s is different from v_a + v_b and from |v_a - v_b|.
* **R7** (`R7A`, `R7B`, `R7_partial`, `RSevenFinal.lean`; new in version 1.5.0). Four distinct indices s, a, b, c; 7 divides v_s and does not divide v_a, v_b, v_c (so exactly one speed is divisible by 7). Write x ~ y for "7 divides x - y or 7 divides x + y". Then the conclusion holds if (A) a ~ b and a ~ c; or (B) b ~ c, a ~ b does not hold, and it is not the case that both [v_s = v_b + v_c or v_s = |v_b - v_c|] and [7 divides v_b - 3 v_a or v_b + 3 v_a]. `R7A` is pattern (A), `R7B` is pattern (B), `R7_partial` is the disjunction. Not covered: three pairwise non-equivalent free speeds, and the excluded sub-case of (B), which contains the tight vector (1,3,4,7).
* **Q3** (`Q3`, `Q3_ndvd`, `Q3_core`, `RQ3Final.lean`; new in version 1.5.0). Four distinct indices s1, s2, a, b; 3 divides v_s1 and v_s2 and v_a, v_b are coprime to 3 (so exactly two speeds are divisible by 3), and for s = s1 and s = s2: v_s is different from v_a + v_b and from |v_a - v_b|. This is the case q = 3 of the hypotheses of QGen, with the class hypothesis automatic. The statement is unconditional: the proof uses a three-runner lemma with the thresholds 1/5, 1/5 and 7/30 (`q3Mix3`, proved here from real-phase building blocks of an earlier module), not the published three-runner theorem at the threshold 1/4.
* **Supporting statements.** `window_lemma` (`RQWindow.lean`, any modulus q >= 2) and `lemmaC_real` (`RQLemmaC.lean`, q = 8); for R7: `r7CaseA` (`RSevenA.lean`) and `r7CaseB` (`RSevenB.lean`); for Q3: `q3Mix3` (`RQ3Mix.lean`).
* **Lean entry points and build facts.** The eight modules `RQWindow`, `RQThree`, `RQFour`, `RQLemmaC`, `RQGen`, `RQPigeon`, `RQT`, `RQG24` were built on 2026-11-12 in the development repository, one module at a time. A fresh review session re-elaborated each of the eight sources (exit status 0), printed `#print axioms` for 52 declarations (the exported theorems and lemmas of the eight modules, and three declarations they use from earlier modules), and compiled restatements of `window_lemma`, `P3`, `Q4`, `QGen`, `T`, `G24` with the distance written out as `|x - round x|`, each closed by `exact` from the theorem. The axioms are `propext`, `Classical.choice`, `Quot.sound` (a few arithmetic declarations use fewer; `cover4` uses none). No `sorry`, no `native_decide`. Review verdict: SOUND-WITH-CAVEATS. The builds are carried over to this archive and were not repeated for it. The trust base also includes the earlier modules of the archive on which these depend (the `RFive*` and `TPFour*` modules of versions 1.2.0 and 1.3.0), whose mathematics was not re-examined in this review.
* **Lean entry points and build facts for R7 and Q3 (version 1.5.0).** The seven modules `RSevenCore`, `RSevenA`, `RSevenB`, `RSevenFinal` (R7) and `RQ3Sweep`, `RQ3Mix`, `RQ3Final` (Q3) were built on 2026-11-12 in the development repository, one module at a time. A fresh review session re-elaborated each of the seven sources (exit status 0), printed `#print axioms` for every constant declared by them (51 on the R7 side, 44 on the Q3 side; the axioms are `propext`, `Classical.choice`, `Quot.sound`; no `ofReduceBool`), and compiled restatements of `R7_partial` and `Q3_ndvd` with the distance and the resonance clause written out, each closed from the theorem. No `sorry`, no `native_decide`. Review verdict: SOUND-WITH-CAVEATS. The builds are carried over to this archive and were not repeated for it. Packaging, stated plainly: the review was made on files in which two lemmas of the `RSeven*` modules were still named `caseA` and `caseB`, names that are also declared in `TPThreeA` and `NormalForm`, so that the `RSeven*` modules could not be imported together with the `RQ3*` modules. The two lemmas were renamed `r7CaseA` and `r7CaseB`; after the renaming `RSevenA`, `RSevenB` and `RSevenFinal` were rebuilt and a joint import of `RSevenFinal`, `RQ3Final` and earlier modules was elaborated with the standard axioms printed for twelve theorems; the renamed files were not reviewed again. The name `badSet` of `RQPigeon` is also declared in two modules of the development tree that are not in this archive, so `RQPigeon` and the family built on it cannot be imported together with those two. The library root file is not updated. The trust base of the seven modules includes the earlier `RFive*`, `TPFour*`, `TPThree*` and `RQ*` modules, and the generated data modules `TPFData` and `TPFCheck` (kernel-checked) that `TPThreeA` imports.
* **Labels.** The Lean statements are VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The written proofs below are a transcription of the Lean proofs; the text of this note has had no independent read, no blind read of the Part H kind and no human reader. The Lean theorems are the authority.
* **Text of the release.** Version 1.5.0 adds Lean formalizations, with the same setting and the same constant, of two further classes: (R7) exactly one speed is divisible by 7, and the other three speeds satisfy pattern (A) or pattern (B) above (theorems `R7A`, `R7B`, `R7_partial`); (Q3) exactly two speeds are divisible by 3 and neither of them equals the sum or the absolute difference of the other two (theorems `Q3`, `Q3_ndvd`, `Q3_core`; unconditional, through a mixed-threshold three-runner lemma). Both are special cases of the shifted lonely runner conjecture for four moving runners (five runners), proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379, version 1, Corollary 1.4 there; the numbering of the published version was not checked), after the reduction of Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2, Corollary 1.11 there); they are not new theorems. Not covered: three pairwise non-equivalent free speeds modulo 7, the excluded sub-case of pattern (B) (it contains (1,3,4,7)), and, for Q3, the resonant cases. The text of version 1.4.0 for the five classes of that version follows.

  Lean 4 formalizations (Mathlib, Lean 4.30.0; axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`) of five classes of speed vectors for which four pairwise distinct positive integer speeds and arbitrary real phases admit a real t with ||v_i t + phi_i|| >= 1/5 for all i: (P3) some q >= 2 divides exactly three of the speeds; (Q4) 4 divides two speeds, the other two are odd, and neither speed divisible by 4 equals the sum or the absolute difference of the two odd speeds; (QGen) the same with any q >= 4 in place of 4, the other two speeds being coprime to q and congruent up to sign modulo q; (T) some q >= 6 divides two speeds and the other two are coprime to q; (G24) two speeds are odd, one is 2 mod 4, one is 0 mod 4 and is not the sum or the absolute difference of the two odd speeds. None of these is a new theorem: all are special cases of the shifted lonely runner conjecture for four moving runners (five runners), proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379, version 1, Corollary 1.4 there; the numbering and the content of the published version were not checked). The prior art as we read it, the coverage of the speed vectors up to speed sum 195 (with exact counts), and the limits of the hypotheses are in the six caveats below. This archive does not contain a proof of the shifted theorem for four moving runners.

### Caveats that bind every use of this note

1. **Not a new theorem.** All seven classes (P3, Q4, QGen, T, G24 of version 1.4.0, and R7 and Q3 of version 1.5.0) are special cases of the shifted lonely runner conjecture for four moving runners (five runners), proved with computer assistance by Alcantara, Criado and Santos, arXiv:2506.13379 (version 1, Corollary 1.4 there; we read version 1 of that paper; the numbering and the content of the published version were not checked), after the reduction of Malikiosis, Santos and Schymura, arXiv:2411.06903 (version 2, Corollary 1.11 there). Their theorem covers all four distinct positive speeds and all real phases, with the constant 1/5.
2. **Prior art, as we read it.** (a) The class P3 is Proposition 2.9 of Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2; "Linearly-exponential checking is enough for the lonely runner conjecture and some of its variants") at four runners, for speed vectors of gcd 1; its three-runner instance is Proposition 4.6 of Cslovjecsek, Malikiosis, Naszodi and Schymura (arXiv:2009.12080). The vectors of T that have a witness q >= 7, q != 8 lie inside Proposition 6.5 of Malikiosis, Santos and Schymura (a pair of speeds whose gcd is odd and at least 5, or even and at least 10; the exact counts are in the census below). The class QGen with q >= 5 adds nothing beyond earlier results (the earlier note of this archive on a speed divisible by 5, the classes of Malikiosis, Santos and Schymura, and T). Primitive speed vectors with sum at least 196 are treated by Corollary 1.11 of Malikiosis, Santos and Schymura, and their Remark 1.12 records that the remaining finite family was settled by Alcantara, Criado and Santos (all numbers of that paper in this note are those of arXiv version 2). (b) The residue-shift and pigeonhole mechanism, with several runners not divisible by the modulus, is classical for zero phases (Barajas and Serra, Electron. J. Combin. 15 (2008), #R48, Section 3 and Lemmas 2, 4 and 9; Rosenfeld, arXiv:2509.14111, Lemma 5; Allikvere, arXiv:2609.02604, Lemma 4.6). A related device at zero phases, a time shift that fixes the runners whose speeds are multiples of its denominator and moves the others through equally spaced positions, is in Lemma 12 and Corollary 15 of Bohman, Holzman and Kleitman (Electron. J. Combin. 8 (2001), #R3), where it is used in an argument for five moving speeds. The merging of two runners of one class modulo plus-or-minus into a difference runner has a zero-phase prototype in Lemmas 4 and 9 of Barajas and Serra. The reduction with one runner not divisible by the modulus and real phases is in the literature (Proposition 4.6 of Cslovjecsek et al.; Proposition 2.9 of Malikiosis et al.). Judgement, not a proved statement: the extension of the pigeonhole count to real phases is routine given those papers, and we make no claim that it is new. (c) What we did not find in the texts read is a computation-free proof, for arbitrary real phases, of the classes with a divisible pair of gcd 4 (Q4), of gcd 6 or 8 (T), or of G24, nor a real-phase form of the window lemma (Theorem 2.3 below). "Computation-free" here means: no enumeration of speed vectors; one finite statement over Z/8 (64 pairs, Section 6) is checked by the kernel. This does not show that no such proof exists. For G24: the same parity pattern (the 2-adic valuations of the four speeds are 0, 0, 1 and at least 2) occurs at zero phases in a reduction that is stated, without its argument, in the four-page conference abstract of Barajas and Serra, "Distance graphs with maximum chromatic number" (a problem about distance graphs with zero phases); the full paper was not obtained and we make no statement about what it proves. (d) Read end to end (in the checks for this release, including a download session of 2026-11-12, or in earlier checks for this archive): Cslovjecsek, Malikiosis, Naszodi and Schymura (arXiv:2009.12080, version 2), Barajas and Serra (arXiv:0710.4495, "The lonely runner with seven runners"), the four-page conference abstract of Barajas and Serra, "Distance graphs with maximum chromatic number" (not the full paper), Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2; as a reading of its statements and arguments, its proofs were not re-verified and the results it cites from the geometry of numbers were not examined), Alcantara, Criado and Santos (version 1), Bohman, Holzman and Kleitman (the long case analyses were read in order, not verified), Beck, Hosten and Schymura (arXiv:1606.01783, version 4) and Henze and Malikiosis (arXiv:1609.01939, version 1). Read in all but about 40 lines: Blanco, Criado and Santos (arXiv:2603.24784, version 4). Read in part: Rifford (arXiv:2111.13688, version 2; 1,236 of 3,437 text lines: the introduction, the definitions and the proofs of the free-starting-positions theorem for at most four runners including the lonely one in Section 5; not read: the covering arguments for the other theorems, Section 6 and the appendices, where a keyword search for divisibility vocabulary found nothing), the survey of Perarnau and Serra, Rosenfeld (arXiv:2509.14111), Allikvere (arXiv:2609.02604), "Mixed thresholds in the LRC" (arXiv:2605.27941), Poliakova (arXiv:2609.23952); in the check made for this release, searched by keyword only (some of them were read more fully for other notes of this archive): further papers on the conjecture (Tao, Czerwinski, Giri-Kravitz, Bedert, Beck-Everett, Zhang and others). Not obtained (publisher access refused, no open copy found), so not read: the published version of Alcantara-Criado-Santos (we used arXiv version 1, the only version on arXiv); the journal versions of Malikiosis-Santos-Schymura; the full paper of Barajas and Serra, "Distance graphs with maximum chromatic number" (Discrete Math.); Renault (Discrete Math., 2004); Bienia et al. (1998); Cusick and Pomerance (1984). The notes of versions 1.2.0 to 1.3.1 list papers as not read that were read later (Beck-Hosten-Schymura, Rifford in part, Barajas-Serra in full); those lists are as of their versions and were not edited. (e) Our proofs are unrefereed and this comparison is limited to the texts named. (f) For the two classes added in version 1.5.0 (R7 and Q3) no further text was read: the reading of (a) to (e) is that of version 1.4.0, with the same lists of papers read, read in part and not obtained. We did not find these two classes, with real phases, stated or proved without a computer in the texts read for version 1.4.0; this does not show that no such statement or proof exists. At zero phases the case of exactly one speed divisible by 5 is known (Barajas and Serra, Section 3 of their paper); we make no statement about zero phases for the primes 7 and 3. For Q3 the hypotheses are the case q = 3 of the hypotheses of QGen; the proof here replaces the three-runner lemma used for QGen (Lemma 3.1) by a three-runner lemma with the thresholds 1/5, 1/5, 7/30, because for q = 3 the window 3/5 - 1/q is 4/15, smaller than the 3/10 that Lemma 4.8 delivers.
3. **Coverage, with exact counts (version 1.5.0).** The census below (COMPUTED, generator `code/rq-census/v2`) is a computation over the 2,133,561 primitive speed vectors (four distinct positive integers, gcd 1) with speed sum at most 195, the set enumerated by Alcantara, Criado and Santos. Of these, 2,002,342 lie in a class with a Lean proof in this archive (R5_core of version 1.3.0, P3, QGen, T, G24, R7, Q3). 131,219 vectors lie in none of these classes and are NOT covered (111,835 without and 19,384 with an additive resonance, see below); they include the tight vectors (1,2,3,4), (1,3,4,6), (1,3,4,7). The two new classes add 134,783 vectors to the 1,867,559 of version 1.4.0 (R7 alone adds 84,842, Q3 alone adds 74,729). The two classes of Malikiosis, Santos and Schymura as we read them (P3 on primitive vectors, and a pair of speeds with gcd odd at least 5 or even at least 10; 1,222,641 vectors together) are contained in the set of version 1.4.0, hence in the larger set. The count of version 1.4.0 (266,002 vectors in no class) is superseded by the count above. Primitive vectors with speed sum at least 196 are handled by Corollary 1.11 of Malikiosis, Santos and Schymura (arXiv version 2), which is not formalised here. This archive therefore does not contain a proof of the shifted theorem for four moving runners, by computation or otherwise.
4. **The hypotheses are limits of the method.** The non-resonance hypotheses (v_s different from v_a + v_b and |v_a - v_b|) and the class hypotheses are not shown to be necessary for the truth of the conclusion, which is a case of the theorem of Alcantara, Criado and Santos. The only information on them: the tight vectors (1,2,3,4) and (1,3,4,6) satisfy every hypothesis of G24 except the non-resonance clause (exact computation by the review session; for both the value 1/5 is attained). Distinct speeds are necessary in all seven statements (Section 11). The constant 1/5 is not claimed sharp for any of the seven classes. For the classes of version 1.5.0 the same remarks hold: the exclusion clause of pattern (B) of R7 and the non-resonance clause of Q3 are limits of the method, not shown to be necessary. The tight vector (1,3,4,7) violates only the exclusion clause of R7 (all other hypotheses hold for exactly two assignments of the roles, those that exchange b and c) and attains the value 1/5 (exact computation by the review session); (1,2,3,4) and (1,3,4,6) violate other hypotheses of R7 (no speed divisible by 7); for Q3, (1,3,4,6) violates only the non-resonance clause (the slow speed 3 equals |1 - 4|), and (1,2,3,4) and (1,3,4,7) have only one speed divisible by 3.
5. **Not claimed.** Not covered by R7: three pairwise non-equivalent free speeds modulo 7 (pattern (C)), and the excluded sub-case of pattern (B), which contains (1,3,4,7); not covered by Q3: the vectors with a slow speed equal to the sum or the absolute difference of the two others. These are not claimed in any form. The note of version 1.4.0 said that two further lemmas of the same method, a class with a divisor 3 conditional on the three-runner theorem and a partial class for one speed divisible by 7, were neither formalised nor claimed. In version 1.5.0 the classes Q3 (proved without that condition, through a mixed-threshold three-runner lemma) and R7 (patterns (A) and (B) only) are formalised; that sentence of 1.4.0 is superseded. Nothing is claimed for a prime p >= 11 with one speed divisible by p.
6. **Build scope.** No whole-library `lake build` was run. The modules were built one at a time and the axioms observed per module. The builds are carried over from the development repository and were not repeated for this archive. The Lean trust base includes the earlier `RFive*`, `TPFour*`, `TPThree*` and `RQ*` modules of this archive, whose mathematics was not re-examined for this release, and the generated data modules `TPFData` and `TPFCheck` imported by `TPThreeA`. Packaging limitations (the renaming of two lemmas after the review of the `RSeven*` modules, the name `badSet` declared also in two development modules that are not in this archive, the library root not updated) are stated in the status above and in `LEAN_MAP.md`.

### Census, version 1.5.0 (computed; generator in `code/rq-census/v2`)

Universe: 4-sets of distinct positive integers with gcd 1 and sum at most 195 (control: the count 2,133,561 equals the number of vectors in the enumeration of Alcantara, Criado and Santos). The program of version 1.4.0 was extended by two class predicates, R7 (the hypotheses of `R7_partial` for some assignment of the roles s, a, b, c) and Q3 (exactly two speeds divisible by 3, and non-resonance of each of them with respect to the two others). Controls: with R7 and Q3 switched off the program reproduces the counts of version 1.4.0 (1,867,559 vectors in a Lean class, 266,002 in no class, and the sizes of the classes R5, QGen, T, G24 and their "only" counts); with the exclusion clause of pattern (B) dropped (planted error) the class R7 grows from 576,799 to 589,579 vectors, the vector (1,3,4,7) enters R7, and the number of vectors in no class falls from 131,219 to 128,169, while (1,2,3,4) and (1,3,4,6) stay out. An independent Python implementation (permutations of the speeds, the definitions applied directly, resonance with an absolute value, the relation ~ by integer congruences) agrees with the Rust program on every number compared at sum at most 60 (total 15,576): the sizes and the "only" counts of the seven Lean classes, the numbers in a Lean class, in an MSS class and in no class, the numbers added by R7 and Q3, and the split of the vectors in no class by resonance and number of even speeds. No third implementation was run, and the Python implementation was not run at sum 195. The predicates are our reading of the Lean statements and of the hypotheses of the two classes of Malikiosis, Santos and Schymura (MSS29: three speeds with a common factor above 1; MSS65: two speeds with gcd odd and at least 5, or even and at least 10).

| Set of vectors | sum <= 195 | sum <= 60 |
|---|---|---|
| universe (primitive, distinct, positive) | 2,133,561 | 15,576 |
| R7 (`R7_partial`) | 576,799 | 3,787 |
| Q3 | 611,118 | 3,930 |
| in some Lean class of version 1.4.0 (union of R5_core, P3, QGen, T, G24) | 1,867,559 | 13,214 |
| in an MSS class (union of the two) | 1,222,641 | 7,227 |
| in R7 and in no Lean class of version 1.4.0 | 84,842 | 768 |
| in Q3 and in no Lean class of version 1.4.0 | 74,729 | 607 |
| in R7 or Q3 and in no Lean class of version 1.4.0 | 134,783 | 1,184 |
| in R7 and in Q3 | 162,666 | 889 |
| in some Lean class of the seven (version 1.4.0 classes, R7, Q3) | 2,002,342 | 14,398 |
| in a Lean class of the seven and in no MSS class | 779,701 | 7,171 |
| in an MSS class and in no Lean class of the seven | 0 | 0 |
| in no class (not covered) | 131,219 | 1,178 |

Vectors in exactly one of the seven Lean classes (in that class and in none of the other six; the MSS classes are ignored), sum <= 195: R5_core 166,804; P3 115,132; QGen 20,051; T 35,083; G24 56,758; R7 60,054; Q3 49,941 (sum <= 60: 1,910; 954; 181; 279; 527; 577; 416). Not covered, by additive resonance (some speed is the sum of two others, or two speeds have the same sum as the other two) and number of even speeds 0, 1, 2 (no vector has 3 or 4 even speeds): non-resonant 17,850; 69,964; 24,021, total 111,835; resonant 572; 11,157; 7,655, total 19,384 (sum <= 60: non-resonant 105; 422; 135; resonant 12; 281; 223). The tight vectors (1,2,3,4), (1,3,4,6), (1,3,4,7) are among the vectors not covered and belong to neither R7 nor Q3. The smallest vectors not covered, by speed sum: (1,2,3,4), (1,2,3,6), (1,2,3,7), (1,3,4,6), (1,2,3,9), (1,3,4,7), (1,2,6,7), (1,3,4,8), (1,2,3,11), (1,3,4,9). Counts are from a computation, not a proof, and depend on our reading of the hypotheses.

### Census of version 1.4.0 (superseded by the census of version 1.5.0 above; kept for reference; generator `code/rq-census`)

Universe: 4-sets of distinct positive integers with gcd 1 and sum at most 195 (control: the count 2,133,561 equals the number of vectors in the enumeration of Alcantara, Criado and Santos). Two independent implementations agree on every output line at sum at most 60 (total 15,576); no third implementation was run beyond that range. The predicates are our reading of the Lean statements and of the hypotheses of the two classes of Malikiosis, Santos and Schymura (class MSS29: three speeds with a common factor above 1; class MSS65: two speeds with gcd odd and at least 5, or even and at least 10).

| Set of vectors | sum <= 195 | sum <= 60 |
|---|---|---|
| universe (primitive, distinct, positive) | 2,133,561 | 15,576 |
| R5_core (some but not all speeds divisible by 5) | 1,237,736 | 8,675 |
| P3 | 750,712 | 4,657 |
| QGen (witness q >= 4) | 416,974 | 1,988 |
| T (witness q >= 6) | 500,937 | 1,905 |
| G24 | 423,532 | 3,230 |
| in some Lean class (union of the five) | 1,867,559 | 13,214 |
| MSS29 (equals P3 as a set) | 750,712 | 4,657 |
| MSS65 | 811,273 | 3,762 |
| in an MSS class (union of the two) | 1,222,641 | 7,227 |
| in a Lean class or an MSS class | 1,867,559 | 13,214 |
| in an MSS class and in no Lean class | 0 | 0 |
| in a Lean class and in no MSS class | 644,918 | 5,987 |
| in a Lean class, in no MSS class, and not in R5_core | 179,090 | 1,681 |
| in no class (not covered) | 266,002 | 2,362 |

Further counts (sum <= 195): Q4, that is QGen with a witness q = 4: 188,383; QGen with a witness q >= 5: 270,708 (the two sets overlap); T with a witness q >= 7, q != 8: 447,075, all of them in MSS65; vectors of T in neither MSS class: 43,514, of which 19,973 have the divisible pair of gcd 6 and 23,541 of gcd 8 (no other gcd occurs). Not covered, by resonance and number of even speeds: non-resonant 237,488, resonant 28,514; with 0, 1, 2 even speeds: 38,944, 165,693, 61,365. Controls: dropping the gcd condition changes the universe to 2,285,448; replacing q >= 6 by q >= 5 in T gives 727,225 vectors instead of 500,937. The smallest not covered vectors by speed sum: (1,2,3,4), (1,2,3,6), (1,2,3,7), (1,3,4,6), (1,2,3,9), (1,3,4,7). Counts are from a computation, not a proof, and depend on our reading of the hypotheses of the two classes of Malikiosis, Santos and Schymura.

### Labels and provenance

The statements of `P3`, `Q4`, `QGen`, `T`, `G24`, `window_lemma`, `lemmaC_real` in Lean are VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The written proof below follows the Lean proof, declaration by declaration; each lemma names the Lean declaration it corresponds to. Where a proof is given only in outline the text says "sketch; the Lean declaration is the proof". Where the Lean proof and earlier informal drafts differ, the Lean proof is followed; in particular the Lean proof of T uses no measure count (Section 7).

Comments in the Lean modules of this release cite development files by their development names. The file cited in the headers of the eight `RQ*` modules as the paper proof is the informal draft of the argument written below; it is not archived and is replaced by this note. The sections of the draft named in the headers correspond to this note as follows: "Lemma B (window)" is Theorem 2.3; "P3" is Theorem 3.2; "Theorem Q4" is Theorem 4.10 and, for a general modulus, Theorem 4.9; "Lemma C" is Theorem 6.3; "exact residue counts" and the "different classes" clause of "Theorem T" are Section 5; "Theorem T" is Theorem 8.1; "Theorem G24" is Theorem 9.7. The headers of the seven modules of version 1.5.0 cite, in the same way, a section of an informal draft: "Theorem R7-partial" (proof sketch) in `RSevenCore` corresponds to Lemmas 12.1 to 12.6 of this note, in `RSevenA` ("case (A)") to Theorem 12.7, in `RSevenB` ("case (B)") to Lemmas 12.8 to 12.11 and Theorem 12.12, and in `RSevenFinal` to Lemmas 12.13 to 12.15 and Theorems 12.16 to 12.18; "Theorem Q3" in `RQ3Sweep`, `RQ3Mix` and `RQ3Final` is Section 13, with Theorem 13.14. The headers of `RQ3Sweep` and `RQ3Mix` also cite two reports of the building sessions (a costing of the three-runner step and a numerical probe of the case of the speeds (1,2,3)); they are not archived, and the arithmetic of the probe for (1,2,3) is redone by hand in Lemma 13.6.

The results were obtained with the assistance of an AI system (Claude, Anthropic). The questions and research directions came from the author. The written proofs and the Lean sources were produced by the AI system; the Lean theorems are checked by the Lean kernel, the Lean statements and sources were read or re-run by a further session of the same system, and the informal draft from which the written proofs were transcribed was checked by computation and read by further sessions; the text of this note has not had an independent read. The author is responsible for all claims.

## Conceptual abstract

Write the time as t = (j + x)/q, with j a residue modulo q and x a real offset. A speed divisible by q sees only the offset x. A speed coprime to q is bad at (j + x)/q only for j in a set of residues that, in a suitable coordinate, is an interval of length about 2q/5, so it blocks at most ceil(2q/5) residues. For q >= 7 and q != 8 two such runners cannot block all q residues. The runners divisible by q are handled by a three-runner lemma applied to the offset. For q = 4, 6, 8, two runners in one class modulo plus-or-minus, with speeds va and vb, are merged: in the coordinate z = va j their blocked intervals have centres q ||D x + sigma|| apart, D = (va -/+ vb)/q, and a window condition on x leaves a free residue. That condition is a condition on one extra runner of speed |D|. Speeds 2 mod 4 are handled by parity.

Added in version 1.5.0. For q = 7 with one slow runner and three free runners, the same coordinate z = v j gives each free runner a blocked interval of residues, and the question is whether the three intervals can cover all seven residues. If the three runners lie in one class modulo plus-or-minus, either two of them have exactly coinciding centres (then they block the same residues and counting leaves a free one) or the offset can be chosen so that all three centres are close and lie in one window of seven integers. If two lie in one class and the third in another, the offset makes the two blocked intervals fit in a window of five or six integers, and a statement over Z/7 shows that the third runner cannot block every free residue left, except in one resonant configuration that the hypothesis excludes. For q = 3, the window condition on the difference runner is the one of QGen with the smaller bound 4/15; it is met by applying a three-runner lemma with the thresholds 1/5, 1/5 and 7/30. That lemma holds for all real phases: for every triple of speeds other than a multiple of (1,2,3) it is a weakening of three-runner results at the threshold 1/4 of an earlier module, and for (1,2,3), where the sweep at 1/4 fails, the same sweep with the lowered thresholds succeeds.

## Outline

* Time written as t = (j + x)/q; three imported facts; one free runner (Sections 0 and 1).
* The window lemma for two free runners of one class (Section 2).
* A three-runner lemma and Theorem P3 (Section 3).
* The reduction of two free runners of one class to a difference runner; Theorems QGen and Q4 (Section 4).
* The residue pigeonhole for two free runners, q >= 7, q != 8 (Section 5).
* Lemma C for q = 8 and two free runners of different classes (Section 6).
* An explicit perturbation argument for resonant same-class pairs at q = 6 and q = 8 (Section 7).
* Theorem T (Section 8) and Theorem G24 (Section 9).
* One speed divisible by 7: tools for a general modulus, pattern (A), pattern (B), assembly of R7 (Section 12).
* Two speeds divisible by 3: the mixed-threshold sweep, the mixed three-runner lemma, Theorem Q3 (Section 13).

## 0. Conventions and imported facts

||y|| denotes `tpDist y = |y - round y|` (`tpDist`, `TPSmall.lean`). For a natural number v and real phi, t, the runner (v, phi) is good at t if `GoodR v phi t`, that is 1/5 <= ||v t + phi|| (`GoodR`, `RFiveBase.lean`); it is bad otherwise. A speed v is called free (for a modulus q) if q does not divide v, and slow if q divides v. Throughout, v is a function `Fin 4 -> N` with positive values, injective, and phi a function `Fin 4 -> R`. For q a natural number and j an integer, x real, "time (j + x)/q" is the real number (j + x)/q.

The proofs use five facts proved in earlier modules of this archive. Their proofs are not repeated here: they are in the Lean modules named, and for F3, F4 and F5 they are also written out in `paper/shifted-real-four/NOTE.md` (Lemmas 3.1, 3.3 and 2.5). For each fact the Lean name and file are given.

* **F1.** ||y + k|| = ||y|| for every real y and integer k. Lean: `tpDist_add_int` (`TPFourBridge.lean`).
* **F2.** If ||y|| < 1/5 then some integer n has |y - n| < 1/5. Lean: `exists_near_of_not_good` (`TPFourBridge.lean`; n = round y).
* **F3 (perturbation).** For every real y there is a real delta with |delta| <= 1/5 and ||y + delta|| >= 1/5. Lean: `exists_perturb` (`TPFourWindow.lean`). This is Lemma 3.1 of the note `paper/shifted-real-four/NOTE.md`.
* **F4 (coset).** Let D be a nonzero integer, w a natural number such that D does not divide w, and sigma, phi real. Then some integer k has ||w (k - sigma)/D + phi|| >= 1/5. Lean: `coset_branchR` (D > 0) and `coset_branchR_ne` (D != 0), `RFiveWindow.lean`. This is Lemma 3.3 of the same note.
* **F5 (Lemma S).** A finite set of at most three runners with positive pairwise distinct speeds and arbitrary real phases has a common good time. Lean: `lemSR` (`RFiveLemS.lean`). This is Lemma 2.5 of the same note.

## 1. The time scale t = (j + x)/q

**Lemma 1.1 (slow runner).** Let q >= 1 and u be natural numbers, phi and x real, j an integer. Then the runner (q u, phi) is good at (j + x)/q iff the runner (u, phi) is good at x. Lean: `goodR_mulq` (`RQWindow.lean`).
Proof. q u (j + x)/q + phi = (u x + phi) + u j, and u j is an integer; apply F1.

**Lemma 1.2 (a bad runner gives an integer near a centre).** Let q >= 1, v natural, phi, x real, j and n integers with |v (j + x)/q + phi - n| < 1/5. Then the integer m = v j - q n satisfies |m - c| < q/5, where c = -(v x + q phi). Lean: `near_to_int` (`RQWindow.lean`).
Proof. m - c = q (v (j + x)/q + phi - n); multiply the hypothesis by q.
Reading. By F2, a runner (v, phi) is bad at (j + x)/q only if there is an integer n with v j - q n in the open interval (c - q/5, c + q/5) of length 2q/5. This is the coordinate used below: z = v j modulo q.

**Lemma 1.3 (one free runner).** Let q >= 1, v a natural number not divisible by q, phi and x real. Then some integer j makes the runner (v, phi) good at (j + x)/q. Lean: `exists_free_j` (`RQWindow.lean`).
Proof. F4 with D = q, w = v, sigma = -x gives an integer k with ||v (k + x)/q + phi|| >= 1/5; take j = k.

## 2. The window lemma

**Lemma 2.1 (two centres).** Let q be a natural number and u, w real with |u - w| <= 3q/5 - 1. Then there is an integer N such that every integer m with |m - u| < q/5 or |m - w| < q/5 satisfies N < m < N + q. Lean: `window_gap` (`RQWindow.lean`).
Proof. Say u <= w (the other case is symmetric). Put N = floor(u - q/5). Every such m has m > u - q/5 >= N. Also m < w + q/5 <= u + 4q/5 - 1 < N + q, since N > u - q/5 - 1.

**Lemma 2.2 (no multiple of q strictly between 0 and q).** For integers q > 0 and k, the conditions 0 < q k and q k < q cannot both hold. Lean: `no_mult_between` (`RQWindow.lean`).

**Theorem 2.3 (window lemma).** Let q >= 2, va and vb natural numbers with va coprime to q, eps = 1 or -1, D an integer with va - eps vb = q D, phi_a, phi_b, x real, and n an integer with |D x + (phi_a - eps phi_b) - n| <= 3/5 - 1/q. Then some integer j makes both runners (va, phi_a) and (vb, phi_b) good at (j + x)/q. Lean: `window_lemma` (`RQWindow.lean`).
Proof. Put u = -(va x + q phi_a) and w = -eps (vb x + q phi_b) - q n. Since va - eps vb = q D, u - w = -q (D x + phi_a - eps phi_b - n), so |u - w| <= q (3/5 - 1/q) = 3q/5 - 1. Lemma 2.1 gives N. Since va is coprime to q there are integers A, B with va A + q B = 1; put j = N A. Then va j - N = q (-N B).
Runner a. If it were bad at (j + x)/q, F2 gives an integer n_1 with |va (j + x)/q + phi_a - n_1| < 1/5, and Lemma 1.2 gives that m = va j - q n_1 has |m - u| < q/5. By Lemma 2.1, N < m < N + q. But m - N = q (-N B - n_1) is a multiple of q, contradicting Lemma 2.2.
Runner b. If it were bad, F2 gives n_2 with |vb (j + x)/q + phi_b - n_2| < 1/5, and Lemma 1.2 gives that m' = vb j - q n_2 has |m' + (vb x + q phi_b)| < q/5. Put m'' = eps m' - q n. Since |eps| = 1, |m'' - w| = |m' + (vb x + q phi_b)| < q/5. By Lemma 2.1, N < m'' < N + q. Using va - eps vb = q D, m'' - N = q (-N B - D N A - eps n_2 - n), a multiple of q, again contradicting Lemma 2.2.
Reading. In the coordinate z = va j (modulo q), the residues blocked by a lie in an interval of integers around u, those blocked by b in an interval around w, and the two centres are q ||D x + sigma|| apart (sigma = phi_a - eps phi_b), so both fit in the q - 1 integers strictly between N and N + q. The residue N is free. Only the coprimality of va is used.

## 3. Three runners and Theorem P3

**Lemma 3.1 (three runners).** Let a, b, c be pairwise distinct positive natural numbers and phi_a, phi_b, phi_c real. Then some real x makes the runners (a, phi_a), (b, phi_b), (c, phi_c) all good. Lean: `lemSR3` (`RQThree.lean`).
Proof. F5 applied to the three runners, indexed by {0,1,2}.

**Theorem 3.2 (P3).** Let v be as in Section 0, q >= 2, z an index with q not dividing v_z and q dividing v_i for every i different from z, and phi real. Then some t is good for all four runners. Lean: `P3` (`RQThree.lean`).
Proof. For i different from z put u_i = v_i / q (exact division). These are positive, and pairwise distinct because v is injective. F5 applied to the three runners (u_i, phi_i) gives a real x. Lemma 1.3 gives an integer j with (v_z, phi_z) good at (j + x)/q. For i different from z, v_i = q u_i, so Lemma 1.1 turns the goodness of (u_i, phi_i) at x into the goodness of (v_i, phi_i) at (j + x)/q. Take t = (j + x)/q.

## 4. Two free runners of one class: the difference runner; Theorems QGen and Q4

In this section s1, s2, a, b are four pairwise distinct indices in Fin 4 (six inequalities), "slow" speeds are v_s1 and v_s2, and the free runners are a and b.

**Lemma 4.1 (cover).** Four pairwise distinct indices s1, s2, a, b in Fin 4 exhaust Fin 4. Lean: `cover4` (`RQFour.lean`; by `decide`, no axioms). Sketch; the Lean declaration is the proof: four distinct elements of a four-element set exhaust it.

**Lemma 4.2 (assembly).** Let q >= 1, v_s1 = q u_1, v_s2 = q u_2, x real, j integer. If (u_1, phi_s1) and (u_2, phi_s2) are good at x, and (v_a, phi_a), (v_b, phi_b) are good at (j + x)/q, then (j + x)/q is good for all four runners. Lean: `assemble4` (`RQGen.lean`).
Proof. Lemma 4.1 and Lemma 1.1.

**Lemma 4.3 (window and assembly).** Under the hypotheses of Lemma 4.2 on the slow runners, and with the hypotheses of Theorem 2.3 on a and b (q >= 2, va coprime to q, eps, D, and |D x + (phi_a - eps phi_b) - n| <= 3/5 - 1/q), some time is good for all four runners. Lean: `finish_window` (`RQGen.lean`). Proof. Theorem 2.3 and Lemma 4.2.

**Lemma 4.4 (class).** If q divides v_a - v_b or v_a + v_b then there are eps = +-1 and an integer D with v_a - eps v_b = q D. Lean: `eps_Dq` (`RQGen.lean`). Proof: if q divides v_a - v_b take eps = 1 and D = (v_a - v_b)/q; if q divides v_a + v_b take eps = -1 and D = (v_a + v_b)/q. For q = 4 and v_a, v_b odd the hypothesis is automatic: if v_a and v_b are congruent mod 4 take eps = 1, otherwise their sum is divisible by 4 and eps = -1. Lean: `eps_D4` (`RQFour.lean`).

**Lemma 4.5 (D is nonzero).** If v_a and v_b are positive and different, and v_a - eps v_b = q D, then D != 0. Lean: `D_neq` (`RQGen.lean`), `D_ne4` (`RQFour.lean`, q = 4). Proof. D = 0 would give v_a = eps v_b, impossible for eps = 1 (v_a != v_b) and for eps = -1 (positivity).
This is the place where positivity and distinctness of v_a and v_b are used.

**Lemma 4.6 (non-resonance).** Let v_s = q u and D with |D| = u and v_a - eps v_b = q D. Then v_s = v_a + v_b, or v_a = v_b + v_s, or v_b = v_a + v_s. Lean: `resonance_of` (`RQGen.lean`); the q = 4 form, with the hypothesis 4 divides v_s, the three inequalities, and the conclusion |D| != v_s / 4, is `nonres4` (`RQFour.lean`). Positivity of u: `pos_of_mul_eq` (`RQGen.lean`).
Proof. D = u or D = -u, eps = 1 or -1: the four sign cases give v_a - v_b = v_s, v_a - v_b = -v_s, v_a + v_b = v_s, v_a + v_b = -v_s, that is the three alternatives (in the last case v_a + v_b + v_s = 0, so all three are 0 and v_s = v_a + v_b holds).

**Lemma 4.7 (sign and half shift).** (i) ||-y|| = ||y|| (`tpDist_neg`). (ii) If ||y + 1/2|| >= 1/5 then some integer n has |y - n| <= 3/10 (`exists_int_of_far`). Both in `RQWindow.lean`.
Proof of (i). Sketch; the Lean declaration is the proof: it shows ||-y|| <= ||y|| from the minimality of the nearest-integer distance (`round_le`) applied to -round(y), and the reverse inequality by applying this to -y.
Proof of (ii). Put r = round(y + 1/2) and d = y + 1/2 - r, so |d| <= 1/2 and, by hypothesis, |d| >= 1/5. If d >= 0 then y - r = d - 1/2 lies in [-3/10, 0]; if d < 0 then y - (r - 1) = d + 1/2 lies in (0, 3/10].

**Lemma 4.8 (offset for the slow runners and the window).** Let u_1, u_2 be positive and different, D a nonzero integer with u_1 != |D| and u_2 != |D|, and phi_1, phi_2, sigma real. Then there are a real x and an integer n such that (u_1, phi_1) and (u_2, phi_2) are good at x and |D x + sigma - n| <= 3/10. Lean: `slow_window` (`RQGen.lean`).
Proof. If D > 0 apply Lemma 3.1 to the speeds u_1, u_2, |D| (positive and pairwise distinct) with phases phi_1, phi_2, sigma + 1/2; if D < 0 use the phase -(sigma + 1/2). The goodness of the third runner at x says ||D x + sigma + 1/2|| >= 1/5 (using ||-y|| = ||y|| when D < 0). By Lemma 4.7 (ii), |D x + sigma - n| <= 3/10 for some integer n.

**Theorem 4.9 (QGen).** Let v, s1, s2, a, b be as above, q >= 4, q dividing v_s1 and v_s2, v_a and v_b coprime to q, q dividing v_a - v_b or v_a + v_b, and for s = s1 and s = s2: v_s != v_a + v_b, v_a != v_b + v_s, v_b != v_a + v_s. Then for every real phi some t is good for all four runners. Lean: `QGen` (`RQGen.lean`); the core with the non-resonance written as u_i != |D| is `QGen_core` (`RQGen.lean`).
Proof. Write v_s1 = q u_1, v_s2 = q u_2 (positive by `pos_of_mul_eq`, different because v is injective). Lemma 4.4 gives eps and D, Lemma 4.5 gives D != 0, and Lemma 4.6 turns the non-resonance hypotheses into u_i != |D|. Lemma 4.8 with sigma = phi_a - eps phi_b gives x and n with both slow runners good and |D x + sigma - n| <= 3/10. Since q >= 4, 1/q <= 1/4 and 3/10 <= 3/5 - 1/q. Lemma 4.3 finishes. (The hypothesis "v_b coprime to q" is carried but not used: it follows from the class relation. This is the linter warning on `hb` in `RQGen.lean`.)
Where q >= 4 is used: only in 3/10 <= 3/5 - 1/q; for q = 3 the window 3/5 - 1/q = 4/15 is smaller than 3/10.

**Theorem 4.10 (Q4).** The case q = 4 of Theorem 4.9, with "coprime to 4" written as "odd" and the class hypothesis dropped (it is automatic by Lemma 4.4). Lean: `Q4` (`RQFour.lean`), proved directly, with `cop4` (odd implies coprime to 4), `eps_D4`, `D_ne4`, `nonres4`, `cover4` and the same steps as in Theorem 4.9 with q = 4 and window 3/10 <= 7/20. Proof. As for Theorem 4.9.

## 5. The residue pigeonhole for two free runners

**Lemma 5.1 (two runners).** Two runners with different positive speeds and arbitrary real phases have a common good time. Lean: `lemSR2` (`RQPigeon.lean`). Proof. F5.

**Definition.** For q, v natural and phi, x real, `badSet q v phi x` is the set of j in {0, ..., q - 1} such that the runner (v, phi) is bad at (j + x)/q. Lean: `badSet` (`RQPigeon.lean`), with `mem_badSet`.

**Lemma 5.2 (size of the bad set).** Let q >= 1 and v coprime to q. Then |badSet q v phi x| <= (2q - 1)/5 + 1 (division of natural numbers, that is floor((2q - 1)/5) + 1). Lean: `card_bad_le` (`RQPigeon.lean`).
Proof. Put c = -(v x + q phi) and N = floor(c - q/5). Let j be in the bad set. By F2 and Lemma 1.2 there is an integer n with |m - c| < q/5, m = v j - q n. Then N < m, and r = m - N - 1 satisfies 0 <= r and 5 r < 2q, that is r <= (2q - 1)/5. Also v j - (N + 1) = r + q n, so the residue of v j - (N + 1) modulo q equals r and lies in {0, ..., (2q - 1)/5}. The map j -> (v j - (N + 1)) mod q on the bad set is injective: equal residues give q dividing v (k - j), hence q dividing k - j since v is coprime to q, hence k = j because |k - j| < q (Lemma 2.2). So the bad set has at most (2q - 1)/5 + 1 elements.

**Theorem 5.3 (pigeonhole).** Let q >= 7, q != 8, and va, vb coprime to q (no condition on their classes). For every x there is an integer j such that both (va, phi_a) and (vb, phi_b) are good at (j + x)/q. Lean: `exists_two_good` (`RQPigeon.lean`).
Proof. Otherwise every j in {0, ..., q - 1} is in one of the two bad sets, so q <= 2 ((2q - 1)/5 + 1) by Lemma 5.2. This is false for q = 7 (6 < 7), for q = 9 (8 < 9) and for every q >= 9, since 2 ((2q - 1)/5 + 1) <= (4q + 8)/5 < q iff q > 8. It does not give a contradiction for q = 6 (6 <= 6) and q = 8 (8 <= 8), which is why those two moduli are treated separately.

## 6. Lemma C: modulus 8, two free runners of different classes

**Definition.** `blk8 s` = {s, s + 1, s + 2, s + 3} in Z/8 (four consecutive residues). Lean: `blk8` (`RQLemmaC.lean`).

**Lemma 6.1 (finite statement).** For mu = 3 and for mu = 5: for all s, t in Z/8 there is z in Z/8 with z not in `blk8 s` and mu z not in `blk8 t`. Lean: `lemmaC3`, `lemmaC5` (`RQLemmaC.lean`), each proved by kernel `decide` (64 pairs). Negative controls: for mu = 1 and for mu = 7 the corresponding statement is false (`lemmaC1_covers`, `lemmaC7_covers`).
Reading. In the coordinate z = va j modulo 8, the runner a blocks at most four consecutive residues and b blocks a set of the form mu^(-1) times four consecutive residues, mu = 3 or 5 (mu^(-1) = mu modulo 8); for these two multipliers two such sets never cover Z/8.

**Lemma 6.2 (four consecutive residues).** For real c and integer m with |m - c| < 8/5, the residue of m modulo 8 lies in `blk8 (floor(c - 8/5) + 1)`. Lean: `mem_blk8_of_near` (`RQLemmaC.lean`).
Proof. With N = floor(c - 8/5): m > c - 8/5 >= N gives m >= N + 1, and m < c + 8/5 < N + 1 + 16/5 gives m <= N + 4.

**Theorem 6.3 (Lemma C).** Let va be coprime to 8, mu = 3 or 5, vb congruent to mu va modulo 8, and phi_a, phi_b, x real. Then some integer j makes both runners good at (j + x)/8, for every x. Lean: `lemmaC_real` (`RQLemmaC.lean`).
Proof. Let c_a = -(va x + 8 phi_a), c_b = -(vb x + 8 phi_b), s = floor(c_a - 8/5) + 1 and t = floor(c_b - 8/5) + 1. Lemma 6.1 gives z in Z/8 with z not in `blk8 s` and mu z not in `blk8 t`. Let A be an inverse of va modulo 8 (va is coprime to 8) and j = A times the representative of z in {0, ..., 7}; then va j is congruent to z. If a were bad, F2 and Lemma 1.2 give n_1 with m = va j - 8 n_1, |m - c_a| < 8/5; by Lemma 6.2, z (the residue of m) is in `blk8 s`, a contradiction. If b were bad, we get n_2 with m' = vb j - 8 n_2, |m' - c_b| < 8/5, whose residue is vb j = mu va j = mu z; by Lemma 6.2, mu z is in `blk8 t`, a contradiction.

## 7. Resonant pairs of one class at q = 6 and q = 8: an explicit perturbation

The inputs are F1, F3, F4 and the results of Section 4. The case concerns a pair a, b of one class modulo q (v_a - eps v_b = q D) in which one slow speed satisfies u_i = |D| (a resonance), so that Lemma 4.8 does not apply. The Lean proof does not use a measure count.

**Lemma 7.1.** ||y|| <= ||y + e|| + |e| for real y, e. Lean: `tpDist_perturb` (`RQT.lean`). Sketch; the Lean declaration is the proof: ||y|| <= |y - round(y + e)| <= |y + e - round(y + e)| + |e|, by minimality of the nearest integer and the triangle inequality.

**Lemma 7.2.** If c = 3/10 or c = -3/10 and d is an integer, then |c + d| >= 3/10. Lean: `abs_ge_of_int` (`RQT.lean`). Sketch; the Lean declaration is the proof: for c = 3/10, d >= 0 gives c + d >= 3/10 and d <= -1 gives |c + d| >= 7/10; the case c = -3/10 is symmetric.

**Lemma 7.3 (shift away from the integers).** For every real u there is a real r with |r| <= 3/10 and ||u + r|| >= 3/10. Lean: `exists_shift` (`RQT.lean`).
Proof. If ||u|| >= 3/10 take r = 0. Otherwise u - round(u) lies in (-3/10, 3/10); if it is >= 0 take r = 3/10 - (u - round u), else r = -3/10 - (u - round u). Then u + r = round(u) +- 3/10, and Lemma 7.2 gives ||u + r|| >= 3/10.

**Lemma 7.4 (resonant offset, D > 0).** Let d >= 1 and u_2 >= 1 be natural numbers with u_2 != d, and phi_1, phi_2, sigma real. Then there are a real x and an integer n such that (d, phi_1) and (u_2, phi_2) are good at x and |d x + sigma - n| <= 2/5. Lean: `resonant_x_pos` (`RQT.lean`).
Proof. Lemma 7.3 applied to u = phi_1 - sigma gives r with |r| <= 3/10 and ||(-sigma + r) + phi_1|| >= 3/10. Case 1: d divides u_2. Write u_2 = d t. Since u_2 >= 1, t >= 1, and t != 1 since u_2 != d; so t >= 2. F3 applied to t(-sigma + r) + phi_2 gives delta, |delta| <= 1/5. Put x = ((-sigma + r) + delta/t)/d and n = 0. Then (a) d x + phi_1 = ((-sigma + r) + phi_1) + delta/t, with |delta/t| <= 1/10, so by Lemma 7.1 ||d x + phi_1|| >= 3/10 - 1/10 = 1/5; (b) u_2 x + phi_2 = (t(-sigma + r) + phi_2) + delta, good by the choice of delta; (c) d x + sigma = r + delta/t, of absolute value at most 3/10 + 1/10 = 2/5. Case 2: d does not divide u_2. F4 (with sigma replaced by -(-sigma + r)) gives an integer k with (u_2, phi_2) good at x = (k + (-sigma + r))/d. Then d x + phi_1 = ((-sigma + r) + phi_1) + k, so ||d x + phi_1|| >= 3/10 by F1, and d x + sigma - k = r, of absolute value at most 3/10, so n = k works.

**Lemma 7.5 (resonant offset, D != 0).** Let D be a nonzero integer, u_2 >= 1 with u_2 != |D|, phi_1, phi_2, sigma real. Then there are x and n with (|D|, phi_1) and (u_2, phi_2) good at x and |D x + sigma - n| <= 2/5. Lean: `resonant_x` (`RQT.lean`). Proof. For D > 0 this is Lemma 7.4. For D < 0 apply Lemma 7.4 with d = |D| and sigma replaced by -sigma, and replace n by -n.

**Theorem 7.6 (same class, q >= 5).** Let v, s1, s2, a, b be as in Section 4, q >= 5, v_s1 = q u_1, v_s2 = q u_2, v_a coprime to q, eps = +-1 and D with v_a - eps v_b = q D. Then for every real phi some t is good for all four runners. There is no non-resonance hypothesis. Lean: `T_same` (`RQT.lean`).
Proof. D != 0 (Lemma 4.5); u_1, u_2 are positive and different. If u_1 = |D| then u_2 != |D|; Lemma 7.5 (with u_2, phi_s1, phi_s2, sigma = phi_a - eps phi_b) gives x and n with (u_1, phi_s1) and (u_2, phi_s2) good at x and |D x + sigma - n| <= 2/5. Since q >= 5, 2/5 <= 3/5 - 1/q, and Lemma 4.3 finishes. If u_2 = |D| the same with the roles of the slow runners exchanged. If neither equals |D|, this is `QGen_core` (Theorem 4.9).

## 8. Theorem T

**Theorem 8.1 (T).** Let v, s1, s2, a, b be as in Section 4, q >= 6, q dividing v_s1 and v_s2, v_a and v_b coprime to q, phi real. Then some t is good for all four runners. Lean: `T` (`RQT.lean`).
Proof. Write v_s1 = q u_1, v_s2 = q u_2 (positive, different). Three cases.
(a) q >= 7 and q != 8. Lemma 5.1 gives x with the slow runners good at x; Theorem 5.3 gives j with a and b good at (j + x)/q. Lemma 4.2 finishes. (Here a and b may be in any classes.)
(b) q = 6 or q = 8, and q divides v_a - v_b or v_a + v_b. Lemma 4.4 gives eps, D, and Theorem 7.6 finishes (q >= 5).
(c) q = 6 or q = 8, and q divides neither v_a - v_b nor v_a + v_b.
 For q = 6: v_a and v_b are coprime to 6, so not divisible by 2 or 3, so each is 1 or 5 modulo 6; in each of the four combinations 6 divides v_a - v_b or v_a + v_b. So case (c) does not occur for q = 6. Lean: the branch `exfalso` of `T` proves exactly this disjunction (it is a proof of the class disjunction from coprimality, not an inconsistent-hypotheses argument).
 For q = 8: v_a and v_b are odd, so each is 1, 3, 5 or 7 modulo 8. Since 8 divides neither v_a - v_b nor v_a + v_b, v_b is congruent to 3 v_a or 5 v_a modulo 8 (check of the 16 residue pairs, by `omega`: if v_a is 1, v_b is 3 or 5; if v_a is 3, v_b is 1 or 7; if v_a is 5, v_b is 1 or 7; if v_a is 7, v_b is 3 or 5). Lemma 5.1 gives x for the slow runners, Theorem 6.3 gives j for a and b at (j + x)/8, and Lemma 4.2 finishes.
Remark. The pigeonhole of Theorem 5.3 already covers q = 7, 9 and every q >= 10 for all classes. Only q = 6 (always one class) and q = 8 (same class) need Section 7. Earlier informal drafts routed same-class resonant pairs through a measure count and listed more moduli; the Lean proof is Sections 5 to 7, with no measure theory.

## 9. Theorem G24

In this section a, b, e, s are four pairwise distinct indices; v_a, v_b are odd, v_e is 2 mod 4, v_s is 0 mod 4.

**Lemma 9.1 (a narrower gap).** Let u, w be real with |u - w| <= 2/5. Then there is an integer N such that every integer m with |m - u| < 4/5 or |m - w| < 4/5 satisfies N < m < N + 3. Lean: `window_gap4` (`RQG24.lean`).
Proof. As Lemma 2.1: with u <= w, N = floor(u - 4/5); then m > N and m < w + 4/5 <= u + 6/5 < N + 3.

**Lemma 9.2 (the runner e sees only the parity of j).** Let v_e = 4k + 2, phi, x real, j an integer. Then there is an integer z with v_e (j + x)/4 + phi = (v_e x/4 + phi) + (j mod 2)/2 + z. Lean: `e_val` (`RQG24.lean`). Proof. v_e j/4 = k j + j/2 and j = (j mod 2) + 2 (j div 2); take z = k j + (j div 2).

**Lemma 9.3 (half shift).** For every real y, ||y|| >= 1/5 or ||y + 1/2|| >= 1/5. Lean: `not_both_near` (`RQG24.lean`).
Proof. Otherwise there are integers n, n' with |y - n| < 1/5 and |y + 1/2 - n'| < 1/5 (F2); then 0 < n' - n < 1, which is impossible.

**Lemma 9.4 (allowed parity).** For v_e = 2 mod 4 and real phi, x there is p in {0, 1} such that the runner (v_e, phi) is good at (j + x)/4 for every integer j with j mod 2 = p. Lean: `parity_ok` (`RQG24.lean`). Proof. Lemma 9.3 with y = v_e x/4 + phi, and Lemma 9.2 with F1: the runner is at y or y + 1/2 modulo 1 according to the parity of j.

**Lemma 9.5 (offset with a tight window).** Let D be a nonzero integer, w >= 1 a natural number with "D does not divide w, or 2|D| <= w", and sigma, phi_d real. Then there are a real x and an integer m with |D x + sigma - m| <= 1/10 and ||w x + phi_d|| >= 1/5. Lean: `lemma4R_tight_pos` (D > 0) and `lemma4R_tight` (D != 0), `RQG24.lean`.
Proof. For D < 0 replace D, sigma, m by -D, -sigma, -m. For D > 0: if D does not divide w, F4 gives k with ||w (k - sigma)/D + phi_d|| >= 1/5; take x = (k - sigma)/D, m = k, so D x + sigma - m = 0. If D divides w then 2D <= w; put x_0 = -sigma/D, take delta from F3 for y = w x_0 + phi_d, and x = x_0 + delta/w, m = 0. Then w x + phi_d = y + delta is far from the integers, and |D x + sigma| = D |delta|/w <= D/(5w) <= 1/10.

**Lemma 9.6 (core).** Let v_a be odd, v_e = 2 mod 4, phi_a, phi_b, phi_e real, eps = +-1 and D with v_a - eps v_b = 4D, and let x be real and n an integer with |D x + (phi_a - eps phi_b) - n| <= 1/10. Then some integer j makes the runners a, b, e all good at (j + x)/4. Lean: `g24_core` (`RQG24.lean`).
Proof. Put u = -(v_a x + 4 phi_a) and w = -eps (v_b x + 4 phi_b) - 4 n, so |u - w| = 4 |D x + phi_a - eps phi_b - n| <= 2/5. Lemma 9.1 gives N: every integer m blocked for a or for b (in the sense of Lemma 1.2, with q = 4; for b after multiplying by eps and subtracting 4n, as in Theorem 2.3) satisfies N < m < N + 3, so m is N + 1 or N + 2. Lemma 9.4 gives a parity p for e. Choose z in {N + 3, N + 4} with z mod 2 = p. Write v_a = 2k + 1 and put j = z v_a. Then j mod 2 = z mod 2 = p, so e is good. Also v_a j = z v_a^2 = z + 4 z k (k + 1), so for a bad candidate, m = v_a j - 4 n_1 = z + 4(...) is congruent to z modulo 4 and to N + 1 or N + 2, but z is congruent to N + 3 or N modulo 4: a contradiction. For b the same congruence holds for m'' = eps (v_b j - 4 n_2) - 4 n = z + 4(...), using v_a - eps v_b = 4D.

**Theorem 9.7 (G24).** Let v be as in Section 0, a, b, e, s pairwise distinct indices, v_a and v_b odd, v_e mod 4 = 2, v_s mod 4 = 0, v_s != v_a + v_b, v_a != v_b + v_s, v_b != v_a + v_s, phi real. Then some t is good for all four runners. Lean: `G24` (`RQG24.lean`).
Proof. Lemma 4.4 (q = 4) gives eps and D with v_a - eps v_b = 4D; D != 0 (Lemma 4.5). Write v_s = 4u, u >= 1. Lemma 4.6 gives |D| != u. Then "D does not divide u, or 2|D| <= u": if D divides u, u = |D| |t| with |t| >= 1, |t| = 1 would give |D| = u, so |t| >= 2. Lemma 9.5 (w = u, sigma = phi_a - eps phi_b, phi_d = phi_s) gives x and m with |D x + sigma - m| <= 1/10 and (u, phi_s) good at x. Lemma 9.6 gives j for a, b, e at (j + x)/4. The runner s has v_s = 4u and is good by Lemma 1.1. Lemma 4.1 (indices s, e, a, b) covers all four runners.
Note. G24 imposes the non-resonance condition only on the slow speed v_s, and none on v_e.

## 10. Where the hypotheses are used

* Positivity and distinctness of the speeds are used to make D nonzero (Lemma 4.5), to make the quotients u_i positive and, by injectivity, different from each other (Theorems 3.2, 4.9, 8.1, 9.7), and in F5, which needs positive pairwise distinct speeds.
* Non-resonance (u_i != |D|) is used so that the three-runner Lemma 3.1 applies to (u_1, u_2, |D|) in Lemma 4.8, and in G24 so that 2|D| <= u or D does not divide u. In T it is not assumed: the resonant case is handled by Section 7.
* q >= 4 (QGen): 3/10 <= 3/5 - 1/q. q >= 5 (Theorem 7.6): 2/5 <= 3/5 - 1/q. q >= 7, q != 8 (Theorem 5.3): 2 ((2q - 1)/5 + 1) < q.
* Coprimality of v_a to q is used in the window lemma (an inverse modulo q), in the pigeonhole and in Lemma C. Coprimality of v_b is used in Theorem 5.3 and in the bookkeeping at q = 6 and q = 8 in T; it is not used in QGen.
* Real phases enter only through the real numbers sigma, phi_i and the offset x. No step uses that a phase is rational, and no step uses that a maximum is attained.
* R7 (Section 12). Positivity and distinctness make D_b, D_c nonzero (`D_neq`) and D_b different from D_c (injectivity of v). Pattern (A) supplies the two class relations v_a - eps_b v_b = 7 D_b and v_a - eps_c v_c = 7 D_c; pattern (B) supplies the class relation of b and c, and "a is not equivalent to b" gives mu different from 1 and -1; "7 does not divide v_a" gives mu different from 0. The exclusion clause is used once, in Theorem 12.17, to obtain mu = 3 or mu = -3 when |D| = w (through Lemma 12.14). The hypothesis "7 does not divide v_c" is carried and unused (it follows from the class relation of b and c). The facts about q = 7 that are used: 2 (floor((2q - 1)/5) + 1) < q (the pigeonhole in Lemma 12.6), q >= 5 (2q/5 <= 3q/5 - 1 in Theorem 12.7), and the sizes of the windows in Lemmas 12.9 and 12.10 (5 and 6 integers out of 7) together with the finite statements of Lemmas 12.8 and 12.14.
* Q3 (Section 13). Coprimality of v_a and v_b to 3 gives the class relation (the units modulo 3 are 1 and 2, that is plus-or-minus 1) and so replaces the class hypothesis of QGen; non-resonance gives u_i different from |D|, as for QGen; q = 3 is used in the window 3/5 - 1/3 = 4/15 and nowhere else; distinctness of the speeds is used for D nonzero, for u_1 different from u_2, and in the three-runner lemma, which needs pairwise distinct positive speeds.

## 11. Distinctness is necessary

The hypothesis that the four speeds are pairwise distinct cannot be dropped in any of the five statements, even when all the other hypotheses hold for four distinct indices. The review session found, by an exact interval computation, speed multisets with a repeated speed and rational phases for which no t exists:

| Class | Speeds | Phases | Source of the claim |
|---|---|---|---|
| P3 (q = 2) | (1,2,2,2) | (0, 0, 1/3, 2/3) | computed; hand check below |
| Q4 | (1,1,4,4) | (0, 1/2, 1/6, 5/6) | computed |
| QGen, T (q = 6) | (1,1,6,6) | (0, 1/2, 1/3, 2/3) | computed; hand check below |
| G24 | (1,1,2,4) | (0, 1/3, 1/3, 1/6) | computed |

(The programs are not archived.) Hand check for (1,1,6,6), phases (0, 1/2, 1/3, 2/3). The runners of speed 1 give ||t|| >= 1/5 and ||t + 1/2|| >= 1/5; the second is equivalent to ||t|| <= 3/10 (since ||t + 1/2|| = 1/2 - ||t||), so t is in [1/5, 3/10] or [-3/10, -1/5] modulo 1. For t in [1/5, 3/10]: 6t + 1/3 lies in [23/15, 32/15], and ||6t + 1/3|| >= 1/5 requires 6t + 1/3 <= 9/5, that is t <= 11/45; 6t + 2/3 lies in [28/15, 37/15], and ||6t + 2/3|| >= 1/5 requires 6t + 2/3 >= 11/5, that is t >= 23/90 (> 11/45 = 22/90). The two conditions are incompatible. For t in [-3/10, -1/5] put t = -s with s in [1/5, 3/10]: ||6t + 1/3|| = ||6s - 1/3|| = ||6s + 2/3|| and ||6t + 2/3|| = ||6s - 2/3|| = ||6s + 1/3||, the same two conditions. So no t exists. For (1,2,2,2), phases (0, 0, 1/3, 2/3): the three runners of speed 2 are at 2t, 2t + 1/3, 2t + 2/3 modulo 1, three points spaced by 1/3; if p in [0, 1/3) is the least fractional part among them, all three are at distance >= 1/5 from the integers only if p >= 1/5 (the smallest) and p + 2/3 <= 4/5 (the largest), that is p >= 1/5 and p <= 2/15, which is impossible. This section has no Lean declaration; it is a remark on the hypotheses.

Added in version 1.5.0 (R7 and Q3). Distinctness cannot be dropped in R7 or in Q3 either. The speeds (1,1,2,7) with phases (0, 1/2, 1/2, 0) satisfy every hypothesis of pattern (B) of R7 for four distinct indices (s the index of 7, a the index of 2, b and c the two indices of 1: b ~ c; a ~ b does not hold since 7 divides neither 2 - 1 nor 2 + 1; and v_s = 7 is neither 1 + 1 nor |1 - 1|, so the exclusion clause holds); the speeds (1,1,3,3) with phases (0, 1/2, 1/4, 3/4) satisfy every hypothesis of Q3 (3 divides the two speeds 3 and 3; the two speeds 1 are coprime to 3; for each slow speed 3: 3 is different from 1 + 1 and from |1 - 1| = 0). In both cases no t has all four distances at least 1/5. The review session computed the best minimum exactly: 1/6 for (1,1,2,7) and 3/16 for (1,1,3,3) (programs not archived; computed). Hand check for (1,1,2,7), which does not need the runner of speed 7. The two runners of speed 1 need ||t|| >= 1/5 and ||t + 1/2|| >= 1/5; since ||t + 1/2|| = 1/2 - ||t||, this forces 1/5 <= ||t|| <= 3/10, that is t = k + r with an integer k and 1/5 <= |r| <= 3/10. Then 2t + 1/2 = 2k + (2r + 1/2). For r in [1/5, 3/10], 2r + 1/2 lies in [9/10, 11/10], within 1/10 of the integer 1; for r in [-3/10, -1/5] it lies in [-1/10, 1/10], within 1/10 of 0. So ||2t + 1/2|| <= 1/10 < 1/5 and the third runner fails. Hand check for (1,1,3,3): as before 1/5 <= |r| <= 3/10 with t = k + r. For r in [1/5, 3/10]: 3t + 1/4 = 3k + (3r + 1/4) with 3r + 1/4 in [17/20, 23/20], within 3/20 of the integer 1, so the third runner has ||3t + 1/4|| <= 3/20 < 1/5. For r in [-3/10, -1/5]: 3t + 3/4 = 3k + (3r + 3/4) with 3r + 3/4 in [-3/20, 3/20], so the fourth runner has ||3t + 3/4|| <= 3/20 < 1/5. So no t exists. These two hand checks were made by the writer of this note and were re-checked by hand, and the values at the stated phases by exact rational arithmetic, in a further session of the same AI system before release.

## 12. R7: exactly one speed divisible by 7

Setting. Let v, phi be as in Section 0. Let s, a, b, c be four pairwise distinct indices (so they exhaust Fin 4, Lemma 4.1 with the four indices in the order s, a, b, c), 7 divide v_s, and 7 divide none of v_a, v_b, v_c. Write v_s = 7 w; w >= 1. Write x ~ y for "7 divides x - y or 7 divides x + y" (divisibility on the integers; in Lean `(7 : Z) dvd x - y \/ (7 : Z) dvd x + y`). The modulus is q = 7 throughout, but Parts K and A are written for a general modulus q, and the time is t = (j + x)/q as in Section 1. The theorems of this section are `R7A` (pattern (A)), `R7B` (pattern (B)) and `R7_partial` (their disjunction). All declarations of this section named below are in `RSevenCore.lean`, `RSevenA.lean`, `RSevenB.lean` or `RSevenFinal.lean`.

Facts imported from earlier modules, besides F1 to F5 and Lemmas 1.1, 1.2, 2.2, 4.1, 4.5, 4.6 above. Their proofs are not repeated; for G2, G4, G5, G6 they are written out in `paper/shifted-real-four/NOTE.md`. (G1) `badSet` and `card_bad_le` (Section 5): for v coprime to q, at most (2q - 1)/5 + 1 residues j in {0, ..., q - 1} make the runner (v, phi) bad at (j + x)/q (`RQPigeon.lean`). (G2) For D nonzero, w >= 1 and real sigma, phi_d there are a real x and an integer m with |D x + sigma - m| <= 1/5 and ||w x + phi_d|| >= 1/5 (Lemma 3.4 of that note; `lemma4R`, `RFiveWindow.lean`). (G3) The same with the bound 1/10 if D does not divide w or 2|D| <= w (Lemma 9.5 above; `lemma4R_tight`, `RQG24.lean`). (G4) `L6 D w sigma phi_d` is the statement "there is an integer t with w = D t and ||phi_d - t sigma|| < 1/5" (`L6`, `RFiveWindow.lean`); if D is nonzero and `L6` does not hold, there are a real x and an integer m with D x + sigma = m exactly and ||w x + phi_d|| >= 1/5 (Lemma 3.5 of that note; `exists_exactR`, `RFiveWindow.lean`). (G5) If d divides w >= 1 and |d| is different from w then 2|d| <= w (Lemma 4.4 of that note; `two_abs_le`, `RFiveCluster.lean`). (G6) The cluster lemma: for w >= 1, D_b, D_c nonzero and different, with D_b, D_c, D_b - D_c all dividing w, and real sigma_b, sigma_c, phi_d, there are a real x and integers m_b, m_c with ||w x + phi_d|| >= 1/5, |D_b x + sigma_b - m_b| <= 2/5, |D_c x + sigma_c - m_c| <= 2/5 and the difference of these two quantities of absolute value at most 2/5 (Lemma 4.5 of that note; `cluster_div`, `RFiveCluster.lean`).

**Part K (general modulus; `RSevenCore.lean`).**

**Lemma 12.1 (an integer near the centre makes the runner bad).** Let q >= 1, v natural, phi, x real, j, n integers with |(v j - q n) + (v x + q phi)| < q/5. Then the runner (v, phi) is bad at (j + x)/q. Lean: `not_good_of_near` (`RSevenCore.lean`).
Proof. With t = (j + x)/q we have (v j - q n) + (v x + q phi) = q (v t + phi - n), so |v t + phi - n| < 1/5. Hence ||v t + phi|| <= |v t + phi - n| < 1/5 (the nearest-integer distance is the least distance to an integer). This is the converse of Lemma 1.2.

**Lemma 12.2 (centre difference).** Let q, v_a, v_i be naturals, eps and D integers with v_a - eps v_i = q D, and x, phi_a, phi_i real, n_i an integer. Put u_a = -(v_a x + q phi_a) and u_i = -eps (v_i x + q phi_i) - q n_i. Then u_i - u_a = q (D x + (phi_a - eps phi_i) - n_i). Lean: `centre_diff` (`RSevenCore.lean`). Proof. Expand: u_i - u_a = (v_a - eps v_i) x + q (phi_a - eps phi_i) - q n_i, and v_a - eps v_i = q D.
Reading. By Lemma 1.2 and F2 the integers m = v_a j - q n_1 that make a bad are those within q/5 of u_a; the integers m' = eps (v_i j - q n_2) - q n_i that make i bad are those within q/5 of u_i. The real number D x + (phi_a - eps phi_i) - n_i is the lifted offset: the centres are q times it apart, with no reduction modulo 1.

**Lemma 12.3 (a free residue makes the runner good).** Let q >= 1, v_a, v_i naturals, A, B integers with A v_a + B q = 1, eps = +-1, D an integer with v_a - eps v_i = q D, phi_i, x real, n_i and N integers, u = -eps (v_i x + q phi_i) - q n_i. Suppose that no integer m with |m - u| < q/5 has q dividing m - N. Then the runner (v_i, phi_i) is good at (N A + x)/q. Lean: `good_of_win` (`RSevenCore.lean`).
Proof. If it were bad, F2 and Lemma 1.2 give an integer n_2 such that m_0 = v_i N A - q n_2 has |m_0 + (v_i x + q phi_i)| < q/5. Put m = eps m_0 - q n_i. Then m - u = eps (m_0 + v_i x + q phi_i), so |m - u| < q/5 (|eps| = 1). Moreover eps v_i = v_a - q D and A v_a - 1 = -B q give m - N = N (A v_a - 1) - q D N A - q eps n_2 - q n_i = q (-N B - D N A - eps n_2 - n_i), which q divides, contradicting the hypothesis. (Taking v_i = v_a, eps = 1, D = 0, n_i = 0 gives the statement for the base runner a itself.)

**Lemma 12.4 (one window for three centres).** (i) If q > 0 and N < m < N + q are integers then q does not divide m - N. Lean: `win_ne_dvd` (`RSevenCore.lean`; Lemma 2.2). (ii) Let q be a natural number and u_1, u_2, u_3 reals with |u_i - u_j| <= 3q/5 - 1 for all pairs. Then there is an integer N such that every integer m with |m - u_i| < q/5 for some i satisfies N < m < N + q. Lean: `window_gap3` (`RSevenCore.lean`).
Proof of (ii). Let lo be the least of u_1, u_2, u_3 and N = floor(lo - q/5). For m near u_i: m > u_i - q/5 >= lo - q/5 >= N; and m < u_i + q/5 <= lo + 3q/5 - 1 + q/5 = lo + 4q/5 - 1 < N + 1 + q/5 + 4q/5 - 1 = N + q, because lo - q/5 < N + 1. This is Lemma 2.1 for three centres.

**Lemma 12.5 (coinciding centres give the same bad residues).** Let q >= 1, v_p, v_r naturals, eps = +-1, D an integer with v_p - eps v_r = q D, M an integer with D x + (phi_p - eps phi_r) = M, and j an integer. If the runner (v_r, phi_r) is bad at (j + x)/q then so is (v_p, phi_p). Lean: `bad_transfer` (`RSevenCore.lean`).
Proof. F2 and Lemma 1.2 give an integer n with |(v_r j - q n) + (v_r x + q phi_r)| < q/5. Put n' = D j + eps n + M. Using v_p = eps v_r + q D and D x + phi_p - M = eps phi_r one finds (v_p j - q n') + (v_p x + q phi_p) = eps ((v_r j - q n) + (v_r x + q phi_r)), of absolute value less than q/5. Lemma 12.1 gives that p is bad.

**Lemma 12.6 (a coinciding pair and a third runner).** Let q be a natural number with 2 (floor((2q - 1)/5) + 1) < q, v_p, v_r, v_o naturals with v_p and v_o coprime to q, eps, D, M as in Lemma 12.5, and phi_p, phi_r, phi_o, x real. Then there is an integer j such that the three runners (v_p, phi_p), (v_r, phi_r), (v_o, phi_o) are all good at (j + x)/q. Lean: `exact_pair` (`RSevenCore.lean`).
Proof. By G1 the bad sets of p and of o have at most floor((2q - 1)/5) + 1 elements each, so their union has fewer than q elements and some j in {0, ..., q - 1} is in neither: p and o are good at (j + x)/q. If r were bad at j, Lemma 12.5 would make p bad.

**Part A (pattern (A), general modulus; `RSevenA.lean`).**

**Theorem 12.7 (three free runners in one class).** Let q >= 5 with 2 (floor((2q - 1)/5) + 1) < q, w >= 1, v_a, v_b, v_c naturals coprime to q, eps_b, eps_c = +-1, D_b, D_c nonzero and different integers with v_a - eps_b v_b = q D_b and v_a - eps_c v_c = q D_c, and phi_a, phi_b, phi_c, phi_d real. Then there is a real x with ||w x + phi_d|| >= 1/5 and an integer j such that a, b, c are all good at (j + x)/q. Lean: `r7CaseA` (`RSevenA.lean`).
Proof. Put sigma_b = phi_a - eps_b phi_b and sigma_c = phi_a - eps_c phi_c. Four cases.
(1) `L6 D_b w sigma_b phi_d` does not hold. G4 gives x and m with D_b x + sigma_b = m and the slow runner good. Lemma 12.6 with (p, r, o) = (a, b, c) gives j.
(2) `L6` holds for D_b but not for D_c: the same with c in place of b and (p, r, o) = (a, c, b).
(3) `L6` holds for D_b and for D_c but not for D_b - D_c (with sigma_b - sigma_c). G4 gives x and m with (D_b - D_c) x + sigma_b - sigma_c = m and the slow runner good. Put eps' = eps_b eps_c and D' = eps_b (D_c - D_b). From the two class relations, v_b - eps' v_c = q D' (use eps_b v_b = v_a - q D_b and eps_b eps_c v_c = eps_b (v_a - q D_c)), and D' x + (phi_b - eps' phi_c) = -eps_b m. Lemma 12.6 with (p, r, o) = (b, c, a) gives j.
(4) `L6` holds for all three. Then D_b, D_c and D_b - D_c all divide w, and G6 gives x, m_b, m_c with the slow runner good and the three quantities r_b = D_b x + sigma_b - m_b, r_c = D_c x + sigma_c - m_c and r_b - r_c of absolute value at most 2/5. With the centres u_a, u_b, u_c of Lemma 12.2 (n_b = m_b, n_c = m_c), u_b - u_a = q r_b, u_c - u_a = q r_c and u_b - u_c = q (r_b - r_c), so all pairwise distances are at most 2q/5, which is at most 3q/5 - 1 because q >= 5. Lemma 12.4 gives N such that no integer within q/5 of a centre is congruent to N modulo q. Let A, B be integers with A v_a + B q = 1. Lemma 12.3 applied to b, to c and to a itself shows that j = N A makes all three good.
Reading. The hypothesis 2 (floor((2q - 1)/5) + 1) < q holds for q = 7 (2 (2 + 1) = 6 < 7), for q = 5 and for every q >= 9, and fails for q = 6 and q = 8 (as in Theorem 5.3).

**Part B (pattern (B), q = 7; `RSevenB.lean`).**

**Lemma 12.8 (two finite statements over Z/7).** (i) For all mu, z, k in Z/7 with mu not in {0, 1, -1}: at least one of z' = z, z + 1, z + 2 has mu z' different from k + 1, k + 2 and k + 3. (ii) For all mu, z, k in Z/7 with mu = 3 or mu = -3: at least one of z' = z, z + 1 has mu z' different from k + 1, k + 2 and k + 3. Lean: `ap3` (i) and `ap2` (ii), `RSevenB.lean`. Sketch; the Lean declaration is the proof (kernel `decide` over 343 cases each, with `synthInstance.maxSize 4096` and `maxRecDepth 100000`). Reading: the three residues k + 1, k + 2, k + 3 are consecutive, so two of them differ by 0, +-1 or +-2, never by +-3 (in Z/7, 3 and 4 are not in {0, 1, 2, 5, 6}). For mu = +-3 two terms of the progression mu z, mu (z + 1) differ by mu = +-3, so they cannot both lie among them; for mu = +-2, mu z and mu (z + 2) differ by 2 mu = +-4 = -+3; so in both cases the progression cannot lie among them. (The hypothesis mu not 0 is needed in (i): mu = 0 puts the whole progression at one residue.)

**Lemma 12.9 (a window for two centres).** Let q be a natural number with q = 7, u_b, u_c reals, rho >= 0, L an integer with 19/5 + 7 rho <= L, and |u_c - u_b| <= 7 rho. Then there is an integer M such that every integer m with |m - u_b| < q/5 or |m - u_c| < q/5 satisfies M < m < M + L. Lean: `bc_window` (`RSevenB.lean`).
Proof. Let lo be the smaller of u_b, u_c and M = floor(lo - q/5). For m near a centre: m > lo - q/5 >= M, and m < lo + 7 rho + q/5 < M + 1 + q/5 + 7 rho + q/5 = M + 19/5 + 7 rho <= M + L (q = 7).

**Lemma 12.10 (b and c on the free range).** Let q = 7, v_b, v_c naturals, A, B integers with A v_b + B q = 1, eps = +-1, D with v_b - eps v_c = q D, phi_b, phi_c, x real, n an integer, rho >= 0, L an integer with 19/5 + 7 rho <= L, and |D x + (phi_b - eps phi_c) - n| <= rho. Then there is an integer M such that for every integer N with M + L <= N <= M + 7 both runners b and c are good at (N A + x)/q. Lean: `bc_good` (`RSevenB.lean`).
Proof. By Lemma 12.2 (n_c = n) the centres u_b, u_c of b and c satisfy |u_c - u_b| = q |D x + (phi_b - eps phi_c) - n| <= 7 rho. Lemma 12.9 gives M. If M + L <= N <= M + 7 and m is an integer within q/5 of a centre then M < m < M + L <= N, and m > M >= N - 7, so N - 7 < m < N and 7 does not divide m - N. Lemma 12.3 (for b with eps = 1, D = 0; for c) gives the claim.

**Lemma 12.11 (the third runner).** Let q = 7, v_a, v_b naturals, A, B integers with A v_b + B q = 1, mu in Z/7 with (v_a : Z/7) = mu (v_b : Z/7), phi_a, x real, N and k integers with k = floor(-(v_a x + q phi_a) - q/5), and suppose mu N is different from k + 1, k + 2 and k + 3 in Z/7. Then the runner (v_a, phi_a) is good at (N A + x)/q. Lean: `a_good` (`RSevenB.lean`).
Proof. If it were bad, F2 and Lemma 1.2 give an integer n_2 such that m' = v_a N A - q n_2 has |m' - c_a| < q/5 with c_a = -(v_a x + q phi_a). Since k <= c_a - q/5 < k + 1, we get k < m' < c_a + q/5 < k + 1 + 2q/5 < k + 4 (q = 7), so m' is one of k + 1, k + 2, k + 3. In Z/7, m' = v_a N A = mu v_b N A = mu N, because q = 0 and A v_b = 1 there. So mu N is one of k + 1, k + 2, k + 3, a contradiction.

**Theorem 12.12 (two free runners in one class, the third in another class).** Let q = 7, w >= 1, v_b, v_c, v_a naturals with v_b coprime to 7, eps = +-1, D a nonzero integer with v_b - eps v_c = 7 D, mu in Z/7 with (v_a : Z/7) = mu (v_b : Z/7), mu not in {0, 1, -1}, and (if |D| = w then mu = 3 or mu = -3). Then for real phases there are a real x with ||w x + phi_d|| >= 1/5 and an integer j such that b, c, a are all good at (j + x)/7. Lean: `r7CaseB` (`RSevenB.lean`).
Proof. Let A, B be integers with A v_b + B q = 1, and sigma = phi_b - eps phi_c. Case (i): D does not divide w, or 2|D| <= w. G3 gives x, m with |D x + sigma - m| <= 1/10 and the slow runner good. Lemma 12.10 with rho = 1/10 and L = 5 (19/5 + 7/10 = 9/2 <= 5) gives M such that b and c are good at (N A + x)/7 for N = M + 5, M + 6, M + 7. Lemma 12.8 (i) with z = M + 5 and k = floor(-(v_a x + 7 phi_a) - 7/5) gives one of these three values N with mu N different from k + 1, k + 2, k + 3 (note mu (M + 5 + i) = mu z' with z' = z + i), and Lemma 12.11 shows that a is good at (N A + x)/7. Case (ii): D divides w and 2|D| > w. Then |D| = w by G5 (if |D| were different from w, 2|D| <= w), so by hypothesis mu = 3 or mu = -3. G2 gives x, m with |D x + sigma - m| <= 1/5 and the slow runner good. Lemma 12.10 with rho = 1/5 and L = 6 (19/5 + 7/5 = 26/5 <= 6) gives M such that b and c are good for N = M + 6 and M + 7. Lemma 12.8 (ii) with z = M + 6 gives one of the two with mu N outside the three residues, and Lemma 12.11 shows that a is good.
Reading. The bound 1/10 (case (i)) leaves three free residues and needs only mu not in {0, +-1}; the bound 1/5 (case (ii)), which cannot be improved when |D| = w, leaves two free residues and needs mu = +-3. This is the only place where the hypotheses on the classes enter beyond Theorem 12.7.

**Part F (the theorems; `RSevenFinal.lean`).**

**Lemma 12.13 (class data).** (i) If x, y are naturals and 7 divides x - y or x + y (in the integers), there are eps = +-1 and an integer D with x - eps y = 7 D. Lean: `eps_D7` (`RSevenFinal.lean`). (ii) If 7 does not divide n then n is coprime to 7. Lean: `cop7` (`RSevenFinal.lean`). Proof. (i) Take eps = 1 and D = (x - y)/7, or eps = -1 and D = (x + y)/7. (ii) 7 is prime.

**Lemma 12.14 (the resonant finite statement).** For y, mu in Z/7 with y nonzero, mu not in {0, 1, -1}, and neither y = 3 (mu y) nor y = -3 (mu y): mu = 3 or mu = -3. Lean: `fin7` (`RSevenFinal.lean`). Sketch; the Lean declaration is the proof (kernel `decide`, 49 cases). Reading: with y nonzero, y = 3 mu y means 3 mu = 1, that is mu = -2, and y = -3 mu y means mu = 2; so the two excluded cases are mu = +-2, and the only values of mu outside {0, +-1, +-2} are +-3.

**Lemma 12.15 (assembly).** Let s, a, b, c exhaust Fin 4, v_s = 7 w, x real with ||w x + phi_s|| >= 1/5, and j an integer such that a, b, c are good at (j + x)/7. Then t = (j + x)/7 is good for all four runners. Lean: `finish7` (`RSevenFinal.lean`). Proof. The runner s is good by Lemma 1.1 (q = 7, u = w); the others by assumption.

**Theorem 12.16 (R7A, pattern (A)).** Let v, s, a, b, c be as in the setting, with a ~ b and a ~ c. Then for every real phi some t is good for all four runners. Lean: `R7A` (`RSevenFinal.lean`).
Proof. Write v_s = 7 w. Lemma 12.13 gives eps_b, D_b and eps_c, D_c with v_a - eps_b v_b = 7 D_b and v_a - eps_c v_c = 7 D_c. D_b and D_c are nonzero by Lemma 4.5 (`D_neq`; positivity, and v_a different from v_b and from v_c). D_b is different from D_c: otherwise the two relations give eps_b v_b = eps_c v_c; if the signs are equal this gives v_b = v_c, contradicting injectivity, and if they are opposite it gives v_b = -v_c, contradicting positivity. The speeds are coprime to 7 (Lemma 12.13). Theorem 12.7 with q = 7 (hypotheses 2 (floor(13/5) + 1) = 6 < 7 and 5 <= 7) gives x and j; Lemma 12.15 with Lemma 4.1 finishes.

**Theorem 12.17 (R7B, pattern (B)).** Let v, s, a, b, c be as in the setting, b ~ c, a ~ b not holding, and not both [v_s = v_b + v_c or v_b = v_c + v_s or v_c = v_b + v_s] and [7 divides v_b - 3 v_a or v_b + 3 v_a]. Then for every real phi some t is good for all four runners. Lean: `R7B` (`RSevenFinal.lean`).
Proof. Lemma 12.13 gives eps and D with v_b - eps v_c = 7 D, D nonzero (Lemma 4.5). Put mu = v_a/v_b in Z/7 (v_b is invertible since 7 does not divide it), so v_a = mu v_b there. mu is not 0 (7 does not divide v_a); mu is not 1, since mu = 1 would give 7 dividing v_a - v_b; mu is not -1, since that would give 7 dividing v_a + v_b. Suppose |D| = w. Then Lemma 4.6 (`resonance_of`, with q = 7, v_a := v_b, v_b := v_c) gives v_s = v_b + v_c or v_b = v_c + v_s or v_c = v_b + v_s. By the exclusion hypothesis, 7 divides neither v_b - 3 v_a nor v_b + 3 v_a, that is y = v_b satisfies neither y = 3 mu y nor y = -3 mu y in Z/7. Lemma 12.14 gives mu = 3 or mu = -3. Theorem 12.12 now gives x and j for b, c, a, and Lemma 12.15 with Lemma 4.1 finishes.
Reading. The excluded sub-case is the case v_s = v_b + v_c or v_s = |v_b - v_c| (the resonant case, |D| = w) together with v_a = +-2 v_b modulo 7 (equivalently v_b = +-3 v_a). The tight vector (1,3,4,7) is in this sub-case: v_s = 7 = 3 + 4.

**Theorem 12.18 (R7_partial).** Under the setting, if (A) or (B) holds, then for every real phi some t is good for all four runners. Lean: `R7_partial` (`RSevenFinal.lean`). Proof. Case split on the hypothesis; Theorems 12.16 and 12.17.
Reading. The indices s, a, b, c are universally quantified, so the theorem applies to every assignment of the roles; the clause of (B) is symmetric in b and c. Not covered: three pairwise non-equivalent free speeds (pattern (C)), and the resonant sub-case of (B) described above.

## 13. Q3: exactly two speeds divisible by 3

Setting. Let v, phi be as in Section 0, s1, s2, a, b four pairwise distinct indices, 3 divide v_s1 and v_s2, v_a and v_b be coprime to 3, and for s = s1 and s = s2: v_s different from v_a + v_b, v_a different from v_b + v_s, v_b different from v_a + v_s (that is, v_s is neither v_a + v_b nor |v_a - v_b|). The proof is that of Theorem 4.9 (QGen) with q = 3, with one change: the three-runner lemma (Lemma 3.1) is replaced by a three-runner lemma with the thresholds 1/5, 1/5, 7/30 (Theorem 13.10), because the window bound 3/5 - 1/q is 4/15 for q = 3, and Lemma 4.8 delivers only 3/10. Facts imported from `TPThreeA.lean`, `TPThreeRed.lean`, `TPThreeR.lean` (grid-note modules of version 1.2.0 whose building blocks are stated for real phases; their proofs are in the Lean files and are not written out in this archive): with GoodQ(y) meaning that y lies in [1/4, 3/4] modulo 1 (`GoodQ`, `TPThreeA.lean`), (H1) `tpDist_of_goodQ`: GoodQ(y) implies 1/4 <= ||y||; (H2) `pairBox`: for a, b positive naturals, W, H >= 0 and real alpha, beta with gcd(a, b) <= b W + a H there are real t and integers j, k with 1/4 <= a t + alpha - j <= 1/4 + W and 1/4 <= b t + beta - k <= 1/4 + H; (H3) `sweepCase`: for naturals 0 < a < b < c with gcd(a, b) = 1 and 2ab + 2c <= c(a + b), and real alpha, beta, gamma, there is a real t with GoodQ(a t + alpha), GoodQ(b t + beta), GoodQ(c t + gamma); (H4) `shiftCase`: the same conclusion for 0 < a < b with gcd(a, b) >= 2 and gcd(a, b) coprime to c; (H5) `ineqL4`: for 0 < a < b < c with c >= 4, 2ab + 2c <= c(a + b); (H6) `split3`: for positive a there are g > 0 and a', b', c' with gcd(gcd(a', b'), c') = 1 and a = g a', b = g b', c = g c' (`TPThreeRed.lean`); (H7) `tpDist_ge_win` (`TPThreeR.lean`): if d <= y - w <= 1 - d for an integer w and 0 <= d <= 1/2 then d <= ||y||.

**Definition 13.1.** `Q3GoodT tau y` is the statement "there is an integer w with tau <= y - w <= 1 - tau" (`Q3GoodT`, `RQ3Sweep.lean`). `Q3Pat x y z` is the statement "(x, y, z) is (1/5, 1/5, 7/30), (7/30, 1/5, 1/5) or (1/5, 7/30, 1/5)", that is, two thresholds equal 1/5 and one equals 7/30 (`Q3Pat`, `RQ3Sweep.lean`).

**Lemma 13.2 (elementary facts).** (i) If Q3Pat(x, y, z) then Q3Pat holds for the other five orderings of (x, y, z). Lean: `q3Pat_perm` (`RQ3Sweep.lean`). (ii) If Q3Pat(x, y, z) then each of x, y, z lies in [0, 1/4]. Lean: `q3Pat_le`. (iii) If Q3GoodT(tau, y) and 0 <= tau <= 1/2 then tau <= ||y||. Lean: `q3_tpDist_of_goodT`. (iv) If GoodQ(y) and tau <= 1/4 then Q3GoodT(tau, y). Lean: `q3_goodT_of_goodQ`. Proof. (i), (ii): the three cases of Q3Pat, by `norm_num`. (iii): H7. (iv): the same integer w; tau <= 1/4 <= y - w and y - w <= 3/4 <= 1 - tau.

**Lemma 13.3 (pair of arcs with thresholds).** Let a, b be positive naturals, tau_a, tau_b, W, H, alpha, beta real with W, H >= 0 and gcd(a, b) <= b W + a H. Then there are a real t and integers j, k with tau_a <= a t + alpha - j <= tau_a + W and tau_b <= b t + beta - k <= tau_b + H. Lean: `q3PairBox` (`RQ3Sweep.lean`). Proof. Apply H2 to the phases alpha + (1/4 - tau_a) and beta + (1/4 - tau_b) and subtract the shifts.

**Lemma 13.4 (making the third runner good by a small shift).** For 0 <= tau <= 1/2 and real z_0 there is a real s with 0 <= s <= 2 tau and Q3GoodT(tau, z_0 + s). Lean: `q3CSweep` (`RQ3Sweep.lean`). Proof. Let w = ceiling(z_0 - (1 - tau)), so z_0 - (1 - tau) <= w < z_0 - (1 - tau) + 1. If w + tau <= z_0 take s = 0: then tau <= z_0 - w <= 1 - tau. Otherwise take s = w + tau - z_0, which is positive and less than 2 tau (since w < z_0 + tau), and z_0 + s - w = tau.

**Lemma 13.5 (the sweep with thresholds).** Let 0 < a < b < c be naturals, tau_a, tau_b, tau_c real with 0 <= tau_c <= 1/2, W = 1 - 2 tau_a - (a/c)(2 tau_c) >= 0, H = 1 - 2 tau_b - (b/c)(2 tau_c) >= 0 and gcd(a, b) <= b W + a H, and real alpha, beta, gamma. Then there is a real tau with Q3GoodT(tau_a, a tau + alpha), Q3GoodT(tau_b, b tau + beta) and Q3GoodT(tau_c, c tau + gamma). Lean: `q3Sweep` (`RQ3Sweep.lean`).
Proof. Lemma 13.3 gives t, j, k. Lemma 13.4 with z_0 = c t + gamma gives s in [0, 2 tau_c] with Q3GoodT(tau_c, c t + gamma + s). Put tau = t + s/c. Then a tau + alpha - j = (a t + alpha - j) + a s/c lies in [tau_a, tau_a + W + (a/c) 2 tau_c] = [tau_a, 1 - tau_a], and likewise for b; and c tau + gamma = c t + gamma + s.

**Lemma 13.6 (the speeds 1, 2, 3).** If Q3Pat(tau_a, tau_b, tau_c) and alpha, beta, gamma are real, there is a real x with Q3GoodT(tau_a, x + alpha), Q3GoodT(tau_b, 2x + beta), Q3GoodT(tau_c, 3x + gamma). Lean: `q3Sweep123` (`RQ3Sweep.lean`).
Proof. Lemma 13.5 with (a, b, c) = (1, 2, 3); the side conditions are numerical, by `norm_num` in Lean. With W = 1 - 2 tau_a - (2/3) tau_c and H = 1 - 2 tau_b - (4/3) tau_c, the three placements of 7/30 give (tau_a, tau_b, tau_c) = (1/5, 1/5, 7/30): W = 4/9, H = 13/45, 2W + H = 53/45; (7/30, 1/5, 1/5): W = 2/5, H = 1/3, 2W + H = 17/15; (1/5, 7/30, 1/5): W = 7/15, H = 4/15, 2W + H = 6/5; each is at least gcd(1, 2) = 1, and W, H >= 0. Control: with all three thresholds equal to 1/4 one gets W = 1/3, H = 1/6, 2W + H = 5/6 < 1, so the sweep at 1/4 does not decide the speeds (1,2,3); this is why the hypothesis c >= 4 of H5 is needed, and why the triple (1,2,3) needs the lowered thresholds.

**Lemma 13.7 (primitive sorted triples).** Let 0 < a < b < c be naturals with gcd(gcd(a, b), c) = 1, Q3Pat(tau_a, tau_b, tau_c), and alpha, beta, gamma real. Then there is a real t with tau_a <= ||a t + alpha||, tau_b <= ||b t + beta||, tau_c <= ||c t + gamma||. Lean: `q3MixPrim` (`RQ3Mix.lean`).
Proof. If (a, b, c) = (1, 2, 3): Lemma 13.6 and Lemma 13.2 (iii). Otherwise c >= 4 (the only positive integers a < b < c with c <= 3 are 1, 2, 3). If gcd(a, b) = 1, H5 gives 2ab + 2c <= c(a + b) and H3 gives t with GoodQ for the three runners; if gcd(a, b) >= 2, H4 applies (gcd(a, b) is coprime to c by primitivity). By H1 the three distances are at least 1/4, which is at least each threshold (Lemma 13.2 (ii)).

**Lemma 13.8 (any sorted triple).** The conclusion of Lemma 13.7 for 0 < a < b < c without the gcd condition. Lean: `q3MixSorted` (`RQ3Mix.lean`). Proof. H6 writes (a, b, c) = g (a', b', c') with a primitive triple; Lemma 13.7 gives t for (a', b', c'); then t/g works for (a, b, c), since a (t/g) = a' t, and so on.

**Lemma 13.9 (any order).** The conclusion of Lemma 13.7 for pairwise different positive a, b, c, in any order. Lean: `q3MixAny` (`RQ3Mix.lean`). Proof. Six orderings; in each, Lemma 13.8 is applied to the sorted triple with the phases and the thresholds permuted accordingly (Lemma 13.2 (i) keeps Q3Pat), and the three conclusions are permuted back.

**Theorem 13.10 (mixed three-runner lemma).** Let p, q, d be pairwise different positive naturals and alpha, beta, gamma real. Then there is a real x with 1/5 <= ||p x + alpha||, 1/5 <= ||q x + beta|| and 7/30 <= ||d x + gamma||. Lean: `q3Mix3` (`RQ3Mix.lean`). Proof. Lemma 13.9 with the thresholds (1/5, 1/5, 7/30).

**Lemma 13.11 (a half-shifted far point is near an integer).** If 7/30 <= ||y + 1/2|| then there is an integer n with |y - n| <= 4/15. Lean: `q3_exists_int_of_far` (`RQ3Final.lean`). Proof. Put r = round(y + 1/2) and d = y + 1/2 - r, so 7/30 <= |d| <= 1/2. If d >= 0 then y - r = d - 1/2 lies in [-4/15, 0]; if d < 0 then y - (r - 1) = d + 1/2 lies in [0, 4/15].

**Lemma 13.12 (offset for the slow runners and the window).** Let u_1, u_2 be positive and different, D a nonzero integer with u_1 and u_2 different from |D|, and phi_1, phi_2, sigma real. Then there are a real x and an integer n such that (u_1, phi_1) and (u_2, phi_2) are good at x and |D x + sigma - n| <= 4/15. Lean: `q3_slow_window` (`RQ3Final.lean`). Proof. If D > 0 apply Theorem 13.10 to the speeds u_1, u_2, |D| (positive and pairwise different) with phases phi_1, phi_2, sigma + 1/2; if D < 0, with phases phi_1, phi_2, -(sigma + 1/2). The third runner gives ||D x + sigma + 1/2|| >= 7/30 (for D < 0 use ||-y|| = ||y||). Lemma 13.11 gives n. This replaces Lemma 4.8, whose bound is 3/10.

**Theorem 13.13 (Q3_core).** Let v, s1, s2, a, b be as in the setting, with u_1, u_2 naturals such that v_s1 = 3 u_1 and v_s2 = 3 u_2, v_a coprime to 3, eps = +-1 and D an integer with v_a - eps v_b = 3 D, u_1 and u_2 different from |D|. Then for every real phi some t is good for all four runners. Lean: `Q3_core` (`RQ3Final.lean`).
Proof. D is nonzero (Lemma 4.5, `D_neq`); u_1, u_2 are positive (`pos_of_mul_eq`) and different (injectivity). Lemma 13.12 with sigma = phi_a - eps phi_b gives x and n with both slow runners good and |D x + sigma - n| <= 4/15 = 3/5 - 1/3. Lemma 4.3 (`finish_window`, with q = 3) finishes.

**Theorem 13.14 (Q3).** Under the setting, for every real phi some t is good for all four runners. Lean: `Q3` (`RQ3Final.lean`).
Proof. Write v_s1 = 3 u_1 and v_s2 = 3 u_2. Since v_a and v_b are coprime to 3, neither is divisible by 3, so each is 1 or 2 modulo 3, and in each of the four combinations 3 divides v_a - v_b or v_a + v_b (`omega`). Lemma 4.4 (`eps_Dq`, q = 3) gives eps and D with v_a - eps v_b = 3 D. If u_i = |D| then Lemma 4.6 (`resonance_of`) gives v_si = v_a + v_b or v_a = v_b + v_si or v_b = v_a + v_si, contradicting the hypotheses; so u_i is different from |D| for i = 1, 2. Theorem 13.13 finishes.

**Theorem 13.15 (Q3_ndvd).** The same with "3 does not divide v_a" and "3 does not divide v_b" in place of coprimality. Lean: `Q3_ndvd` (`RQ3Final.lean`). Proof. 3 is prime, so not dividing is the same as being coprime; Theorem 13.14.
Where the hypotheses are used: Section 10.

## Lean correspondence

All declarations are in namespace `LRSpectrumFull`. Files are in `lean/LRSpectrumFull/`. The full module list and the build order are in `LEAN_MAP.md`.

| Part of the proof | Lean declaration (file) | Written proof |
|---|---|---|
| Distance, good runner | `tpDist` (`TPSmall.lean`), `GoodR` (`RFiveBase.lean`) | definitions |
| F1, F2 | `tpDist_add_int`, `exists_near_of_not_good` (`TPFourBridge.lean`) | imported |
| F3 | `exists_perturb` (`TPFourWindow.lean`) | imported |
| F4 | `coset_branchR`, `coset_branchR_ne` (`RFiveWindow.lean`) | imported |
| F5 | `lemSR` (`RFiveLemS.lean`) | imported |
| Lemma 1.1 | `goodR_mulq` (`RQWindow.lean`) | full |
| Lemma 1.2 | `near_to_int` (`RQWindow.lean`) | full |
| Lemma 1.3 | `exists_free_j` (`RQWindow.lean`) | full |
| Lemma 2.1 | `window_gap` (`RQWindow.lean`) | full |
| Lemma 2.2 | `no_mult_between` (`RQWindow.lean`) | full |
| Theorem 2.3 | `window_lemma` (`RQWindow.lean`) | full |
| Lemma 3.1 | `lemSR3` (`RQThree.lean`) | full (from F5) |
| Theorem 3.2 | `P3` (`RQThree.lean`) | full |
| Lemma 4.1 | `cover4` (`RQFour.lean`) | statement; sketch; the Lean declaration is the proof |
| Lemma 4.2 | `assemble4` (`RQGen.lean`) | full |
| Lemma 4.3 | `finish_window` (`RQGen.lean`) | full |
| Lemma 4.4 | `eps_Dq` (`RQGen.lean`), `eps_D4` (`RQFour.lean`) | full |
| Lemma 4.5 | `D_neq` (`RQGen.lean`), `D_ne4` (`RQFour.lean`) | full |
| Lemma 4.6 | `resonance_of`, `pos_of_mul_eq` (`RQGen.lean`), `nonres4` (`RQFour.lean`) | full |
| Lemma 4.7 | `tpDist_neg`, `exists_int_of_far` (`RQWindow.lean`) | (i) statement; (ii) full |
| Lemma 4.8 | `slow_window` (`RQGen.lean`) | full |
| Theorem 4.9 | `QGen`, `QGen_core` (`RQGen.lean`) | full |
| Theorem 4.10 | `Q4`, `cop4` (`RQFour.lean`) | full (by reduction to the steps of 4.9) |
| Lemma 5.1 | `lemSR2` (`RQPigeon.lean`) | full (from F5) |
| Definition badSet | `badSet`, `mem_badSet` (`RQPigeon.lean`) | definition |
| Lemma 5.2 | `card_bad_le` (`RQPigeon.lean`) | full |
| Theorem 5.3 | `exists_two_good` (`RQPigeon.lean`) | full |
| Definition blk8, Lemma 6.1 | `blk8`, `lemmaC3`, `lemmaC5`, `lemmaC1_covers`, `lemmaC7_covers` (`RQLemmaC.lean`) | statements; the finite check is by kernel `decide` (sketch; the Lean declaration is the proof) |
| Lemma 6.2 | `mem_blk8_of_near` (`RQLemmaC.lean`) | full |
| Theorem 6.3 | `lemmaC_real` (`RQLemmaC.lean`) | full |
| Lemma 7.1 | `tpDist_perturb` (`RQT.lean`) | statement; sketch; the Lean declaration is the proof |
| Lemma 7.2 | `abs_ge_of_int` (`RQT.lean`) | statement; sketch; the Lean declaration is the proof |
| Lemma 7.3 | `exists_shift` (`RQT.lean`) | full |
| Lemma 7.4 | `resonant_x_pos` (`RQT.lean`) | full |
| Lemma 7.5 | `resonant_x` (`RQT.lean`) | full |
| Theorem 7.6 | `T_same` (`RQT.lean`) | full |
| Theorem 8.1 | `T` (`RQT.lean`) | full |
| Lemma 9.1 | `window_gap4` (`RQG24.lean`) | full |
| Lemma 9.2 | `e_val` (`RQG24.lean`) | full |
| Lemma 9.3 | `not_both_near` (`RQG24.lean`) | full |
| Lemma 9.4 | `parity_ok` (`RQG24.lean`) | full |
| Lemma 9.5 | `lemma4R_tight_pos`, `lemma4R_tight` (`RQG24.lean`) | full |
| Lemma 9.6 | `g24_core` (`RQG24.lean`) | full (outline of the arithmetic; the Lean declaration is the proof of the congruences) |
| Theorem 9.7 | `G24` (`RQG24.lean`) | full |
| Section 11 | none | remark; not formalised |
| G1 (Section 12) | `badSet`, `card_bad_le` (`RQPigeon.lean`) | imported (Lemma 5.2) |
| G2, G4 (Section 12) | `lemma4R`, `L6`, `exists_exactR` (`RFiveWindow.lean`) | imported (`paper/shifted-real-four/NOTE.md`, Lemmas 3.4, 3.5) |
| G3 (Section 12) | `lemma4R_tight` (`RQG24.lean`) | imported (Lemma 9.5) |
| G5, G6 (Section 12) | `two_abs_le`, `cluster_div` (`RFiveCluster.lean`) | imported (`paper/shifted-real-four/NOTE.md`, Lemmas 4.4, 4.5) |
| Lemma 12.1 | `not_good_of_near` (`RSevenCore.lean`) | full |
| Lemma 12.2 | `centre_diff` (`RSevenCore.lean`) | full |
| Lemma 12.3 | `good_of_win` (`RSevenCore.lean`) | full |
| Lemma 12.4 | `win_ne_dvd`, `window_gap3` (`RSevenCore.lean`) | full |
| Lemma 12.5 | `bad_transfer` (`RSevenCore.lean`) | full |
| Lemma 12.6 | `exact_pair` (`RSevenCore.lean`) | full |
| Theorem 12.7 | `r7CaseA` (`RSevenA.lean`) | full |
| Lemma 12.8 | `ap3`, `ap2` (`RSevenB.lean`) | statements; kernel `decide` (sketch; the Lean declaration is the proof) |
| Lemma 12.9 | `bc_window` (`RSevenB.lean`) | full |
| Lemma 12.10 | `bc_good` (`RSevenB.lean`) | full |
| Lemma 12.11 | `a_good` (`RSevenB.lean`) | full |
| Theorem 12.12 | `r7CaseB` (`RSevenB.lean`) | full |
| Lemma 12.13 | `eps_D7`, `cop7` (`RSevenFinal.lean`) | full |
| Lemma 12.14 | `fin7` (`RSevenFinal.lean`) | statement; kernel `decide` (sketch; the Lean declaration is the proof) |
| Lemma 12.15 | `finish7` (`RSevenFinal.lean`) | full |
| Theorem 12.16 | `R7A` (`RSevenFinal.lean`) | full |
| Theorem 12.17 | `R7B` (`RSevenFinal.lean`) | full |
| Theorem 12.18 | `R7_partial` (`RSevenFinal.lean`) | full |
| H1 to H7 (Section 13) | `tpDist_of_goodQ`, `GoodQ`, `pairBox`, `sweepCase`, `shiftCase`, `ineqL4` (`TPThreeA.lean`), `split3` (`TPThreeRed.lean`), `tpDist_ge_win` (`TPThreeR.lean`) | imported (statements only; the Lean declarations are the proofs) |
| Definition 13.1 | `Q3GoodT`, `Q3Pat` (`RQ3Sweep.lean`) | definitions |
| Lemma 13.2 | `q3Pat_perm`, `q3Pat_le`, `q3_tpDist_of_goodT`, `q3_goodT_of_goodQ` (`RQ3Sweep.lean`) | full (the finite checks of (i), (ii) by `norm_num`) |
| Lemma 13.3 | `q3PairBox` (`RQ3Sweep.lean`) | full (from H2) |
| Lemma 13.4 | `q3CSweep` (`RQ3Sweep.lean`) | full |
| Lemma 13.5 | `q3Sweep` (`RQ3Sweep.lean`) | full |
| Lemma 13.6 | `q3Sweep123` (`RQ3Sweep.lean`) | full (numerical side conditions by `norm_num`, values listed) |
| Lemma 13.7 | `q3MixPrim` (`RQ3Mix.lean`) | full |
| Lemma 13.8 | `q3MixSorted` (`RQ3Mix.lean`) | full |
| Lemma 13.9 | `q3MixAny` (`RQ3Mix.lean`) | full (the six orderings are summarised) |
| Theorem 13.10 | `q3Mix3` (`RQ3Mix.lean`) | full |
| Lemma 13.11 | `q3_exists_int_of_far` (`RQ3Final.lean`) | full |
| Lemma 13.12 | `q3_slow_window` (`RQ3Final.lean`) | full |
| Theorem 13.13 | `Q3_core` (`RQ3Final.lean`) | full |
| Theorem 13.14 | `Q3` (`RQ3Final.lean`) | full |
| Theorem 13.15 | `Q3_ndvd` (`RQ3Final.lean`) | full |
| Section 11, added examples | none | remark; hand checks for (1,1,2,7) and (1,1,3,3), not formalised |
