# Four moving runners with real phases: five divisibility classes and a residue argument, with their Lean version

Version 1.4.0 (12 November 2026).

Vico Bonfioli. Version of 12 November 2026 (release 1.4.0 of this archive). Preprint note, not peer reviewed.

## Status

* **Setting of every statement.** Four pairwise distinct positive integer speeds v_1, ..., v_4, arbitrary real phases phi_1, ..., phi_4, and the conclusion: some real t has ||v_i t + phi_i|| >= 1/5 for i = 1, ..., 4 (non-strict inequality), where ||y|| = |y - round(y)| is the distance from y to the nearest integer. In Lean the speeds are `v : Fin 4 -> N` with `forall i, 0 < v i` and `Function.Injective v`, the phases are `phi : Fin 4 -> R`, and the conclusion is `exists t, forall i, GoodR (v i) (phi i) t`.
* **P3** (`P3`, `RQThree.lean`). Some q >= 2 divides exactly three of the four speeds.
* **Q4** (`Q4`, `RQFour.lean`). The speeds v_a and v_b are odd, 4 divides v_s1 and v_s2 (four distinct indices s1, s2, a, b), and for s = s1 and s = s2: v_s is different from v_a + v_b and from |v_a - v_b|.
* **QGen** (`QGen`, `RQGen.lean`). The same with 4 replaced by any q >= 4: q divides v_s1 and v_s2, v_a and v_b are coprime to q, q divides v_a - v_b or v_a + v_b, and v_s is different from v_a + v_b and from |v_a - v_b| for s = s1 and s = s2.
* **T** (`T`, `RQT.lean`). Some q >= 6 divides two speeds v_s1, v_s2 and the other two speeds v_a, v_b are coprime to q. No further hypothesis.
* **G24** (`G24`, `RQG24.lean`). Four distinct indices a, b, e, s: v_a and v_b are odd, v_e is 2 mod 4, v_s is 0 mod 4, and v_s is different from v_a + v_b and from |v_a - v_b|.
* **Supporting statements.** `window_lemma` (`RQWindow.lean`, any modulus q >= 2) and `lemmaC_real` (`RQLemmaC.lean`, q = 8).
* **Lean entry points and build facts.** The eight modules `RQWindow`, `RQThree`, `RQFour`, `RQLemmaC`, `RQGen`, `RQPigeon`, `RQT`, `RQG24` were built on 2026-11-12 in the development repository, one module at a time. A fresh review session re-elaborated each of the eight sources (exit status 0), printed `#print axioms` for 52 declarations (the exported theorems and lemmas of the eight modules, and three declarations they use from earlier modules), and compiled restatements of `window_lemma`, `P3`, `Q4`, `QGen`, `T`, `G24` with the distance written out as `|x - round x|`, each closed by `exact` from the theorem. The axioms are `propext`, `Classical.choice`, `Quot.sound` (a few arithmetic declarations use fewer; `cover4` uses none). No `sorry`, no `native_decide`. Review verdict: SOUND-WITH-CAVEATS. The builds are carried over to this archive and were not repeated for it. The trust base also includes the earlier modules of the archive on which these depend (the `RFive*` and `TPFour*` modules of versions 1.2.0 and 1.3.0), whose mathematics was not re-examined in this review.
* **Labels.** The Lean statements are VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The written proofs below are a transcription of the Lean proofs; the text of this note has had no independent read, no blind read of the Part H kind and no human reader. The Lean theorems are the authority.
* **Text of the release.** Lean 4 formalizations (Mathlib, Lean 4.30.0; axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`) of five classes of speed vectors for which four pairwise distinct positive integer speeds and arbitrary real phases admit a real t with ||v_i t + phi_i|| >= 1/5 for all i: (P3) some q >= 2 divides exactly three of the speeds; (Q4) 4 divides two speeds, the other two are odd, and neither speed divisible by 4 equals the sum or the absolute difference of the two odd speeds; (QGen) the same with any q >= 4 in place of 4, the other two speeds being coprime to q and congruent up to sign modulo q; (T) some q >= 6 divides two speeds and the other two are coprime to q; (G24) two speeds are odd, one is 2 mod 4, one is 0 mod 4 and is not the sum or the absolute difference of the two odd speeds. None of these is a new theorem: all are special cases of the shifted lonely runner conjecture for four moving runners (five runners), proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379, version 1, Corollary 1.4 there; the numbering and the content of the published version were not checked). The prior art as we read it, the coverage of the speed vectors up to speed sum 195 (with exact counts), and the limits of the hypotheses are in the six caveats below. This archive does not contain a proof of the shifted theorem for four moving runners.

### Caveats that bind every use of this note

1. **Not a new theorem.** All five classes are special cases of the shifted lonely runner conjecture for four moving runners (five runners), proved with computer assistance by Alcantara, Criado and Santos, arXiv:2506.13379 (version 1, Corollary 1.4 there; we read version 1 of that paper; the numbering and the content of the published version were not checked). Their theorem covers all four distinct positive speeds and all real phases, with the constant 1/5.
2. **Prior art, as we read it.** (a) The class P3 is Proposition 2.9 of Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2; "Linearly-exponential checking is enough for the lonely runner conjecture and some of its variants") at four runners, for speed vectors of gcd 1; its three-runner instance is Proposition 4.6 of Cslovjecsek, Malikiosis, Naszodi and Schymura (arXiv:2009.12080). The vectors of T that have a witness q >= 7, q != 8 lie inside Proposition 6.5 of Malikiosis, Santos and Schymura (a pair of speeds whose gcd is odd and at least 5, or even and at least 10; the exact counts are in the census below). The class QGen with q >= 5 adds nothing beyond earlier results (the earlier note of this archive on a speed divisible by 5, the classes of Malikiosis, Santos and Schymura, and T). Primitive speed vectors with sum at least 196 are treated by Corollary 1.11 of Malikiosis, Santos and Schymura, and their Remark 1.12 records that the remaining finite family was settled by Alcantara, Criado and Santos (all numbers of that paper in this note are those of arXiv version 2). (b) The residue-shift and pigeonhole mechanism, with several runners not divisible by the modulus, is classical for zero phases (Barajas and Serra, Electron. J. Combin. 15 (2008), #R48, Section 3 and Lemmas 2, 4 and 9; Rosenfeld, arXiv:2509.14111, Lemma 5; Allikvere, arXiv:2609.02604, Lemma 4.6). A related device at zero phases, a time shift that fixes the runners whose speeds are multiples of its denominator and moves the others through equally spaced positions, is in Lemma 12 and Corollary 15 of Bohman, Holzman and Kleitman (Electron. J. Combin. 8 (2001), #R3), where it is used in an argument for five moving speeds. The merging of two runners of one class modulo plus-or-minus into a difference runner has a zero-phase prototype in Lemmas 4 and 9 of Barajas and Serra. The reduction with one runner not divisible by the modulus and real phases is in the literature (Proposition 4.6 of Cslovjecsek et al.; Proposition 2.9 of Malikiosis et al.). Judgement, not a proved statement: the extension of the pigeonhole count to real phases is routine given those papers, and we make no claim that it is new. (c) What we did not find in the texts read is a computation-free proof, for arbitrary real phases, of the classes with a divisible pair of gcd 4 (Q4), of gcd 6 or 8 (T), or of G24, nor a real-phase form of the window lemma (Theorem 2.3 below). "Computation-free" here means: no enumeration of speed vectors; one finite statement over Z/8 (64 pairs, Section 6) is checked by the kernel. This does not show that no such proof exists. For G24: the same parity pattern (the 2-adic valuations of the four speeds are 0, 0, 1 and at least 2) occurs at zero phases in a reduction that is stated, without its argument, in the four-page conference abstract of Barajas and Serra, "Distance graphs with maximum chromatic number" (a problem about distance graphs with zero phases); the full paper was not obtained and we make no statement about what it proves. (d) Read end to end (in the checks for this release, including a download session of 2026-11-12, or in earlier checks for this archive): Cslovjecsek, Malikiosis, Naszodi and Schymura (arXiv:2009.12080, version 2), Barajas and Serra (arXiv:0710.4495, "The lonely runner with seven runners"), the four-page conference abstract of Barajas and Serra, "Distance graphs with maximum chromatic number" (not the full paper), Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2; as a reading of its statements and arguments, its proofs were not re-verified and the results it cites from the geometry of numbers were not examined), Alcantara, Criado and Santos (version 1), Bohman, Holzman and Kleitman (the long case analyses were read in order, not verified), Beck, Hosten and Schymura (arXiv:1606.01783, version 4) and Henze and Malikiosis (arXiv:1609.01939, version 1). Read in all but about 40 lines: Blanco, Criado and Santos (arXiv:2603.24784, version 4). Read in part: Rifford (arXiv:2111.13688, version 2; 1,236 of 3,437 text lines: the introduction, the definitions and the proofs of the free-starting-positions theorem for at most four runners including the lonely one in Section 5; not read: the covering arguments for the other theorems, Section 6 and the appendices, where a keyword search for divisibility vocabulary found nothing), the survey of Perarnau and Serra, Rosenfeld (arXiv:2509.14111), Allikvere (arXiv:2609.02604), "Mixed thresholds in the LRC" (arXiv:2605.27941), Poliakova (arXiv:2609.23952); in the check made for this release, searched by keyword only (some of them were read more fully for other notes of this archive): further papers on the conjecture (Tao, Czerwinski, Giri-Kravitz, Bedert, Beck-Everett, Zhang and others). Not obtained (publisher access refused, no open copy found), so not read: the published version of Alcantara-Criado-Santos (we used arXiv version 1, the only version on arXiv); the journal versions of Malikiosis-Santos-Schymura; the full paper of Barajas and Serra, "Distance graphs with maximum chromatic number" (Discrete Math.); Renault (Discrete Math., 2004); Bienia et al. (1998); Cusick and Pomerance (1984). The notes of versions 1.2.0 to 1.3.1 list papers as not read that were read later (Beck-Hosten-Schymura, Rifford in part, Barajas-Serra in full); those lists are as of their versions and were not edited. (e) Our proofs are unrefereed and this comparison is limited to the texts named.
3. **Coverage, with exact counts.** The census below is a computation over the 2,133,561 primitive speed vectors (four distinct positive integers, gcd 1) with speed sum at most 195, the set enumerated by Alcantara, Criado and Santos. Of these, 1,867,559 lie in a class with a Lean proof in this archive (R5_core of version 1.3.0, P3, QGen, T, G24). The two classes of Malikiosis, Santos and Schymura as we read them (P3 on primitive vectors, and a pair of speeds with gcd odd at least 5 or even at least 10; 1,222,641 vectors together) are contained in that set. 644,918 vectors lie in a Lean class and in neither of the two classes. 266,002 vectors lie in no class and are NOT covered; they include the tight vectors (1,2,3,4), (1,3,4,6), (1,3,4,7). Primitive vectors with speed sum at least 196 are handled by Corollary 1.11 of Malikiosis, Santos and Schymura (arXiv version 2), which is not formalised here. This archive therefore does not contain a proof of the shifted theorem for four moving runners, by computation or otherwise.
4. **The hypotheses are limits of the method.** The non-resonance hypotheses (v_s different from v_a + v_b and |v_a - v_b|) and the class hypotheses are not shown to be necessary for the truth of the conclusion, which is a case of the theorem of Alcantara, Criado and Santos. The only information on them: the tight vectors (1,2,3,4) and (1,3,4,6) satisfy every hypothesis of G24 except the non-resonance clause (exact computation by the review session; for both the value 1/5 is attained). Distinct speeds are necessary in all five statements (Section 11). The constant 1/5 is not claimed sharp for any of the five classes.
5. **Not claimed.** Two further lemmas obtained by the same method, a class with a divisor 3 conditional on the three-runner theorem and a partial class for one speed divisible by 7, are neither formalised nor claimed.
6. **Build scope.** No whole-library `lake build` was run. The modules were built one at a time and the axioms observed per module. The builds are carried over from the development repository and were not repeated for this archive. The Lean trust base includes the earlier `RFive*` and `TPFour*` modules of this archive, whose mathematics was not re-examined for this release.

### Census (computed; generator in `code/rq-census`)

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

Comments in the Lean modules of this release cite development files by their development names. The file cited in the headers of the eight `RQ*` modules as the paper proof is the informal draft of the argument written below; it is not archived and is replaced by this note. The sections of the draft named in the headers correspond to this note as follows: "Lemma B (window)" is Theorem 2.3; "P3" is Theorem 3.2; "Theorem Q4" is Theorem 4.10 and, for a general modulus, Theorem 4.9; "Lemma C" is Theorem 6.3; "exact residue counts" and the "different classes" clause of "Theorem T" are Section 5; "Theorem T" is Theorem 8.1; "Theorem G24" is Theorem 9.7.

The results were obtained with the assistance of an AI system (Claude, Anthropic). The questions and research directions came from the author. The written proofs and the Lean sources were produced by the AI system; the Lean theorems are checked by the Lean kernel, the Lean statements and sources were read or re-run by a further session of the same system, and the informal draft from which the written proofs were transcribed was checked by computation and read by further sessions; the text of this note has not had an independent read. The author is responsible for all claims.

## Conceptual abstract

Write the time as t = (j + x)/q, with j a residue modulo q and x a real offset. A speed divisible by q sees only the offset x. A speed coprime to q is bad at (j + x)/q only for j in a set of residues that, in a suitable coordinate, is an interval of length about 2q/5, so it blocks at most ceil(2q/5) residues. For q >= 7 and q != 8 two such runners cannot block all q residues. The runners divisible by q are handled by a three-runner lemma applied to the offset. For q = 4, 6, 8, two runners in one class modulo plus-or-minus, with speeds va and vb, are merged: in the coordinate z = va j their blocked intervals have centres q ||D x + sigma|| apart, D = (va -/+ vb)/q, and a window condition on x leaves a free residue. That condition is a condition on one extra runner of speed |D|. Speeds 2 mod 4 are handled by parity.

## Outline

* Time written as t = (j + x)/q; three imported facts; one free runner (Sections 0 and 1).
* The window lemma for two free runners of one class (Section 2).
* A three-runner lemma and Theorem P3 (Section 3).
* The reduction of two free runners of one class to a difference runner; Theorems QGen and Q4 (Section 4).
* The residue pigeonhole for two free runners, q >= 7, q != 8 (Section 5).
* Lemma C for q = 8 and two free runners of different classes (Section 6).
* An explicit perturbation argument for resonant same-class pairs at q = 6 and q = 8 (Section 7).
* Theorem T (Section 8) and Theorem G24 (Section 9).

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

## 11. Distinctness is necessary

The hypothesis that the four speeds are pairwise distinct cannot be dropped in any of the five statements, even when all the other hypotheses hold for four distinct indices. The review session found, by an exact interval computation, speed multisets with a repeated speed and rational phases for which no t exists:

| Class | Speeds | Phases | Source of the claim |
|---|---|---|---|
| P3 (q = 2) | (1,2,2,2) | (0, 0, 1/3, 2/3) | computed; hand check below |
| Q4 | (1,1,4,4) | (0, 1/2, 1/6, 5/6) | computed |
| QGen, T (q = 6) | (1,1,6,6) | (0, 1/2, 1/3, 2/3) | computed; hand check below |
| G24 | (1,1,2,4) | (0, 1/3, 1/3, 1/6) | computed |

(The programs are not archived.) Hand check for (1,1,6,6), phases (0, 1/2, 1/3, 2/3). The runners of speed 1 give ||t|| >= 1/5 and ||t + 1/2|| >= 1/5; the second is equivalent to ||t|| <= 3/10 (since ||t + 1/2|| = 1/2 - ||t||), so t is in [1/5, 3/10] or [-3/10, -1/5] modulo 1. For t in [1/5, 3/10]: 6t + 1/3 lies in [23/15, 32/15], and ||6t + 1/3|| >= 1/5 requires 6t + 1/3 <= 9/5, that is t <= 11/45; 6t + 2/3 lies in [28/15, 37/15], and ||6t + 2/3|| >= 1/5 requires 6t + 2/3 >= 11/5, that is t >= 23/90 (> 11/45 = 22/90). The two conditions are incompatible. For t in [-3/10, -1/5] put t = -s with s in [1/5, 3/10]: ||6t + 1/3|| = ||6s - 1/3|| = ||6s + 2/3|| and ||6t + 2/3|| = ||6s - 2/3|| = ||6s + 1/3||, the same two conditions. So no t exists. For (1,2,2,2), phases (0, 0, 1/3, 2/3): the three runners of speed 2 are at 2t, 2t + 1/3, 2t + 2/3 modulo 1, three points spaced by 1/3; if p in [0, 1/3) is the least fractional part among them, all three are at distance >= 1/5 from the integers only if p >= 1/5 (the smallest) and p + 2/3 <= 4/5 (the largest), that is p >= 1/5 and p <= 2/15, which is impossible. This section has no Lean declaration; it is a remark on the hypotheses.

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
