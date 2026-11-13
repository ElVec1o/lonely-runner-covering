# Four moving runners with real phases and speed sum at most 195: a Lean proof from class theorems and kernel-checked certificates

Version 1.6.0 (13 November 2026). Vico Bonfioli. Preprint note, not peer reviewed. The note describes the Lean theorem `sLRC4_le195` and its proof as formalised; it is a transcription of the Lean files, and the Lean files are the authority.

Notation: Lean code is quoted in ASCII (`N`, `Z`, `R` for the naturals, integers, reals; `->`, `<=`, `forall`, `exists` for the arrows, the inequality and the quantifiers). All Lean declarations are in namespace `LRSpectrumFull.D0`, except those of the time-cover modules, which are in `LRSpectrumFull.TC`. Files are in `lean/LRSpectrumFull/`.

## Status

* **The statement (Lean: `sLRC4_le195`, `S4Final.lean`).** For all natural numbers 0 < a < b < c < d with gcd(a,b,c,d) = 1 and a + b + c + d <= 195, and every real phase vector phi in R^4, there is a real t with 1/5 <= ||v_i t + phi_i|| for i = 1, ..., 4, where v = (a,b,c,d) and ||y|| = |y - round(y)| is the distance from y to the nearest integer. The quantifiers are "for all phi, exists t"; the inequality is non-strict; the phases are real. Quoted from the Lean sources:

        def tpDist (x : R) : R := |x - round x|                                   -- TPSmall.lean
        def GoodR (v : N) (phi : R) (t : R) : Prop := 1 / 5 <= tpDist ((v : R) * t + phi)   -- RFiveBase.lean
        def S4 (v : Fin 4 -> N) : Prop := forall phi : Fin 4 -> R, exists t : R, forall i, GoodR (v i) (phi i) t   -- D0Bridge.lean

        theorem sLRC4_le195 : forall a b c d : N, 0 < a -> a < b -> b < c -> c < d ->
            Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 -> a + b + c + d <= 195 -> S4 ![a, b, c, d]

  Two corollaries are in the same file: `sLRC4_le195_fin` (any injective positive `v : Fin 4 -> N` with `Finset.univ.gcd v = 1` and sum at most 195) and `sLRC4_le195_any` (the same without the gcd hypothesis; rescaling by the gcd, `S4Cor.lean`). The file also contains a fully unfolded restatement (with `|x - round x|` written out) closed by `exact`, and three sanity instances.
* **Known result; this is not a new theorem and not the full four-runner theorem.** The shifted lonely runner conjecture for four moving runners (five runners including the stationary one) was proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379, version 1, Corollary 1.4 there; the numbering of the published version was not checked), after the reduction of Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2, Corollary 1.11 there) to speed vectors with sum at most 195. The statement above is the case of speed sum at most 195 of that theorem. The case of speed sum at least 196 rests on the published reduction, which is not formalised here. The archive therefore contains a Lean proof for speed sum at most 195 only, and nothing in this note proves the four-runner theorem for all speeds.
* **What this release adds.** A machine-checked Lean proof of the statement for speed sum at most 195. Of the 2,133,561 primitive speed vectors with sum at most 195, 2,002,342 are handled by the seven class theorems released in versions 1.3.0 to 1.5.0 (computation-free proofs, Lean), dispatched by a Boolean test with a soundness proof, and 131,219 are handled by certificates whose soundness theorems are proved in Lean and whose data are checked by the Lean kernel: 130,914 depth-0 certificates and 305 exact time covers. The data are not trusted: only the soundness theorems, the class test and the loop lemmas are.
* **No priority claim for the formalisation.** We did not look for, and do not know of, an earlier Lean formalisation of this range; we searched only the sources we hold (see Caveat 2).
* **Axioms and build facts.** Built on 2026-11-13 in the development repository, module by module (293 modules in the import closure of `S4Final` and `S4Cor`, of which 253 are added to the archive in this release). Axioms printed for the final theorems and for the soundness theorems: `propext`, `Classical.choice`, `Quot.sound` only (243 axiom lines in the build log of the closure, none different). No `sorry`, no `admit`, no `native_decide` (the string "native_decide" occurs once, in a comment of `D0Chunk.lean` that says the file does not use it). The certificate data are closed by `decide +kernel` (509 occurrences in the closure). A fresh review session gave the verdict SOUND-WITH-CAVEATS. The builds are carried over from the development repository and were not repeated for this archive.
* **Labels.** The Lean statements are VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The counts are COMPUTED. The written proofs below are a transcription of the Lean proofs; the text of this note has had no independent read, no blind read of the Part H kind and no human reader.
* **Text of the release.** "Lean 4 formalization (Mathlib, Lean 4.30.0; axioms propext, Classical.choice, Quot.sound only; no sorry, no native_decide) that for four distinct positive integer speeds with gcd 1 and sum at most 195, and every real phase vector, some real time puts all four runners at distance at least 1/5 from the origin of the circle. This is the case of speed sum at most 195 of the shifted lonely runner conjecture for four moving runners, proved with computer assistance by Alcantara, Criado and Santos; it is not a new theorem, and it is not the full four-runner theorem (speed sum at least 196 rests on the published reduction of Malikiosis, Santos and Schymura, not formalised here). We did not look for, and do not know of, an earlier Lean formalisation of this range; we searched only the sources we hold. 2,002,342 vectors are handled by class theorems and 131,219 by kernel-checked certificates (130,914 depth-0 certificates and 305 exact time covers); the certificate data are not trusted, only the soundness theorems, the class test and the loop lemmas."

### Caveats that bind every use of this note

1. **Known result.** See the second bullet of the status. The theorem is due to Alcantara, Criado and Santos with computer assistance, after Malikiosis, Santos and Schymura; the statement here is its case of speed sum at most 195. No claim of a new theorem is made, and the sentence "the full four-runner theorem is proved in Lean" would be false.
2. **Prior art, as we read it, and its scope.** The depth-0 certificate of Section 4 is our re-derivation in runner coordinates of the depth-0 certificate of Alcantara, Criado and Santos, as we read that paper (arXiv version 1, the only version on arXiv; we did not obtain the published version); we make no claim that it is new. The time covers of Section 5 are our own formulation of a closed-box covering check, with no claim of novelty. On earlier Lean formalisations: the searches were a search of GitHub repositories, code, issues and pull requests for "lonely runner" with "lean" and "formalization", a Zenodo search, an arXiv listing (all 2026-10-18), an abstract-page and web search (2026-10-31, 2026-11-01 and 2026-11-09); they found Lean statement files (the `formal-conjectures` repository of Google DeepMind, statements only), an asymptotic bound in Lean (Cheng Li), and a Zenodo record listed as a Lean proof for 14 runners, whose content we did not verify; they found no Lean formalisation of the four-runner shifted case. We make no statement about sources not listed here (as far as our records show we did not search the Lean Zulip archive or the Archive of Formal Proofs directly; a Zulip thread was reported by a web search and not read). The searches were not repeated for this release. The index of the code hosts is weak, so "not found" does not mean "absent". The papers of Alcantara-Criado-Santos and Malikiosis-Santos-Schymura were read as in versions 1.3.1 to 1.5.0 (their proofs were not re-verified); no further paper was read for this release.
3. **Coverage by class theorems.** The count 2,002,342 rests on the programme's own census program (archived in version 1.5.0, `code/rq-census`) and on the Lean class test `classB`, whose acceptance set equals the census set exactly (classB accepts 2,002,342 vectors, misses 0 and adds 0 relative to the census; Section 3). The Lean theorem does not use the census: the case split is proved exhaustive in Lean (Section 7).
4. **What the review did not re-read.** The reviewing session did not re-read the proofs of the seven class theorems (they were reviewed in versions 1.3.0 to 1.5.0), nor the proofs in `D0Chunk.lean` (`recOK_sound`) and `TCCover.lean` (kernel and signatures only); for these the reliance is on the Lean kernel and on the matching statements. Only ten of the 293 sources were re-elaborated by the reviewer; one of the longest modules (`S4R_21_022_057`) was not completed in the review session (it was built, 728 s, in the development repository).
5. **Rebuild cost and danger.** A rebuild of the closure from a clean tree took, in the development repository, about 4.5 hours of wall time over 296 build jobs (including reruns, failures and negative controls), the longest module 728 s, the check of `S4Final` itself 6.3 GB, several modules with sampled peaks above 10 GB, the largest 10.6 GB (Section 9), and the closure has 293 modules. Do NOT run a bare `lake build` of `S4Final` from a clean tree. Lake builds modules in parallel: on 2026-11-13 a parallel rebuild of seven failed layer modules was sampled at 29.6 GB on a 24 GB machine before a watchdog killed it. Build the closure one module at a time in the order of `lean/S4_BUILD_ORDER.txt`, with a memory watchdog on the whole process tree (Section 11). The range modules are split because the initial partition into 110 modules exceeded 10.8 GB in several cases.
6. **Build scope.** No whole-library `lake build` was run. The modules were built one at a time, and the axioms were observed per module and for the final theorems. The Lean trust base includes all earlier `RFive*`, `TPFour*`, `TPThree*`, `RQ*`, `RSeven*` and `RQ3*` modules and the generated data modules `TPFData` and `TPFCheck`, whose mathematics was not re-examined for this release.
7. **Naming limitation.** As in version 1.5.0, the name `badSet` is declared in the archived `RQPigeon` and in two older development modules that are not in this archive (`BadTripleFamilies`, `PerturbStrip`), so those cannot be imported together with this family in one file; the library root file `lean/LRSpectrumFull.lean` is not updated and was already not buildable as a whole.
8. **Comments.** The 253 added Lean files were copied byte for byte. The header comments of 216 of the 293 closure files cite development files by path (a path below the directory of the development repository that holds the work of November 2026); in two files (`RQGen.lean`, `TPThreeA.lean`) a comment calls a building session by a role word, and in one of them (`TPThreeA.lean`) a comment names a model. The files cited are not archived. The generated data modules (`S4R_*`, `S4B_*`, `TCP_*`, `S4A_*`, `S4All_*`) are mapped to this note as follows: the header "generated by s4gen block2 (...s4_range/census_b)" or "s4asm (...s4_asm/gen)" names the generator, whose sources are in `code/s4-range/gen`; "generated (s4_asm/layers.py)" names `code/s4-range/layers.py`; the argument to which the headers of the hand-written modules refer is written out in Sections 3 to 7 of this note.

### Census (computed; generator `code/rq-census/v2` and `code/s4-range/gen`)

Universe: 4-sets of distinct positive integers with gcd 1 and sum at most 195; 2,133,561 vectors (the count of Alcantara, Criado and Santos, Theorem 1.3 there). Numbers from the census of version 1.5.0 and from the Rust mirror of `classB` (`code/s4-range/gen`, mode `census`, in the same enumeration):

| set of vectors | count |
|---|---|
| primitive vectors, sum <= 195 | 2,133,561 |
| in a class with a Lean class theorem (R5, P3, QGen, T, G24, R7, Q3) | 2,002,342 |
| accepted by the Lean test `classB` (mirror) | 2,002,342 |
| in a class but missed by `classB` (mirror) | 0 |
| accepted by `classB` but not in a class (mirror) | 0 |
| not in a class: handled by certificates | 131,219 |
| of which: depth-0 certificates (`.d0` records in the data modules) | 130,914 |
| of which: exact time covers (`.pre` records and `tcs_` theorems) | 305 |

Class sizes (a vector can be in several classes): R5 1,237,736; P3 750,712; QGen (q >= 4, contains Q4) 416,974; T 500,937; G24 423,532; R7 576,799; Q3 611,118. The 305 vectors without a depth-0 certificate are by first coordinate: a = 1: 237; a = 2: 3; a = 3: 39; a = 4: 26. They include the three tight vectors (1,2,3,4), (1,3,4,6), (1,3,4,7), for which the worst case over the phases is exactly 1/5 (see Section 5 for what was recomputed) and which have no depth-0 certificate at all (exhaustive search by the building session). The counts 130,914 and 305 were re-counted from the text of the archived Lean files for this release (130,914 lines `.d0 `, 305 theorems `tcs_`, 305 `.pre` records, no inline time cover).

## Conceptual abstract

Every speed vector with sum at most 195 is either in a class for which a computation-free proof exists (the class test), or has a finite certificate of one of two kinds: a depth-0 certificate (three integer vectors and six integer inequalities, which give the conclusion by a rounding argument and a one-dimensional Helly step), or, for 305 vectors including the three tight ones, a time cover (a finite set of rational times whose closed "good boxes" cover the three-dimensional torus of the other three phases). A Boolean loop enumerates all vectors in a fixed order, consumes the certificate list in lockstep and falls back on the class test; the Lean kernel evaluates the loop, and a loop-invariant lemma turns "the loop returns true" into the statement for every vector in the range. The certificates are untrusted data.

## Outline

1. Conventions and the statement.
2. Architecture of the proof.
3. The class test `classB` and the permutation lemma.
4. Depth-0 certificates and `d0_sound`.
5. Time covers and `tc_sound`.
6. The loop and its invariant.
7. Assembly and exhaustiveness.
8. Certificate formats.
9. Cost.
10. Limitations.
11. How to rebuild.
Lean correspondence (table), provenance.

## 1. Conventions and the statement

For y in R, ||y|| = |y - round(y)| (`tpDist`), where `round` is the nearest integer, so ||y|| is the distance to Z. For a speed v in N and phase phi in R, the runner is good at time t if 1/5 <= ||v t + phi|| (`GoodR`). `S4 v` says that for every phase vector there is a time at which the four runners are simultaneously good. Phases are real, the time is chosen after the phases, and no genericity is assumed. The distinctness and the ordering of the speeds are hypotheses of the loop, not of `S4`.

Lemma 1.1 (`tpDist_ge_of_frac`, `D0Sound.lean`). If x in R, n in Z, 1/5 <= x - n and x - n <= 4/5, then 1/5 <= ||x||. Proof: let m = round(x). If m <= n, then x - m >= x - n >= 1/5 and |x - m| >= x - m >= 1/5. If m >= n + 1, then m - x >= n + 1 - x >= 1 - 4/5 = 1/5 and |x - m| >= m - x. QED.

The statement is not vacuous: the review session proved in Lean that S4 fails for the repeated speeds (1,1,1,5) (phases (0,1/5,3/5,0)), so S4 depends on its hypotheses; and `S4Final.lean` contains instances at (1,2,3,4), (1,3,4,7) and (10,20,30,40).

## 2. Architecture

(1) Class theorems. For each of the seven classes there is a Lean theorem concluding `exists t, forall i, GoodR (v i) (phi i) t` for four positive pairwise distinct speeds `v : Fin 4 -> N` and arbitrary `phi`: `R5_core` (`RFiveFinal.lean`), `P3` (`RQThree.lean`), `QGen` (`RQGen.lean`, with q = 4 giving the class Q4), `T` (`RQT.lean`), `G24` (`RQG24.lean`), `R7_partial` (`RSevenFinal.lean`), `Q3_ndvd` (`RQ3Final.lean`); their written proofs are in `paper/shifted-real-four-classes/NOTE.md` and `paper/shifted-real-four/NOTE.md`. They are used here as imported theorems. A Boolean function `classB a b c d` (`S4Class.lean`) tests, in integer arithmetic, whether a sorted vector satisfies the hypotheses of one of them for some assignment of roles; `classB_sound` proves that `classB = true` implies `S4`.

(2) Certificates. The vectors not accepted by `classB` are given a record in a list: a depth-0 record (checked by `recOK3`, soundness `d0_sound`), or a pointer `.pre` to a vector whose `S4` has been proved by a time cover (`tc_sound`).

(3) The loop (`S4Loop.lean`, `S4Loop2.lean`). For a fixed first speed a and a range of second speeds b, the loop `rangeB` enumerates (b,c,d) with b < c < d and sum at most 195 in a fixed order, skips the non-primitive vectors, and for each primitive vector accepts if the next record certifies it, else if `classB` holds, else the whole check fails; at the end the record list must be exhausted. `rangeOK_sound` and `rangeOK2_sound` turn `rangeB = true` into the statement for all primitive (b,c,d) in the range.

(4) Assembly. 175 range theorems (156 modules `S4R_*`, five probe modules `S4Range*`, 14 blocked-range modules `S4B_*`, the last with 11 time-cover modules `TCP_*`) cover every pair (a,b) exactly once (1,488 pairs); 47 modules `S4A_<aa>` (one per a) join the b-intervals of one a by an `omega` case split; five modules `S4All_<k>` join groups of values of a; `S4Final` joins the five groups (a <= 47 because 4a + 6 <= 195 is necessary).

## 3. The class test and the permutation lemma

Definitions (`S4Class.lean`, all scalar `Nat` arithmetic, short-circuit `Bool`): `r5B` (some speed divisible by 5, some not); `fP3` (q = gcd of three speeds is at least 2 and does not divide the fourth); `fT` (some q in 6..gcd(x,y) divides gcd(x,y) and is coprime to the other two speeds); `fQ` (the same with q >= 4, plus congruence up to sign of the two other speeds modulo q and non-resonance of x and y, where `nonresB s a b` says s != a + b, a != b + s, b != a + s); `fQ3` (x, y divisible by 3, u, w not, non-resonance); `fG24` (x, y odd, u = 2 mod 4, w = 0 mod 4, w non-resonant against x, y); `fR7` (patterns (A) and (B) with the exclusion clause, written with `Sim7 x y := x % 7 = y % 7 \/ (x + y) % 7 = 0`). `classB` is the disjunction of `r5B`, `anyPerm g24L fG24`, `anyPerm p3L fP3`, `anyPerm pairL fPair` (with `fPair = fT || fQ || fQ3`) and `anyPerm r7L fR7`, where `anyPerm L f a b c d` tests `f` on the speeds rearranged by every index quadruple in the list `L`.

Lemma 3.1 (`S4_of_cover`, `S4Perm.lean`). Let v, w : Fin 4 -> N with v injective, and assume every w r equals some v s and every v j equals some w r. If `S4 w` then `S4 v`. Proof: given phi, choose s with w r = v (s r); apply `S4 w` to the phases phi (s r), obtaining t; for each j pick r with w r = v j; then s r = j by injectivity, so the runner j with speed v j and phase phi j is good at t. QED.

Lemma 3.2 (`anyPerm_sound`, `S4Perm.lean`). Let L be a list of index quadruples each of which is a permutation of {0,1,2,3} (`IsPerm`; checked once per list by `decide`: `pairL_ok`, `p3L_ok`, `g24L_ok`, `r7L_ok`), and let f be a scalar test that is sound for four positive pairwise distinct speeds (f x y u w = true implies `S4q x y u w`). If `anyPerm L f a b c d = true` and a, b, c, d are positive and pairwise distinct, then `S4q a b c d`. Proof: some quadruple p in L has f true on the rearranged speeds; the rearranged speeds are positive and pairwise distinct (`sel_pos`, `sel_ne`); apply Lemma 3.1 to the rearranged vector, whose entries cover the original ones because p is a permutation. QED.

Lemma 3.3 (`sound_P3`, `sound_T`, `sound_Q`, `sound_Q3`, `sound_Pair`, `sound_G24`, `sound_R7`, `sound_R5`, `S4Class.lean`). Each scalar test implies `S4q`, by applying the corresponding class theorem to `![x,y,u,w]` with the roles 0 1 2 3 and discharging its hypotheses from the Boolean test (unfolding `decide`, `Nat.Coprime`, divisibility from `mod`, and, for R7, a conversion of the mod-7 pattern to the integer hypothesis of `R7_partial` by `omega`). Sketch; the Lean declarations are the proofs.

Theorem 3.4 (`classB_sound`). If 0 < a < b < c < d and `classB a b c d = true`, then `S4 ![a,b,c,d]`. Proof: the speeds are positive and pairwise distinct; each disjunct is handled by Lemma 3.3 (the first directly, the others through Lemma 3.2). QED.

Coverage statement (COMPUTED, not a Lean theorem): `classB` accepts exactly the 2,002,342 vectors of the census (Rust mirror with the same lists and tests; the Lean `classB` was checked by `decide +kernel` on seven positive examples and five negative controls in a checking file of the development repository, `S4Check`, which is not archived, and, implicitly, by the range modules).

## 4. Depth-0 certificates and `d0_sound`

Definitions (`D0Core.lean`). For v, k1, k2, k3 : Fin 4 -> Z put g_l(i,j) = k_l(j) v(i) - k_l(i) v(j), sumG(i,j) = |g_1(i,j)| + |g_2(i,j)| + |g_3(i,j)|, and detC = the 4x4 determinant of the matrix with columns v, k1, k2, k3 (`det4`, a Laplace expansion proved equal to Mathlib's determinant, `det4_eq`). The predicate `D0cert v k1 k2 k3` says: detC != 0 and, for each of the six pairs 0<=i<j<=3, 5 sumG(i,j) <= 3 (v(i) + v(j)). It is decidable by `decide`. This is our re-derivation in runner coordinates of the depth-0 certificate of Alcantara, Criado and Santos, as we read that paper.

Theorem 4.1 (`d0_sound`, `D0Sound.lean`). For v, k1, k2, k3 : Fin 4 -> Z with 0 < v i for all i, and `D0cert v k1 k2 k3`, and every phi : Fin 4 -> R, there is t in R with 1/5 <= ||v_i t + phi_i|| for all i. Only 0 < v i and the certificate are used (not distinctness, not gcd, not |det| = 1). `d0_sound_nat` (`D0Bridge.lean`) states `S4 v` for natural speeds from `D0cert` of the integer cast.

Lemma 4.2 (`pair_all`, `D0Core.lean`). Under 0 < v i and the certificate, 5 sumG(i,j) <= 3 (v(i) + v(j)) for all ordered pairs (i,j). Proof: sumG(j,i) = sumG(i,j) because g_l(j,i) = -g_l(i,j) (`sumG_comm`), sumG(i,i) = 0 (`sumG_self`), and the six given inequalities are the unordered pairs; the case i = j needs 0 <= 3 (v i + v i), which holds by positivity (`omega`).

Lemma 4.3 (`solve4`, `D0Sound.lean`). If detC != 0 then for every psi : Fin 4 -> R there is a : Fin 4 -> R with psi_r = a_0 v_r + a_1 k1_r + a_2 k2_r + a_3 k3_r for all r. Proof: the real matrix M with columns v, k1, k2, k3 has determinant equal to the integer detC cast to R (`det4_eq` and a direct expansion), which is non-zero, so M is invertible and a = M^{-1} psi. QED.

Proof of Theorem 4.1, following `d0_sound`. Step 1 (coordinates). Put psi = phi - 1/2 (componentwise) and take a from Lemma 4.3. Step 2 (rounding). Let n_l = round(a_l) in Z and y_l = a_l - n_l, so |y_l| <= 1/2 (`abs_sub_round`), for l = 1,2,3. Put X_i = y_1 k1_i + y_2 k2_i + y_3 k3_i (real) and K_i = n_1 k1_i + n_2 k2_i + n_3 k3_i (an integer). Then phi_i = a_0 v_i + X_i + K_i + 1/2 (`hpsi`). Step 3 (pair bound). X_j v_i - X_i v_j = y_1 g_1(i,j) + y_2 g_2(i,j) + y_3 g_3(i,j), so |X_j v_i - X_i v_j| <= (1/2) sumG(i,j) <= (3/10)(v_i + v_j) by Lemma 4.2 (`hpair`). Step 4 (a one-dimensional Helly step, done by hand). Let lo_j = (-3/10 - X_j)/v_j; choose i0 maximising lo_j over j (`Finset.exists_max_image`), and s = lo_{i0}. Then s >= lo_j, that is -3/10 <= X_j + s v_j for all j (`hs_lo`). Also X_j + s v_j <= 3/10 for all j (`hs_hi`): otherwise v_{i0} (X_j + s v_j - 3/10) > 0, and v_{i0}(X_j + s v_j - 3/10) = (X_j v_{i0} - X_{i0} v_j) - (3/10)(v_{i0} + v_j), using s v_{i0} = -3/10 - X_{i0}; this is <= 0 by Step 3 for the pair (i0, j), a contradiction. Step 5. Put t = s - a_0. Then v_i t + phi_i = K_i + 1/2 + (X_i + s v_i), and X_i + s v_i + 1/2 lies in [1/5, 4/5]. Lemma 1.1 with n = K_i gives 1/5 <= ||v_i t + phi_i||. QED.

The kernel part: `D0Chunk.lean` defines the record `Rec` (16 integers: v0..v3, then k1 = (a0..a3), k2 = (b0..b3), k3 = (c0..c3)) and `recOK` (positivity and `D0cert`); `D0Fast.lean` defines a faster scalar checker `recOK3` (the six inequalities as `Nat` comparisons of `natAbs` values and a 4x4 determinant by scalar expansion) with `recOK3_imp : recOK3 r = true -> recOK2 r = true`, `recOK2_imp : recOK2 r = true -> recOK r = true`, and `recOK_sound : recOK r = true -> S4 r.vn` (from `d0_sound_nat`); hence `recOK3_sound`. The reviewer read the signatures of this chain and not the proof of `recOK_sound`.

## 5. Time covers and `tc_sound`

Idea. For four speeds, shift time so that runner 0 has phase 0. The remaining three phases are a point of a three-dimensional torus. A rational time n/q makes runner c good for the phases in a closed arc of length 3/5 of the circle; the three arcs together are a closed box. If finitely many boxes cover the torus, the statement holds. The cover is checked on a finite grid of "pieces".

Pieces. For y in R the integer floor(y) + ceil(y) is 2j if y = j and 2j + 1 if j < y < j + 1: it names the point or open cell of the grid Z containing y. Put M = 10 q.

Definitions (`TCArc.lean`, `TCCover.lean`, `TCSound.lean`). `wv q v n = (10 v n + 8 q) mod 10 q`. `tcBoxes q v0 v1 v2 v3 times` keeps the numerators n with `wv q v0 n <= 6 q` and maps each to the triple (wv q v1 n, wv q v2 n, wv q v3 n). `coverB M2 L2 bs` is the Boolean check below. `tcOK v0 v1 v2 v3 q times = decide (0 < q /\ 0 < v0) && coverB (10 q) (6 q) (tcBoxes ...)`.

Lemma 5.1 (`arc_of_floor_ceil`). For y in R and integers c, r, L with 0 <= r <= 2L: if floor(y) + ceil(y) = 2c + r then c <= y <= c + L. Proof: ceil(y) <= floor(y) + 1, so 2c + r <= 2 floor(y) + 1, and r >= 0 gives floor(y) >= c, so y >= floor(y) >= c; also floor(y) >= ceil(y) - 1, so 2c + r >= 2 ceil(y) - 1 and r <= 2L gives ceil(y) <= c + L, so y <= ceil(y) <= c + L. QED.

Lemma 5.2 (`coord_good`). Let q > 0, v, n in N, phi in R, and p in [0, 10q) with p = (floor(5 q phi) + ceil(5 q phi)) mod 10 q. If (p + wv q v n) mod 10 q <= 6 q, then 1/5 <= ||v (n/q) + phi||. Proof: write P = floor(5 q phi) + ceil(5 q phi). Euclidean division three times gives P = p + 10 q a_1, 10 v n + 8 q = wv + 10 q a_2, p + wv = R + 10 q a_3 with R = (p + wv) mod 10 q in [0, 6 q]; hence P + 10 v n + 8 q = 10 q m + R with m = a_1 + a_2 + a_3. Put y = 5 q phi + 5 v n; then floor(y) + ceil(y) = P + 10 v n = 2 (5 q m - 4 q) + R. Lemma 5.1 with c = 5 q m - 4 q, L = 3 q gives 5 q m - 4 q <= y <= 5 q m - q. Dividing by 5 q: m - 4/5 <= v n/q + phi <= m - 1/5, that is 1/5 <= x - (m - 1) <= 4/5 for x = v n/q + phi. Lemma 1.1 finishes. QED.

Lemma 5.3 (masks; `maskAt_testBit`, `mem_dedup`, `chk3_sound`, `exists_testBit`, `TCCover.lean`). For a list of boxes and a piece p, `maskAt` is the natural number whose bit k is 1 iff (p + w_k) mod M <= L2 for the k-th box (`maskAt_testBit`: a set bit k gives k < length and the arc inequality); `tab` lists the masks for p = 0..M-1; `dedup` removes consecutive repeats, and every element of the list is kept (`mem_dedup`). The check `chk3 D1 D2 D3` tests, for every x1 in D1, every s in dedup(x1 AND y : y in D2) and every x3 in D3, that s AND x3 != 0; `chk3_sound` says that then every triple (m1, m2, m3) in D1 x D2 x D3 has (m1 AND m2) AND m3 != 0 (because m1 AND m2 is in the deduplicated middle list), and `exists_testBit` gives a common set bit.

Theorem 5.4 (`cover_sound`). If `coverB M2 L2 bs = true` then for all p1, p2, p3 < M2 there is k < length bs with (p1 + b_k.1) mod M2 <= L2, (p2 + b_k.2.1) mod M2 <= L2 and (p3 + b_k.2.2) mod M2 <= L2. Proof: the masks of p1, p2, p3 are in the three deduplicated tables (`mem_tab`); Lemma 5.3 gives a common bit k; `maskAt_testBit` in each coordinate. QED.

Theorem 5.5 (`tc_sound`, `TCSound.lean`). If `tcOK v0 v1 v2 v3 q times = true` then `S4 ![v0,v1,v2,v3]`. Proof: let phi be given. Put tau = -phi_0/v0 (v0 > 0), so that phi_0 + v0 tau = 0. For i = 1,2,3 let p_i = pidx(q, phi_i + v_i tau) in [0, 10 q) (`pidx_nat`). `cover_sound` gives a box k, which is (wv q v1 n, wv q v2 n, wv q v3 n) for an admissible numerator n (wv q v0 n <= 6 q). Apply `coord_good` to the four runners with the phases phi_i + v_i tau, using p = 0 for runner 0 (floor(0) + ceil(0) = 0, and wv q v0 n < 10 q so the inequality is wv q v0 n <= 6 q). Then each runner i is good at the time n/q + tau for the original phase phi_i. QED.

Soundness uses only closed boxes. The three tight vectors have worst-case value exactly 1/5 over the phases, so a strict version is false. Recomputed in exact integer arithmetic for the release review (grid of denominator 720720, which contains all breakpoints of these piecewise linear functions): for (1,2,3,4) and for (1,3,4,7) with phi = 0, max_t min_i ||v_i t|| = 1/5, attained at t = 1/5. For (1,3,4,6) the value at phi = 0 is 2/7, so its tightness lies at other phases and rests on the closed-semantics test of the building session, which was not recomputed for this release. That test: the full set of admissible times of (1,3,4,6), (1,2,3,4) and (1,3,4,7) covers with closed arcs and does not cover with open arcs.

## 6. The loop and its invariant

Types (`S4Loop.lean`, `S4Loop2.lean`). `Cert2` has three constructors: `d0 vb vc vd a0 .. c3` (literals b, c, d and twelve integers), `tc vb vc vd q times` (an inline time cover, defined and proved sound, not used in the archived data), and `pre vb vc vd` (the vector (a,vb,vc,vd) must be in a list L of vectors proved separately: `PreOK L := forall x in L, S4 ![x.1, x.2.1, x.2.2.1, x.2.2.2]`). `certOK2 L a b c d r` checks that (b,c,d) equals the literals and the certificate (`recOK3` on the record, `tcOK`, or `inL`). `Cert` of `S4Loop.lean` has `d0` and `other` only and is used by the 161 modules `S4R_*` and `S4Range*`; `Cert2` is used by the 14 modules `S4B_*`.

Definitions. `Claim a b c d := gcd(gcd a b)(gcd c d) = 1 -> S4 ![a,b,c,d]`. `step L a b c d cs`: if the gcd is not 1 return `some cs`; else if the next record certifies the vector return `some` of the rest; else if `classB a b c d` return `some cs`; else `none`. The three nested loops `goD2`, `goC2`, `goB2` run d over c+1 .. c + (195 - a - b - 2c), c over b+1 .. b + ((194 - a - b)/2 - b) and b over blo .. blo + n - 1, which are exactly the vectors with b < c < d and a + b + c + d <= 195. `rangeB2 L a blo n cs` returns `true` iff `goB2` returns `some []` (the record list is exhausted).

Lemma 6.1 (`step2_sound`). If 0 < a < b < c < d and `step2 L a b c d cs = some cs'` then `Claim a b c d`. Proof: by cases on `cs`; the three accepting branches are `certOK2_sound` (with `d0_sound` through `recOK3_sound`, `tc_sound`, `inL_sound`) and `classB_sound` (Theorem 3.4); the rejecting branch gives `none`. Note that soundness does not depend on the lockstep: a record that does not match is simply not used and the vector falls to `classB` or is rejected; exhaustion of the record list is an additional completeness check that the kernel verifies but the soundness proof does not use.

Lemma 6.2 (loop invariant; `goD2_sound`, `goC2_sound`, `goB2_sound`). If `goD2 L a b c n d cs = some cs'` and c < d then `Claim a b c e` for all e with d <= e < d + n. If `goC2 L a b n c cs = some cs'` and b < c then `Claim a b e d` for all e, d with c <= e < c + n, e < d and a + b + e + d <= 195. If `goB2 L a n b cs = some cs'` and a < b then `Claim a e c d` for all e, c, d with b <= e < b + n, e < c < d and a + e + c + d <= 195. Proof: induction on n; the successor step unfolds one iteration, uses `step2_sound` for the current vector and the induction hypothesis for the rest, and the side conditions on the ranges are discharged by `omega`. QED.

Theorem 6.3 (`rangeOK2_sound`; `rangeOK_sound` for `Cert`). If `PreOK L`, 0 < a, a < blo and `rangeB2 L a blo n cs = true`, then for all b, c, d with blo <= b < blo + n, b < c < d, a + b + c + d <= 195 and gcd(gcd a b)(gcd c d) = 1: `S4 ![a,b,c,d]`. Proof: Lemma 6.2 for `goB2` with the exhausted list. QED. (`S4PreApp.lean` adds `preOK_append : PreOK L1 -> PreOK L2 -> PreOK (L1 ++ L2)`, used to join the lists of the `TCP_*` modules.)

A data module (`S4R_<aa>_<blo>_<bhi>`) contains the list `certs_a_blo_bhi : List Cert`, the theorem `rng_... : rangeB a blo n certs = true := by decide +kernel`, and `s4_range_... := rangeOK_sound _ _ rng_...`. A blocked-range module `S4B_*` first proves, for each time-cover vector, `tcv_a_b_c_d : TC.tcOK a b c d q [...] = true := by decide +kernel` and `tcs_a_b_c_d : S4 ![a,b,c,d] := TC.tc_sound ... tcv_...` (one declaration per cover, each with a fresh kernel cache; a version with the covers inline was killed at 10.8 GB), assembles `preOK_...` by a case split over the list, and applies `rangeOK2_sound`.

## 7. Assembly and exhaustiveness

`S4A_<aa>` (47 modules, a = 1..47) states `forall b c d, a < b -> b < c -> c < d -> a + b + c + d <= 195 -> gcd(...) = 1 -> S4 ![a,b,c,d]`. Its proof introduces the hypotheses, proves by `omega` the disjunction `hcase` that b lies in one of the intervals [blo, blo + n) of the range theorems of this a, and applies the corresponding range theorem in each branch. If the intervals left a gap, `omega` would fail; the kernel check of `hcase` is therefore the exhaustiveness proof. `S4All_<k>` (k = 1..5, a in 1..10, 11..20, 21..30, 31..40, 41..47) splits on a by `omega` and applies `S4A_a`. `S4Final` proves by `omega` that 1 <= a <= 47 (from 4a + 6 <= 195 and a < b < c < d) and splits into the five groups. As a text-level cross-check (not part of the proof) `code/s4-range/check_layers.py` parses the 175 range statements, checks for each a that the intervals of `S4A_a` are contiguous from a + 1 to floor((192 - a)/3) with no gap or overlap and that each cited theorem has the matching (a, blo, n), and that the groups cover a = 1..47 (output of this release: 175 statements parsed, 0 problems).

Corollaries (`S4Cor.lean`, generic in the statement `SortedStmt` of `sLRC4_le195`; `S4Final` instantiates them). `cor_fin`: for injective positive v : Fin 4 -> N with `Finset.univ.gcd v = 1` and sum <= 195, sort v by `Tuple.sort`, apply the sorted statement (the sorted vector is strictly increasing, has gcd 1 and the same sum) and transfer back by `S4_of_cover`. `cor_any`: let g = gcd of v; the vector v/g is injective with gcd 1 and sum <= 195; if t works for v/g with phases phi_i, then t/g works for v with phases phi_i (the position v_i t/g + phi_i = (v_i/g) t + phi_i).

## 8. Certificate formats

Depth-0 record (130,914 of them, one per vector, sorted in the loop order of the module): `.d0 vb vc vd a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3`, that is three literals (the b, c, d of the vector, checked by the loop to equal the current vector) and 12 integers: k1 = (a0..a3), k2 = (b0..b3), k3 = (c0..c3) as in Section 4 (the first speed a is the module's). Source size about 51 bytes per record.

Time-cover record (305): a denominator q > 0 and a list of numerators n_1 < ... < n_N, the times n/q; `tcOK v0 v1 v2 v3 q times`. For the three tight vectors: (1,2,3,4): q = 60, N = 27; (1,3,4,6): q = 20, N = 12; (1,3,4,7): q = 60, N = 20. Over the 305 covers q lies in 15..60 and the number of numerators has median 13 and maximum 27 (building-session report). The loop sees a time-cover vector as `.pre vb vc vd`.

## 9. Cost

Measured in the development repository on 2026-11-13 on a shared 10-core, 24 GB machine (load 20 to 90 during part of the builds; peaks are samples of the resident memory of the whole process tree every 2 seconds, so short spikes can be missed; times are wall times of `lake build` of one module, including the import of Mathlib, about 5.6 GB of memory-mapped oleans and 10 to 13 s).

| item | modules | time | peak memory |
|---|---|---|---|
| range modules `S4R_*` (driver log, 156 successful builds) | 156 | sum 12,007 s, longest 728 s (`S4R_21_022_057`) | up to 10,614 MB (`S4R_16_017_030`, 240 s); kill line of the watchdog 10,800 MB |
| failed builds of the initial partition (110 modules, before the split into 156) | 6 lines | 59 to 411 s | five memory failures at 10,796 to 11,371 MB (four killed by the watchdog at 10,847 to 11,371 MB; one ended with Lean exit code 137 at a sampled 10,796 MB, without the watchdog flag); one build (`S4R_03_022_028`, 6,357 MB) killed by the disk-floor check of the wrapper (`WATCHDOG KILL disk 1GB`: free disk had fallen to 1 GB because of space used outside this project; it was not a memory failure; old logs were compressed and the module was rebuilt successfully, 211 s, 9,654 MB) |
| blocked ranges `S4B_*` (12 built in the assembly block) | 14 | 46 to 207 s each (a = 1, b = 2: 66 s) | 7,502 to 9,178 MB (`S4B_01_006_007`, 207 s); the two built earlier: 8,484 and 8,937 MB |
| time-cover modules `TCP_*` | 11 | 19 to 81 s each | 6,493 to 7,701 MB |
| `S4PreApp`, `S4Cor` | 2 | 15 s, 21 s | 5,999 and 6,059 MB |
| layers `S4A_<aa>`, `S4All_5` | 47 + 5 | 10 to 14 s | 5.7 to 6.2 GB |
| `S4Final` (check of the final module, all oleans present) | 1 | 11 s | 6,283 MB |
| all logged build jobs of the range and assembly blocks (reviewer's sum) | 296 | 16,282 s (4.5 h), including reruns, failures and negative controls (16 non-zero exits) | |

Largest memory samples, with scope (resident memory of the whole process tree, 2-second samples, all logs of the range, assembly and time-cover builds): 10,614 MB for a successfully built single module (`S4R_16_017_030`; six successful range modules exceeded 10,000 MB); 11,371 MB for a single-module build that the watchdog killed (`S4R_04_027_062`); 29,598 MB for the one parallel rebuild of seven modules (killed). The figure 9,178 MB is the largest peak of the blocked-range modules `S4B_*` only, not of the whole build.

Per-record cost: a depth-0 check on a bare list costs about 10 to 17 ms per record in the kernel; inside the loop 0.06 to 0.14 s per record (the cause of the factor 3 to 7 was not found); a time-cover unit (one box tested at one piece, one mask step) costs 100 to 250 microseconds and about 13 KB of kernel memory, the three tight covers needing 100,380, 12,144 and 62,340 units. The class-only vectors cost 0.6 to 3 ms each.

Memory model for a module of the initial partition (least squares over the 99 modules built before the split): peak in MB = 6277.1 + 0.07037 E + 0.4990 R, where E is the number of vectors enumerated by the module and R its number of records. Root mean square error 566 MB; worst residuals +1,137 MB (`S4R_12_025_060`, measured peak 10,200 MB) and -2,104 MB (`S4R_09_029_042`). It underestimated the five failed modules by 1.0 to 1.5 GB (predicted 9.8 to 10.4 GB, actual 10.8 to 11.4 GB). It is a trend, not a law. The split rule was: predicted peak plus 1,137 MB at most 8,500 MB, which is the rule for the 57 modules that replaced eleven of the initial partition; the 156 successful builds in the first line of the table include the 57 split modules.

Disk: about 10.5 KB of build output per record plus 4.9 MB of `setup.json` per module; the sources of the 253 added Lean files are 7.9 MB.

## 10. Limitations

* Speed sum at least 196 is not treated (Status).
* The statement is for four pairwise distinct positive integer speeds, with the constant 1/5; the constant is attained (exactly 1/5) at (1,2,3,4), (1,3,4,6), (1,3,4,7) with suitable phases (recomputed here only for (1,2,3,4) and (1,3,4,7) at phi = 0, see Section 5); nothing else about sharpness is claimed here. No more than four moving runners.
* The trust base: the Lean kernel; Mathlib; the statements of the seven class theorems and their proofs (not re-read by the reviewer of this release); `classB_sound` and the permutation lemma; `d0_sound`; `tc_sound` (the proofs in `D0Chunk` and `TCCover` were read by the building sessions and not by the reviewer; the kernel checks them); the loop lemmas; the `omega` case splits. The data (130,914 + 305 records and the time lists) are not trusted.
* The count of the census is computed by programs of this programme (a Rust census and an independent Python implementation, which agree at speed sum at most 60); it does not enter the Lean proof.
* Two of the generated modules (`S4B_01_002_002`, `S4B_01_003_003`) were edited by hand in one line (`preL_...` re-nested to the right, because `++` is left associative); the archived generator source was patched in the same way after the binary that produced them was compiled, so that the generator output differs from those two files in that line. The generator and the data were not re-run for this release.
* The build was done under a memory arrangement authorised for this machine (a 12 GB declared ceiling and a watchdog on the process tree); a rebuild from scratch of the archive has not been attempted.
* The reviewer re-elaborated only 10 of the 293 sources (and printed the axioms of `sLRC4_le195`, `sLRC4_le195_fin`, `sLRC4_le195_any`, `d0_sound`, `d0_sound_nat`, `TC.tc_sound`, `classB_sound`, `rangeOK_sound`, `rangeOK2_sound`, `cor_fin`, `cor_any`, `S4_of_cover`: all standard); the other modules rest on the axiom lines of the building logs.

## 11. How to rebuild

Rebuilding is expensive and has a memory hazard. Do not run `lake build LRSpectrumFull.S4Final` (or `lake build` without arguments) on a clean tree: Lake starts one worker per core, one worker on this project needed 6 to 10.6 GB, and a parallel rebuild of seven modules was sampled at 29.6 GB. Instead build the 293 modules one at a time, in the order of `lean/S4_BUILD_ORDER.txt` (a post-order of the import lines, checked so that every module comes after all its imports inside the project), each with `lake build LRSpectrumFull.<Module>`, and before building a module make sure that every module it imports already has an up-to-date `.olean` (otherwise Lake rebuilds those in parallel). A helper that builds modules one after another and watches the memory of the whole process tree is in `code/s4-range` (`build_modules.sh`, `launch_watchdog.sh`; written for macOS, edited for the archive only in its paths and comments, and not run in this form); a plain loop `for m in $(cat lean/S4_BUILD_ORDER.txt); do lake build LRSpectrumFull.$m || break; done` from `lean/` does the same without the watchdog (the existing `code/lean_build/gbound_build.sh` also builds its arguments one at a time and stops on the first failure). Expect about 4.5 hours of wall time on the machine described in Section 9, with single modules up to about 10.6 GB. After the build, `lake env lean` on a file containing `import LRSpectrumFull.S4Final` and `#print axioms LRSpectrumFull.D0.sLRC4_le195` should print `[propext, Classical.choice, Quot.sound]`.

## Lean correspondence

| Part of the argument | Lean declaration (file) | Written proof |
|---|---|---|
| Statement | `S4` (`D0Bridge.lean`), `GoodR` (`RFiveBase.lean`), `tpDist` (`TPSmall.lean`) | definitions |
| Lemma 1.1 | `tpDist_ge_of_frac` (`D0Sound.lean`) | full |
| Class theorems | `R5_core` (`RFiveFinal.lean`), `P3` (`RQThree.lean`), `QGen`, `Q4` (`RQGen.lean`, `RQFour.lean`), `T` (`RQT.lean`), `G24` (`RQG24.lean`), `R7_partial` (`RSevenFinal.lean`), `Q3_ndvd` (`RQ3Final.lean`) | imported (earlier notes) |
| Lemma 3.1 | `S4_of_cover` (`S4Perm.lean`) | full |
| Lemma 3.2 | `anyPerm_sound`, `sel_pos`, `sel_ne`, `vec_inj`, `vec_pos` (`S4Perm.lean`) | full (sketch of the auxiliary lemmas; the Lean declarations are the proofs) |
| Lemma 3.3 | `sound_P3`, `sound_T`, `sound_Q`, `sound_Q3`, `sound_Pair`, `sound_G24`, `sound_R7`, `sound_R5` (`S4Class.lean`) | sketch; the Lean declarations are the proofs |
| Theorem 3.4 | `classB_sound` (`S4Class.lean`) | full |
| Definitions of Section 4 | `det4`, `det4_eq`, `detC`, `gf`, `sumG`, `D0cert` (`D0Core.lean`) | definitions |
| Lemma 4.2 | `pair_all`, `sumG_comm`, `sumG_self` (`D0Core.lean`) | full |
| Lemma 4.3 | `solve4` (`D0Sound.lean`) | full |
| Theorem 4.1 | `d0_sound` (`D0Sound.lean`), `d0_sound_nat` (`D0Bridge.lean`) | full |
| Record checkers | `Rec`, `recOK`, `recOK_sound` (`D0Chunk.lean`), `recOK2`, `recOK3`, `recOK3_sound` (`D0Fast.lean`) | sketch (the chain of implications; not re-read by the reviewer for `recOK_sound`) |
| Lemma 5.1 | `arc_of_floor_ceil` (`TCArc.lean`) | full |
| Lemma 5.2 | `coord_good`, `wv` (`TCArc.lean`) | full |
| Lemma 5.3 | `maskAt_testBit`, `mem_dd`, `mem_dedup`, `chk3_sound`, `exists_testBit`, `mem_tab` (`TCCover.lean`) | statements and proof idea; the Lean declarations are the proofs |
| Theorem 5.4 | `cover_sound`, `coverB` (`TCCover.lean`) | full |
| Theorem 5.5 | `tc_sound`, `tcOK`, `tcBoxes`, `pidx`, `pidx_nat` (`TCSound.lean`) | full |
| Certificate type, membership | `Cert2`, `PreOK`, `inL`, `inL_sound`, `certOK2`, `certOK2_sound` (`S4Loop2.lean`); `Cert`, `certOK`, `certOK_sound` (`S4Loop.lean`) | full for `inL_sound`, `certOK2_sound`; sketch otherwise |
| Lemma 6.1 | `step2_sound` (`S4Loop2.lean`), `step_sound` (`S4Loop.lean`) | full |
| Lemma 6.2 | `goD2_sound`, `goC2_sound`, `goB2_sound` (`S4Loop2.lean`); `goD_sound`, `goC_sound`, `goB_sound` (`S4Loop.lean`) | statements and proof idea (induction, `omega`); the Lean declarations are the proofs |
| Theorem 6.3 | `rangeOK2_sound` (`S4Loop2.lean`), `rangeOK_sound` (`S4Loop.lean`), `preOK_append` (`S4PreApp.lean`) | full |
| Data modules | `s4_range_*` (`S4R_*`, `S4Range*`), `s4_blk_*` (`S4B_*`), `tcv_*`, `tcs_*`, `preOK_*` (`S4B_*`, `TCP_*`) | none (generated data and one-line applications of Theorem 6.3) |
| Section 7 | `S4A_<aa>` (`S4A_01.lean` ... `S4A_47.lean`), `S4All_1` ... `S4All_5`, `sLRC4_le195` (`S4Final.lean`) | full (case splits by `omega`) |
| Corollaries | `cor_fin`, `cor_any`, `SortedStmt` (`S4Cor.lean`), `sLRC4_le195_fin`, `sLRC4_le195_any` (`S4Final.lean`) | full for `cor_fin`; sketch for `cor_any` |

## Provenance

The results were obtained with the assistance of an AI system (Claude, Anthropic). The questions and research directions came from the author. The Lean sources, the generators and the written proofs were produced by the AI system; the Lean theorems are checked by the Lean kernel, the Lean statements and sources were read or re-run by a further session of the same system (a review with the verdict SOUND-WITH-CAVEATS, which did not re-read the proofs of the seven class theorems, of `recOK_sound` and of the time-cover checker), and the written proofs above were transcribed from the Lean files by the AI system; the text of this note has not had an independent read. The author is responsible for all claims.
