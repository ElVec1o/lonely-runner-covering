# Four moving runners with real phases when a speed is divisible by 5: a computation-free proof and its Lean version

Vico Bonfioli. Version of 12 November 2026 (release 1.3.0 of this archive). Preprint note, not peer reviewed.

## Status

* **Statement (Theorem R5).** Let v_1, ..., v_4 be pairwise distinct positive integers with gcd 1, at least one of them divisible by 5, and let phi_1, ..., phi_4 be arbitrary real numbers. Then there is a real t with ||v_i t + phi_i|| >= 1/5 for i = 1, ..., 4 (non-strict inequality), where ||y|| = |y - round(y)| is the distance from y to the nearest integer.
* **What the proof gives.** Theorem R5_core: the hypothesis gcd = 1 is replaced by "some v_i is not divisible by 5" (and some v_i is divisible by 5). Theorem R5_gcd: with g the gcd of the four speeds, the conclusion holds whenever 5 divides v_i / g for some i. Theorem R5 is the case g = 1 of R5_gcd, and follows from R5_core because gcd = 1 forces a speed not divisible by 5.
* **Lean entry points.** `LRSpectrumFull.R5` and `LRSpectrumFull.R5_core` in `lean/LRSpectrumFull/RFiveFinal.lean`; `LRSpectrumFull.R5_tp` and `LRSpectrumFull.R5_gcd` in `lean/LRSpectrumFull/RFiveCor.lean`. The seven modules `RFiveBase`, `RFiveWindow`, `RFiveCluster`, `RFiveLemS`, `RFiveCase`, `RFiveFinal`, `RFiveCor` were built on 2026-11-12 in the development repository, one module at a time. The axioms `propext`, `Classical.choice`, `Quot.sound` were observed for `R5`, `R5_core`, `R5_tp`, `R5_gcd` by a fresh review session, and for the intermediate declarations `caseHR`, `lemSR`, `cluster_div`, `case3R`, `case21R`, `lemma4R`, `exists_exactR`, `three_free`, `exists_coincide`, `goodR_of_not_mem_badImg`, `step_le2R` by the building session. No `sorry`, no `native_decide`. Review verdict: SOUND-WITH-CAVEATS. The builds are carried over to this archive and were not repeated for it. The proof does not use `five_runners` or any enumeration.
* **Text of the release (base wording of the review).** A Lean 4 formalization of a computation-free argument that for four distinct positive integer speeds v_i and arbitrary real phases phi_i, if gcd(v) = 1 and some v_i is divisible by 5 (for speeds with a common factor g: if some v_i / g is divisible by 5), some real t has ||v_i t + phi_i|| >= 1/5 for all i. This is a special case of the shifted lonely runner conjecture for four moving runners, proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379, Corollary 1.4); it is not a new theorem. We found no computation-free proof of this sub-case in the sources we hold, which does not show that none exists. Not covered: speed vectors with no multiple of 5 after removing common factors, including the vectors (1,2,3,4), (1,3,4,6), (1,3,4,7) that are tight in that paper. The constant 1/5 is not claimed sharp for this class. Trust base: Lean 4.30.0 and Mathlib, axioms `propext`, `Classical.choice`, `Quot.sound` only, no `sorry`, no `native_decide`.

### Caveats that bind every use of this note

1. **Not a new theorem.** The statement is a special case of the shifted lonely runner conjecture for four moving runners, proved with computer assistance by Alcantara, Criado and Santos, arXiv:2506.13379 (Corollary 1.4; we read version 1 of that paper; its journal status was not checked). Their theorem covers all four distinct positive speeds and all real phases, with the constant 1/5.
2. **Contribution and prior art.** What this note offers is a computation-free proof of the sub-case "some speed divisible by 5" and its Lean version. We found no computation-free proof of this sub-case in the sources we hold, which does not show that none exists. The reading was local. Held and read (to the extent stated in `RELEASE_CHECK.md`): Alcantara-Criado-Santos, version 1, end to end; Cslovjecsek-Malikiosis-Naszodi-Schymura, arXiv:2009.12080, Section 1 and Section 4; Blanco-Criado-Santos, arXiv:2603.24784, parts; Beck-Everett, Zhang, Poliakova, the survey of Perarnau and Serra, Barajas and Serra (arXiv:0710.4495), Tao, Rosenfeld in parts or by search. Not held, so not read: Malikiosis-Santos-Schymura (arXiv:2411.06903; Forum Math. Sigma 13 (2025), e164); the published version of Alcantara-Criado-Santos; Beck-Hosten-Schymura, "Lonely runner polyhedra" (Integers 19 (2019), A29); Rifford (Acta Appl. Math. 180 (2022)); Henze-Malikiosis (Aequationes Math. 91 (2017)); Bohman-Holzman-Kleitman (2001); Renault (Discrete Math., 2004); Cusick-Pomerance (1984); Barajas-Serra, "On the chromatic number of circulant graphs" (Discrete Math. 309 (2009)). For zero phases, Section 3 of Barajas and Serra (arXiv:0710.4495) treats the five-runner case of the unshifted conjecture; as we read it, a reduction leaves the case of three speeds prime to 5 and one divisible by 5, which they settle by an explicit computation with multipliers. Only the first part of that paper was read. We did not establish whether their argument extends to real phases, and we do not claim that it does not.
3. **Not covered.** Speed vectors with no multiple of 5 after removing common factors. These include the three vectors (1,2,3,4), (1,3,4,6), (1,3,4,7) that are tight for the constant 1/5 in Alcantara-Criado-Santos. The method does not reach them: the proof below uses a speed divisible by 5 in an essential way.
4. **The constant 1/5 is not claimed sharp for this class.** The smallest value found in computer searches over this class is 5/24, at the speeds (2,3,5,7). This is computed evidence, not a proof. Range, as recorded: all 2,874 speed vectors 1 <= v_1 < v_2 < v_3 < v_4 <= 20 with gcd 1 and a multiple of 5, with phi_1 = 0 and phi_2, phi_3, phi_4 on the grids (1/q)Z for q = 7, 12, 20, 30, 60 (exhaustive for each q); a second search, in floating point (the value at (2,3,5,7) was recomputed exactly), over all such speed vectors with maximum speed up to 30 on several grids (for example q = 12 at maximum speed 30, q = 60 and 120 at maximum speed 8) gave the same minimum. The minimum is attained at phases (0, 12, 10, 8)/60, and also at (0, 1/4, 1/4, 1/4). A minimum over a grid is an upper bound for the infimum over all real phases. Nothing here shows that the infimum over the class exceeds 1/5 for all speeds; the theorem says it is at least 1/5.
5. **Distinctness is necessary.** For v = (1,1,1,5) and phases (0, 1/5, 3/5, 0) there is no t with all four distances at least 1/5 (Section 8 below; the best value is exactly 1/6 by an exact rational computation that is not archived).
6. **Build scope.** No whole-library `lake build` was run. The modules were built one at a time and the axioms were observed per module. The builds are carried over from the development repository.

Other scope limits: thresholds other than 1/5 and more than four moving runners are not covered. The hypothesis "some speed is divisible by 5" and the hypothesis on the gcd reflect the method; neither is shown to be necessary for the statement (the statement is a case of the theorem of Alcantara, Criado and Santos for all distinct positive speeds).

### Labels and provenance

The statements of R5, R5_core, R5_tp, R5_gcd in Lean are VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The written proof below follows the Lean proof, declaration by declaration; each lemma names the Lean declaration it corresponds to. Where the Lean proof and earlier informal drafts differ, the Lean proof is followed. The prose proof as written here has not been read by an independent reader; no blind read of the Part H kind has been run, and no human reader has checked it. The Lean statements and the kernel check are the authority.

Comments in the Lean modules of this release cite development files by their development names. The file cited in the headers of the `RFive*` modules as the paper proof is the informal draft of the argument written below; it is not archived. Its self-contained version, named in `RFiveBase` and `RFiveCluster`, is replaced by this note. The lemma numbers used in those headers are those of the draft, not of this note: draft Lemma 1 is Lemma 1 here, Lemma S is Lemma 2.5, Lemma 4 is Lemma 3.4, Lemma 6 is Lemma 3.5, Lemma 5 (the 2+1 configuration) is Lemma 5.1, and Lemma 7' with the shape R* (absorbed into one lemma in the Lean proof) is Lemma 4.5; the table "Lean correspondence" at the end gives the declaration for each lemma of this note. The headers of the `TPFour*` modules cite `HANDPROOF_v2.md`, the hand proof published as `paper/shifted-grid-four/NOTE.md`.

The results were obtained with the assistance of an AI system (Claude, Anthropic). The questions and research directions came from the author. The written proof and the Lean sources were produced by the AI system; the Lean theorem is checked by the Lean kernel, the Lean statement and the sources were read or re-run by further sessions of the same system, and the informal draft from which the written proof was transcribed was read by a further session; the text of this note has not had an independent read. The author is responsible for all claims.

## Conceptual abstract

Write the time as a whole number of fifths plus a real offset. A runner whose speed is a multiple of five sees only the offset. Every other runner, once the offset is fixed, forbids at most two of the five residue classes of the whole number. When some speed is a multiple of five and not all are, at most three runners are of the second kind. With at most two of them, counting leaves a residue. With three, either two lie in one class modulo plus-or-minus and the third in the other, and a choice of offset brings the two forbidden sets of the pair within distance one, which leaves a residue; or all three share a class, and then either two of them can be made to coincide exactly, or every pairwise speed difference divides the slow speed, and the three forbidden sets can be bunched together by a choice of offset and a small adjustment that keeps the slow runner away from zero. Phases never need to be rational.

## Outline

* Decompose t = (j+x)/5, with j a residue modulo 5 and x real (Section 1).
* At most three runners with distinct positive speeds always have a good time (Section 2).
* Two lemmas on the offset x: a window lemma and an exact-coincidence lemma (Section 3).
* A cluster lemma for three free runners in one class (Section 4).
* The two configurations of three free runners and one slow runner (Section 5).
* Assembly of R5_core, R5, R5_tp, R5_gcd (Section 6).

## 0. Conventions

||y|| denotes `tpDist y = |y - round y|` (`tpDist`, `TPSmall.lean`). For a natural number v >= 1 and a real phase phi, the runner (v, phi) is good at time t if ||v t + phi|| >= 1/5 (`GoodR v phi t`, `RFiveBase.lean`). A speed is free if 5 does not divide it, slow if 5 divides it. The residue j in Z/5 is lifted to the integer j.val in {0,...,4}.

For a free speed v and a real beta put B(v, beta) := `badImg v beta` (`TPFourLocal.lean`), the set of residues -(v^{-1} k) in Z/5 for the integers k with floor(beta) <= k <= ceil(beta). For real gamma put arc(gamma) := `arc gamma` (`TPFourArcs.lean`), the set of residues of the integers k with floor(gamma) <= k <= ceil(gamma). Then B(v, beta) = -(v^{-1}) * arc(beta) (`badImg_eq`, `TPFourArcs.lean`), equivalently j is in B(v, beta) iff -(v j) is in arc(beta) (`mem_badImg_iff`, `TPFourArcs.lean`). Two elements of one arc are equal or consecutive (`arc_adj`, `TPFourArcs.lean`).

## 1. Decomposition of the time

**Lemma 1 (decomposition).**

(a) Slow runner. For a natural number w, the runner (5w, phi) is good at (j+x)/5 iff the runner (w, phi) is good at x. In particular this does not depend on j. Lean: `goodR_mul5` (`RFiveBase.lean`).
Proof. 5w (j+x)/5 + phi = (w x + phi) + w j, and ||y + k|| = ||y|| for an integer k (`tpDist_add_int`, `TPFourBridge.lean`).

(b) Free runner. Let v be free, phi and x real, j in Z/5, beta = 5 phi + v x. If j is not in B(v, beta), then the runner (v, phi) is good at (j.val + x)/5. Lean: `goodR_of_not_mem_badImg` (`RFiveBase.lean`).
Proof. If the runner is bad at (J+x)/5, J = j.val, then some integer n has |v (J+x)/5 + phi - n| < 1/5 (`exists_near_of_not_good`, `TPFourBridge.lean`). Put k = 5n - v J. Then beta - k = 5 (v (J+x)/5 + phi - n), so |beta - k| < 1; hence floor(beta) <= k <= ceil(beta). Since k is congruent to -v J modulo 5, J = -(v^{-1} k) in Z/5, so j is in B(v, beta).

(c) Size. |B(v, beta)| <= 2, because ceil(beta) <= floor(beta) + 1. Lean: `card_badImg_le_two` (`TPFourLocal.lean`).

(d) Union bound. Let A be a finite set of free runners (v_i, phi_i), let x be real, and let b_i be bounds with |B(v_i, 5 phi_i + v_i x)| <= b_i and the sum of the b_i less than 5. Then some residue j gives a good runner for every i in A at (j.val + x)/5. Lean: `exists_resR` (`RFiveBase.lean`).
Proof. The union of the sets B has fewer than 5 elements; take j outside it and use (b).

(e) At most two free runners. Let F be a finite set of runners with at most two free ones, and let x be real such that every slow runner (v_i, phi_i) of F, replaced by (v_i / 5, phi_i), is good at x. Then some time t is good for every runner of F. Lean: `step_le2R` (`RFiveBase.lean`).
Proof. By (c) and (d) the free runners leave a common residue j (at most 4 residues are excluded). Every slow runner is good at (j.val + x)/5 by (a).

## 2. At most three runners

**Lemma 2.1 (same class).** If v_b is congruent to eps v_a modulo 5 with eps = 1 or -1, then 5 divides v_a - eps v_b. Lean: `dvd5_class` (`RFiveBase.lean`).

**Lemma 2.2 (centres in one class give equal bad sets).** Let v_b be congruent to eps v_a modulo 5 (eps = +-1), v_a free, and beta_a = eps beta_b + 5m for an integer m. Then B(v_b, beta_b) = B(v_a, beta_a). Lean: `badImg_eq_of_class` (`TPFourCoincide.lean`). The same hypotheses give: j is in B(v_b, beta_b) iff -(v_a j) is in arc(eps beta_b + 5m). Lean: `mem_badImg_class` (`TPFourWindow.lean`).

**Lemma 2.3 (coincidence).** Let v_a be free, v_b congruent to eps v_a modulo 5 (eps = +-1), phases phi_a, phi_b real, and v_a different from eps v_b as integers. Then there is a real x with B(v_b, 5 phi_b + v_b x) = B(v_a, 5 phi_a + v_a x). Lean: `exists_coincide` (`RFiveBase.lean`).
Proof. By Lemma 2.1, 5D = v_a - eps v_b with D an integer, D nonzero by hypothesis. Take x = (eps phi_b - phi_a)/D. Then 5 phi_a + v_a x = eps (5 phi_b + v_b x), because their difference is 5 (phi_a - eps phi_b) + 5 D x = 0. Apply Lemma 2.2 with m = 0.

**Lemma 2.4 (three free runners).** Let v_a, v_b, v_c be free, positive and pairwise distinct, with arbitrary real phases. Then there are a real x and a residue j that is outside B(v_i, 5 phi_i + v_i x) for i = a, b, c. Lean: `three_free` (`RFiveLemS.lean`).
Proof. Among three nonzero residues modulo 5, two lie in one class {r, -r} (`same_class_pair`, `RFiveLemS.lean`, by `decide`). For that pair, v_a is different from eps v_b as integers, since the speeds are positive and distinct (`hne_of`, `TPFourGlue.lean`; `exists_eps`, `TPFourGlue.lean`, gives the sign eps). Lemma 2.3 gives x at which the two bad sets are equal. Then the union of the three bad sets has at most 2 + 2 = 4 elements (`good_of_eq3`, `RFiveLemS.lean`), and a residue j outside it exists. This is the step where positivity and distinctness of the speeds are used.

**Lemma 2.5 (Lemma S: at most three runners).** Let F be a finite set of at most three runners with positive, pairwise distinct speeds and arbitrary real phases. Then some real t is good for every runner of F. Lean: `lemSR` (`RFiveLemS.lean`).
Proof. Strong induction on the sum of the speeds. The empty set is trivial. If at most two runners of F are free, the slow runners (v_i / 5, phi_i) are at most three in number, with positive distinct speeds and a smaller sum of speeds (`sum_div5_lt`, `TPFourReduce.lean`); by induction they have a good x, and Lemma 1(e) gives t. Otherwise F has exactly three runners, all free, and Lemma 2.4 together with Lemma 1(b) gives t.

## 3. Two lemmas on the offset

In this section D is a nonzero integer, w >= 1 is a natural number (the slow speed is 5w), and sigma, phi_d are real.

**Lemma 3.1 (perturbation).** For every real y there is a real delta with |delta| <= 1/5 and ||y + delta|| >= 1/5. Lean: `exists_perturb` (`TPFourWindow.lean`).

**Lemma 3.2 (coset).** Let p >= 2 and q be coprime integers and y real. Then some integer k has ||y + q k / p|| >= 1/5. Lean: `exists_coset_far` (`TPFourCoset.lean`; it uses `bezout_solve`, `TPFourCoset.lean`). The values y + q k / p run over a coset of (1/p)Z, whose spacing 1/p <= 1/2 is smaller than 3/5, the length of [1/5, 4/5].

**Lemma 3.3 (D does not divide w).** If D does not divide w, then some integer k has ||w (k - sigma)/D + phi_d|| >= 1/5. Lean: `coset_branchR_ne` (`RFiveWindow.lean`; the case D > 0 is `coset_branchR`).
Proof. Write D = g D', w = g w' with g = gcd(D, w) and D' >= 2 coprime to w' (for D < 0 replace D, sigma by -D, -sigma). Then w (k - sigma)/D + phi_d = (phi_d - w sigma / D) + w' k / D', and Lemma 3.2 applies.

**Lemma 3.4 (window).** There are a real x and an integer m with |D x + sigma - m| <= 1/5 and ||w x + phi_d|| >= 1/5. Lean: `lemma4R` (`RFiveWindow.lean`; the case D > 0 is `lemma4R_pos`).
Proof (D > 0; for D < 0 replace D, sigma by -D, -sigma). If D does not divide w, take x = (k - sigma)/D from Lemma 3.3; then D x + sigma = k and m = k. If D divides w, then D <= w. Put x_0 = -sigma/D, so D x_0 + sigma = 0. Lemma 3.1 with y = w x_0 + phi_d gives delta; put x = x_0 + delta/w and m = 0. Then w x + phi_d = y + delta, and |D x + sigma| = |D delta / w| <= D/(5w) <= 1/5.

**Definition (L6).** `L6 D w sigma phi_d` is the statement: there is an integer t with w = D t and ||phi_d - t sigma|| < 1/5. Lean: `L6` (`RFiveWindow.lean`).

**Lemma 3.5 (exact coincidence).** If `L6 D w sigma phi_d` does not hold, there are a real x and an integer m with D x + sigma = m and ||w x + phi_d|| >= 1/5. Lean: `exists_exactR` (`RFiveWindow.lean`).
Proof. If D divides w, w = D t, take x = -sigma/D; then D x + sigma = 0 and w x + phi_d = phi_d - t sigma, whose distance from Z is at least 1/5 because L6 fails. If D does not divide w, Lemma 3.3 gives x = (k - sigma)/D with m = k.

## 4. The cluster lemma

Here D_b and D_c are nonzero integers, sigma_b, sigma_c, phi_d are real, and w >= 1. For integers m_b, m_c put r_b(x) = D_b x + sigma_b - m_b and r_c(x) = D_c x + sigma_c - m_c.

**Lemma 4.1 (window of length 1/2).** Let p >= 2 and q be coprime integers and y real. Then there are integers k, m with |y + q k / p - m| <= 1/4. Lean: `exists_coset_window4` (`RFiveCluster.lean`).
Proof. Take r = ceil((-1/4 - y) p) and k, b with q k = r + p b (`bezout_solve`). Then y + q k / p - b = y + r/p lies in [-1/4, 1/4).

**Lemma 4.2 (one difference does not divide the other).** If D_b is nonzero and does not divide D_c, there are a real x and integers m_b, m_c with r_b(x) = 0 and |r_c(x)| <= 1/4. Lean: `tight_left4` (`RFiveCluster.lean`; it uses `exists_window4`, and `exists_window4_pos` for D_b > 0, `RFiveCluster.lean`).
Proof. Reduce D_b, D_c by their gcd to get p = D_b/g >= 2 coprime to q = D_c/g (for D_b < 0 change signs). Put x_k = (k - sigma_b)/D_b, so r_b(x_k) = 0 with m_b = k. Then D_c x_k + sigma_c = (sigma_c - D_c sigma_b / D_b) + D_c k / D_b, and Lemma 4.1 chooses k and m_c.

**Lemma 4.3 (perturbation of the three differences).** Let x_0, m_b, m_c be given with |r_b(x_0)| <= b_0, |r_c(x_0)| <= c_0, |r_b(x_0) - r_c(x_0)| <= d_0, and let e_b, e_c, e_d >= 0 satisfy |D_b| <= e_b w, |D_c| <= e_c w, |D_b - D_c| <= e_d w, with b_0 + e_b/5, c_0 + e_c/5, d_0 + e_d/5 all at most 2/5. Then there is a real x with ||w x + phi_d|| >= 1/5 and |r_b(x)|, |r_c(x)|, |r_b(x) - r_c(x)| all at most 2/5 (same m_b, m_c). Lean: `cluster_perturb` (`RFiveCluster.lean`; it uses `pert_le`, `RFiveCluster.lean`).
Proof. Lemma 3.1 with y = w x_0 + phi_d gives delta, |delta| <= 1/5. Put x = x_0 + delta/w. Then w x + phi_d = y + delta. Each of r_b, r_c, r_b - r_c changes by E delta / w with E = D_b, D_c, D_b - D_c respectively, of absolute value at most e/5 where e is the corresponding e_b, e_c, e_d.

**Lemma 4.4 (divisor inequalities).** Let d, w be integers, w >= 1, and d divide w. Then |d| <= w (`abs_le_of_dvd'`); if moreover |d| is different from w, then 2|d| <= w (`two_abs_le`). If a divides w and a does not divide d, then |d| is different from w (`abs_ne_of_not_dvd`) and |a - d| is different from w (`abs_sub_ne_of_not_dvd`). Lean: all four in `RFiveCluster.lean`.
Proof of `two_abs_le`: w = d e with |e| >= 1; |e| = 1 would give |d| = w; so |e| >= 2.

**Lemma 4.5 (cluster).** Let w >= 1, D_b, D_c nonzero and distinct, and suppose D_b, D_c and D_b - D_c all divide w. Then there are a real x and integers m_b, m_c with ||w x + phi_d|| >= 1/5, |r_b(x)| <= 2/5, |r_c(x)| <= 2/5 and |r_b(x) - r_c(x)| <= 2/5. Lean: `cluster_div` (`RFiveCluster.lean`).
Proof. Three branches; in each Lemma 4.3 is applied with the constants shown, and the arithmetic 1/4 + 1/10 = 7/20 <= 2/5 is the only inequality used beyond Lemma 4.4.
* Branch 1: D_b does not divide D_c. Lemma 4.2 gives x_0 with r_b = 0 and |r_c| <= 1/4. Since D_b divides w and does not divide D_c, |D_c| and |D_b - D_c| are different from w (Lemma 4.4), so both are at most w/2. Apply Lemma 4.3 with (b_0, c_0, d_0) = (0, 1/4, 1/4) and (e_b, e_c, e_d) = (1, 1/2, 1/2).
* Branch 2: D_b divides D_c and D_c does not divide D_b. The same with the roles of b and c exchanged: Lemma 4.2 gives r_c = 0 and |r_b| <= 1/4; |D_b| and |D_b - D_c| are at most w/2; apply Lemma 4.3 with (b_0, c_0, d_0) = (1/4, 0, 1/4) and (e_b, e_c, e_d) = (1/2, 1, 1/2).
* Branch 3: D_b and D_c divide each other. Then |D_b| = |D_c|, and D_b is different from D_c, so D_c = -D_b. Here D_b - D_c = 2 D_b divides w, hence |2 D_b| <= w and |D_b| = |D_c| <= w/2. Let n = round(sigma_b + sigma_c) and choose x_0 with D_b x_0 = (sigma_b + sigma_c)/2 - n/2 - sigma_b. With m_b = 0 and m_c = n, r_b(x_0) = r_c(x_0) = (sigma_b + sigma_c - n)/2, of absolute value at most 1/4, and r_b - r_c = 0. Apply Lemma 4.3 with (b_0, c_0, d_0) = (1/4, 1/4, 0) and (e_b, e_c, e_d) = (1/2, 1/2, 1) (here |D_b - D_c| <= w).

## 5. Three free runners and one slow runner

Let v_a, v_b, v_c be free, and let the slow runner have speed 5w, w >= 1, and real phase phi_d. Write beta_i(x) = 5 phi_i + v_i x. The goal is a real x with ||w x + phi_d|| >= 1/5 and a residue j outside B(v_i, beta_i(x)) for i = a, b, c; by Lemma 1(a),(b) this gives a time (j.val + x)/5 good for all four runners.

**Lemma 5.1 (b in the class of a, c in the other class).** Let v_b be congruent to eps v_a (eps = +-1), v_c congruent to lambda v_a with lambda = 2 or 3, v_a different from eps v_b as integers. Then the goal holds. Lean: `case21R` (`RFiveCase.lean`); its covering core is `exists_good_21` (`TPFourArcs.lean`), which uses `core5` (`TPFourArcs.lean`).
Proof. Write 5D = v_a - eps v_b (D nonzero). Lemma 3.4 with sigma = phi_a - eps phi_b gives x and m with |D x + sigma - m| <= 1/5 and ||w x + phi_d|| >= 1/5. Then |beta_a - (eps beta_b + 5m)| = 5 |D x + sigma - m| <= 1. The covering core says: if |beta_a - (eps beta_b + 5m)| <= 1, then some j is outside B(v_a, beta_a), B(v_b, beta_b) and B(v_c, beta_c). In the coordinate z = -(v_a j), the sets of a and b are the arcs arc(beta_a) and arc(eps beta_b + 5m) (Lemma 2.2), whose centres are within 1. Either some integer k lies in the integer range of both arcs, and then both arcs are inside {k-1, k, k+1} (`arc_far`, `core_inter`, `TPFourArcs.lean`), so k+2 and k+3 are free of both; or both centres are integers and both arcs are single residues. The third set, in the coordinate z, is the set of z with lambda z in arc(beta_c). It has at most two elements (Lemma 1(c)). Two elements of arc(beta_c) differ by 0 or +-1 (`arc_adj`), so two elements of the third set differ by lambda^{-1} times 0 or +-1, that is by 0 or +-2 modulo 5 (lambda^{-1} is 3 or 2); hence no two of them differ by 1. In the case of a common integer k it cannot contain both k+2 and k+3, so one of them is free. In the case of two integer centres the three sets together have at most 1 + 1 + 2 = 4 elements.

**Lemma 5.2 (all three in one class).** Let v_b be congruent to eps_b v_a and v_c congruent to eps_c v_a modulo 5 (eps_b, eps_c = +-1), with v_a different from eps_b v_b, v_a different from eps_c v_c, and eps_b v_b different from eps_c v_c, as integers. Then the goal holds. Lean: `case3R` (`RFiveCase.lean`); its covering core is `exists_good_3` (`TPFourWindow.lean`), which uses `three_arcs` (`TPFourWindow.lean`), and `spread3` (`TPFourTight.lean`).
Proof. Write 5 D_b = v_a - eps_b v_b, 5 D_c = v_a - eps_c v_c, sigma_b = phi_a - eps_b phi_b, sigma_c = phi_a - eps_c phi_c. Then D_b, D_c, D_b - D_c are nonzero and D_b is different from D_c. Moreover beta_a(x) - (eps_b beta_b(x) + 5m) = 5 (D_b x + sigma_b - m), and likewise for c. Consider `L6 D_b w sigma_b phi_d`, `L6 D_c w sigma_c phi_d` and `L6 (D_b - D_c) w (sigma_b - sigma_c) phi_d`.
* If `L6` fails for (D_b, sigma_b): Lemma 3.5 gives x and m with D_b x + sigma_b = m exactly and the slow runner good. Then beta_a = eps_b beta_b + 5m, so B(v_a, beta_a) = B(v_b, beta_b) (Lemma 2.2), and the union of the three bad sets has at most 4 elements (`good_of_eq3`, `RFiveLemS.lean`).
* If `L6` fails for (D_c, sigma_c): the same with c in place of b.
* If `L6` fails for (D_b - D_c, sigma_b - sigma_c): Lemma 3.5 gives x and m with (D_b - D_c) x + sigma_b - sigma_c = m, the slow runner good, and eps_b beta_b + 5m = eps_c beta_c. So B(v_b, beta_b) = B(v_c, beta_c) (`mem_badImg_class`, `TPFourWindow.lean`, applied to both runners relative to a), and again at most 4 elements.
* If `L6` holds for all three, then D_b, D_c and D_b - D_c all divide w, and Lemma 4.5 gives x, m_b, m_c with the slow runner good and |r_b|, |r_c|, |r_b - r_c| <= 2/5. By `spread3` there is lo <= 0 with 0, r_b, r_c all in [lo, lo + 2/5]. The three centres beta_a, eps_b beta_b + 5 m_b = beta_a - 5 r_b, eps_c beta_c + 5 m_c = beta_a - 5 r_c then lie in an interval [L, L + 2] with L = beta_a - 5 lo - 2. `exists_good_3` gives a residue outside the three bad sets: the three arcs lie in four consecutive integers (`three_arcs`), so the residue of floor(L) + 4 is outside all three.

## 6. Assembly

**Lemma 6.1 (one slow runner, three free).** Let v_1, ..., v_4 be distinct positive integers, phases real, z an index with 5 dividing v_z and 5 not dividing v_i for i different from z. Then some t is good for all four runners. Lean: `caseHR` (`RFiveFinal.lean`; it uses `good_pinnedR` and `finish_fourR`, `RFiveFinal.lean`).
Proof. Let a, b, c be the other three indices and w = v_z / 5 >= 1. Class of b and c relative to a: if both are in the class of a, Lemma 5.2; if exactly one, Lemma 5.1 with a as base (`other_of_not_same`, `TPFourGlue.lean`); if neither, then b and c lie in one class relative to each other and a lies in the other (`other_other`, `TPFourGlue.lean`), and Lemma 5.1 applies with b as the base. The integer hypotheses of Lemmas 5.1 and 5.2 (v_a different from eps v_b, and so on) follow from positivity and distinctness (`hne_of`, `TPFourGlue.lean`; for eps_b v_b different from eps_c v_c an `omega` check in `caseHR`). In each case Lemmas 5.1 and 5.2 give x and j with ||w x + phi_z|| >= 1/5 and a, b, c good at (j.val + x)/5; the slow runner is good there by Lemma 1(a) (`good_pinnedR`).

**Theorem R5_core.** Let v_1, ..., v_4 be distinct positive integers, at least one divisible by 5 and at least one not, and phi_i real. Then some t has ||v_i t + phi_i|| >= 1/5 for all i. Lean: `R5_core` (`RFiveFinal.lean`).
Proof. Let A be the set of free indices, z a slow index, a_0 a free index. If |A| <= 2: the slow indices number at most 3 (a_0 is not among them); Lemma 2.5 applied to the slow runners (v_i / 5, phi_i) gives x, and Lemma 1(e) gives t. Otherwise |A| = 3, since A does not contain z; then no index other than z is slow (a second slow index would leave |A| <= 2), and Lemma 6.1 applies.

**Theorem R5.** Under the hypotheses of the Status section (gcd 1, some speed divisible by 5). Lean: `R5` (`RFiveFinal.lean`).
Proof. If all four speeds were divisible by 5, then 5 would divide the gcd (`Finset.dvd_gcd`), contradicting gcd = 1. So some speed is not divisible by 5, and R5_core applies.

**Theorem R5_tp.** R5_core with the conclusion written as 1/5 <= tpDist(v_i t + phi_i). Lean: `R5_tp` (`RFiveCor.lean`).

**Theorem R5_gcd.** Let v_1, ..., v_4 be distinct positive integers, g their gcd, and suppose 5 divides v_i / g for some i. Then for every real phases some t has ||v_i t + phi_i|| >= 1/5 for all i. Lean: `R5_gcd` (`RFiveCor.lean`).
Proof. Put u_i = v_i / g (exact division, g >= 1). The u_i are positive, distinct, with gcd 1 (`Finset.extract_gcd`), and 5 divides some u_i. R5 applied to u gives t with ||u_i t + phi_i|| >= 1/5; then v_i (t/g) + phi_i = u_i t + phi_i, so t/g works for v. The phases are not rescaled.

## 7. Where the hypotheses are used

* Positivity and distinctness of the speeds are used to make the integers D, in 5D = v_a - eps v_b, nonzero (`hne_of`, `TPFourGlue.lean`), in `three_free`, `case21R` and `case3R`; and in Lemma 2.5 to keep the speeds v_i / 5 positive and distinct.
* "At least one speed divisible by 5" excludes four free runners; "at least one not divisible by 5" excludes four slow runners, which this method does not handle (for example (5,10,15,20) is (1,2,3,4) rescaled, and (1,2,3,4) has no multiple of 5).
* Real phases enter only through the real numbers sigma and phi_d. No step uses that a phase is rational or lies on a grid, and no step uses that a maximum is attained.

## 8. Distinctness is necessary

Take v = (1,1,1,5) and phases (0, 1/5, 3/5, 0); this vector has gcd 1 and a multiple of 5. The three runners of speed 1 are bad (distance below 1/5) exactly when t lies in the open arcs of half-width 1/5 centred at 0, 4/5 and 2/5 modulo 1, that is in (-1/5, 1/5), (3/5, 1) and (1/5, 3/5). Their union is the circle minus the two points 1/5 and 3/5. At t = 1/5 and t = 3/5 the runner of speed 5 and phase 0 is at 5t = 1 and 5t = 3, an integer, so its distance is 0. Hence no t makes all four distances at least 1/5. (The value 1/6 for the best achievable minimum comes from an exact rational computation and is not proved here.)

## Lean correspondence

All declarations are in namespace `LRSpectrumFull`. Files are in `lean/LRSpectrumFull/`. The full module list is in `LEAN_MAP.md`.

| Part of the proof | Lean declaration (file) |
|---|---|
| Distance, good runner | `tpDist` (`TPSmall.lean`), `GoodR` (`RFiveBase.lean`) |
| Lemma 1(a) | `goodR_mul5` (`RFiveBase.lean`), `tpDist_add_int` (`TPFourBridge.lean`) |
| Lemma 1(b) | `goodR_of_not_mem_badImg` (`RFiveBase.lean`), `exists_near_of_not_good` (`TPFourBridge.lean`) |
| Lemma 1(c) | `badImg`, `card_badImg_le_two` (`TPFourLocal.lean`) |
| Lemma 1(d), 1(e) | `exists_resR`, `step_le2R` (`RFiveBase.lean`) |
| Arcs | `arc`, `badImg_eq`, `mem_badImg_iff`, `arc_adj`, `arc_far`, `core_inter`, `core5`, `exists_good_21` (`TPFourArcs.lean`) |
| Lemma 2.1 | `dvd5_class` (`RFiveBase.lean`) |
| Lemma 2.2 | `badImg_eq_of_class` (`TPFourCoincide.lean`), `mem_badImg_class` (`TPFourWindow.lean`) |
| Lemma 2.3 | `exists_coincide` (`RFiveBase.lean`) |
| Lemma 2.4 | `same_class_pair`, `good_of_eq3`, `three_free` (`RFiveLemS.lean`); `hne_of`, `exists_eps` (`TPFourGlue.lean`) |
| Lemma 2.5 | `lemSR` (`RFiveLemS.lean`), `sum_div5_lt` (`TPFourReduce.lean`) |
| Lemma 3.1 | `exists_perturb` (`TPFourWindow.lean`) |
| Lemma 3.2 | `exists_coset_far`, `bezout_solve` (`TPFourCoset.lean`) |
| Lemma 3.3 | `coset_branchR`, `coset_branchR_ne` (`RFiveWindow.lean`) |
| Lemma 3.4 | `lemma4R_pos`, `lemma4R` (`RFiveWindow.lean`) |
| Definition L6, Lemma 3.5 | `L6`, `exists_exactR` (`RFiveWindow.lean`) |
| Lemma 4.1, 4.2 | `exists_coset_window4`, `exists_window4_pos`, `exists_window4`, `tight_left4` (`RFiveCluster.lean`) |
| Lemma 4.3 | `pert_le`, `cluster_perturb` (`RFiveCluster.lean`) |
| Lemma 4.4 | `abs_le_of_dvd'`, `two_abs_le`, `abs_ne_of_not_dvd`, `abs_sub_ne_of_not_dvd` (`RFiveCluster.lean`) |
| Lemma 4.5 | `cluster_div` (`RFiveCluster.lean`) |
| Lemma 5.1 | `case21R` (`RFiveCase.lean`) |
| Lemma 5.2 | `case3R` (`RFiveCase.lean`); `exists_good_3`, `three_arcs` (`TPFourWindow.lean`); `spread3` (`TPFourTight.lean`) |
| Lemma 6.1 | `caseHR`, `good_pinnedR`, `finish_fourR` (`RFiveFinal.lean`); `other_of_not_same`, `other_other` (`TPFourGlue.lean`) |
| Theorem R5_core, R5 | `R5_core`, `R5` (`RFiveFinal.lean`) |
| Theorem R5_tp, R5_gcd | `R5_tp`, `R5_gcd` (`RFiveCor.lean`) |
