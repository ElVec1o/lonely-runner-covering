# Lonely runner conjecture: dense windows and the covering framework, an obstruction catalogue, a perturbation bound, a reduction, and eight runners

Version 1.0.3. Archived at Zenodo: version 1.0.3 [10.5281/zenodo.23445368](https://doi.org/10.5281/zenodo.23445368); version 1.0.2 [10.5281/zenodo.23439967](https://doi.org/10.5281/zenodo.23439967); version 1.0.1 [10.5281/zenodo.23436538](https://doi.org/10.5281/zenodo.23436538); version 1.0.0 [10.5281/zenodo.23435305](https://doi.org/10.5281/zenodo.23435305); all versions [10.5281/zenodo.23435304](https://doi.org/10.5281/zenodo.23435304).
Author: Vico Bonfioli (vicobonfioli@gmail.com). License: CC-BY-4.0 (`LICENSE.md`). Snapshot of 18 October 2026, matching the
`\date` line of the manuscripts. The manuscripts are preprints and have not been peer reviewed.

## Abstract

For positive integer speeds `v_1,...,v_m` let `ML(v) = sup_t min_i dist(v_i t, Z)`. The lonely runner conjecture (LRC) is
`ML(v) >= 1/(m+1)` for all `v`. This archive contains six manuscripts and the material behind their computed statements:
(1) the inequality for speeds in `[1,2m]`, formalized in Lean 4 for every `m` with `2m+1` prime and for 67 values of `m <= 126`
with `2m+1` composite; (2) a covering framework for bounded velocity windows with a classification of the small bad sets;
(3) a catalogue of obstructions to certificate-based proofs for divisor-complete families, with a section on leave-one-out descent and on the topology of the bad region; (4) a covering bound for
modifications of the tight instance `[1,n-1]` and its consequences; (5) a Lean-checked reduction of LRC for all `m` to
three finite-range statements and one remaining statement (`FloorCruxU`) that is equivalent to LRC given the other three;
(6) a Lean formalization of the case of eight runners. No proof of LRC is claimed.

## Idea in words

Every statement here rests on one fact: `ML(v) >= delta` holds as soon as some time `t` has `dist(v_i t, Z) >= delta` for all `i`.
A velocity set with no such time must contain, for every time, a velocity whose phase is within `delta` of an integer, that is it must
hit the "bad set" of that time. For a window `[1,2m]` and `delta = 1/(m+1)` there are finitely many distinct bad sets, so the inequality for the
whole window is a finite hitting-set statement: no `m` velocities hit all bad sets. Such a statement is certified by a
fractional weighting of times (weak LP duality), by a cover of the window by parts with capacities, or by exhaustive search. The
Lean files check the certificates with the kernel. The other manuscripts study the limits of this method (barrier theorem, level drift),
a measure argument for single and multiple modifications of `[1,n-1]`, the reduction to one crux, and the case of eight runners.

## Changes since version 1.0.2 (draft, unreleased)

* Obstruction note: new Section 8 (descent and topological obstructions), items 20 to 33. PROVED: deletion and dilation lemma (20), descent lemma (22), the inclusion of the bad region into the torus is an isomorphism on `H_1` for `m >= 2` and on `pi_1` for `m >= 3` (29), every `v` is represented by a loop in the bad region for `m >= 2` (30), the parity statement for equivariant loops (31), and `ML(v) = 1/2` exactly when all `v_i` have the same 2-adic valuation (33). HEURISTIC (exact finite computation, not formalized): the exact instances and the descent discontinuity at `m` in `{7, 31, 61, 73, 91, 121, 143, 151, 181, 211, 241}` (23, 24), the leave-one-out values of 70 known tight vectors (25). CONJECTURE: (C1) (26). FALSE statement, with witnesses: `ML(V) < 1/m` implies a tight leave-one-out (27). Items 1 to 19 and their numbers are unchanged. The introduction, the abstract, the conceptual abstract, the results table, the evidence table, the open statements and the attribution table of the note are updated.
* New checker `code/obstructions/descent_check.py` (Python glue, exact fractions; the standard exact `ML` routine with its control battery copied in) and outputs `data/obstructions/descent_*.out`; the input table `data/obstructions/descent_gw_loo.tsv`.
* Regression tests for `ml` (all numerators) added to `code/reduction/mdr/src/main.rs` and `code/reduction/levelfit/src/mdr_base.rs` (the function is unchanged; `cargo test` was not run for this revision); one row of `paper/reduction/LEAN_MAP.md` corrected (the equality of T2 at `m = 12` is marked withdrawn).
* The Lean build was not run for 1.0.3; no Lean file changed. `.zenodo.json` still says version 1.0.2 and `CITATION.cff` still says version 1.0.2 with the DOI of 1.0.2; both must be changed at release.

## Changes since version 1.0.1 (draft, unreleased)

* Dense-window paper, Theorem 3 (prime case): the section is rewritten with a conceptual abstract, a zoom map and Lemmas 1 to 4 (witnesses, speeds avoiding 1, forced pair, pair summing to a prime). The proof of Lemma 4 is given in class form (the `m` classes `{s, 2m+1-s}`; the speeds meet at most `m-1` of them; the inverse of a missed class is the multiplier); the Lean declaration `floor_of_pairsum_prime` counts multipliers instead, and the two counts correspond under `c <-> c^{-1}`. Statement of Theorem 3 and all numbers of later items are unchanged. The Lean module names in the paper and in `LEAN_MAP.md` are corrected (`floor_of_not_dvd_le` is called by `dense_floor_of_prime`; `tao_5_1_i` is a separate declaration). The convention (`m` speeds = `m+1` runners) is stated. Attribution to Bohman and Peng is reworded (they select `c` from a pair of non-speeds `s, t` with `c = s^{-1}`; Lemma 4 obtains such a pair by counting classes). The case `m = 14` is stated to rest on Allikvere, arXiv:2609.02604 v2 (unrefereed, computer-assisted). Zhang, arXiv:2608.13599, is added as related work.
* New exact checks for the prime case: `code/dense/src/thmd` (four programs), outputs in `data/dense/thmd`: window `[1,2m]` for `m <= 12` (12 independent values of `m`, RESOLVED-TRUE), class form of Lemma 4 for the primes `2m+1` with `m <= 9`, case counts, controls.
* The Lean build was not run for 1.0.2; no Lean file changed. `.zenodo.json` still says version 1.0.1 and must be changed before the release.

## Changes since version 1.0.0 (draft)

* Dense-window paper, Statements 8 and 9 (extremal kept block; reduction to irreducible blocks): the proofs are now written out in the paper (they were previously
  referred to development notes that are not archived). New checker `code/dense/src/st89` and its output `data/dense/st89_check.out`. New paragraph on the block with empty `T`.
* Obstructions paper: the denominator proposition no longer carries the `m <= 12` clause or the dependence on the unrefereed preprint of Sungkawichai and Trakulthongchai; `lonely time` is defined;
  the doubling-chain proposition is restated as an isolated-vertex statement on the window `[1,2m]` (not modulo `2m+1`); `(T)`, `(T')` are stated with explicit hypotheses and the proposition is
  restated as implications; the conceptual abstract is rewritten; a new proposition (tight corner) with checker `code/obstructions/cornercheck.py`. Item numbers of this paper changed; the numbers
  in version 1.0.0 of this README and of `CLAIMS.tsv` did not match the manuscript and are corrected here.
* The Lean build was not run for 1.0.1; no Lean file changed.

## Corrections and withdrawn claims (version 1.0.0 snapshot)

* Reduction paper: the claim that `ML = 2/(2m+1)` is attained at `m = 12` by `(1,4,6,7,10,11,12,13,16,17,19,23)` is withdrawn. The value
  came from `mdr ml`, which skipped numerators not coprime to the denominator; the exact value is `ML = 1/9`. The function is corrected in
  `code/reduction/mdr` and `code/reduction/levelfit`, and `code/obstructions/mlcheck.rs` recomputes `ML` independently (details in
  `code/reduction/README.md`). All other values of `ML` quoted in the manuscripts were recomputed by `mlcheck` and agree.
* Dense-window paper: for `m` in `{97, 103, 109, 115, 122}` a certificate accepted by the independent Rust checker exists but no Lean module was
  built; for `m = 94` a three-hour search ended UNRESOLVED (exact phases stopped at node caps). The dense-window statement is not claimed for these six `m`.
* Covering paper: "all computations are reproduced by committed programs" was replaced by a pointer to `code/covering`, `code/dense` and this README.
* Perturbation paper: the localization step is cited to Zhang, arXiv:2608.13599v2, Section 2 (Lemmas 2.1, 2.2, proof of Lemma 2.4; Lemma 2.5 for `2r > n-1`).
* Counts and tables without an archived generator are marked in the manuscripts and in `CLAIMS.tsv` ("generator not archived"; label HEURISTIC).
* The Lean build of this archive was not run when it was assembled. `#print axioms` records in the `LEAN_MAP.md` files are records of earlier runs.

## Idea in words, obstruction note

The note tests seven standard routes to the floor at tight vectors. A fixed integrable weight cannot certify a tight vector: its good set is countable and without mass. Bounded-denominator certificates fail without a leave-one-out hypothesis, because a speed divisible by `lcm(1,...,Q)` vanishes at every time of denominator at most `Q`. Doubling pairings fail because, for odd composite `2m+1` above 9, the non-unit `2m+1-2p`, with `p` the least prime factor, has no partner in the window. Corner analysis fails because a corner maximum depends on the residues of all other speeds. Covering-radius bounds fail because the shifted statement is false. Descent through leave-one-out subsets fails because some tight vectors have every leave-one-out value above the next value attained by `m-1` speeds. Topological conditions fail because the bad region has the first homology of the torus. What remains is an explicit rational time or a classification of tight vectors.

## Main results

Labels: VERIFIED (Lean 4 with Mathlib, build clean, no `sorry`, axioms among `propext`, `Classical.choice`, `Quot.sound`, as recorded in the cited
`LEAN_MAP.md`), PROVED (complete written proof, not formalized), COMPUTED (finite computation, not formalized), HEURISTIC, CONJECTURE.
The effective label is the weakest label in the dependency chain.

### `paper/dense-window` (Lean-verified instances for integer speeds in `[1,2m]`)

* Theorem 3, Lean declaration VERIFIED (carried over from the development repository, not rebuilt for this archive); the written proof in the paper is PROVED. If `m >= 2`, `2m+1` is prime and `v_1,...,v_m` are integers in `[1,2m]`, then `ML(v) >= 1/(m+1)`. A short consequence of known ingredients (Tao Lemma 5.1(i), the Bohman-Peng witness device, one forcing step); it gives the window `[1,2m]` for all `m` with `2m+1` prime and does not settle Problem 6 of the Perarnau-Serra survey. The case `m <= 13` is contained in published computer-assisted proofs of LRC for at most 13 speeds, and `m = 14` in an unrefereed preprint (arXiv:2609.02604 v2).
* Conceptual abstract of Theorem 3: speeds avoiding 1 are beaten by the time `1/(2m+2)`; if 1 is a speed and no time `1/q` wins, every integer in `[2,m+1]` divides a speed, which forces `m+1` and one of `m`, `2m`, hence two speeds summing to the prime `N = 2m+1`; at times `c/N` a speed spoils the time only if it lies in the class `{s,N-s}` of `s = c^{-1}`; the `m` classes partition `[1,2m]` and the pair lies in one class, so a class is missed and its inverse is a good multiplier. A search over real times becomes a count of classes.
* Exact checks for Theorem 3 (COMPUTED, `code/dense/src/thmd`, `data/dense/thmd`): every subset of `[1,2m]` of size at most `m` has a witness time for `m <= 12` (13,015,070 sets, 12 independent values of `m`, 8 with `2m+1` prime and 4 composite; RESOLVED-TRUE; HEURISTIC beyond `m = 12`); the class form of Lemma 4 holds for the primes `2m+1` with `m <= 9` (6 independent values, 0 exceptions). For composite `2m+1` the proof of Lemma 4 fails (smallest case `m = 7`, `V = {1,2,4,5,6,7,8}`, `ML = 2/13`, no time `c/15`); the statement for composite `2m+1` is covered only by the rows of Tables 1 and 2.
* Proposition (fractional blocking), VERIFIED. If weights `y_j` on times `p_j/q_j` give every `x in [1,2m]` load at most `D` and `sum y_j > mD`,
  then every `v` with `0 < v_i <= 2m` satisfies `ML(v) >= 1/(m+1)`. Instances `m = 4, 7, 12, 13`, regenerated by `code/dense/src/fb`.
* Theorem (cover capacity), VERIFIED. If parts `U_i` cover `[1,2m]` and every `T` in `U_i` with `|T| > c_i` contains a bad set and `sum c_i < m`, then
  `ML(v) >= 1/(m+1)` for every injective `v` with values in `[1,2m]`.
* Theorem (table), VERIFIED per row. For the 67 composite values `m` of Table 1 (`m = 4, 7, 12, 13`) and Table 2 (63 rows, `m <= 126`) the inequality holds for every `m` distinct integers in `[1,2m]`.
  Rows marked S have raw build and axiom output archived; 16 rows marked L (`m = 24, 25, 27, 28, 31, 32, 34, 37, 38, 40, 42, 43, 45, 46, 47, 55`) rest on records in `LEAN_MAP.md` without archived raw output.
  Consequently the statement is Lean-verified for all `2 <= m <= 126` except `m` in `{94, 97, 103, 109, 115, 122}`.
* Statement 8, PROVED (not formalized). Call a block `(T,L)` (`T` in `Y`, `L` in `{2,...,m}`) valid if `tau(T u L) >= |L|`, kept if valid, no larger `L` and no smaller `T` is valid. Every valid block is dominated (`T` smaller or equal, `L` larger or equal) by a kept block. Proof: extremal block (largest `L`, then smallest `T`) among the valid blocks dominating it. Finite check: `code/dense/src/st89`, `2 <= m <= 17`.
* Statement 9, PROVED (not formalized). Let `F_k` be the kept blocks with `|T| <= k` and `R_k` those that are not reducible (`T` and `L` split into two nonempty parts, both parts valid). Then `R_k` has a cover iff `F_k` has a cover (cover: pairwise disjoint `T` parts, `L` parts with union `{2,...,m}`). Proof: a cover of least `sum |T|^2` has no reducible block, by Statement 8. Finite check: `code/dense/src/st89`, `2 <= m <= 17`.
* Conceptual abstract of Statements 8 and 9: replace a block by the extremal block it dominates; replace a reducible block by two kept blocks of smaller `T`, which lowers the squared weight of the cover.
* HEURISTIC: Statement 6 (`Y = {m+2,...,2m}` contains no minimal bad set, checked for `2 <= m <= 62`) and Statement 7 (packing of blocks). Reported size reductions of the block families at `m = 49, 62` are logged runs, not re-run.

### `paper/lrc_covering` (covering framework)

* Theorem (equivalence), VERIFIED. For `N >= m+1` the inequality holds for all `m`-element sets in `[1,N]` iff the hitting number `tau(N) > m`; always `tau(N) <= m+1`.
* Theorem (surplus form), VERIFIED. If parts `U_i` cover `[1,2m]`, `sum |U_i| = 2m`, every subset of `U_i` with more than `c_i` elements contains a bad set and `sum (|U_i| - 2c_i) >= 2`, then the inequality holds for all `m`-sets in `[1,2m]`.
* Theorem (prime), VERIFIED. If `2m+1` is prime the inequality holds for all `m`-sets of distinct velocities `<= 2m`.
* Theorems (bad pairs), VERIFIED. A bad pair is `{a,2a}` or has `a+b` in `{2m+1, 2m+2}` with `gcd(a,a+b) = 1`; the top third of the window carries no bad set.
* Theorem (classification of small bad sets), COMPUTED for exhaustiveness: families verified; singleton and pair families exhaustive for `4 <= m <= 260`; the triple families are not exhaustive.
* Theorems (window decisions), COMPUTED. The window `{1,...,2m}` is decided for `4 <= m <= 63` by exhaustive enumeration and again from the nine families alone; every 13-element set in `[1,39]` is lonely (`8,122,425,444` sets).
* Further COMPUTED results: a counterexample at `m = 19` to the `(6,3)` block template; counterexamples at `m = 150, 318, 486, 570` to a regularity of the bad-pair graph.

### `paper/obstructions`

* Theorem 2 (barrier), VERIFIED. If `ML(v) <= delta` then the good set `G_delta` is countable, hence null; no integrable weight `F >= 0` gives a first-moment certificate `sum_i int_{B_i} F < int F` at a tight value. Corollary 3, VERIFIED: no Riesz-product certificate `U_D` fires on a tight family.
* Propositions 5 and 6, VERIFIED. Escape lemma; a missing divisor `j` in `[2,m+1]` gives `||v_i/j|| >= 1/j`, hence `ML >= 1/j` (the Lean lemma states the weak bound `1/(m+1)`; the strict form is PROVED in one line).
* Proposition 7, PROVED. For `m >= 2`, `Q >= 1`, `L = lcm(1,...,Q)`, `v = (1,L,2L,...,(m-1)L)`: a time `a/q` in lowest terms with positive gap has `q > Q`; `ML(v) >= 1/(m+1)` at `t = c/(L(m+1))`, `c = 1 mod (m+1)`, `L <= c <= Lm`; hence no function `Q(m)` bounds the denominators of lonely times for all vectors.
* Theorem 9, VERIFIED. Under the Goddyn-Wong GCD condition `m+1` divides no speed of `[n-1]_mu`. Corollary 10: such vectors are not divisor-complete.
* Proposition 13, PROVED (implications only). If `m+1` divides some `v_i` then `gap(a/(m+1)) = 0 < ML(v)` for all `a`; hence `(T')` implies `(T)`, and `(T)` implies that no tight primitive vector is divisor-complete.
* Proposition 14 (tight corner), PROVED. If `ML(v) = a/b < 1/2` in lowest terms and `k/L` is a maximizer in lowest terms, then there are speeds `v_i`, `v_j` at `+a/b` and `-a/b` with `b | L`, `L | b gcd(v_i,v_j)`, `L | v_i + v_j`; for tight `v` (`b = m+1`), `(T')` holds at the maximizer iff `L = m+1`. Finite check: `code/obstructions/cornercheck.py`.
* Proposition 16 (chain parity), PROVED. For odd composite `q = 2m+1 > 9` with least prime factor `p`, `q - 2p` is an isolated vertex of the doubling graph on the non-units of `[1,2m]`; all components are even iff `q` is prime or `q = 9`.
* Proposition 18, VERIFIED. There is no `t` with the six shifted gap conditions for speeds `(1,2,3,4,6,9)` and phases `(0,1/2,1/2,1/2,1/2,0)`.
* Lemma 20, PROVED. For a multiset `V` of at least two positive integers and `c >= 1`: `ML(V \ v) >= ML(V)` for every element `v`, and `ML(cV) = ML(V)`. Remark 21: this gives no lower bound `ML(V \ v) >= 1/m`, so it does not show that a subset of a counterexample is not a counterexample.
* Lemma 22 (descent lemma), PROVED. If `F` satisfies `loo(V) <= F(ML(V))` for all sets `V` of `m` distinct positive integers (`loo(V) = min_v ML(V \ v)`), then `F(1/(m+1)) >= loo(V)` for every tight `V`.
* Proposition 29, PROVED. For `0 < delta <= 1/2`, `U_delta = {x in T^m : some ||x_i|| < delta}` is the torus minus one closed cube; the inclusion `U_delta -> T^m` induces an isomorphism on `H_1` for `m >= 2` and on `pi_1` for `m >= 3` (for `m = 2` a strong deformation retraction onto a wedge of two circles, and `pi_1` is only onto, the induced map being the abelianization of the free group of rank 2; false for `m = 1`). Corollary 30, PROVED (by lifting to `R^m`, independent of Proposition 29): for `m >= 2` and every `v` there is a loop in `U_delta` homotopic rel base point to the loop `t -> tv`.
* Proposition 31, PROVED. For `m >= 2`, the loop `t -> tv` is equivariantly homotopic (for `t -> -t`, `x -> -x`) into `U_delta` iff not all `v_i` are odd. Consequently a necessary condition obtained from the inclusion `U_delta -> T^m` excludes no `v`; this concerns arguments of that form (Remark 32, HEURISTIC), not invariants of the class `v` in general. The proof is by lifting to `R^m` and does not use Proposition 29. Remark 33, PROVED: `ML(v) = 1/2` if and only if all `v_i` have the same 2-adic valuation.
* Conceptual abstract of Section 8, descent: to run an induction on the number of speeds one asks for an inequality that sends a counterexample with `m` speeds to a tight subset with `m-1` speeds, bounded in terms of `ML(V)` alone and continuous at the floor; some tight sets have every leave-one-out value above the next value attained by `m-1` speeds, so the bound must jump at the floor. Topology: one asks what the inclusion of the bad region (the torus minus one cube) into the torus can detect; removing the cube changes neither `H_1` (`m >= 2`) nor `pi_1` (`m >= 3`), a curve symmetric under negation can be pushed into the bad region unless its midpoint is the central fixed point, which happens exactly when all speeds are odd, so such conditions detect only the all-odd vectors, where the maximum is already 1/2.

#### Heuristic, conjectural and false statements of the obstruction note

* Observation 8 (level drift) HEURISTIC; Remark 4 HEURISTIC; Conjectures 12 `(T)`, `(T')` and 15 `(T2)` CONJECTURE.
* Observation 23 and Proposition 24, HEURISTIC (the deduction is PROVED, the instances are exact finite computations, not formalized). `ML(1,4,5,6,7,11,13) = 1/8` and `loo = 2/13`; `ML(1,5,6,11,16,17) = 5/33 < 2/13`; for `m` in `{7, 31, 61, 73, 91, 121, 143, 151, 181, 211, 241}` there is a tight set `V_m` of `m` distinct speeds with `loo(V_m) > sigma(m-1)` (`sigma(k)` = infimum of `ML` over `k`-speed sets with `ML > 1/(k+1)`). Hence a function `F` of `ML(V)` alone with `loo(V) <= F(ML(V))` for all `V`, `F < sigma(m-1)` below the floor and left-continuous at `1/(m+1)` does not exist at these `m`. Not excluded: structural hypotheses, other invariants, higher thresholds, deletion of two or more speeds, jumps. Recomputed in this archive: all removals for `m <= 73`; `V` and one removal for `m <= 151`; the others are taken from a table whose generator is not archived.
* Observation 25, HEURISTIC. Of 70 known tight vectors (66 Goddyn-Wong type with one replaced entry, `n <= 260`; 1 with two; 3 sporadic: `(1,3,4,7)`, `(1,3,4,5,9)`, `(1,4,5,6,7,11,13)`), 11 have a tight leave-one-out; of the other 59 (56 Goddyn-Wong type and 3 sporadic) 46 have `loo = 2/(2m-1)` (43 Goddyn-Wong type and 3 sporadic) and 13 have `loo > 2/(2m-1)`; none is below. The list is not a classification.
* Conjecture 26 (C1), CONJECTURE. A tight set with `gcd = 1` and no tight leave-one-out has `loo >= 2/(2m-1)`. Evidence: the 59 vectors above and the exhaustive boxes of the note. Consequence: every descent function is at least `2/(2m-1)` at the floor wherever such a set exists.
* Observation 27, FALSE (the statement), exact witnesses. `ML(V) < 1/m` does not imply that some `V \ v` has `ML = 1/m`: `(1,2,3,5,8)` (`ML = 2/11`, `loo = 2/9`), `(1,2,3,4,5,7,18,40)` (`5/41`, `3/23`), `(1,5,6,7,8,11,13,19,20,27)` (`3/31`, `2/17`). The first two have tight subsets with fewer elements; the third has none of size 2 to 9.

### `paper/perturbation`

* Theorem (covering bound), PROVED. If `V` is a `k`-speed modification of `[n-1]` with `2k < n` and `LR(V) <= 1/n`, then `sum_{v in R} 1/v >= ell(n,M)(n-2k)/2`; no upper bound on the inserted speeds is assumed.
* Theorems (component bounds), PROVED. `ell(n,M) >= 1/(n(n-1))` when `M` contains an element coprime to `n`; `ell(n,M) >= 1/(2n^3)` always; an explicit formula for `ell(n,M)` as a maximum of window lengths. Some are formalized (the paper's Formalization section lists the declarations).
* COMPUTED: no covering `R` for `|M| = 2`, `5 <= n <= 100` (regenerated by `perturb_coverk 2 5 100`, about 2 hours in total) and for `|M| = 3`, `7 <= n <= 40` (original log archived; rows `7 <= n <= 22` reproduced, `23 <= n <= 40` not re-run).

### `paper/reduction`

* Theorem (reduction), VERIFIED. `A1 and A2 and A3 and FloorCruxU` imply LRC for every `m >= 3`. Theorem (equivalence), VERIFIED: given `A1`, `A2`, `A3`, `FloorCruxU` is equivalent to LRC for all `m`.
* VERIFIED: first-moment criterion for families with relations; no absolutely continuous weight certifies a tight family; one-entry families `([1,m] \ {r}) u {w}` satisfy two sufficient conditions for `ML >= 2/(2m+1)`.
* CONJECTURE: (T), (T'), T2, and the formula for `ML(F(m,j))`. The equality case of T2 at `m = 12` is withdrawn (see above).

### `paper/eight`

* Theorem (eight runners), VERIFIED modulo 27 certificate axioms in the default build: for every `v : Fin 7 -> Z` with `v_i > 0`, `ML(v) >= 1/8`. A second module outside the default build proves the same statement from the standard axioms alone by importing 27 kernel proofs kept as object files; that module was not rebuilt here.
* Theorem (seven runners, Barajas and Serra), VERIFIED.

### Heading for HEURISTIC and CONJECTURE material

All HEURISTIC and CONJECTURE statements are those marked as such above and in `CLAIMS.tsv`. The computed totals whose generator is not archived (listed in `CLAIMS.tsv` under "NOT REGENERATED" or "generator not archived") carry the label HEURISTIC.

## File map

| Path | Content |
|---|---|
| `paper/dense-window/` | `main.tex`, `rows.tex`, `rows_ext.tex`, `refs.bib`, `LEAN_MAP.md`, `main.pdf` |
| `paper/lrc_covering/` | `lrc_covering.tex`, `lrc_covering.pdf` |
| `paper/obstructions/` | `main.tex`, `refs.bib`, `LEAN_MAP.md`, `main.pdf` |
| `paper/perturbation/` | `perturbation.tex`, `perturbation.pdf` |
| `paper/reduction/` | `main.tex`, `refs.bib`, `LEAN_MAP.md`, `main.pdf` |
| `paper/eight/` | `main.tex`, `refs.bib`, `LEAN_MAP.md`, `main.pdf` |
| `lean/` | Lean sources (196 modules), `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `README.md` (modules containing `sorry` or `axiom`) |
| `code/reproduce.sh` | entry point regenerating the finite computations that have a program here |
| `code/dense/` | `thmd` (exact checks for Theorem 3: `dense_check.rs`, `cross_check.py`, `class_check.rs`, `case_recount.rs`), `v1` (independent certificate checker), `g1`, `lg`, `cg`, `xc`, `pool` (searches), `fb` (fractional blocking checker), `yind` (Y-independence), `st89` (brute-force check of Statements 8, 9), `m94` (search driver), `build.sh`, `check_rows.py`, `regen_lean.sh`, `run_glp.sh` |
| `code/obstructions/` | `repro_O4.sh`, `mlcheck.rs` (exact `ML`), `shift_grid.py` (exact rational scan of the shifted gap), `mlexact.py`, `gwcheck.py`, `tightscan.py`, `t2box.py`, `chainparity.py`, `cornercheck.py` (check of the tight-corner proposition), `descent_check.py` (exact checks for the descent and topology section, with the standard `ML` routine and its controls), `README.md` |
| `code/perturbation/` | 33 Rust programs and `README.md` (commands and observed outputs) |
| `code/reduction/` | cargo projects `mdr`, `levelfit`, `fcuspec`, `gdn`, `ecalc`, `t2hunt`, `t2sweep`, `rmj`, `modchk`; `axioms/` |
| `code/covering/` | Rust programs for the covering paper and `README.md` |
| `code/eight/` | generator, per-prime records, checkers, scripts |
| `code/lean_build/` | sequential single-module Lean build script |
| `data/dense/` | `thmd/` (outputs of the Theorem 3 checks: `window_2m.out`, `window_higher.out`, `steps.out`, `cross_check.out`, `class_check.out`, `case_recount.out`), certificates `certs/`, `results.tsv`, `check_rows.out`, `regen_lean.out`, `fb_check.out`, `yind_2_62.out`, `st89_check.out`, `dev_logs/` (raw development logs), `m94/` |
| `data/obstructions/` | `seeds/` and `census/` input lists, outputs of the reruns, `cornercheck.out`, `chainparity.out`, `descent_gw_loo.tsv` (input table), `descent_controls.out`, `descent_d0.out`, `descent_instances.out`, `descent_gw.out`, `descent_table.out`, `descent_strict.out` |
| `data/repro_logs/` | outputs of reproduction runs |
| `MANIFEST.tsv`, `CLAIMS.tsv`, `RELEASE_CHECK.md`, `CITATION.cff`, `LICENSE.md` | file list with SHA-256, claim-to-evidence map, release check, citation metadata, license |

## Reproduction

Toolchain: `rustc 1.96.0 (ac68faa20 2026-05-25)`, edition 2021; Python 3.12.8 (glue only: `code/dense/check_rows.py`, `code/dense/src/cg/lp.py`,
`code/obstructions/shift_grid.py`, `code/obstructions/cornercheck.py`, `code/obstructions/chainparity.py`, `code/obstructions/descent_check.py`, `code/eight/checks/bs_card4/falsify.py`); LaTeX: latexmk 4.88 with pdflatex (TinyTeX);
Lean `leanprover/lean4:v4.30.0`, Lake 5.0.0, Mathlib `v4.30.0` (revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`). The cargo projects in
`code/reduction` use `rayon`, `num-bigint`, `num-traits` (locked); all other Rust files use only the standard library. GLPK `glpsol`, `kissat` and HiGHS were used by the original searches only.

    bash code/reproduce.sh build        # regenerates the listed computations that have a program; the measured steps sum to about 43 minutes; the script itself was not run end to end

Individual steps (run from the archive root; outputs of the runs made for this snapshot are in `data/`):

| Step | Command | Expected output |
|---|---|---|
| dense rows | `bash code/dense/build.sh build/dense; python3 -I code/dense/check_rows.py build/dense/v1` | 63 rows, 0 failures; composite lists and exceptions `{94,97,103,109,115,122}` |
| fractional blocking | `build/dense/fb check lean/LRSpectrumFull/Delta2FracBlocking.lean`; `fb selftest` | 4 certificates ACCEPT (`5/1`, `15/2`, `25/2`, `145/11`); selftest failures 0 |
| Theorem 3 checks | `cd code/dense/src/thmd; rustc -O dense_check.rs; ./dense_check controls; ./dense_check window M 2M` for `M = 1..12`; `./dense_check steps M` for `M = 2..12`; `rustc -O class_check.rs && ./class_check`; `rustc -O case_recount.rs && ./case_recount`; `python3 -I cross_check.py` (not in `reproduce.sh`; seconds) | `failures=0` for each `M`; case counts of the unnumbered table in Section 2 of the paper (`5811 3830 266 32` at `M = 7`); `class_check`: 0 exceptions for the six primes, controls OK; `cross_check`: no set without witness for `M = 2..8`. Outputs `data/dense/thmd/` |
| Statements 8, 9 | `build/dense/st89 control`; `st89 run M 4` for `M = 2..17` (`M = 16, 17` take 3 and 8 minutes); `st89 s0 M` | 0 undominated valid blocks, covers of `F_4` and `R_4` agree, negative control fires; singleton bad sets `{1}`, `{m+1}` only; full output `data/dense/st89_check.out` |
| Y-independence | `build/dense/yind 2 62`; `yind control 13` | `Y_independent true` for 61 values; control finds a bad set inside `{m+1,...,2m}` |
| tight corner, chain parity | `python3 -I code/obstructions/cornercheck.py`; `python3 -I code/obstructions/chainparity.py 20001` | 0 failures on 10,642 maximisers; control `L == b` fails on 4,264; no mismatch for odd `q <= 20001` |
| descent and topology section | `python3 -I code/obstructions/descent_check.py controls`; `d0`; `instances`; `gw`; `table 73`; `strict 151` (about 3 minutes in total; `table 73` takes 75 s, `strict 151` 50 s) | `SELFTEST PASS`; 0 failures on 1500 random vectors; the three instances of Observation 27 and the `m = 7` values; the 66 single-replacement triples regenerated, control differs; 70 vectors, 11 / 59 / 46 / 13 / 0 and 56 / 43; strict witnesses for the 11 values of `m`. Outputs `data/obstructions/descent_*.out` |
| obstruction table | `bash code/obstructions/repro_O4.sh build/obs` | ML `14/121, 11/84, 168/1697, 28/191, 30/203`; U1, U2 as in the table; levels 22, 13, 35, 38, 39 |
| perturbation | see `code/perturbation/README.md` (`perturb_coverk 2 5 100` is not in `reproduce.sh`; about 2 hours) | e.g. `perturb_degen`: 65504 / 43849 / 62816; `perturb_cfire 2000 10`: 331291 at `k = 1`, 0 for `k = 2..10` |
| covering | see `code/covering/README.md` | e.g. `identchk 4 90`: 11528 instances, control fires 3280 times; `tmpl63 19`: 969154513 nodes, template does not exist |
| eight hashes | `bash code/eight/stage/build_generator.sh; bash code/eight/stage/repro_all.sh` | `P<p> REPRODUCED <sha256>` for 27 primes |
| Lean | `cd lean && bash ../code/lean_build/gbound_build.sh Delta2CoverRangeS66` | not run for this snapshot; needs network for Mathlib and about 10 GB per worker; never a bare `lake build` |

Manuscripts: `cd paper/<name> && latexmk -pdf main.tex` (`lrc_covering.tex`, `perturbation.tex` for the two papers not named `main.tex`).

## Formalization status

The complete tables (paper item, label, Lean declaration, module) are `paper/dense-window/LEAN_MAP.md`, `paper/obstructions/LEAN_MAP.md`,
`paper/reduction/LEAN_MAP.md`, `paper/eight/LEAN_MAP.md`, and the Formalization sections of `paper/perturbation/perturbation.tex` and
`paper/lrc_covering/lrc_covering.tex`. Principal rows:

| Paper item | Lean declaration (module) | State |
|---|---|---|
| dense, Theorem 3 | `dense_floor_of_prime` (`Delta2DenseWindow`); case 2 `floor_of_not_dvd_le` (`Delta2DigitGreedy`); pair lemma `floor_of_pairsum_prime` (`Delta2Pigeonhole`); class form `floor_of_missed_class` (`Delta2DenseWindow`) | Lean declaration VERIFIED, carried over, not rebuilt; axiom print recorded, raw output in `data/dense/dev_logs`; written proof PROVED |
| dense, fractional blocking | `floor_of_frac_blocking` (`Delta2FracBlocking`), `dense_floor_m4,7,12,13` | VERIFIED; prints in `dev_logs` |
| dense, cover capacity | `floor_of_cover_capacity` (`Delta2CoverCapacity`) | VERIFIED |
| dense, rows | `dense_floor_m<m>`, `dense_floor_m<m>_split` (`Delta2CoverRange*`) | VERIFIED; 47 rows with archived prints, 16 rows (L) with records only |
| covering, equivalence | `floor_of_no_hitting_set`, `not_floor_of_hitting_set` | VERIFIED |
| covering, surplus | `floor_of_surplus` | VERIFIED |
| obstructions, barrier | `goodSet_countable`, `goodSet_null`, `integral_le_sum_badSet`, `lt_ML_of_integral_unionBound` (`RoomA4Barrier`) | VERIFIED |
| obstructions, half shift | `halfShift_not_lonely` (`RoomFCUMss`) | VERIFIED |
| obstructions, T statements | `tightNoDvd_of_strong` (`RoomFCU_f5`) | stated with `sorry`; CONJECTURE |
| dense Statements 8, 9; obstructions Propositions 7, 13, 14, 16, Lemmas 20, 22, Propositions 29, 31, Corollary 30, Remark 33 | none (ABSENT; a Lean statement of `ML(cV) = ML(V)` for tuples, `ML_smul` in `Delta2Scaling`, is in the source tree and was not checked for this version) | PROVED, not formalized |
| obstructions Observations 23, 25, 27, Proposition 24, Conjecture 26 | none (ABSENT) | HEURISTIC, FALSE (statement) or CONJECTURE; exact computations, not formalized |
| perturbation | `exists_interval_uncovered`, `exists_lonely_time`, `lonely_of_criterion_c'`, `exists_deleted_fraction` | VERIFIED (declaration list in the paper) |
| reduction | `universalFloor_of_four_atoms_U` (`RoomA4Compress`), `floorCruxU_iff_universalFloor` (`RoomFCUErdos`) | VERIFIED |
| eight | `eight_runners_unconditional` (`EightRunners`) | VERIFIED modulo 27 axioms `lemma7Check_seven_p<p>_verified` (`EightCert27`) |

Modules with `sorry` bodies or `axiom` declarations are listed in `lean/README.md`. Nothing was built when this archive was assembled; whether the
tree builds as archived (comments rewritten, 196 of the development modules) is untested.

## Data provenance

* `data/dense/certs/m*.g1.sol`, `m*.sol`: certificates found by `g1` (local search) or the earlier pipelines; accepted by `v1`; those embedded in the cited Lean modules are VERIFIED, the others COMPUTED.
* `data/dense/results.tsv`: build seconds and axiom prints for `m >= 66`, from the development batch driver.
* `data/dense/dev_logs/`, `data/dense/m94/`: raw development logs (build output with axiom prints, column-generation driver outputs, the `m = 94` search). Paths were rewritten to `<dev-tree>`; content otherwise unchanged. Not regenerated by this archive.
* `data/obstructions/descent_gw_loo.tsv`: leave-one-out values of the 67 Goddyn-Wong type tight vectors (66 single replacement, 1 double), from an exact Rust job of 18 October 2026 whose source is not archived (generator not archived). The 66 single-replacement triples are regenerated from the GCD condition by `descent_check.py gw`; the rows with `m <= 73` are recomputed by `descent_check.py table 73`; the other rows are not recomputed in this archive. Label HEURISTIC.
* `data/obstructions/seeds/`, `census/`: seed lists of the exact-scan hunt and the 1067 census residual and 147 adversarial families used by `mdr cert`.
* `data/repro_logs/`: outputs of the runs made for the 17 and 18 October 2026 snapshots, including `perturb_coverk_k3_7_40_original.log`, the log of the original `k = 3` run.
