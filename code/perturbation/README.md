# code/perturbation

Programs behind the computations of `paper/perturbation/perturbation.tex`. Notation: `V = ([n-1] \ M) u R`,
`|M| = |R| = k`, every replacement at least `n`; `U(n,M)` is the region left uncovered by the baseline.
All arithmetic is exact (`i128` rationals); no floating point is load-bearing. Standard library only.

Build: `rustc --edition 2021 -O -o build/perturbation/NAME code/perturbation/NAME.rs` for each `NAME`
(all 28 files compile with rustc 1.96.0). Run from any directory. Every sweep is exhaustive over the stated
range; the printed counts are the binomial coefficients or the sizes of the enumerated sets, which is the check
that nothing was skipped.

## Values regenerated and verified on 2026-10-17 and 2026-10-18

| Command | Paper statement | Observed |
|---|---|---|
| `perturb_divis` | divisibility equivalences: 593,442 / 132,684 instances, 121,368 subsets M | `593442 instances, 0 violations`; `132684 ... 0 violations`; `121368 ... 0 violations` (1 s) |
| `perturb_thm` | sufficient condition `8kb <= n`: 4,563,449 triples | `4563449 triples, 0 failures` (2 s) |
| `perturb_twopuncture` | exhaustive two-puncture sweep: 5,241,348 configurations, minimum 3/22 at n=13, M={5,6,7}, W={13,14} | `5241348 configs`, `min ratio = 0.136364`, `3/22` (400 s) |
| `perturb_window exact` | `ell(n,M)` formula: 134,721 pairs (n,M), |M| <= 4 | `total pairs (n,M) checked: 134721` (80 s) |
| `perturb_split 6 44 1` | 594 unit-class instances, 0 violations | `unit-class instances checked: 594  VIOLATIONS: 0` |
| `perturb_p7 6 70` | closed form: 1186 exact, 0 overshoot; min 1.65254 | as stated (2 s) |
| `perturb_cover2 30` | no admissible R for |M| = 2, 9 <= n <= 30 | `COVERS FOUND: 0 ... capped (UNDECIDED): 0` (4 s) |
| `perturb_selfcheck` | self-checks of the verifiers | `ALL CHECKS PASSED` |
| `perturb_cfire 2000 10` | condition (c) of the unconditional corollary holds 331,291 times at k = 1, n <= 2000, never for 2 <= k <= 10 | `k= 1: ... 331291`, `2<=k<=KMAX: 0`; controls (two expressions agree, proof inequality has 0 violations) true |
| `perturb_degen` | 65,504 nonempty proper M, 3 <= n <= 16; degenerate components in 43,849; every positive component is a window; summing over base points without deduplication is wrong in 62,816 | `TOTAL ... M 65504 ; ... degenerate component 43849 ; ... not a window 0 ; window not a component 0 ; naive sum != lambda 62816 ; deduplicated sum != lambda 0`; control n = 4, M = {2}: 3 components, 1 window |
| `perturb_window measexact` | lambda(U) equals the deduplicated sum of the base-point components on 7,315 pairs (n,M), |M| <= 3, n in {12,16,20,24,28} | sets 95 + 935 + 6285 = 7315, `100.00%` equal, 0 over |
| `perturb_thm` | 4,563,449 triples with b >= 1, of which 4,338,029 with b >= 2 | `(1) ... 4563449 triples, 0 failures`; `(1b) ... 4338029` (one counter line added to the original program) |
| `perturb_ratio` | ratio of ell(n,{n-2}) n^2 to 2/P(n-2): 1.163, 1.036, 1.009, 1.002 at n = 50, 200, 800, 3200 | `1.162791`, `1.036269`, `1.008827`, `1.002192`; control: formula equals the interval sweep for 20 <= n <= 60, all b, and at n = 50, 200 |
| `g1_gap_criterion` | gap criterion decides 94.17% of 147,099 normal-form instances, no ground-truth violation | `147099`, `138527 (94.17%)`, violations 0 (ground truth in f64, tolerance 1e-12) |
| `r1_fourier_criterion 40` | 49,121 instances, 49,120 decided, one undecided | undecided tuple (3,4,7,11); `CROSS-VALIDATION failures : 0` (f64) |
| `perturb_coverk 2 5 30` | k = 2 decision, 5 <= n <= 30 | `TOTAL (M,v1): 74722 tests: 137629 COVERS: 0 capped: 0`; rows equal the rows of the earlier partial run |
| `perturb_coverk 3 7 16` | k = 3 decision, 7 <= n <= 16 | `TOTAL (M,v1): 42649 tests: 1883904 COVERS: 0 capped: 0`; rows equal the rows of the original log `perturb_coverk_k3_7_40_original.log` |

Status of the long runs. k = 2, 5 <= n <= 100: regenerated. The rows sum to 161,696 sets, 7,520,944 pairs (M,v1) and 13,989,171 steps, 0 covers, 0 capped, equal to the paper
(rows 5..66 from `data/repro_logs/perturb_coverk_2_5_66_partial.txt`, a run of 2026-10-17; rows 5..30, 67..76, 77..100 from the runs of 2026-10-18 in `perturb_coverk_2_5_30.txt`,
`perturb_coverk_2_67_76.txt`, `perturb_coverk_2_77_100.txt`; rows present in two runs are identical). The deletion-set totals are also arithmetic (161,696 = C(100,3) - C(4,3);
161,414 = 161,696 - 282, 282 = C(13,3) - C(4,3) for n <= 13).
k = 3, 7 <= n <= 40: the totals (91,375 sets, 3,021,814 pairs, 153,363,483 steps, 0 covers, 0 capped) are the column sums of the original log
`data/repro_logs/perturb_coverk_k3_7_40_original.log`; the archived program reproduced its rows for 7 <= n <= 22 exactly (`perturb_coverk_3_7_16.txt`, `perturb_coverk_3_17_22.txt`,
`perturb_coverk_3_7_23_partial.txt`); rows 23 <= n <= 40 (the bulk of the 153 million steps) were not re-run: COMPUTED in a development run, not regenerated.
The first, unsound version of the k = 3 search had 21,347,666 steps; step counts depend on the program version.
Not regenerated by any program of this archive: the margin statement of the paper's Fourier section ("never below 0.372 mu unless v4 satisfies an integer relation of coefficients at most 3").

## Commands

Components of `U(n,M)`, unit versus non-unit M:

    perturb_ucomp          # components of U(n,M), minimum over all M
    perturb_split 6 44 1   # 594 unit-class instances, 0 violations, bound attained
    perturb_split 6 34 2   # 4847 unit-class instances, 0 violations
    perturb_locate 32 30   # ell = 1/2576, simplest rational inside = 13/30
    perturb_locate 2312 2310   # ell*n(n-1) = 0.1548 against predicted 2/13 = 0.1538
    perturb_rigid 8 20 2 4 400 # 631 rigid-residual configurations, 0 failures
    perturb_gw             # Goddyn-Wong {1..29,31,90} consistency check

P7 and P8:

    perturb_classes        # 3-way classification of M
    perturb_p7 6 70        # min ell*n(n-1)*P(b) = 1.65254; closed form 1186 exact / 0 overshoot
    perturb_p7lb 6 90      # 3995 pairs, 0 violations; min LB*n(n-1)*P(b) = 1.39048
    perturb_tight          # tightness of the degenerate family; LR*n = 1.000000000
    perturb_adv 400        # attacks each step of the P7 proof
    perturb_p8b 8 34 6     # P8 for |M| = 2: 0 degenerate cases; min maxcomp(U')*n(n-1) = 0.375

`perturb_p8` tests |M| = 1 against two speeds, which is not a k-speed modification; its four degenerate cases
are one-speed modifications and are tight instances (`perturb_tight`). Use `perturb_p8b` for k = 2.

Isolated points of the uncovered region (the sweep records a gap when the next left endpoint is at least the
running right endpoint, so isolated points are kept):

    perturb_isolated 8 12 6    # U(8,{6}) \ B_12 = {1/8,3/8,5/8,7/8}: nonempty, no component
    perturb_isolated 14 24 12  # same shape at n=14, 20, 26

Ceiling and multi-puncture form:

    perturb_ceiling        # min of longest(U\B_v1) / [(n-2)/(n v1)] = 0.04075 at (18,{6,8},19)
    perturb_multipuncture  # single puncture 21<=n<=44: min ratio 0.207341 at (32,{18,30},36);
                           # two punctures k=3, 9<=n<=22: 0.145455 at (9,{2,4,5}); ell(n,{1,2})*n = 2/3

Unconditional criterion and reach:

    perturb_uncond         # fraction of k-subsets settled outright by ell > 2k/(n(n-2k))
    perturb_thm            # sufficient condition 8kb <= n
    perturb_twopuncture    # exhaustive two-puncture sweep
    perturb_widen          # C3 => C2 => C1 over all k-subsets, 0 failures

`perturb_window` (localization, exact formula, reach): `perturb_window exact | measure | reach` (no argument runs all).
`perturb_window` has two windows: `window`, the true component adjacent to `a/b`, and `windowLean`, which caps
the right offset at `1/(nb)` (the hypothesis `hdelta1` of `lonely_of_window`).

The k = 2 falsification search `perturb_cover2` decides, for every M with |M| = 2 and every n in range, whether an
admissible R = {v1, v2} exists with `U(n,M)` inside `B_v1 u B_v2`:

    perturb_cover2 30          # 9 <= n <= 30, seconds
    perturb_cover2 50          # 9 <= n <= 50, about 7 minutes, negligible memory
    perturb_cover2 50 2000000  # second argument: cap on v2 (never reached in this range)

The enumeration is finite: `v1 = min R <= 2k/(ell (n-2k))` (covering lemma), and a connected subset of `B_v` lies in
one constituent interval, so a residual component of length L forces `v2 < 2/(L n)`. The residual-is-finite branch
is decided by congruences modulo `lcm(q_i)`. Both caps are printed; a nonzero value means the corresponding
branches are undecided. `selftest()` runs first and prints positive controls; a null result from a run whose
controls did not print `true` is void.

Divisibility: `perturb_divis` regenerates the figures of the divisibility section (equivalences `b | v` and
`n | v` as above; criterion D against the measure criterion at k = 1; the truth column runs a genuine cover test).

Classification of tight modifications, `perturb_tight K N1 N2`:

    perturb_tight 2 5 45   # k=2, 5 <= n <= 45, about 3 minutes
    perturb_tight 3 7 32   # k=3

Output for k = 2, 5 <= n <= 45: exactly two tight configurations, `V = {2,4,6,8}` at n = 5 and
`V = {1,4,5,6,7,11,13}` at n = 8. To evaluate LR(V) by hand use the denominators `v_i + v_j` and `|v_i - v_j|`,
not the breakpoint set `{(2a+1)/(2v)}`; test the baseline `{1,2,3,4}` (LR = 1/5) first.

`perturb_coverk` carries an end-to-end control that runs before every search: it relaxes the bad sets to
`||v t|| <= 1/n` and must rediscover `n=8, M={2,3}, R={11,13}`. If it prints `0 tight configurations rediscovered`,
every null result of the program is void.

`perturb_selfcheck` exits 1 on any failure. It covers: textbook values (`LR([n-1]) = 1/n` for 3 <= n <= 26 and the
four known tight sets), sweep completeness (subset counts against `C(n-1,k)`), strict-mode positive controls
(isolated survivors `1/8`, `7/8` at `n=8, M={2,3}`), the interval stripper, non-vacuity of every criterion, and
agreement of the interval sweep with the base-point window formula.
