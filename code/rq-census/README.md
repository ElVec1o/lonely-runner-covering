# code/rq-census

This directory holds two programs. The program of release 1.4.0 (`src/main.rs`, `check60.py`, `Cargo.toml`, `Cargo.lock`; outputs `data/rq-census/*.out`) is unchanged and is described in the sections before the last one (seven class predicates, two of Malikiosis, Santos and Schymura and five Lean classes; the census of version 1.4.0). Its extension of release 1.5.0 (`v2/`; outputs `data/rq-census/v2/`) adds the two classes R7 and Q3 and is described in the last section, "Version 2 (release 1.5.0)". The counts of version 1.4.0 are superseded by those of version 2 in `paper/shifted-real-four-classes/NOTE.md`; the version 1.4.0 outputs are kept as they were.

Program behind the census of version 1.4.0, quoted in `paper/shifted-real-four-classes/NOTE.md` (caveat 3 and the census table). Outputs of the runs for that snapshot are in `data/rq-census/`.

| File | Role |
|---|---|
| `src/main.rs` | Rust, standard library only. Enumerates the 4-sets of distinct positive integers `a < b < c < d` with gcd 1 and sum at most `MAXSUM`, evaluates seven class predicates on each, and prints exact counts. Usage: `rq_census MAXSUM [std|nogcd|tq5]`. |
| `check60.py` | Independent cross-check for sum at most 60 only (Python, standard library, about 3 seconds, about 15 MB). Different structure: permutations of the four speeds and the definitions applied directly; no shared code with `main.rs`. |
| `Cargo.toml`, `Cargo.lock` | A cargo project for the same source (`overflow-checks = true` in the release profile). `rustc` alone is enough. |

## What is counted

The universe is the set of 4-sets of distinct positive integers with gcd 1 and sum at most `MAXSUM` (for `MAXSUM = 195` this is the set of 2,133,561 vectors enumerated by Alcantara, Criado and Santos, arXiv:2506.13379; the count is the control). Each vector gets a 7-bit mask of classes. Mode `std`: the classes are as below; `nogcd` drops the gcd condition (negative control: the universe changes); `tq5` replaces `q >= 6` by `q >= 5` in class T (planted error: the class T changes).

| Bit | Class | Predicate in `main.rs` |
|---|---|---|
| 0 | MSS29 | for some speed `z`, the gcd of the other three is at least 2 |
| 1 | MSS65 | some pair of speeds has gcd odd and at least 5, or even and at least 10 |
| 2 | R5 | the number of speeds divisible by 5 is 1, 2 or 3 (Lean theorem `R5_core`, version 1.3.0) |
| 3 | P3 | some `q >= 2` divides all speeds but one and does not divide that one (Lean theorem `P3`) |
| 4 | QGEN | for some pair `{i, j}` and some `q >= 4` dividing the gcd of `v_i, v_j`, with the other two speeds coprime to `q`, `q` dividing their sum or difference, and `v_i`, `v_j` each different from the sum and from the difference of the other two (Lean theorem `QGen`; `q = 4` is `Q4`) |
| 5 | T | for some pair `{i, j}` and some `q >= 6` dividing the gcd of `v_i, v_j`, the other two speeds are coprime to `q` (Lean theorem `T`) |
| 6 | G24 | two speeds odd, one speed 2 mod 4, one speed 0 mod 4 and different from the sum and from the difference of the odd pair (Lean theorem `G24`) |

"Lean class" is the union of bits 2 to 6; "MSS class" is the union of bits 0 and 1. The predicates are our reading of the Lean statements and of the hypotheses of Proposition 2.9 and Proposition 6.5 (with n = 4) of Malikiosis, Santos and Schymura (arXiv:2411.06903, version 2); they are not the statements of those papers. The program makes no statement about vectors with speed sum at least 196. Nothing here proves the shifted theorem for four moving runners: the counts say how many vectors of the enumerated set lie in a class with a Lean proof in this archive, and how many do not.

## Commands

From the archive root. The Rust runs take about one second and use a few MB; the Python cross-check takes about 3 seconds.

    cd code/rq-census
    rustc -O -C overflow-checks=on src/main.rs -o rq_census
    ./rq_census 195 std   > ../../data/rq-census/main195.out
    ./rq_census 195 nogcd > ../../data/rq-census/nogcd195.out
    ./rq_census 195 tq5   > ../../data/rq-census/tq5_195.out
    ./rq_census 60 std    > ../../data/rq-census/rust60.out
    python3 -I check60.py > ../../data/rq-census/py60.out
    sed -n '/^TOTAL/,/^T7_NOT_MSS65/p' ../../data/rq-census/rust60.out | diff - ../../data/rq-census/py60.out    # no output expected

The five outputs in `data/rq-census/` were regenerated from this source for the archive (build with `rustc -O -C overflow-checks=on`, the commands above) and are byte-identical to the outputs of the original runs.

## Expected output (lines of `data/rq-census/main195.out`, mode `std`, `MAXSUM 195`)

    TOTAL 2133561
    LEAN 1867559
    MSS 1222641
    COVERED 1867559
    RESIDUAL 266002
    LEAN_NOT_MSS 644918
    LEAN_NOT_MSS_OR_R5 179090
    COVERED_NOT_LEAN 0
    P3_xor_MSS29 0
    CLASS MSS29 750712 only 0
    CLASS MSS65 811273 only 0
    CLASS R5 1237736 only 282821
    CLASS P3 750712 only 0
    CLASS QGEN 416974 only 42066
    CLASS T 500937 only 1294
    CLASS G24 423532 only 115015
    Q4 188383
    QG5 270708
    QG5_NOT_R5_MSS_T 0
    T7 447075
    T7_NOT_MSS65 0
    TNM g6=1 g8=0 other=0 : 19973
    TNM g6=0 g8=1 other=0 : 23541
    RESID 266002
    INRES [1, 2, 3, 4] true
    INRES [1, 3, 4, 6] true
    INRES [1, 3, 4, 7] true

Here `COVERED` is the union of the Lean and the MSS classes, `RESIDUAL` the vectors in none of the seven classes, `only` the number of vectors whose mask has only that bit, `Q4` the vectors with a QGEN witness `q = 4`, `QG5` those with a witness `q >= 5`, `T7` those with a T witness `q >= 7`, `q != 8`, `T7_NOT_MSS65` those among them outside MSS65, `TNM` the vectors of T in neither MSS class by the gcd of the divisible pair, and `RESID` the list of vectors in none of the classes (the 20 smallest by speed sum are printed after `RESID`, with `INRES` lines for the three tight vectors of Alcantara, Criado and Santos). `COVERED_NOT_LEAN 0` says that on this universe every vector in an MSS class is in a Lean class.

Controls, in the other outputs: `nogcd195.out` has `TOTAL 2285448` (the gcd condition is part of the universe); `tq5_195.out` has `CLASS T 727225` instead of 500937 (the planted error changes the class). `rust60.out`: `TOTAL 15576`, `LEAN 13214`, `MSS 7227`, `RESIDUAL 2362`, `LEAN_NOT_MSS 5987`; `py60.out` agrees with the lines `TOTAL` to `T7_NOT_MSS65` of `rust60.out` (54 lines). No third implementation was run beyond sum 60.

## Version 2 (release 1.5.0): the classes R7 and Q3

`v2/src/main.rs` is `src/main.rs` extended by two more classes, and `v2/check60_v2.py` is an independent cross-check for sum at most 60 that includes them. `v2/Cargo.toml` and `v2/Cargo.lock` are the files of version 1.4.0. The program changed only by the additions below; with the two classes switched off (mode `noRQ`) it reproduces the counts of version 1.4.0 (`RESIDUAL 266002`, `LEAN 1867559`, the class sizes and the `only_with_mss` counts of `data/rq-census/main195.out`). The output format differs from version 1.4.0 (lines `H <mask> <count>` for every mask that occurs, and `CLASS <name> <size> only_with_mss <n> only_among_7_lean <m>`), so the outputs of the two versions are not byte-comparable.

| Bit | Class | Predicate in `v2/src/main.rs` (our reading of the Lean statement) |
|---|---|---|
| 7 | R7 | for some assignment of roles `(s, a, b, c)` of the four speeds: `v_s` is divisible by 7, `v_a`, `v_b`, `v_c` are not, and either (A) `v_a ~ v_b` and `v_a ~ v_c`, or (B) `v_b ~ v_c`, not `v_a ~ v_b`, and not [`v_s = v_b + v_c` or `v_b = v_c + v_s` or `v_c = v_b + v_s`, together with `v_b = +3 v_a` or `-3 v_a` modulo 7]; here `x ~ y` means that 7 divides `x - y` or `x + y` (Lean theorem `R7_partial`) |
| 8 | Q3 | exactly two speeds are divisible by 3, and for each of them `v_s` is different from `v_a + v_b`, from `v_a - v_b` and from `v_b - v_a`, where `v_a`, `v_b` are the other two (Lean theorem `Q3`) |

"Lean class" in version 2 is the union of bits 2 to 8; the lines `LEAN`, `MSS`, `COVERED`, `RESIDUAL`, `LEAN_NOT_MSS`, `LEAN_NOT_MSS_OR_R5`, `COVERED_NOT_LEAN` keep their meaning of version 1.4.0 (Lean class = bits 2 to 6), and the new lines are `LEAN2` (bits 2 to 8), `RESIDUAL2` (in no Lean class of bits 2 to 8 and in no MSS class), `R7_ADDED_BEYOND_LEAN`, `Q3_ADDED_BEYOND_LEAN`, `R7_OR_Q3_ADDED_BEYOND_LEAN` (in the class and in no class of bits 2 to 6), `R7_AND_Q3` and `LEAN2_NOT_MSS`. In the rows `CLASS`, `only_with_mss` counts the vectors whose mask has only that bit (so in no other of the nine classes), and `only_among_7_lean` counts the vectors that lie in that Lean class and in none of the other six Lean classes (the two MSS bits are ignored).

Usage: `rq_census_v2 MAXSUM [std|nogcd|tq5|noRQ|r7noexcl]`. Mode `noRQ` switches R7 and Q3 off (regression against version 1.4.0); mode `r7noexcl` drops the exclusion clause of pattern (B) of R7 (planted error: the tight vector `(1,3,4,7)` must enter R7); modes `nogcd` and `tq5` are the controls of version 1.4.0.

### Commands (from the archive root)

    cd code/rq-census/v2
    rustc -O -C overflow-checks=on src/main.rs -o rq_census_v2
    ./rq_census_v2 195 std     > ../../../data/rq-census/v2/std195.out
    ./rq_census_v2 195 noRQ    > ../../../data/rq-census/v2/noRQ195.out
    ./rq_census_v2 195 r7noexcl > ../../../data/rq-census/v2/noexcl195.out
    ./rq_census_v2 60 std      > ../../../data/rq-census/v2/std60.out
    python3 -I check60_v2.py   > ../../../data/rq-census/v2/py60_v2.out
    diff <(grep '^CLASS' ../../../data/rq-census/v2/std60.out | grep -v MSS | awk '{print $2,$3,$7}') \
         <(grep '^CLASS' ../../../data/rq-census/v2/py60_v2.out | awk '{print $2,$3,$5}')    # no output expected

The Rust runs take about one second each (a few MB); the Python run takes a few seconds. The five outputs in `data/rq-census/v2/` are the logs of the runs of 12 November 2026 of this program; they were not regenerated again for this archive (the command line used for the original build was not recorded; `rustc -O -C overflow-checks=on` is the one of version 1.4.0, and `overflow-checks = true` is also set in `v2/Cargo.toml`). The diff command above was run on the archived outputs and printed nothing.

### Expected output (lines of `data/rq-census/v2/std195.out`, mode `std`, `MAXSUM 195`)

    TOTAL 2133561
    CLASS R7 576799 only_with_mss 60054 only_among_7_lean 60054
    CLASS Q3 611118 only_with_mss 49941 only_among_7_lean 49941
    LEAN 1867559
    MSS 1222641
    COVERED 1867559
    RESIDUAL 266002
    LEAN2 2002342
    RESIDUAL2 131219
    R7_ADDED_BEYOND_LEAN 84842
    Q3_ADDED_BEYOND_LEAN 74729
    R7_OR_Q3_ADDED_BEYOND_LEAN 134783
    R7_AND_Q3 162666
    LEAN2_NOT_MSS 779701
    COVERED_NOT_LEAN 0
    RES resonant=0 even0..4 [17850, 69964, 24021, 0, 0]
    RES resonant=1 even0..4 [572, 11157, 7655, 0, 0]
    RESID 131219
    INRES [1, 2, 3, 4] true
    INR7 [1, 2, 3, 4] false
    INQ3 [1, 2, 3, 4] false
    (likewise INRES true, INR7 false, INQ3 false for [1, 3, 4, 6] and [1, 3, 4, 7])

In `RES`, "resonant" means that some speed is the sum of two others, or that the sum of two speeds equals the sum of the other two; the five numbers are the vectors in no Lean class and no MSS class with 0, 1, 2, 3, 4 even speeds. `RESID` lists, after its count, the 20 vectors of smallest speed sum in none of the classes (the first is `[1, 2, 3, 4]`, sum 10).

Controls, in the other outputs. `noRQ195.out`: `TOTAL 2133561`, `LEAN 1867559`, `RESIDUAL 266002`, `RESID 266002`, `CLASS R7 0`, `CLASS Q3 0`, and the class sizes and `only_with_mss` counts of version 1.4.0 (`R5 1237736 ... 282821`, `QGEN 416974 ... 42066`, `T 500937 ... 1294`, `G24 423532 ... 115015`). `noexcl195.out` (R7 without its exclusion clause): `CLASS R7 589579` instead of 576799, `RESIDUAL2 128169` instead of 131219, and `INR7 [1, 3, 4, 7] true`, `INRES [1, 3, 4, 7] false`, while `[1, 2, 3, 4]` and `[1, 3, 4, 6]` stay out of R7. `std60.out` (sum at most 60): `TOTAL 15576`, `CLASS R7 3787`, `CLASS Q3 3930`, `LEAN2 14398`, `RESIDUAL2 1178`, `R7_ADDED_BEYOND_LEAN 768`, `Q3_ADDED_BEYOND_LEAN 607`, `R7_OR_Q3_ADDED_BEYOND_LEAN 1184`. `py60_v2.out` (independent Python implementation, permutations of the speeds and the definitions applied directly) agrees with the Rust output on all of these values, on the `only_among_7_lean` counts of the seven Lean classes (R5 1910, P3 954, QGEN 181, T 279, G24 527, R7 577, Q3 416) and on the split of the vectors in no class by resonance and number of even speeds. No third implementation was run, and no run beyond sum 60 other than the Rust one.

The predicates of R7 and Q3 are our reading of the Lean statements `R7_partial` and `Q3` (the Lean statement is the authority), and the predicates of the two MSS classes are our reading of Malikiosis, Santos and Schymura as in version 1.4.0. The program makes no statement about vectors with speed sum at least 196. Nothing here proves the shifted theorem for four moving runners.
