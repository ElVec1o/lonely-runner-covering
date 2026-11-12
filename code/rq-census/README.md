# code/rq-census

Program behind the census quoted in `paper/shifted-real-four-classes/NOTE.md` (caveat 3 and the census table). Outputs of the runs for this snapshot are in `data/rq-census/`.

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
