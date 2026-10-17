# Programs for "A machine-checked reduction of the lonely runner conjecture"

Every number in `paper/reduction/main.tex` that is not a Lean theorem is produced by one of the
programs below. All computation is Rust with exact integer arithmetic (`levelfit` has two short Python scripts that only tabulate its output). Build each with
`cargo build --release` inside its directory (toolchain: rustc 1.96.0, edition 2021); the
commands below are run from that directory. `ML` is computed as the maximum of
`min_i ||v_i t||` over the candidate times `t = c/(v_i+v_j)`, `i <= j`.

| Paper item | Program | Command |
|---|---|---|
| Table 1 (boxes, tight families, maximiser denominators, (T2) minima for m <= 10) | `fcuspec` | `./target/release/fcuspec sweep M H` for (M,H) in (3,1500) (4,500) (5,200) (6,110) (7,60) (8,48) (9,40) (10,36) |
| Independent enumeration of tight families | `gdn` | `./target/release/gdn tight M H 0` for (M,H) in (4,400) (5,200) (6,100) (7,64) (8,50) (9,42) (10,38) |
| Third enumeration, m <= 8 | `ecalc` | `./target/release/ecalc enum M H OUTFILE` for (M,H) in (3,80) (4,80) (5,60) (6,80) (7,60) (8,56) |
| ML(1,5,6,11,16,17) = 5/33 (Remark on (T2)) | `fcuspec` | `./target/release/fcuspec eval 1,5,6,11,16,17` |
| Table 2 (searches for counterexamples to (T2)) | `t2hunt` | `bash driver.sh` (seeds 101m+1 at height 5000, 101m+2 at height 60; 4 threads; wall-clock budgets make the evaluation counts machine dependent, the minima are the reported quantity) |
| Withdrawn: (T2) equality at m = 12 | `mdr`, `mlcheck` | `./target/release/mdr ml 1,4,6,7,10,11,12,13,16,17,19,23` now prints `ML=1/9`. The family was found by `mdr hunt3 12 200 SECS SEED` (seed not recorded) with the original `ml`, which skipped numerators not coprime to the denominator and returned 2/25; the paper no longer claims equality at m = 12 |
| Conjecture on F(m,j): 499 pairs, m <= 56 | `rmj` | `./target/release/rmj thmF 2 400 40` (witness for m <= 400, exact ML for m <= 40: 264 pairs) and `./target/release/rmj thmF 41 56 56` (235 pairs) |
| Level-drift examples (first certificate levels 22, 38, 46; ML = 28/191) | `mdr` | `./target/release/mdr certv 60 V` and `./target/release/mdr ml V` for each listed V |
| Level-drift example at m = 16 (first window level 35) | `mdr` | `MDR_QMIN=18 ./target/release/mdr certv 60 1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680` |
| Independent re-check of the level-drift families | `modchk` | `./target/release/modchk full V` |
| Invariant fit of certificate levels (Appendix) | `levelfit` | `./target/release/levelfit fitv 80 V ...`; `python3 analyze.py fit.tsv` |
| One-entry families: 15,307 families, minimum (2m+1)ML = 2, 42 uncovered | `t2sweep` | `./target/release/t2sweep 3 40 20 > full.txt` then `./target/release/t2sweep cover < full.txt` (the 42 lines are `uncovered.txt`) |


## Correction of `mdr` / `levelfit`

The function `ml` of `mdr/src/main.rs` (copied as `levelfit/src/mdr_base.rs`) originally enumerated the times `c/(v_i+v_j)` with `gcd(c, v_i+v_j) = 1` only. A maximiser whose reduced denominator is not a sum of two speeds was missed and the printed ML was too small (example: `mdr ml 3,4,7,11` printed 3/14, the exact value is 2/9 at t = 1/9). The archived sources enumerate every numerator. The SHA-256 of the sources before the change were `fb6559aa9fab235469a8f1d96cb60b234551c91d9c17f7982695c15abf4846c6` (`mdr/src/main.rs`) and `2b9e78f2ed59753691c232192dc73b8c2198e9adcb7dfe012daa67ea5f0f9fe7` (`levelfit/src/mdr_base.rs`). The independent program `code/obstructions/mlcheck.rs` computes ML with all numerators and has a selftest. The programs `fcuspec`, `gdn`, `ecalc`, `rmj`, `modchk`, `t2sweep` and `t2hunt` enumerate all numerators and were not affected. The certificate commands of `mdr` (`cert`, `certv`, `cert_m`) do not use `ml`.
