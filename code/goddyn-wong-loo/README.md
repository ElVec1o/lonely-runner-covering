# code/goddyn-wong-loo

Programs behind the finite computations quoted in `paper/goddyn-wong-loo/main.tex`. Outputs of the runs for this snapshot are in `data/goddyn-wong-loo/`. All Rust files are standalone (`rustc -O FILE.rs -o BIN`, standard library only) except where an `include!` or `#[path]` of `mlcore.rs` is noted.

| File | Role |
|---|---|
| `mlcore.rs` | Exact `ML(v)` as a reduced fraction (`u128`, every numerator `k` of `k/(v_i+v_j)`); verbatim copy of the routine used for all `ML` values of the note. |
| `loo_tables.rs` | Includes `mlcore.rs`. Modes `selftest` (six known values, prints `SELFTEST PASS`), `example` (n=8, r=6, mu=2), `thmA` (even r<=32: 240 vectors), `triples NMAX` (all triples of criterion (1) with n<=NMAX, all deletions), `vec n r mu`. Written for this archive; `thmA` and `triples 160` reproduce earlier logs (see the data README line). |
| `example_check.py` | Exact check of the two worked examples of the note (n=8; n=74 deletion of n-1). Python, `fractions`, under one second. |
| `enum_coprime_case.py` | Lists the triples with criterion (1), s>=4, gcd(r,n-1)=1 for n<=1100 (13 triples). Integer arithmetic only. |
| `fixchk/fixchk.rs` | `fixchk primes`: exact prime-window counts for n, r<=10^7 (sieve to 2*10^7), sharpness data and a floating-point evidence line for the analytic bound; `fixchk witA RMIN RMAX proof|any`: exact check of the witness times of Theorem A. |
| `fixchk/dus.rs` | Checks the two prime-counting inequalities used in Lemma 6 against a sieve to 2*10^7. |
| `fixchk/win.rs` | Window count for Lemma 6(c), n in [33,10^7]. |
| `chkL.rs` | Exact check of the witness times of Lemma 7 with u=n-1 (n in [31,140], mu*s<=r+1). |
| `chkC.rs` | Exact check of the witness times of Lemma 7 with u=n-2, Lemma 12 and the lower bound of Corollary 11 (n in [33,260], mu<=12, s>=4, mu*s<=r+1, gcd(r,n-1)=1). |
| `review/drv.rs` | Driver calling `ml()` of `mlcore.rs` (`#[path = "../mlcore.rs"]`): all deletions for every triple of criterion (1) with s>=4 in n in [33,300], mu<=12; classifies by gcd(r,n-1). |
| `review/wit.rs` | Second, separate sieve for the window of Lemma 6(c) and a second witness check for Lemma 7 (u=n-2, rule for large divisors) and Lemma 12 on a synthetic superset. |

Commands used for the logs in `data/goddyn-wong-loo/`:

    rustc -O -C overflow-checks=on loo_tables.rs -o loo_tables
    loo_tables selftest ; loo_tables example > example_n8.out ; loo_tables vec 74 70 2 > vec_74_70_2.out
    loo_tables thmA > thmA_small.log ; loo_tables triples 160 > loo_gw160.log
    rustc -O fixchk/fixchk.rs -o fixchk ; fixchk primes > primes_check.log
    fixchk witA 34 160 proof > witA_34_160.log ; fixchk witA 4 32 any > witA_4_32.log
    rustc -O fixchk/dus.rs -o dus ; dus > dusart_sanity.log
    rustc -O fixchk/win.rs -o win ; win > window_c_n33.log
    rustc -O chkL.rs -o chkL ; chkL > chkL_31_140.log
    rustc -O chkC.rs -o chkC ; chkC 33 260 12 > chkC_33_260.log
    rustc -O -C overflow-checks=on review/drv.rs -o drv ; drv 33 300 12 > classc_review_33_300.log
    rustc -O review/wit.rs -o wit ; wit > review_wit.log
    python3 example_check.py > example_check.out ; python3 enum_coprime_case.py 1100 > coprime_case_triples.out

Resources: the sieves use about 100 MB; `loo_tables triples 160` takes about 30 s and `drv 33 300 12` about 50 s on the machine used; the other runs take seconds to about a minute. `fixchk witA 4 32 any` ends with two reported "NO WITNESS" lines for r=4 and r=6; this is the expected output (the proof's rules need r>=34, and the run in mode `any` falls back to other times).
