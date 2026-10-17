# code/eight: reproduction material for paper/eight/main.tex

Lean statements and axioms are listed in `paper/eight/LEAN_MAP.md`. Everything here uses only the
Rust standard library (no crates) and `bash`. Paths are relative to this repository.

## Layout

| Path | Content |
|---|---|
| `print_axioms.lean` | `#print axioms` of the main theorem and its components |
| `generator/l7v4.rs` | certificate generator for `lemma7Check 7 p` (checker `lean/LRSpectrumFull/EightCheckV4.lean`) |
| `records/P<p>/record.txt` | per-prime record: generator command, SHA-256 of generator, checker, soundness file, each generated module and their concatenation; axiom output of the kernel proof; timings |
| `records/P<p>/manifest.txt` | generator statistics for that prime |
| `stage/` | scripts: `build_generator.sh`, `repro_check.sh`, `repro_all.sh`, `run_prime.sh`, `compile1.sh`, `run_campaign.sh`, `status.sh`, `env.sh` |
| `checks/` | exact-integer falsification checkers cited in the paper and in `errata_barajas_serra.md` |

The records were written on 2026-09-24/26, when these files lived in an unpublished directory;
their `generator:` lines name that path. `generator/l7v4.rs` is the file with SHA-256
`f467166f...a61a1` named by 24 records. The records for p = 31, 37, 43 name an earlier revision
(`18f58606...c7f17`); the present generator reproduces their source hashes. The generator writes its
own former path into the header comment of each generated module, which is why that string is
unchanged: editing it would change every hash.

## Axioms of the main theorem

```
cd lean && lake env lean ../code/eight/print_axioms.lean
```

Expected for `EightRunners.eight_runners_unconditional`: `propext`, `Classical.choice`,
`Quot.sound` and the 27 axioms `EightCert27.lemma7Check_seven_p<p>_verified`.

## The 27 certificates

```
bash code/eight/stage/build_generator.sh      # rustc -O, a few seconds
bash code/eight/stage/repro_all.sh            # hash check, no Lean; 10 to 15 min for all 27
bash code/eight/stage/repro_check.sh 163      # one prime
```

Each line reads `P<p> REPRODUCED <sha256>`; the hash must equal `combined_sha256` in the record
and the hash in the docstring of the corresponding axiom in `EightCert27.lean`. Result on
2026-09-27: 27/27 REPRODUCED.

Full kernel re-check of one prime (needs the built `lean` dependencies of
`EightCheckSound`; staging goes to `stage/work/`, at most 2 `lean` processes machine-wide,
each near 1 GB; refuses below 1.6 GB free disk; resumable; `touch stage/work/STOP` stops it):

```
bash code/eight/stage/run_prime.sh 31
bash code/eight/stage/status.sh
bash code/eight/stage/run_campaign.sh        # all 27, several hours
```

Success writes `stage/work/records/P<p>/record.txt`, whose `combined_sha256` must match the
committed record and whose axiom line must read
`'LRSpectrumFull.EightV4.Cert<p>.lemma7Check_seven_p<p>' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Checkers

Build each with `rustc -O --edition 2021 -o /some/dir/<name> code/eight/checks/<dir>/<name>.rs`
and run it without arguments (`sec6b`, `lean18`, `lean19` accept an optional subset name; the
default runs everything). Each finished in under 20 s on the machine used (2026-09-27).
Negative controls (`NC`) are expected to report failures.

| File | Checks | Output on 2026-09-27 (last lines) |
|---|---|---|
| `bs_card4/relax.rs`, `tab.rs` | n = 4 finite model: good-multiplier masks | `distinct 80 minimal 80` |
| `bs_card4/falsify.py` | Lemma 2 / Cor. 3, n = 2, 4 cases (Python, 8 s) | 0 failures; NC fails as expected |
| `bs_sec5/sec5.rs` | Section 5: F1, F2, F3 arc claims, Z-lemmas; claim (12) from eq. (9) | `F3 (2,len2): 28 / 12544 fail` (the erratum) |
| `bs_sec5/sec5c.rs` | Section 5, claim (12) itself | `m=2: 7056 ... 0 violate`, `m=3: 351918 ... 0 violate` |
| `bs_sec5/sec5f.rs`, `sec5d.rs`, `sec5b.rs`, `bad24.rs` | Farey carry model and the Lean `decide` tables | `sec5d`: Z1-Z3 0 failures, dispatch 0 uncovered of 81 |
| `bs_sec6/lem56.rs`, `lem5prof.rs` | Lemmas 5, 6, 12 over Z7 | Lemma 5: 56 failures outside the stated exception (erratum 2) |
| `bs_sec6/lean17.rs` (`ctrl17.rs` = negative control) | Lemma 4 (corrected), Lemma 7 | all `fail=0`; `ctrl17` reports failures |
| `bs_sec6/lean18.rs` | Lemmas 10, 11; 6.1, 6.2, 6.4 | all `fail=0`, NCs fail |
| `bs_sec6/lean19.rs`, `tab63.rs`, `z63.rs`, `z66.rs` | 6.3, 6.5, 6.6 | all `fail=0`, NCs fail |
| `bs_sec6/sec6b.rs`, `z7extra.rs`, `lem9path.rs`, `gfals.rs` | 6.3 table, 6.5, 6.6(b), Remark 8, Lemma 9 path, G1/G2 | printed formula of 6.6(b) wrong on 302526 configurations (erratum); the rest 0 |
| `bs_sec6/g4.rs` | reduction to the seven patterns of Section 6 | `FULL: 7776 tuples, 0 failures` |
| `e5/e5retry.rs` | Proposition 4.2 (rounding step), exact rationals, 200000 random instances | `tests=200000 fails=0` |

`falsify.py` is run with `python3 -u code/eight/checks/bs_card4/falsify.py`.

## Removing the 27 axioms (real-proof variant, added 2026-09-30)

The default build carries the 27 compacted axioms `EightCert27.lemma7Check_seven_p<p>_verified`.
`lean/LRSpectrumFull/EightRunnersReal.lean` proves the same theorem with the 27 facts as real kernel
theorems. It is outside the lake build. Steps:

1. `bash code/eight/stage/build_generator.sh` (once).
2. `nohup bash -c 'set -m; nohup <abs>/code/eight/stage/real27_driver.sh >><abs>/build/logs/real27.out 2>&1 </dev/null & disown' >/dev/null 2>&1 </dev/null & disown`
   The driver runs `run_prime.sh` with `KEEP=1` for the 27 primes in increasing order: about 12 h wall,
   about 2.6 GB of kept oleans in `code/eight/stage/work/olean/E8Stage/`, at most 2 lean processes,
   resumable (rerun it), waits while free disk is under 2100 MB, stops when `code/eight/stage/work/HALT` exists.
   Progress: `build/logs/real27.log` (line `ALL27 KEPT` at the end).
3. `bash code/eight/stage/assemble_real.sh` compiles `EightRunnersReal.lean` against those oleans
   (raw `lean`, about 40 s, 7 GB peak RSS) and prints `#print axioms` for
   `eight_runners_unconditional_real` and `hchk_all_real`. Expected: `ASSEMBLY OK`, both
   `[propext, Classical.choice, Quot.sound]`. It refuses when 2 or more lean processes run.

Result on 2026-09-30: `ASSEMBLY OK`. Control: `EightRunners.eight_runners_unconditional` in the same
environment lists the 27 `EightCert27` axioms.
