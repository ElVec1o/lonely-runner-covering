# code/dense

Tools for the cover-capacity certificates of `paper/dense-window/main.tex`. Rust (edition 2021, standard library
only) except `src/cg/lp.py` (master LP of the column generation, Python with HiGHS) and `src/pool/*.py`.

| Directory | Role |
|---|---|
| `src/v1` | independent verifier of a certificate (`v1 check M FILE [mask\|list]`); no code shared with the searches |
| `src/g1` | local search plus `glpsol`/`kissat` calls; writes `certs/mM.g1.sol` (needs `glpsol`, `kissat` on the path) |
| `src/lg` | emits the Lean module from a certificate (`lg2 gen2 M FILE S<M> OUT`) |
| `src/cg` | column generation with a HiGHS master LP (Python), used for some rows with m <= 62 |
| `src/xc` | block family, reduction of blocks, MIP model for `glpsol` (`run_glp.sh`), exact search |
| `src/pool` | the early pool-based pipeline (rows m = 10..28) |
| `src/fb` | exact checker for the fractional blocking certificates of Table 1 (m = 4, 7, 12, 13); reads them from `lean/LRSpectrumFull/Delta2FracBlocking.lean`; `fb check FILE`, `fb selftest FILE` |
| `src/yind` | independent exact enumeration of all bad sets; checks that Y = {m+2,...,2m} contains no bad set (Proposition on Y), `yind M1 M2`, `yind control M` |
| `src/m94` | the driver of the three-hour search at m = 94 (ended UNDECIDED); log in `data/dense/m94`; not re-run |

Scripts: `build.sh` (builds `v1`, `g1`, `lg2`, `cg`, `xc`, `fb`, `yind`, `m94`), `check_rows.py` (regenerates parts/max/times of all
rows from the Lean modules in `lean/` and has `v1` accept each certificate), `regen_lean.sh` (regenerates the
Lean modules for m >= 64 from `data/dense/certs/mM.g1.sol` and compares them with the shipped modules),
`run_glp.sh`.

The tools were developed with an absolute path constant `DIR` for their working directory. In this archive the
constant is `"."` (and the Python helper path of `cg` is `../../code/dense/src/cg/lp.py`), so `g1`, `cg`, `xc` are
to be run from `data/dense`, which holds `certs/`. Strings naming development files in comments and in the headers
of generated Lean modules were rewritten to archive paths. `ORIGINAL_SOURCE_SHA256.txt` lists the hashes of the
sources before these edits, including `m94/main.rs` (added 2026-10-18; its constant `DIR` and one comment path were changed); no other change was made. `src/fb` and `src/yind` are new programs written for this archive and have no original.

Certificate formats: `mM.g1.sol` is one part per line, `CAP e1 e2 ...` (list form); `mM.sol` is `MASK CAP` with
the part as a bitmask over 1..2m (mask form). Certificates for 97, 103, 109, 115, 122 are accepted by `v1`; no Lean
module has been built for them (see the paper, Section "What is not claimed").

Outputs of the checks made when the archive was assembled, in `data/dense/`: `check_rows.out` (63 table rows),
`regen_lean.out` (34 regenerated modules), `check_g1_certs.out` (40 list-form certificates, all ACCEPT),
`check_mask_certs.out` (39 mask-form certificates including the alternative `.old.sol` and `.rust.sol` variants,
all ACCEPT). Acceptance by `v1` is a COMPUTED statement; only the certificates that are embedded in the Lean
modules listed in the paper are VERIFIED.
