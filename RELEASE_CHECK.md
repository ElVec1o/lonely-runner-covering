# Release check (Rule 11)

Assembled 2026-10-17, repaired and regenerated 2026-10-18. No git command that writes was run, nothing was uploaded or published, no Lean build was run.

## 1. Authorship fields

* `CITATION.cff`: author Vico Bonfioli, vicobonfioli@gmail.com; license CC-BY-4.0.
* `\author` of each manuscript: Vico Bonfioli (`grep -h "\\author" paper/*/*.tex`).
* No AI attribution lines (`Claude`, `Anthropic`, `Co-Authored-By`, `Generated with`) occur in any file other than this one, which quotes the patterns (section 2).
* Git commit author for a future repository push: `ElVec1o` (not applicable to this archive).

## 2. Pattern search over all files

Command: `grep -rIil -e PATTERN .` (case-insensitive, text files). Hits are counted per file.

| Pattern | Files with a hit | Assessment |
|---|---|---|
| `/Users/` | 0 | none |
| `private/` | 29 | intentional, hash-bearing: the string `private/eight/src/l7v4.rs` is written by `code/eight/generator/l7v4.rs` into the header of every generated certificate module, so it is part of the data hashed in `code/eight/records/P*/record.txt`; editing it would change all 27 hashes. The same string appears in the `generator:` line of the records. It names no file that the archive depends on. |
| `Claude` | 0 | none |
| `Anthropic` | 0 | none |
| `ChatGPT` | 0 | none |
| `GPT` | 0 | none |
| `TODO` | 5 | benign: Rust variable names `todo` in `code/dense/src/{v1,g1,xc,m94}`; no task markers |
| `HANDOFF` | 0 | none |
| `RESEARCH_LOG` | 0 | none |
| `api_key` | 0 | none |
| `token` | 0 | none |
| `secret` | 0 | none |
| `password` | 0 | none |
| `Co-Authored` | 0 | none |
| `Generated with` | 0 | none |

Files containing `private/`: 28 files under `code/eight/` (generator and records, hash-bearing, see above) and `lean/README.md`, where the string occurs in a sentence that describes the rewriting of comment paths; no file depends on a path under `private/`.

The word "programme" occurs in four Lean docstrings as ordinary English (research programme). The string `gmail` occurs in the author line of the manuscripts and in `README.md` and `CITATION.cff` (author address).

## 3. Confirmations

* Files whose development location is under `private/` (copied because the papers' programs and certificates live there, as instructed): `code/dense/src/**` and `code/dense/run_glp.sh` (from `private/dense/src`), `data/dense/certs/*` (from `private/dense/certs`), `data/dense/results.tsv` (from `private/dense/logs/batch/results.tsv`, a table of build seconds and axiom prints), `code/reduction/axioms/*` (from `private/paper_reduction`), `code/covering`, `code/perturbation` (from `code/tools`; 2026-10-18 additions: `paircls`, `clsweep`, `bad_triple_classify`, `bt_dbl_extend`, `identchk`, `tmpl63`, `g1_gap_criterion`, `r1_fourier_criterion`), `data/dense/dev_logs`, `data/dense/m94`, `code/dense/src/m94` (from `private/dense/logs`, `private/dense/src`, paths rewritten), `data/obstructions/seeds` and `census` (from `private/ROOM/FCU` and `private/ROOM/A4`; list files only), `paper/*` (from `private/release_bundle_2026_10/stage`, then edited in the bundle). No log, report, strategy, narration, draft or scratch file was copied, and `HANDOFF.md`, `RESEARCH_LOG.md`, `CLAUDE.md`, the memory files and the `.md` reports of `private/` are absent.
* No path under `private/` or `/Users/` is referenced by any file, with the single hash-bearing exception above.
* No binary executables, object files, `.lake`, `target/` or build directories; no hidden files.
* Comments in Lean modules were rewritten only where they named files outside the archive (`scrub`, see `lean/README.md`); definitions, statements and proofs are unchanged.

## 4. File list with justification

Every file is listed in `MANIFEST.tsv` with its SHA-256. One line per file:

| File | Justification |
|---|---|
| `CITATION.cff` | archive metadata (all) |
| `CLAIMS.tsv` | archive metadata (all) |
| `LICENSE.md` | archive metadata (all) |
| `README.md` | archive metadata (all) |
| `code/covering/README.md` | covering-paper program (lrc_covering) |
| `code/covering/alphaex.rs` | covering-paper program (lrc_covering) |
| `code/covering/bad_triple_classify.rs` | covering-paper program (lrc_covering) |
| `code/covering/bt_dbl_extend.rs` | covering-paper program (lrc_covering) |
| `code/covering/bt_membership.rs` | covering-paper program (lrc_covering) |
| `code/covering/clsweep.rs` | covering-paper program (lrc_covering) |
| `code/covering/famcheck.rs` | covering-paper program (lrc_covering) |
| `code/covering/famdec.rs` | covering-paper program (lrc_covering) |
| `code/covering/famdec2.rs` | covering-paper program (lrc_covering) |
| `code/covering/hitdec.rs` | covering-paper program (lrc_covering) |
| `code/covering/hitnum.rs` | covering-paper program (lrc_covering) |
| `code/covering/hitsweep.rs` | covering-paper program (lrc_covering) |
| `code/covering/identchk.rs` | covering-paper program (lrc_covering) |
| `code/covering/indcount.rs` | covering-paper program (lrc_covering) |
| `code/covering/k3m13dec.rs` | covering-paper program (lrc_covering) |
| `code/covering/kedecide.rs` | covering-paper program (lrc_covering) |
| `code/covering/paircls.rs` | covering-paper program (lrc_covering) |
| `code/covering/tmpl63.rs` | covering-paper program (lrc_covering) |
| `code/dense/ORIGINAL_SOURCE_SHA256.txt` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/README.md` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/build.sh` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/check_rows.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/regen_lean.sh` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/run_glp.sh` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/check.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/edges.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/gen.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/lp.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/cg/valid.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/fb/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/g1/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/lg/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/m94/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/dumpkept.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/emit.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/enum.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/mipkept.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/pool.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/rcfix.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/solve.py` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/tocnf.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/pool/xc_zero_rc.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/st89/main.rs` | dense-window tool or script (dense-window) |
| `code/dense/src/v1/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/xc/blocks.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/xc/common.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/xc/comp.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/xc/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/xc/search.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/dense/src/yind/main.rs` | dense-window tool or script (dense-window,lrc_covering) |
| `code/eight/README.md` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_card4/falsify.py` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_card4/relax.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_card4/tab.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/bad24.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/sec5.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/sec5b.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/sec5c.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/sec5d.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec5/sec5f.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/ctrl17.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/g4.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/gfals.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lean17.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lean18.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lean19.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lem56.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lem5prof.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/lem9path.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/sec6b.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/tab63.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/z63.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/z66.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/bs_sec6/z7extra.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/checks/e5/e5retry.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/generator/l7v4.rs` | eight-runner tool, script or checker (eight) |
| `code/eight/print_axioms.lean` | eight-runner tool, script or checker (eight) |
| `code/eight/records/P101/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P101/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P103/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P103/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P107/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P107/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P109/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P109/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P113/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P113/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P127/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P127/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P131/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P131/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P137/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P137/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P139/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P139/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P149/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P149/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P151/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P151/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P157/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P157/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P163/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P163/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P31/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P31/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P37/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P37/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P43/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P43/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P47/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P47/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P53/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P53/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P59/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P59/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P61/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P61/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P67/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P67/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P71/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P71/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P73/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P73/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P79/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P79/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P83/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P83/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P89/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P89/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P97/manifest.txt` | eight-runner per-prime record (eight) |
| `code/eight/records/P97/record.txt` | eight-runner per-prime record (eight) |
| `code/eight/stage/assemble_real.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/build_generator.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/compile1.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/env.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/real27_driver.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/repro_all.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/repro_check.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/run_campaign.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/run_prime.sh` | eight-runner tool, script or checker (eight) |
| `code/eight/stage/status.sh` | eight-runner tool, script or checker (eight) |
| `code/lean_build/gbound_build.sh` | sequential Lean build script (all papers with Lean content) |
| `code/obstructions/README.md` | obstruction reproduction (obstructions) |
| `code/obstructions/cornercheck.py` | obstructions tool or script (obstructions) |
| `code/obstructions/mlcheck.rs` | obstruction reproduction (obstructions) |
| `code/obstructions/repro_O4.sh` | obstruction reproduction (obstructions) |
| `code/obstructions/shift_grid.py` | obstruction reproduction (obstructions) |
| `code/perturbation/README.md` | perturbation program (perturbation) |
| `code/perturbation/g1_gap_criterion.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_adv.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_ceiling.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_cfire.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_classes.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_cover2.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_coverk.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_degen.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_div.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_divis.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_gw.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_isolated.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_loc2.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_locate.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_multipuncture.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_p7.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_p7lb.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_p8.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_p8b.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_ratio.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_regime.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_rigid.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_selfcheck.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_split.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_thm.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_tight.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_twopuncture.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_twosided.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_ucomp.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_uncond.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_widen.rs` | perturbation program (perturbation) |
| `code/perturbation/perturb_window.rs` | perturbation program (perturbation) |
| `code/perturbation/r1_fourier_criterion.rs` | perturbation program (perturbation) |
| `code/reduction/README.md` | reduction program (reduction,obstructions) |
| `code/reduction/axioms/ax.lean` | axiom print input/output (reduction) |
| `code/reduction/axioms/ax.out` | axiom print input/output (reduction) |
| `code/reduction/axioms/ax_t2sub.lean` | axiom print input/output (reduction) |
| `code/reduction/axioms/ax_t2sub.out` | axiom print input/output (reduction) |
| `code/reduction/ecalc/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/ecalc/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/ecalc/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/fcuspec/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/fcuspec/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/fcuspec/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/gdn/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/gdn/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/gdn/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/analyze.py` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/src/mdr_base.rs` | reduction program (reduction,obstructions) |
| `code/reduction/levelfit/top.py` | reduction program (reduction,obstructions) |
| `code/reduction/mdr/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/mdr/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/mdr/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/modchk/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/modchk/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/modchk/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/rmj/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/rmj/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/rmj/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/t2hunt/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/t2hunt/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/t2hunt/driver.sh` | reduction program (reduction,obstructions) |
| `code/reduction/t2hunt/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/t2sweep/Cargo.lock` | reduction program (reduction,obstructions) |
| `code/reduction/t2sweep/Cargo.toml` | reduction program (reduction,obstructions) |
| `code/reduction/t2sweep/src/main.rs` | reduction program (reduction,obstructions) |
| `code/reduction/t2sweep/uncovered.txt` | reduction program (reduction,obstructions) |
| `code/reproduce.sh` | reproduction entry point (all) |
| `data/dense/certs/m100.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m101.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m102.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m103.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m104.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m106.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m107.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m108.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m109.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m110.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m112.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m115.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m117.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m118.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m121.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m122.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m123.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m124.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m126.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m17.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m25.old.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m25.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m27.old.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m27.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m28.old.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m28.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m31.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m32.old.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m32.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m34.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m37.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m38.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m40.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m42.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m43.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m45.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m45.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m46.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m46.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m47.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m47.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m49.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m49.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m52.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m52.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m55.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m57.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m58.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m58.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m59.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m60.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m61.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.cg15.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.cheap.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.cheap2.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.rust.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m62.xc_t4.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m64.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m66.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m67.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m70.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m71.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m72.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m73.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m76.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m77.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m79.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m80.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m82.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m84.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m85.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m87.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m88.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m91.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m92.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m93.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/certs/m97.g1.sol` | dense-window certificate (dense-window,lrc_covering) |
| `data/dense/cg_edges_4_62.out` | dense-window result record (dense-window) |
| `data/dense/check_g1_certs.out` | dense-window result record (dense-window) |
| `data/dense/check_mask_certs.out` | dense-window result record (dense-window) |
| `data/dense/check_rows.out` | dense-window result record (dense-window) |
| `data/dense/dev_logs/mk57.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mk59.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mk60.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mk61.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mk62.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mkSA.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/mkSB.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run27.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run28.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run28_long.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run31.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run31_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run32_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run34_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run37_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run38_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run40_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run42_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run43_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run45_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run46_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run47_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run49_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run52_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run55_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run57_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run58_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/run59_drv.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/thmD_axioms.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/dev_logs/thmD_chain.out` | raw development log (build output, axiom prints, search drivers) (dense-window) |
| `data/dense/fb_check.out` | dense-window result record (dense-window) |
| `data/dense/fb_selftest.out` | dense-window result record (dense-window) |
| `data/dense/m94/drive_state.txt` | m=94 search log (UNDECIDED) (dense-window) |
| `data/dense/m94/final.txt` | m=94 search log (UNDECIDED) (dense-window) |
| `data/dense/m94/rounds.tsv` | m=94 search log (UNDECIDED) (dense-window) |
| `data/dense/regen_lean.out` | dense-window result record (dense-window) |
| `data/dense/results.tsv` | dense-window result record (dense-window) |
| `data/dense/st89_check.out` | dense-window data (dense-window) |
| `data/dense/yind_2_62.out` | dense-window result record (dense-window) |
| `data/dense/yind_control.out` | dense-window result record (dense-window) |
| `data/obstructions/census/adversarial_147.txt` | census or adversarial family list (obstructions) |
| `data/obstructions/census/resid_m12_h22.txt` | census or adversarial family list (obstructions) |
| `data/obstructions/census/resid_m12_h26_gt24.txt` | census or adversarial family list (obstructions) |
| `data/obstructions/census/resid_m14_h22.txt` | census or adversarial family list (obstructions) |
| `data/obstructions/cert_adversarial_147.out` | output of a rerun (obstructions) |
| `data/obstructions/cert_resid_m12_h22.out` | output of a rerun (obstructions) |
| `data/obstructions/cert_resid_m12_h26_gt24.out` | output of a rerun (obstructions) |
| `data/obstructions/cert_resid_m14_h22.out` | output of a rerun (obstructions) |
| `data/obstructions/chainparity.out` | obstructions data (obstructions) |
| `data/obstructions/cornercheck.out` | obstructions data (obstructions) |
| `data/obstructions/enumw_m10_h30.out` | output of a rerun (obstructions) |
| `data/obstructions/enumw_m12_h26.out` | output of a rerun (obstructions) |
| `data/obstructions/enumw_m14_h24.out` | output of a rerun (obstructions) |
| `data/obstructions/enumw_m6_h50.out` | output of a rerun (obstructions) |
| `data/obstructions/enumw_m8_h24.out` | output of a rerun (obstructions) |
| `data/obstructions/mlcheck_selftest.out` | output of a rerun (obstructions) |
| `data/obstructions/repro_O4.out` | output of a rerun (obstructions) |
| `data/obstructions/seeds/seed_m18.txt` | seed list of the exact-scan hunt (obstructions) |
| `data/obstructions/seeds/seed_m20.txt` | seed list of the exact-scan hunt (obstructions) |
| `data/obstructions/seeds/seed_m22.txt` | seed list of the exact-scan hunt (obstructions) |
| `data/obstructions/seeds/seed_m24.txt` | seed list of the exact-scan hunt (obstructions) |
| `data/repro_logs/alphaex_4_63.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/bad_triple_classify_4_260.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/bt_dbl_extend_150.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/bt_membership_2_300.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/clsweep_4_260.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/bad24.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/ctrl17.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/e5retry.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/g4.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/gfals.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lean17.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lean18.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lean19.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lem56.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lem5prof.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/lem9path.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/relax.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec5.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec5b.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec5c.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec5d.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec5f.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/sec6b.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/tab.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/tab63.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/z63.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/z66.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_checks/z7extra.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_e5retry.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_g4.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_repro_all_27.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/eight_repro_check_31_37_43_47.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/famcheck_4_250.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/famdec_4_56.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/fcuspec_eval.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/fcuspec_sweep_3_1500.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/fcuspec_sweep_4_500.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/fcuspec_sweep_5_200.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/fcuspec_sweep_6_110.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/g1_gap_criterion.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/hitdec_4_58_partial.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/identchk_4_90.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/indcount_4_24.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/k3m13dec.stdout.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_150.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_318.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_486.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_4_500.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_4_63.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_501_700.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_570.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/kedecide_701_900.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/mdr_ml_3_4_7_11_original_bug.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/obstructions_O4.out` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/paircls_4_32.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_cfire_2000_10.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_cover2_30.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_2_5_30.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_2_5_66_partial.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_2_67_76.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_2_77_100.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_3_17_22.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_3_7_16.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_coverk_3_7_23_partial.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_degen.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_divis.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_p7_6_70.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_ratio.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_selfcheck.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_selfcheck_2026_10_18.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_split_6_44_1.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_thm.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_twopuncture.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_window_exact.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/perturb_window_measexact.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/r1_fourier_criterion_40.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/t2sweep_cover.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/tmpl63_m10.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/tmpl63_m13.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/tmpl63_m16.txt` | output of a reproduction run made at assembly (all) |
| `data/repro_logs/tmpl63_m19.txt` | output of a reproduction run made at assembly (all) |
| `lean/LRSpectrumFull.lean` | Lean project file (dense-window,obstructions,perturbation,reduction,lrc_covering,eight) |
| `lean/LRSpectrumFull/BarajasSerra.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraCard4.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraCard4Table.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraCaseA.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraG.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraLRC6.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraLRC6BCD.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraLRC6M1.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraLRC6M1Table.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraLRC6Plan.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec5.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec5Fin.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6G4.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6L10.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6L9.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_1.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_2.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_3.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_3a.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_4.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_5.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraSec6_6.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/BarajasSerraZ7.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/Cascade.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/CaseA.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Chen7RunnerImport.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/Coherence.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Confinement.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/CoordConstruction.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/CoordSumBound.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/CoveringWitness.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/D3Classify.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/DSignFlip.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/DValue.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2Boundary.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2BridgeDisjunction.lean` | Lean module cited by reduction (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CaseRoute.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2Circle.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2Connect.lean` | Lean module cited by reduction (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CoverCapacity.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeA.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAA.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAB.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAC.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAD.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAE.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeAF.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeI.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeJ.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeK.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeL.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeM.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeN.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeO.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeP.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeQ.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeR.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS100.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS101.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS102.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS104.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS106.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS107.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS108.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS110.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS112.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS117.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS118.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS121.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS123.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS124.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS126.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS66.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS67.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS70.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS71.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS72.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS73.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS76.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS77.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS79.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS80.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS82.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS84.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS85.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS87.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS88.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS91.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS92.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeS93.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeSA.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeSB.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeT.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeU.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeV.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeW.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeX.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CoverRangeZ.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2CubeAllOdd.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeCert.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeDecouple.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeFull.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeLine.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubePair.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubePara.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeTriple.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2CubeWitness.lean` | Lean module cited by dense-window (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2DenseWindow.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2DigitGreedy.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2DisjointTriples.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2Example.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2FiveRunners.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/Delta2FracBlocking.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2FreeGrowth.lean` | Lean module cited by reduction (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2GrandReduction.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2GridBridge.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2MassCorrespond.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2PFLAssembly.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/Delta2PFLDigits.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/Delta2PFLMaster.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/Delta2Pigeonhole.lean` | Lean module cited by dense-window (dense-window) |
| `lean/LRSpectrumFull/Delta2RieszBound.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2RieszMass.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2Scaling.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2SeparationWindow.lean` | Lean module cited by reduction (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2WebAbsorb.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2WebRieszSharp.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Delta2WindowClosed.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/Delta2WindowK3.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/EightCert27.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightCheckSound.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightCheckV4.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightE5.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightMSS.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightMSSImport.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightPlan.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightRunners.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightRunnersFinal.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightRunnersReal.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EightZonotope.lean` | Lean module cited by eight (eight) |
| `lean/LRSpectrumFull/EvenlySpaced.lean` | Lean module (import dependency) (reduction,eight) |
| `lean/LRSpectrumFull/FarSet.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/GeneralLower.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzBandGe.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzCaseA.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzCovering.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzHookup.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzPieceA.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/KravitzStrict.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/LRCEightWLOG.lean` | Lean module (import dependency) (eight) |
| `lean/LRSpectrumFull/LRCFourRunnersCore.lean` | Lean module (import dependency) (eight) |
| `lean/LRSpectrumFull/Lemma5.lean` | Lean module (import dependency) (reduction,eight) |
| `lean/LRSpectrumFull/LonelyRunner3.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/MaxLoneliness.lean` | Lean module cited by dense-window,obstructions (dense-window,obstructions,reduction,eight) |
| `lean/LRSpectrumFull/MultiRunner.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/NearestIntCont.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/NearestIntLipschitz.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/NearestInteger.lean` | Lean module (import dependency) (dense-window,obstructions,reduction,eight) |
| `lean/LRSpectrumFull/NormalForm.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/NormalFormExists.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/OddRelation.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/OddRelationBound.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/PermInvariance.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Pigeonhole.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/RationalCert.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/RoomA4_barrier.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomA4_compress.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomA4_rosenfeld.lean` | Lean module cited by reduction (reduction,eight) |
| `lean/LRSpectrumFull/RoomEm.lean` | Lean module cited by obstructions (obstructions) |
| `lean/LRSpectrumFull/RoomFCU_compress.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_erdos.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_f5.lean` | Lean module cited by obstructions (obstructions) |
| `lean/LRSpectrumFull/RoomFCU_goddyn.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_hilbert.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_lemmaP.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_moderator.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_mss.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_ramanujan.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/RoomFCU_tao.lean` | Lean module (import dependency) (reduction) |
| `lean/LRSpectrumFull/RoomO6.lean` | Lean module cited by obstructions (obstructions) |
| `lean/LRSpectrumFull/RoomT2.lean` | Lean module cited by obstructions (obstructions) |
| `lean/LRSpectrumFull/Saturation.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Spectrum3.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Spectrum3Converse.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/SpectrumSymmetry.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/SquareWave.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Subtorus.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/SubtorusMono.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/Sweep.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/T2Sub.lean` | Lean module cited by reduction (reduction) |
| `lean/LRSpectrumFull/TripleNormalize.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/TwoRunnerBound.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/WeylNormalize.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/LRSpectrumFull/WitnessInt.lean` | Lean module (import dependency) (dense-window,reduction,eight) |
| `lean/README.md` | Lean project file (dense-window,obstructions,perturbation,reduction,lrc_covering,eight) |
| `lean/lake-manifest.json` | Lean project file (dense-window,obstructions,perturbation,reduction,lrc_covering,eight) |
| `lean/lakefile.toml` | Lean project file (dense-window,obstructions,perturbation,reduction,lrc_covering,eight) |
| `lean/lean-toolchain` | Lean project file (dense-window,obstructions,perturbation,reduction,lrc_covering,eight) |
| `paper/dense-window/LEAN_MAP.md` | Lean map (label to declaration) |
| `paper/dense-window/main.pdf` | manuscript PDF |
| `paper/dense-window/main.tex` | manuscript source |
| `paper/dense-window/refs.bib` | bibliography |
| `paper/dense-window/rows.tex` | manuscript source |
| `paper/dense-window/rows_ext.tex` | manuscript source |
| `paper/eight/LEAN_MAP.md` | Lean map (label to declaration) |
| `paper/eight/main.pdf` | manuscript PDF |
| `paper/eight/main.tex` | manuscript source |
| `paper/eight/refs.bib` | bibliography |
| `paper/lrc_covering/lrc_covering.pdf` | manuscript PDF |
| `paper/lrc_covering/lrc_covering.tex` | manuscript source |
| `paper/obstructions/LEAN_MAP.md` | Lean map (label to declaration) |
| `paper/obstructions/main.pdf` | manuscript PDF |
| `paper/obstructions/main.tex` | manuscript source |
| `paper/obstructions/refs.bib` | bibliography |
| `paper/perturbation/perturbation.pdf` | manuscript PDF |
| `paper/perturbation/perturbation.tex` | manuscript source |
| `paper/reduction/LEAN_MAP.md` | Lean map (label to declaration) |
| `paper/reduction/main.pdf` | manuscript PDF |
| `paper/reduction/main.tex` | manuscript source |
| `paper/reduction/refs.bib` | bibliography |
| `MANIFEST.tsv` | file list with hashes (not self-hashed) |
| `RELEASE_CHECK.md` | this file (not hashed in the manifest) |

## Final scan before publication (18 October 2026)

* 687 files in the tree (`MANIFEST.tsv` hashes all except itself). Pattern scan for `/Users/`, the author's work address, `Claude`, `Anthropic`, `ChatGPT`, `HANDOFF`, token and key patterns, `Co-Authored`, `Generated with`: 0 hits outside this file.
* No `.DS_Store`, no LaTeX build files, no file above 5 MB.
* Commit author for the publication commit: ElVec1o <vicobonfioli@gmail.com>.


## Scan for version 1.0.1 (draft, 18 October 2026)

* 692 files in the tree (`MANIFEST.tsv` hashes all except itself and this file: 690 rows). Added: `code/dense/src/st89/main.rs`, `code/obstructions/cornercheck.py`, `data/dense/st89_check.out`, `data/obstructions/cornercheck.out`, `data/obstructions/chainparity.out`. Changed: `README.md`, `CLAIMS.tsv`, `MANIFEST.tsv`, this file, `code/reproduce.sh`, `code/dense/build.sh`, `code/dense/README.md`, `code/obstructions/README.md`, `paper/dense-window/{main.tex,main.pdf,LEAN_MAP.md}`, `paper/obstructions/{main.tex,main.pdf,LEAN_MAP.md}`. No Lean file changed.
* Pattern scan (`grep -rIil`, this file excluded) for `/Users/`, `Claude`, `Anthropic`, `ChatGPT`, `GPT`, `HANDOFF`, `RESEARCH_LOG`, `api_key`, `token`, `secret`, `password`, `Co-Authored`, `Generated with`, `anvilstack`, `sk-` keys, `ghp_`, `AKIA` keys: 0 hits. `TODO`: 5 (Rust variables, unchanged); `private/`: 29 (unchanged, hash-bearing, see section 2).
* The two rebuilt manuscripts compile with latexmk without undefined references or citations; build files deleted afterwards (`paper/obstructions/main.bbl` is kept, as in 1.0.0).
* No `.DS_Store`, no LaTeX build files, no file above 5 MB. Sync coupling table walked for every changed statement: README results and formalization sections, `CLAIMS.tsv`, both `LEAN_MAP.md`, file map and reproduction rows updated.
* Not done: no Lean build; (the fresh-session review of the new PROVED statements was done afterwards, see the next section); Zenodo DOI lines of 1.0.0 kept in `README.md` and `CITATION.cff`; `CITATION.cff` and `.zenodo.json` still say version 1.0.0 and must be updated at release.
* Identity: the last commit is by ElVec1o <vicobonfioli@gmail.com>; the repository's local `git config` says `elvec1o <elvec1o@users.noreply.github.com>`, which must be set to the Rule 11 identity before the next commit.

## Scan after the review fixes (18 October 2026)

* Fixes D1, D2, D3, N1, N2 and the Proposition 14 wording items K1 to K3 of `REVIEW_V101` applied to `paper/dense-window/main.tex` and `paper/obstructions/main.tex`; `CLAIMS.tsv` (rows 23, 24, 33, 39, 40, 133), `README.md` (Propositions 5, 6 and 7) and `paper/obstructions/LEAN_MAP.md` (missing divisor, Proposition 7) updated. No mathematical claim changed; the label of the missing-divisor bound is split into the weak form (VERIFIED, carried over, as stated in the Lean signature) and the strict form (PROVED, one line). No Lean file changed, no Lean build run.
* Both manuscripts compile with latexmk, no undefined references or citations; build files (`aux`, `log`, `out`, `fls`, `fdb_latexmk`, `blg`, `toc`) deleted afterwards; `paper/obstructions/main.bbl` kept, no `main.bbl` in `paper/dense-window`.
* Pattern scan (`grep -rIil`, `.git`, `MANIFEST.tsv` and this file excluded) for `/Users/`, `anvilstack`, `Claude`, `Anthropic`, `ChatGPT`, `HANDOFF`, `Co-Authored`, `Generated with`, `ghp_`, `gho_`, `github_pat`: 0 hits for every pattern.
* 692 files in the tree; `MANIFEST.tsv` hashes all except itself (691 rows), each file once, regenerated after the last edit of this file.
