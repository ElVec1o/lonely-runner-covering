# Release check (Rule 11)

Assembled 2026-10-17, repaired and regenerated 2026-10-18; version 1.1.0 staged 2026-11-09 (section at the end). No git command that writes was run, nothing was uploaded or published, no Lean build was run.

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
| `code/dense/src/thmd/case_recount.rs` | dense-window tool or script (dense-window) |
| `code/dense/src/thmd/class_check.rs` | dense-window tool or script (dense-window) |
| `code/dense/src/thmd/cross_check.py` | dense-window tool or script (dense-window) |
| `code/dense/src/thmd/dense_check.rs` | dense-window tool or script (dense-window) |
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
| `code/goddyn-wong-loo/README.md` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/chkC.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/chkL.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/enum_coprime_case.py` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/example_check.py` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/fixchk/dus.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/fixchk/fixchk.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/fixchk/win.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/loo_tables.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/mlcore.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/review/drv.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/goddyn-wong-loo/review/wit.rs` | leave-one-out note program or script (goddyn-wong-loo) |
| `code/lean_build/gbound_build.sh` | sequential Lean build script (all papers with Lean content) |
| `code/obstructions/README.md` | obstruction reproduction (obstructions) |
| `code/obstructions/cornercheck.py` | obstructions tool or script (obstructions) |
| `code/obstructions/descent_check.py` | exact checks for Section 8 of the obstruction note (obstructions) |
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
| `data/dense/thmd/case_recount.out` | dense-window data (dense-window) |
| `data/dense/thmd/class_check.out` | dense-window data (dense-window) |
| `data/dense/thmd/cross_check.out` | dense-window data (dense-window) |
| `data/dense/thmd/steps.out` | dense-window data (dense-window) |
| `data/dense/thmd/window_2m.out` | dense-window data (dense-window) |
| `data/dense/thmd/window_higher.out` | dense-window data (dense-window) |
| `data/dense/yind_2_62.out` | dense-window result record (dense-window) |
| `data/dense/yind_control.out` | dense-window result record (dense-window) |
| `data/goddyn-wong-loo/README.md` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/chkC_33_260.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/chkL_31_140.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/classc_review_33_300.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/coprime_case_triples.out` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/dusart_sanity.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/example_check.out` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/example_n8.out` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/loo_gw160.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/primes_check.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/review_wit.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/thmA_small.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/vec_74_70_2.out` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/window_c_n33.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/witA_34_160.log` | leave-one-out note program output (goddyn-wong-loo) |
| `data/goddyn-wong-loo/witA_4_32.log` | leave-one-out note program output (goddyn-wong-loo) |
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
| `data/obstructions/descent_controls.out` | output of a run: control battery of the exact ML routine (obstructions) |
| `data/obstructions/descent_d0.out` | output of a run: Lemma 20 on random vectors (obstructions) |
| `data/obstructions/descent_gw.out` | output of a run: Goddyn-Wong triples from the GCD condition (obstructions) |
| `data/obstructions/descent_gw_loo.tsv` | input table: leave-one-out values of the 67 Goddyn-Wong type tight vectors (generator not archived) (obstructions) |
| `data/obstructions/descent_instances.out` | output of a run: exact instances and near-tight sets (obstructions) |
| `data/obstructions/descent_strict.out` | output of a run: strict values of m (obstructions) |
| `data/obstructions/descent_table.out` | output of a run: the 70 tight vectors (obstructions) |
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
| `paper/goddyn-wong-loo/LEAN_MAP.md` | leave-one-out note, manuscript file (goddyn-wong-loo) |
| `paper/goddyn-wong-loo/main.bbl` | leave-one-out note, manuscript file (goddyn-wong-loo) |
| `paper/goddyn-wong-loo/main.pdf` | leave-one-out note, manuscript file (goddyn-wong-loo) |
| `paper/goddyn-wong-loo/main.tex` | leave-one-out note, manuscript file (goddyn-wong-loo) |
| `paper/goddyn-wong-loo/refs.bib` | leave-one-out note, manuscript file (goddyn-wong-loo) |
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

## Scan for version 1.0.2 (draft, unreleased, 18 October 2026)

* 702 files in the tree excluding `.DS_Store` (ignored by `.gitignore`, not tracked); `MANIFEST.tsv` hashes all except itself (701 rows), each file once, regenerated after the last edit of this file. Added: `code/dense/src/thmd/{dense_check.rs,cross_check.py,class_check.rs,case_recount.rs}`, `data/dense/thmd/{window_2m,window_higher,steps,cross_check,class_check,case_recount}.out`. Changed: `README.md`, `CLAIMS.tsv`, `MANIFEST.tsv`, this file, `code/dense/README.md`, `paper/dense-window/{main.tex,main.pdf,refs.bib,LEAN_MAP.md}`. No Lean file changed, no Lean build run, nothing committed or pushed.
* Sync coupling walked for the changed Theorem 3 material: README (version line, changes, results, file map, reproduction row, Lean table), `CLAIMS.tsv` (rows for Lemmas 1 to 4, Theorem 3, the new checks), `LEAN_MAP.md` (module names corrected, status carried over, not rebuilt), `code/dense/README.md`, section 4 of this file. Numbers of all later items of the dense-window paper (Proposition 4, Theorem 5, Statements 6 to 9, Theorem 10, Remark 11, Tables 1 to 3) are unchanged.
* The dense-window manuscript compiles with latexmk, no undefined references or citations; build files (`aux`, `log`, `out`, `fls`, `fdb_latexmk`, `blg`, `toc`, `bbl`) deleted afterwards.
* Pattern scan (`grep -rIil`, `.git`, `MANIFEST.tsv` and this file excluded) for `/Users/`, `anvilstack`, `Claude`, `Anthropic`, `ChatGPT`, `HANDOFF`, `Co-Authored`, `Generated with`, `ghp_`, `gho_`, `github_pat`: 0 hits for every pattern. No file above 5 MB; no LaTeX build files.
* Open before release: `.zenodo.json` says version 1.0.1 and must be set to 1.0.2; `CITATION.cff` has no version field and `date-released: 2026-10-18` must be updated; no DOI exists for 1.0.2; the README version line says draft, unreleased and must be changed at release; the repository identity must be ElVec1o <vicobonfioli@gmail.com> before the commit; no Lean rebuild or axiom print was made for `dense_floor_of_prime`, and the fresh-session reader test of the conceptual abstract of Theorem 3 has not been run.

## Scan for version 1.0.3 (draft, unreleased, 18 October 2026)

* 710 files in the tree excluding `.DS_Store`; `MANIFEST.tsv` hashes all except itself (709 rows), each file once, regenerated after the last edit of this file. Added: `code/obstructions/descent_check.py`, `data/obstructions/descent_{controls,d0,gw,instances,strict,table}.out`, `data/obstructions/descent_gw_loo.tsv`. Changed: `README.md`, `CLAIMS.tsv`, `MANIFEST.tsv`, this file, `code/reproduce.sh`, `code/obstructions/README.md`, `paper/obstructions/{main.tex,main.pdf,main.bbl,LEAN_MAP.md}`. Present from the exact-`ML` audit and kept: regression tests in `code/reduction/mdr/src/main.rs` and `code/reduction/levelfit/src/mdr_base.rs`, one row of `paper/reduction/LEAN_MAP.md`. No Lean file changed, no Lean build run, `cargo test` not run, nothing committed or pushed. `refs.bib` unchanged.
* Sync coupling walked for the new statements (items 20 to 33 of the obstruction note): README (version line, changes, idea in words, results, file map, reproduction row and runtime, formalization rows, data provenance), `CLAIMS.tsv` (13 rows), `paper/obstructions/LEAN_MAP.md` (all new items: ABSENT), `code/obstructions/README.md`, `code/reproduce.sh` (six commands added, runtime line 40 to 43 minutes), section 4 of this file. Items 1 to 19 of the note and their numbers are unchanged.
* The obstruction note compiles with latexmk, no undefined references or citations; build files (`aux`, `log`, `out`, `fls`, `fdb_latexmk`, `blg`, `toc`) deleted afterwards; `main.bbl` kept as before.
* Pattern scan (`grep -rIil`, `.git`, `MANIFEST.tsv` and this file excluded) for `/Users/`, `anvilstack`, `Claude`, `Anthropic`, `ChatGPT`, `HANDOFF`, `Co-Authored`, `Generated with`, `ghp_`, `gho_`, `github_pat`: 0 hits for every pattern; the text of `main.pdf` has 0 hits for `Claude`, `Anthropic`, `/Users/`, `anvilstack`. No file above 5 MB; no LaTeX build files; no `.DS_Store` in the tree.
* Checks run for this version (Python, exact, one process each, all under 2 minutes; outputs in `data/obstructions/descent_*.out`): control battery PASS; Lemma 20 on 1500 random vectors, 0 failures; instances and near-tight sets; 66 Goddyn-Wong triples regenerated with a negative control; 70-vector table (21 rows recomputed, 49 from the table); strict values (m <= 151 recomputed in part). The table `descent_gw_loo.tsv` comes from an exact job whose source is not archived.
* Open before release: `.zenodo.json` says version 1.0.2 and must be set to 1.0.3; `CITATION.cff` carries `version: 1.0.2`, the DOI of 1.0.2 and `date-released: 2026-10-18` and must be updated; no DOI exists for 1.0.3 and none is stated; the README version line says draft, unreleased; the repository identity must be ElVec1o <vicobonfioli@gmail.com> before the commit; the proofs of Propositions 29 and 31 were reviewed in REVIEW_SEC8.md (accepted with fixes) and the fixes were applied afterwards by the author, whose check of the changed text is the only one so far (Corollary 30 and Proposition 31 now have lifting proofs, Remark 33 is new); the generator of `descent_gw_loo.tsv` is not archived.

## Scan for version 1.0.4 (draft, unreleased, 31 October 2026)

* Tree: 743 files excluding `.git` (no `.DS_Store`); `MANIFEST.tsv` hashes all except itself (742 rows), each file once, regenerated after the last edit of this file. Added (33 files): `paper/goddyn-wong-loo/{main.tex,main.pdf,main.bbl,refs.bib,LEAN_MAP.md}`, `code/goddyn-wong-loo/` (README, `mlcore.rs`, `loo_tables.rs`, `chkL.rs`, `chkC.rs`, `example_check.py`, `enum_coprime_case.py`, `fixchk/{fixchk,dus,win}.rs`, `review/{drv,wit}.rs`), `data/goddyn-wong-loo/` (README and 15 outputs). Changed: `README.md`, `CLAIMS.tsv` (17 rows), `CITATION.cff`, `.zenodo.json`, `MANIFEST.tsv`, this file. No Lean file changed, no Lean build run, other manuscripts unchanged, nothing committed, pushed or uploaded.
* Authorship fields: `CITATION.cff` version 1.0.4, `date-released: 2026-10-31`; the field `doi` temporarily carries the concept DOI and the identifier list has no entry for 1.0.4 (no DOI exists yet); `.zenodo.json` version 1.0.4, publication date 2026-10-31.
* AI attribution: the new manuscript contains one provenance paragraph naming the AI system (`Claude`, `Anthropic`), in `main.tex` and `main.pdf`, marked in the source by the comment `% H6: pending author approval`; the wording has no clause on what the author checked. This is the only file besides this one with those two words. The README and metadata contain no such statement yet.
* Pattern scan (`grep -rIil`, `.git` excluded, this file included for the count) for `/Users/`, `private/`, `Claude`, `Anthropic`, `ChatGPT`, `GPT`, `TODO`, `HANDOFF`, `RESEARCH_LOG`, `api_key`, `token`, `secret`, `password`, `Co-Authored`, `Generated with`, `sonnet`, `fable`, `anvilstack`, `ghp_`, `gho_`, `github_pat`, and the internal labels `Zoom map`, `RESOLVED-TRUE`, `GWLOO`, `Class C`, `Theorem U`, `Lemma D`, `W5`, `ML_AUDIT`: identical hit lists to version 1.0.3 for every pattern, except `Claude` and `Anthropic` (the new manuscript, expected, see above). The text of `paper/goddyn-wong-loo/main.pdf` has 1 hit each for `Claude` and `Anthropic` and 0 for `/Users/`, `private`, `anvilstack`, `gmail`, the internal labels. Hits found during the scan and fixed: internal lemma labels in comments and printed strings of `fixchk.rs`, `chkL.rs`, `chkC.rs`, `review/wit.rs` (renamed; comments and labels only, the arithmetic is unchanged; `witA_34_160.log` reproduced byte for byte after the rename) and a log file name containing an internal label.
* The new manuscript compiles with latexmk (rc 0, no undefined references or citations, 11 pages); build files deleted afterwards; `main.bbl` kept as in 1.0.0. No file above 5 MB.
* Checks run for this version (Rust `-O`, standard library only, all under 1 minute each): `loo_tables selftest` PASS; `thmA` 240 vectors, 0 mismatches; `triples 160` 38 triples, FAILS 0 (log identical to the earlier one); `drv 33 300 12`, three triples and two controls as stated in the note; `chkL`, `chkC`, `review/wit` 0 failures; prime-window and Dusart sieves; `example_check.py` OK; `enum_coprime_case.py 1100` 13 triples.
* Open before release: user approval of the provenance paragraph (and the README and Zenodo texts); commit identity ElVec1o; the DOI of 1.0.4 after deposit; no human reading of the new note yet (the reader gate of Part H is not run); the proofs were checked by AI sessions only; Dusart and Goddyn-Wong statements are quoted, not re-proved; the unified witness lemma was not reviewed again as a unit; ten of the thirteen triples of the coprime case have no recomputed values.

### Files added in version 1.1.0 (24)

`lean/LRSpectrumFull/Delta2PinnedCover.lean`, `Delta2CoverRangeS94.lean`, `Delta2CoverRangeS94s416A.lean`, `...B.lean`, `...C.lean`, `Delta2CoverRangeS97.lean`, `S103.lean`, `S109.lean`, `S115.lean`, `S122.lean` (Lean modules cited by dense-window); `code/dense/src/gen94/main.rs` (generator of the three leaf modules of the case m = 94); `code/dense/src/examples/ex.rs` (numbers of the worked examples); `data/dense/m94_lean/{certs/leafA_state416.cert, certs/leaf_s416B67.cert, certs/leaf_s416C67.cert, ax_S94.out, axioms_fresh_review.out, regen_check.out}`; `data/dense/results_L16.tsv`; `data/dense/examples.out`; `data/eight/recheck_2026_11_01/{README.md, assemble_real_2026_11_01.log, chk_parsed.txt, lean_Ctl2.log}`.

## Scan for version 1.1.0 (draft, 9 November 2026)

* Tree: 767 files excluding `.git` (no `.DS_Store`: one stray file of 18 October at the root, ignored by `.gitignore`, was deleted; no LaTeX build files; no file above 5 MB; 20 MB in total). `MANIFEST.tsv` hashes all files except itself (766 rows), regenerated after the last edit of this file. Added: 24 files (list above). Changed: `README.md`, `CITATION.cff`, `.zenodo.json`, `CLAIMS.tsv`, `RELEASE_CHECK.md`, `MANIFEST.tsv`, `lean/README.md`, `lean/LRSpectrumFull.lean` (seven imports added), `code/dense/build.sh` (builds `gen94`), `code/dense/check_rows.py` (exception list `{94}`), `code/eight/README.md`, `paper/dense-window/{main.tex, main.pdf, rows.tex, rows_ext.tex, refs.bib, LEAN_MAP.md}`, `paper/eight/{main.tex, main.pdf, LEAN_MAP.md}`, `data/dense/{results.tsv, check_rows.out, regen_lean.out}`. Other manuscripts unchanged. Nothing committed, pushed, tagged or uploaded.
* Authorship fields: `CITATION.cff` version 1.1.0, `date-released: 2026-11-09`; the version DOI of 1.1.0 does not exist yet: the field `doi` carries the concept DOI (as in the draft of 1.0.4) and a comment says so; the identifier list has no entry for 1.1.0; to be recorded in a follow-up commit after deposit. `.zenodo.json` version 1.1.0, publication date 2026-11-09, description regenerated from the manuscripts as they stand (with the paragraph on what is not claimed). The metadata were not copied from the previous text.
* AI attribution: the wording of the provenance paragraph of 1.0.4 (`paper/goddyn-wong-loo/main.tex`, Section 1) was reused and adapted in `paper/dense-window/main.tex` (Section 1, paragraph Provenance), `paper/eight/main.tex` (Section 7), `README.md` (section Provenance) and `.zenodo.json`. The adapted wording (it lists the Lean sources and programs as produced by the AI system and says that further sessions of the same system read the arguments and statements) needs the author's approval. `Claude` and `Anthropic` now occur in five files besides this one (`.zenodo.json`, `README.md`, `paper/dense-window/main.tex`, `paper/eight/main.tex`, and `paper/goddyn-wong-loo/main.tex` of 1.0.4).
* Pattern scan (`grep -rIil`, `.git` excluded, this file excluded) for `/Users/`, `private/`, `Claude`, `Anthropic`, `ChatGPT`, `GPT`, `TODO`, `HANDOFF`, `RESEARCH_LOG`, `api_key`, `token`, `secret`, `password`, `Co-Authored`, `Generated with`, `sonnet`, `fable`, `anvilstack`, `ghp_`, `gho_`, `github_pat`, `Zoom map`, `RESOLVED-TRUE`, `GWLOO`, `Class C`, `Theorem U`, `Lemma D`, `W5`, `ML_AUDIT`: hit lists identical to version 1.0.4 for every pattern, except `Claude` and `Anthropic` (four new files, expected, see above), and `Zoom map` and `RESOLVED-TRUE` (2 files each instead of 3: a text in the dense-window manuscript was replaced). `/Users/` has 0 hits: the results file `data/dense/results_L16.tsv` had one local path per line, rewritten to `<dev-tree>`; the Lean docstrings and `gen94/main.rs` had `private/` paths, rewritten to archive paths.
* Lean sources: for the 206 modules of `lean/LRSpectrumFull/` a comment-stripped comparison with the files of the development tree found no difference in code (119 identical, 87 differing in comments only, 0 differing in code), run 2026-11-09 with a thin Python script; the ten new modules were produced from the development files by replacing paths in docstrings. A text search finds no `sorry`, `native_decide`, `axiom` or `ofReduceBool` in them. No Lean build and no `lake` command was run for this version.
* Checks run for this version (Rust `-O`, standard library only, under 1 minute each, through `code/launch_job.sh`): `code/dense/build.sh` (including `gen94`) rc 0; `check_rows.py`: 68 rows, 0 failures, composite exceptions `{94}`; `regen_lean.sh`: 39 compared, 0 differing; `gen94 gen` on the three certificates: output byte-identical to the shipped leaf modules, `gen94 verify` OK on each; `examples/ex.rs`: output identical to the development run. Outputs: `data/dense/{check_rows.out, regen_lean.out, examples.out}`, `data/dense/m94_lean/regen_check.out`.
* Import closure of `lean/LRSpectrumFull.lean` (computed by following `import` lines, 2026-11-09): 206 modules, all in the tree; the only imports from outside the project are `Mathlib` and the generated `E8Stage.P<p>.Asm` modules imported by `EightRunnersReal.lean`.
* The dense-window and eight manuscripts compile with latexmk (rc 0, no undefined references or citations; dense-window 25 pages after the review fixes, eight 7 pages); build files were created outside the tree and not copied.
* Not verified in this release, and where the existing material disagrees: (1) the exhaustive computation for m = 94 is quoted from run reports and two review reports that are not archived, and no program of it is archived; (2) `EightRunnersReal.lean` imports generated modules `E8Stage.P<p>.Asm` that are not in the tree, and the root file `lean/LRSpectrumFull.lean` imports `EightRunnersReal`, so the default target does not build as archived; (3) the 27 kernel proofs were not rebuilt and no whole-lake rebuild was run; (4) the prints for 21 rows of the dense-window table are lines of development results files of 2026-11-03; (5) Theorem 3 (prime case) keeps its single archived print of 2026-10-01; (6) bibliographic fields: `refs.bib` records for Beck-Everett and Blanco-Criado-Santos are incomplete (first names, title), and the titles filled in for Pandey and Pomerance come from the working version of the manuscript and were not re-checked; the Tao blog post of 2017 has no bibliography entry (the cited arXiv:1701.02048 is Tao's note); Zhang is cited at version 2 while the sweep of 2026-11-09 reports a version 3; (7) version 1.0.4 stated the range of published computer-assisted proofs one off (m <= 13, m = 14); the manuscript of 1.1.0 and the README state m <= 12 and m = 13, 14; (8) the statement of significance is a negative search result; (9) no blind read (Part H, gate H4) of the dense-window or eight manuscripts has been run, no talk or FAQ exists for them, and no human has read them; (10) no check of the eight-runner claim against the `formal-conjectures` repository.
* Independent review (9 November 2026, a separate session working from the files): outcome PASS-WITH-FIXES; the Lean statements, axiom prints, range 2 <= m <= 126 (73 composite values, each with an archived print), Theorem D and the multiset reduction were found consistent with the sources. Eight required fixes were then applied: bibliography placeholders replaced (Tao blog post added as a separate entry and cited for the statements on [1,1.2m] and [1,2m]; Pandey and Pomerance reduced to what the sources show), the contradictory sentence on LP duality in the prior-art paragraph, `.zenodo.json` provenance sentence aligned with the README and its build dates corrected, the "default build" wording of the E8 paper and README, the superseded 1.0.0 correction bullet, and this section. The PDFs were rebuilt without undefined references and the checksums regenerated.
* Still open: the Part H blind-read gate (H4) and TALK.md / FAQ.md (H5) for the two changed manuscripts have not been run; the user's decisions on the provenance wording, on the label wording for the eight-runner theorem ("VERIFIED outside lake build") and on the gate are recorded by the commit that publishes this version, not by this file; the DOI of 1.1.0 after deposit; commit identity ElVec1o.

## Scan for version 1.1.1 (patch release, 10 November 2026)

* Changes: `paper/dense-window/main.tex` (four text edits and one added line after the lemma on speeds avoiding 1), `refs.bib` (Pandey10, Pomerance22), `main.pdf` (rebuilt with latexmk, rc 0, no undefined references or citations), `README.md` (version line, new section "Changes since version 1.1.0", wording on the prior-art reading), `CITATION.cff` (version 1.1.1, date 2026-11-10; the `doi` field carries the concept DOI until the follow-up commit; 1.1.0 DOI kept in the identifiers), `.zenodo.json` (version, date, wording), `CLAIMS.tsv` (one cell), `MANIFEST.tsv` (regenerated), this file. No Lean file, data file or code changed; no Lean build was run.
* Prior-art read of 2026-11-09 (a literature session, local texts): Bohman-Peng arXiv version 1 (abstract, Section 1, Theorem 2.1 with proof, Section 3; proofs of the number-theoretic lemmas and small-n casework only skimmed; published Mathematika text not read), Pomerance arXiv version 1 (in full), Pandey (in full). Result: none states the window [1,2m] for any m; Pandey's Theorem 3.1 contains the case of the lemma on speeds avoiding 1.
* An independent review of this patch release is to run; its outcome is not yet recorded here.

### Files added in version 1.2.0 (25)

`paper/shifted-grid-four/{NOTE.md, LEAN_MAP.md}`; 23 Lean modules in `lean/LRSpectrumFull/`, copied byte for byte from the development files: `TPFourFinal`, `TPFourCase3`, `TPFourHub`, `TPFourLemma7`, `TPFourTight`, `TPFourWindow`, `TPFourCoincide`, `TPFourCase21`, `TPFourArcs`, `TPFourCoset`, `TPFourGlue`, `TPFourReduce`, `TPFourFive`, `TPFourLocal`, `TPFourBridge`, `TPPrime`, `TPThreeR`, `TPSmall` (the 18 modules of the import closure of `TPFourFinal` that were not present) and `TPThreeA`, `TPThreeRed`, `TPFMain`, `TPFCheck`, `TPFData` (context for the cases `m = 1, 2, 3`; not in that closure).

## Scan for version 1.2.0 (draft, 12 November 2026)

* Tree: 792 files excluding `.git` (no `.DS_Store`, no LaTeX build files, no file above 5 MB). `MANIFEST.tsv` hashes all files except itself (791 rows), regenerated after the last edit of this file. Added: 25 files (list above). Changed: `README.md`, `CITATION.cff`, `.zenodo.json`, `CLAIMS.tsv` (ten rows added), `RELEASE_CHECK.md`, `MANIFEST.tsv`, `lean/README.md`. The root file `lean/LRSpectrumFull.lean` is unchanged: the new modules are not imported by it (the default target does not build as archived in any case; build single modules). No earlier manuscript, data file, program or Lean file changed. Nothing committed, pushed, tagged or uploaded.
* Authorship fields: `CITATION.cff` version 1.2.0, `date-released: 2026-11-12`; the version DOI of 1.2.0 does not exist yet: the field `doi` carries the concept DOI and a comment says so; the identifier list has no entry for 1.2.0; to be recorded in a follow-up commit after deposit. `.zenodo.json` version 1.2.0, publication date 2026-11-12, description extended by the new result with its caveats and the corresponding "not claimed" items. `CITATION.cff` lists no references, so the Alcantara-Criado-Santos paper is named in its abstract only.
* AI attribution: the provenance paragraph of the new note (`paper/shifted-grid-four/NOTE.md`, section Labels and provenance) is the wording of 1.1.0 adapted to this result (the written proof and the Lean sources produced by the AI system; the Lean theorem checked by the kernel; the written argument, the statement and the sources read or re-run by further sessions of the same system). The adapted wording needs the author's approval. `Claude` and `Anthropic` now occur in six files besides this one (`.zenodo.json`, `README.md`, `paper/shifted-grid-four/NOTE.md`, `paper/dense-window/main.tex`, `paper/eight/main.tex`, `paper/goddyn-wong-loo/main.tex`); no commit metadata should carry them.
* The result and its caveats: the release text is the three-sentence wording of the fresh review of 2026-11-12 (verdict SOUND-WITH-CAVEATS), unstrengthened, in `README.md` (section "Changes since version 1.1.1") and the note. The five caveats (not a new theorem; grid phases only; dependence on `five_runners`; distinctness necessary; no whole-library build) appear in the README, the note, `CLAIMS.tsv` and `.zenodo.json`. The reference to Alcantara, Criado and Santos, arXiv:2506.13379, gives authors and arXiv number only: no title and no first names are recorded locally.
* Import closure of `LRSpectrumFull.TPFourFinal` inside the project (computed by following `import` lines of the development files, 2026-11-12): 25 modules; outside the project only `Mathlib` and Mathlib sub-modules. Seven were already in the archive and are byte-identical to the development files (`Delta2FiveRunners`, `Delta2PFLMaster`, `Delta2PFLDigits`, `Delta2PFLAssembly`, `Delta2GridBridge`, `MaxLoneliness`, `NearestInteger`); 18 were added. SHA-256 of each added file is in `MANIFEST.tsv`; the table of the closure is `paper/shifted-grid-four/LEAN_MAP.md`.
* Lean sources: a text search of the 23 added files finds no `sorry`, `native_decide`, `axiom`, `ofReduceBool`, `admit` or `unsafe`. The files were copied byte for byte, so, unlike the modules of 1.1.0, their comments were not rewritten: 18 comment lines in 18 files cite development files by path (`INVENTION_2026_11/...`, in some cases with a leading `private/`), and one comment in `TPThreeA.lean` mentions the session that produced a proof. The `lean/README.md` says so. The headers of the `TPFour*` modules cite the hand proof as `HANDPROOF_v2`; its cleaned text is `paper/shifted-grid-four/NOTE.md`.
* Pattern scan (`grep`, `.git` and this file excluded) of the added and changed files other than the 23 Lean modules for `/Users/`, `programme/private`, `INVENTION_`, `ROOMS`, `seat`, `orchestrator`, `HANDOFF`, `Co-Authored`, `Generated with`, `sonnet`, `fable`: 0 hits. The words "new theorem" occur only in negations ("not a new theorem"); no sentence claims arbitrary or real phases for the result.
* Not done in this release: no Lean or `lake` command of any kind was run (no whole-library build, no single-module build, no axiom print: every Lean fact is quoted from the development record and from the review of 2026-11-12); `five_runners` was not re-derived end to end by anyone in this review chain (statement, decide sites and axioms only); the journal status of arXiv:2506.13379 was not checked and its proof was not examined (the review session read Conjecture 1.1, Theorems 1.2 and 1.3, Corollary 1.4 and one footnote of a local text); no blind read (Part H, gate H4) of the note, no talk or FAQ (H5), no human reading of the note; the corrected text of the hand proof was not re-read as a text by a fresh session (the first version was reviewed twice); the programs behind the quoted computations (the review scan giving the value 1/6, the development checkers of about 406 million instances) are not archived and nothing was recomputed for this release; the generator of `TPFData.lean` is not archived; the prior art of the cases `m = 1, 2, 3` was not re-read (the `TPp 3` case is recorded in the development notes as known from the literature on the shifted conjecture); the build and axiom print of `TPp_three`, `TPp_three_of_caseA`, `caseF`, `caseR` and `TP_prime_free` are those recorded on 2026-11-03 and were not observed again (only `TPp_one`, `TPp_two`, `TPp_four` and `five_runners` were observed on 2026-11-12); the root aggregator was not extended; and the user's decisions on the provenance wording and on the gate are recorded by the commit that publishes this version, not by this file.
* An independent review of this release is to run; its outcome is not yet recorded here.

### Files added in version 1.3.0 (9)

`paper/shifted-real-four/{NOTE.md, LEAN_MAP.md}`; 7 Lean modules in `lean/LRSpectrumFull/`, copied byte for byte from the development files: `RFiveBase`, `RFiveWindow`, `RFiveCluster`, `RFiveLemS`, `RFiveCase`, `RFiveFinal`, `RFiveCor`.

## Scan for version 1.3.0 (draft, 12 November 2026)

* Tree: 801 files excluding `.git` (no `.DS_Store`, no LaTeX build files, no file above 5 MB). `MANIFEST.tsv` hashes all files except itself (800 rows), regenerated after the last edit of this file. Added: 9 files (list above). Changed: `README.md`, `CITATION.cff`, `.zenodo.json`, `CLAIMS.tsv` (ten rows added), `RELEASE_CHECK.md`, `MANIFEST.tsv`, `lean/README.md`, and `paper/shifted-grid-four/LEAN_MAP.md` (one added warning on the build order of the 25-module closure). The root file `lean/LRSpectrumFull.lean` is unchanged: the new modules are not imported by it (the default target does not build as archived in any case; build single modules). No earlier manuscript, data file, program or Lean file changed. Nothing committed, pushed, tagged or uploaded.
* Authorship fields: `CITATION.cff` version 1.3.0, `date-released: 2026-11-12`; the version DOI of 1.3.0 does not exist yet: the field `doi` carries the concept DOI and a comment says so; the identifier list keeps the entry for 1.2.0; to be recorded in a follow-up commit after deposit. `.zenodo.json` version 1.3.0, publication date 2026-11-12, description extended by the new result with its caveats and the corresponding "not claimed" items.
* AI attribution: the provenance paragraph of the new note (`paper/shifted-real-four/NOTE.md`, section Labels and provenance) is word for word the paragraph of `paper/shifted-grid-four/NOTE.md`. The author's approval of this wording is still needed. No commit metadata should carry `Claude` or `Anthropic`.
* The result and its caveats: the release text follows the four-sentence wording of the fresh review of 2026-11-12 (verdict SOUND-WITH-CAVEATS), with the computed range for the value 5/24 added. The six caveats (not a new theorem; contribution and prior art; not covered; the constant 1/5 not claimed sharp; distinctness necessary; no whole-library build) appear in the README, the note, `CLAIMS.tsv` and `.zenodo.json`. The reference to Alcantara, Criado and Santos, arXiv:2506.13379, gives authors and arXiv number only. The note states that Corollary 1.4 was read in version 1 of the preprint. No correction of the wording of their conjecture is published.
* Import closure of `LRSpectrumFull.RFiveCor` inside the project (computed by following `import` lines of the development files, 2026-11-12): 20 modules; outside the project only `import Mathlib`. Thirteen were already in the archive and are byte-identical to the development files (SHA-256 compared on both sides); seven were added. SHA-256 of each file is in `MANIFEST.tsv`; the table of the closure is `paper/shifted-real-four/LEAN_MAP.md`. The closure contains neither `TPFourFive` nor `TPFourCase3` and no occurrence of `five_runners`.
* Lean sources: a text search of the 7 added files finds no `sorry`, `native_decide`, `axiom`, `ofReduceBool`, `admit`, `unsafe`, `implemented_by` or `extern`. The files were copied byte for byte, so their comments were not rewritten: 8 comment lines in 6 of the 7 files cite development files by path (a directory named `ROOMS`, in one file below a directory named `INVENTION_2026_11`); one cited file name contains the name of a model. The `lean/README.md` says so, without the paths. The argument these comments refer to is written out in `paper/shifted-real-four/NOTE.md`.
* Process note on the Lean build: the building session initially reported all modules as written but not built, and in a later block reported that all seven modules built at the initial attempt without a source edit. The reviewing session found this unusual but consistent with file times and logs, and re-elaborated each source against the built object files (exit 0, no output). The memory ceiling declared to the job wrapper was not enforced for the Lean child process (the wrapper tracks the `lake` process, not the `lean` child); peak resident memory of the `lean` child was about 5.3 GB by sampling at 2-second intervals, not recorded for `RFiveBase`.
* Pattern scan (`grep`, `.git` and this file excluded) of the added and changed files other than the 7 Lean modules for `/Users/`, `programme/private`, `INVENTION_`, `ROOMS`, `seat`, `orchestrator`, `HANDOFF`, `Co-Authored`, `Generated with`, model names and e-mail addresses: 0 hits in the added lines of the changed files and in the two new Markdown files, except the quoted pattern names in this file. The words "new theorem" occur only in negations; no sentence claims that the constant 1/5 is attained or sharp for the class.
* Not done in this release: no Lean or `lake` command of any kind was run for this archive (no whole-library build, no single-module build, no axiom print: every Lean fact is quoted from the review of 2026-11-12 and from the building session; only `shasum`, `cmp` and text searches were run on the files); the prose proof in the note was not read by an independent reader (the correspondence to Lean declarations was checked only by searching for each declaration name in the stated file), no blind read (Part H, gate H4), no talk or FAQ (H5), no human reading; the prior-art reading was local: Alcantara-Criado-Santos was read in version 1 only and its proof was not examined, and the papers not held (Malikiosis-Santos-Schymura arXiv:2411.06903 and its published form; the published version of Alcantara-Criado-Santos; Beck-Hosten-Schymura; Rifford; Henze-Malikiosis; Bohman-Holzman-Kleitman; Renault; Cusick-Pomerance; Barajas-Serra on circulant graphs) were not read, the other papers only in part, so the statement that no computation-free proof was found in the sources we hold is a statement about those sources; the sharpness of the constant 1/5 for the class is not established (the value 5/24 is a minimum over phase grids and over a bounded range of speeds, computed evidence only, and the infimum over real phases is not known); the programs behind the computed values (1/6, 5/24) are not archived and nothing was recomputed for this release; the Lean memory ceiling was not enforced by the job wrapper during the builds (peak about 5.3 GB observed by sampling); the root aggregator was not extended; and the user's decisions on the provenance wording and on the gate are recorded by the commit that publishes this version, not by this file.
* An independent review of this release is to run; its outcome is not yet recorded here.

## Scan for version 1.3.1 (patch release, 12 November 2026)

* Changes: `paper/shifted-real-four/NOTE.md` (a dated version line at the top, the release text in the Status section, Caveat 2 with its list of papers read and not held), `README.md` (version line, new section "Changes since version 1.3.0", pointers next to the retained sentences of the 1.3.0 entry, one clause in "What is not claimed"), `CLAIMS.tsv` (the contribution row and the prior-art row of the note corrected, the label of the written-proof row changed from PROVED (qualified) to UNVERIFIED, one row added), `CITATION.cff` (version 1.3.1, date 2026-11-12; the `doi` field carries the concept DOI until the follow-up commit; the entry for 1.3.0 is kept in the identifiers; abstract extended), `.zenodo.json` (version, description), `MANIFEST.tsv` (regenerated), this file. No Lean file, data file, program or manuscript changed; no Lean or `lake` command was run; nothing was recomputed. The mathematical sections of the note (Sections 0 to 8 and the Lean correspondence) are untouched.
* Why: version 1.3.0 stated that no computation-free proof of the sub-case "some speed divisible by 5" was found in the sources held, and listed Malikiosis-Santos-Schymura (arXiv:2411.06903) as not held. That paper was read afterwards. As we read it (arXiv version 2 of 21 June 2025): Corollary 1.11 gives the shifted conjecture for four moving runners when the speed sum is at least 196; Proposition 2.9 gives it when three of the four speeds have a common factor above 1 (given the three-runner case); Proposition 6.5 with n = 4 gives it when two speeds have a common divisor that is odd and at least 5 or even and at least 10 (given the three-runner case); the case of four moving runners is completed there by Alcantara, Criado and Santos (Remark 1.12). So the parts of Theorem R5 with at least two speeds divisible by 5, or with speed sum at least 196, are not new even as computation-free statements. The case of exactly one speed divisible by 5 with speed sum at most 195 (after dividing by the gcd) was not found in the sources read; no residue-class argument modulo 5 appears in that paper.
* Two readers: a literature session read the whole text of version 2 and wrote the first reading; this staging session then re-read, in the local text, the introduction (indexing: n is the number of moving runners, the bound is 1/(n+1), shifts are arbitrary real, velocities are distinct positive integers after the reduction cited there), Proposition 1.8, Lemma 2.2, Proposition 2.9, Lemma 5.1, Theorem 6.3, Remark 6.4, Proposition 6.5, Corollary 6.6, Theorem 7.1 and Corollary 7.2, Corollary 1.11 and Remark 1.12, and agreed with the first reading, with three precisions that are built into the wording: (1) Corollary 1.11 is printed without a gcd hypothesis, while its reduction (Proposition 1.8) is stated for gcd 1, so the wording says "speed sum after dividing by the gcd" or "of gcd 1"; (2) "without a computer search" means that no computation is carried out in that paper, while the proofs rest on results cited from the geometry of numbers (its Lemmas 2.10 and 2.11 and a width bound for hollow 3-dimensional bodies) that we did not examine; (3) one apparent misprint in the proof of Proposition 6.5 (the parallelogram of covering radius 3/5 is in part (4) of Theorem 6.3, not part (3)) does not affect the reading. Arithmetic checked for n = 4: the hypothesis of Proposition 6.5 reads delta >= 10 for even delta and delta >= 5 for odd delta, where delta is the gcd of the two speeds outside the chosen pair; two multiples of 5 have gcd a multiple of 5, so delta >= 5 if odd and delta >= 10 if even, and both branches satisfy it. A pair of speeds with gcd 3 is not covered.
* Authorship fields: `CITATION.cff` version 1.3.1, `date-released: 2026-11-12`; the version DOI of 1.3.1 does not exist yet: the field `doi` carries the concept DOI and a comment says so; to be recorded in a follow-up commit after deposit. `CITATION.cff` lists no references, so the papers of Alcantara, Criado and Santos and of Malikiosis, Santos and Schymura are named in its abstract only. `.zenodo.json` version 1.3.1, publication date 2026-11-12. The provenance paragraph of the note is unchanged.
* Not done in this release: the proofs of Malikiosis-Santos-Schymura were not re-verified, the results they cite were not examined, and the case analysis for lattice-width three in its Section 7.2 was read in full by the first reader only; the published version of Alcantara-Criado-Santos, the journal version of Malikiosis-Santos-Schymura and the remainder of Barajas-Serra (arXiv:0710.4495, beyond its first part) remain unread, as do the other papers listed as not held in the note; no Lean or `lake` command was run (every Lean fact is as in the section for 1.3.0); no blind read (Part H, gate H4), no talk or FAQ (H5), no human reading of the note; the statement that the text of the note has had no independent read is kept in the note and in the README, while the row of `CLAIMS.tsv` for the written proof records that one further session compared the note with the Lean declarations during the review of 1.3.0 (28 of 28 items matching), which is a check against the declarations and not a blind read; the user's decisions on the provenance wording and on the gate are recorded by the commit that publishes this version, not by this file.
* An independent review of this patch release is to run; its outcome is not yet recorded here.
