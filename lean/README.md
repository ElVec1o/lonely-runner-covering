# lean

Lean 4 sources cited by the seven manuscripts (namespace `LRSpectrumFull`).

* `lean-toolchain`: `leanprover/lean4:v4.30.0`. `lakefile.toml`, `lake-manifest.json`: Mathlib pinned at
  `v4.30.0` (revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`). Building needs network access to fetch Mathlib
  or a local Mathlib checkout; this archive does not contain it.
* `LRSpectrumFull/`: the 130 modules named in the `LEAN_MAP.md` files of the papers, together with every module
  they import inside the project (206 files in total at version 1.1.1). `LRSpectrumFull.lean` imports the 130 named modules.
  Version 1.1.0 added ten files: `Delta2PinnedCover`, `Delta2CoverRangeS94`, `Delta2CoverRangeS94s416A`, `...B`, `...C`
  (the case m = 94) and `Delta2CoverRangeS97`, `S103`, `S109`, `S115`, `S122`. A text search finds no `sorry`,
  `native_decide`, `axiom` or `ofReduceBool` in them; comments were rewritten as for the other modules, and a
  comment-stripped comparison with the development files found no difference in code for any of the 206 files.
  Version 1.2.0 added 23 files (229 in total), copied byte for byte from the development files and not imported by
  `LRSpectrumFull.lean`: the 18 modules of the import closure of `TPFourFinal` that were not yet present
  (`TPFourBridge`, `TPFourLocal`, `TPFourReduce`, `TPFourFive`, `TPFourArcs`, `TPFourCoset`, `TPFourCoincide`,
  `TPFourCase21`, `TPFourGlue`, `TPFourWindow`, `TPFourTight`, `TPFourLemma7`, `TPFourHub`, `TPFourCase3`,
  `TPFourFinal`, `TPPrime`, `TPThreeR`, `TPSmall`; the other seven modules of that closure were already present)
  and, as context for `m = 1, 2, 3`, `TPThreeA`, `TPThreeRed`, `TPFMain`, `TPFCheck`, `TPFData`
  (see `paper/shifted-grid-four/LEAN_MAP.md`). A text search finds no `sorry`, `native_decide`, `axiom` or
  `ofReduceBool` in them. Unlike the other modules, their comments were not rewritten: some comments cite
  development files by path (`HANDPROOF_v2.md` in those comments is the hand proof published as
  `paper/shifted-grid-four/NOTE.md`; the other files cited are not archived).
  Version 1.3.0 added 7 files (236 in total), copied byte for byte from the development files and not imported by
  `LRSpectrumFull.lean`: `RFiveBase`, `RFiveWindow`, `RFiveCluster`, `RFiveLemS`, `RFiveCase`, `RFiveFinal`, `RFiveCor`
  (theorems `R5`, `R5_core`, `R5_tp`, `R5_gcd`; see `paper/shifted-real-four/LEAN_MAP.md`). The import closure of `RFiveCor` has 20
  modules; the other 13 were already present and are byte-identical to the development files. A text search finds no `sorry`,
  `native_decide`, `axiom` or `ofReduceBool` in the seven new files. Their comments were not rewritten: the header comments of six
  of them cite development files by path; the argument they refer to is written out in
  `paper/shifted-real-four/NOTE.md`, and the files cited are not archived. They do not import `five_runners`.
  Version 1.4.0 added 8 files (244 in total), copied byte for byte from the development files and not imported by
  `LRSpectrumFull.lean`: `RQWindow`, `RQThree`, `RQFour`, `RQLemmaC`, `RQGen`, `RQPigeon`, `RQT`, `RQG24`
  (theorems `P3`, `Q4`, `QGen`, `T`, `G24`, `window_lemma`, `lemmaC_real`; see `paper/shifted-real-four-classes/LEAN_MAP.md`).
  The import closure of `RQT` and `RQG24` has 23 modules; the other 15 were already present and are byte-identical to the
  development files. A text search finds no `sorry`, `native_decide`, `axiom` or `ofReduceBool` in the eight new files. Their
  comments were not rewritten: the header of each of the eight cites a development file by path; the argument they refer to is written
  out in `paper/shifted-real-four-classes/NOTE.md`, which says which of its sections correspond, and the file cited is not archived.
  They do not import `five_runners`. The Lean trust base of these eight modules includes the earlier `RFive*` and `TPFour*` modules.
  Version 1.5.0 added 7 files (251 in total), copied byte for byte from the development files and not imported by
  `LRSpectrumFull.lean`: `RSevenCore`, `RSevenA`, `RSevenB`, `RSevenFinal` (theorems `R7A`, `R7B`, `R7_partial`) and
  `RQ3Sweep`, `RQ3Mix`, `RQ3Final` (theorems `Q3`, `Q3_ndvd`, `Q3_core`; see `paper/shifted-real-four-classes/LEAN_MAP.md`).
  The union of the import closures of `RSevenFinal` (28 modules) and `RQ3Final` (27 modules) has 36 modules; the other 29 were
  already present and are byte-identical to the development files (SHA-256 compared on both sides). A text search finds no
  `sorry`, `admit`, `native_decide`, `axiom` or `ofReduceBool` in the seven new files; `set_option` occurs only in
  `RSevenB` and `RSevenFinal` (`synthInstance.maxSize 4096` and `maxRecDepth 100000` on three kernel `decide` statements over
  `ZMod 7`). Their comments were not rewritten: the header of each of the seven cites a development file by path; the argument they
  refer to is written out in `paper/shifted-real-four-classes/NOTE.md` (Sections 12 and 13), and the files cited are not archived.
  They do not import `five_runners`. The import closure of `RQ3Final` contains `TPThreeA` and, through it, the generated
  data modules `TPFData` and `TPFCheck` (kernel-checked, `decide +kernel`; generator not archived).
  Packaging limitation, stated plainly: the name `LRSpectrumFull.badSet` is declared in the already archived `RQPigeon` and also in two
  older modules of the development tree (`BadTripleFamilies`, `PerturbStrip`; they are not in this archive), so those two cannot be
  imported together with the `RQ*`/`RSeven*` family in one file. The library root `LRSpectrumFull.lean` is not updated and was
  already not buildable as a whole. In the development tree, two lemmas of the `RSeven*` modules carried the names `caseA` and `caseB`, which clash
  with `TPThreeA.caseA` and `NormalForm.caseB`; they were renamed `r7CaseA` and `r7CaseB` before this archive was assembled (a renaming of
  the two lemmas, of their two uses and of one comment line, nothing else), so the archived files carry the new names. The independent review of the `RSeven*` and `RQ3*` modules was made on the files
  before this renaming; after it, `RSevenA`, `RSevenB` and `RSevenFinal` were rebuilt one at a time (success) and one file importing
  `RSevenFinal`, `RQ3Final`, `RQT`, `RQG24`, `RFiveCor` and `NormalForm` elaborated without error, with the standard axioms printed for
  `R7_partial`, `R7A`, `R7B`, `Q3` and eight earlier theorems. The renamed files were not re-reviewed.
  Nothing was built for this archive in 1.1.0, 1.2.0, 1.3.0, 1.4.0 or 1.5.0 (1.3.1 changed no Lean file). The default target `LRSpectrumFull` cannot be built as it stands:
  `EightRunnersReal.lean` imports the generated modules `E8Stage.P<p>.Asm`, which are not in this archive
  (regenerated by `code/eight`), and a single build of all range modules needs more than 20 GB of memory.
  Build single modules only, and treat the sources as provided as is.
* The tree is a subset of the development tree: modules not needed by any cited declaration were left out.
  The modules below contain a declaration whose proof is `sorry`, or an `axiom`, and are in the archive because a
  manuscript cites them. They are needed only by the paper named; the authority for any label is
  `#print axioms` of the cited declaration, as listed in the `LEAN_MAP.md` of that paper. The modules on which
  the dense-window, covering, perturbation and reduction manuscripts depend contain no `sorry` body (checked by search;
  the Lean build was not re-run).

  | Module | Content | Needed by |
  |---|---|---|
  | `BarajasSerra.lean` (line 1044) | `primeFilteringCor3` stated, body `sorry` | eight |
  | `EightPlan.lean` (line 379) | superseded stub `e5_sum_STUB_SUPERSEDED` | eight |
  | `EightMSS.lean` (line 456), `EightZonotope.lean` (lines 1800, 1830) | statements with `sorry` body | eight |
  | `Chen7RunnerImport.lean`, `EightMSSImport.lean` | one `axiom` each (imported results) | eight |
  | `EightCert27.lean` | the 27 axioms `lemma7Check_seven_p<p>_verified` (kernel checks whose sources were deleted; hashes in the docstrings, regeneration in `code/eight`) | eight |
  | `RoomFCU_f5.lean` (line 79), `RoomT2.lean` (line 83) | `tightNoDvd_of_strong`, `t2Weak` stated with `sorry` | obstructions |
* Do not run a bare `lake build` on a machine with less than about 30 GB of memory: one worker needs about
  10 GB and `lake` starts one per core. Use `bash code/lean_build/gbound_build.sh Module...` to build single
  modules sequentially. A single named target builds its whole import closure (25 modules for `TPFourFinal`, 20 for `RFiveCor`, 23 for `RQT` together with `RQG24`, 28 for `RSevenFinal`, 27 for `RQ3Final`);
  give the closure modules to the script one after another in dependency order, as listed in `paper/shifted-grid-four/LEAN_MAP.md`,
  `paper/shifted-real-four/LEAN_MAP.md` and `paper/shifted-real-four-classes/LEAN_MAP.md`.
* Comments and docstrings in some modules carry development history (session numbers, internal rule
  names) and cite development reports by file name (for example `report_f5_room.md`, `bridge31_notes.md`) that are
  not in this archive. They were left unchanged except for the replacement of paths beginning with `private/`.
