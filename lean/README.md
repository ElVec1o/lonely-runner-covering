# lean

Lean 4 sources cited by the six manuscripts (namespace `LRSpectrumFull`).

* `lean-toolchain`: `leanprover/lean4:v4.30.0`. `lakefile.toml`, `lake-manifest.json`: Mathlib pinned at
  `v4.30.0` (revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`). Building needs network access to fetch Mathlib
  or a local Mathlib checkout; this archive does not contain it.
* `LRSpectrumFull/`: the 123 modules named in the `LEAN_MAP.md` files of the papers, together with every module
  they import inside the project (196 files in total). `LRSpectrumFull.lean` imports the 123 named modules.
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
  modules sequentially.
* Comments and docstrings in some modules carry development history (session numbers, internal rule
  names) and cite development reports by file name (for example `report_f5_room.md`, `bridge31_notes.md`) that are
  not in this archive. They were left unchanged except for the replacement of paths beginning with `private/`.
