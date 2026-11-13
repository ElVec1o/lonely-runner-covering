# LEAN_MAP: paper/shifted-four-sum195/NOTE.md

Lean project: `lean/` (Lean 4.30.0, Mathlib as pinned in `lean/lake-manifest.json`). Modules are `LRSpectrumFull.<Module>` in `lean/LRSpectrumFull/<Module>.lean`; names below omit the prefix. Declarations are in namespace `LRSpectrumFull.D0`, except those of `TCArc`, `TCCover`, `TCSound`, which are in `LRSpectrumFull.TC`. None of the new modules is imported by the root file `lean/LRSpectrumFull.lean`, which is not updated. The builds and the axiom prints are those of the development repository of 2026-11-13; nothing was built for this archive.

## Warning on building: one module at a time, never a bare `lake build`

The import closure of `S4Final` and `S4Cor` has 293 modules, 253 of them added in version 1.6.0 (the other 40 were already in the archive and are byte-identical to the development files). A single call `lake build LRSpectrumFull.S4Final` from a clean tree builds the whole closure and lets Lake run several modules in parallel. One Lean worker on these modules needs 6 to about 10.6 GB when it succeeds (sampled peaks; builds that the watchdog killed reached 11.4 GB; Section 9 of the note), and on 2026-11-13 a parallel rebuild of seven layer modules whose imports had not been built was sampled at 29.6 GB on a 24 GB machine before a watchdog killed it. Therefore:

1. Build the modules one at a time, in the order of `lean/S4_BUILD_ORDER.txt` (293 lines, one module name per line, a post-order of the import lines of the files in `lean/LRSpectrumFull/`, checked for this release so that every module comes after all the modules it imports; it ends with `S4All_5`, `S4Cor`, `S4Final`). Example, from `lean/`: `for m in $(cat S4_BUILD_ORDER.txt); do lake build LRSpectrumFull.$m || break; done`.
2. Before `lake build X`, every module that `X` imports must have an up-to-date `.olean`; if one is missing, Lake rebuilds it, in parallel with others.
3. Put a memory watchdog on the whole process tree. `code/s4-range/build_modules.sh` with `code/s4-range/launch_watchdog.sh` do this for macOS (ceiling argument, kill at 90 percent of the ceiling, one module at a time, a disk floor); they were edited for the archive only in their paths and comments and were not run in that form. `code/lean_build/gbound_build.sh` builds its arguments one at a time without a watchdog.
4. Expect about 4.5 hours of wall time (296 build jobs in the development repository, including reruns and failures), the longest module 728 s, the final module `S4Final` itself 6.3 GB.

## Main theorems

    sLRC4_le195     (S4Final.lean)  : forall a b c d : N, 0 < a -> a < b -> b < c -> c < d ->
                                      Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 -> a + b + c + d <= 195 -> S4 ![a, b, c, d]
    sLRC4_le195_fin (S4Final.lean)  : forall v : Fin 4 -> N, (forall i, 0 < v i) -> Function.Injective v ->
                                      Finset.univ.gcd v = 1 -> sum_i v i <= 195 -> S4 v
    sLRC4_le195_any (S4Final.lean)  : the same without the gcd hypothesis

with `S4 v := forall phi : Fin 4 -> R, exists t : R, forall i, GoodR (v i) (phi i) t` (`D0Bridge.lean`), `GoodR v phi t := 1/5 <= tpDist (v * t + phi)` (`RFiveBase.lean`), `tpDist x := |x - round x|` (`TPSmall.lean`).

Axioms printed for the final theorems and the soundness theorems (`#print axioms`, in the build log of the final module and in the review session): `sLRC4_le195`, `sLRC4_le195_fin`, `sLRC4_le195_any`, `d0_sound`, `d0_sound_nat`, `TC.tc_sound`, `classB_sound`, `rangeOK_sound`, `rangeOK2_sound`, `cor_fin`, `cor_any`, `S4_of_cover`: `[propext, Classical.choice, Quot.sound]`. In the whole closure the build logs show 243 axiom lines, none different from this list. No `sorry`, `admit`, `axiom` declaration, `unsafe`, `implemented_by`, `ofReduceBool` or `native_decide` (the word occurs in one comment of `D0Chunk.lean`, which says that the file does not use it).

## Modules added in version 1.6.0 (253 files, 7,886,940 bytes)

| group | modules | content |
|---|---|---|
| depth-0 certificate | `D0Core`, `D0Sound`, `D0Bridge`, `D0Chunk`, `D0Fast` | definitions, `d0_sound`, `S4`, `d0_sound_nat`, record checkers `recOK`, `recOK3` |
| time covers | `TCArc`, `TCCover`, `TCSound` | `arc_of_floor_ceil`, `coord_good`, `cover_sound`, `tc_sound` |
| class test | `S4Perm`, `S4Class` | `S4_of_cover`, `anyPerm_sound`, `classB`, `classB_sound` |
| loop | `S4Loop`, `S4Loop2`, `S4PreApp` | `rangeOK_sound`, `rangeOK2_sound`, `preOK_append` |
| corollaries | `S4Cor` | `cor_fin`, `cor_any` |
| generated data, first coordinate a with b-intervals | 156 `S4R_<aa>_<blo>_<bhi>`, 5 `S4Range{5,11b12n3,22,28,41}` | `s4_range_*`, `S4_a5`, `S4_a11_12_3`, `S4_a22`, `S4_a28`, `S4_a41` (130,914 depth-0 records in total with the blocked ranges) |
| generated data, blocked ranges with time covers | 14 `S4B_<aa>_<blo>_<bhi>`, 11 `TCP_<aa>_<b>_<b>_<k>` | `s4_blk_*`, `tcv_*`, `tcs_*`, `preOK_*` (305 covers) |
| layers | 47 `S4A_<aa>`, 5 `S4All_<k>`, `S4Final` | case splits by `omega`, `sLRC4_le195` |
The group counts add up to 253 (5 + 3 + 2 + 3 + 1 + 161 + 25 + 53). The other 40 modules of the closure (the class theorems `R5_core`, `P3`, `QGen`, `Q4`, `T`, `G24`, `R7_partial`, `Q3_ndvd` and the modules they import: 18 `TP*` modules, 7 `RFive*`, 8 `RQ*`, 4 `RSeven*`, 3 `RQ3*`; the closure contains no `Delta2*` module) were already in the archive from versions 1.2.0 to 1.5.0 and are unchanged. The 293 modules and their order are listed in `lean/S4_BUILD_ORDER.txt`.

Files that are NOT in the archive although they exist in the development tree, because they are outside the import closure of `S4Final` and `S4Cor`: deliberate negative controls that fail to build (`TCNegTight1234`, `S4BNegDropTc_03_006_006`, `S4Neg41Corrupt`, `S4Neg41Drop`), superseded range modules (`S4Range24`, `S4Range40`, `S4Range5b6n3`, and the eleven first-partition range modules replaced by 57 split modules), the cost probes `D0Probe*`, `D0FProbe*`, and checking files (`S4Check`, `TCCheck`, `TCTight*`, `D0Examples`).

## Comments in the copied files

The files were copied byte for byte. Header comments of 216 of the 293 closure files cite development files by path (a path below the directory of the development repository that holds the work of November 2026); the files cited are not archived. The generated modules name their generator in the header (`s4gen block2`, `s4asm`, `layers.py`); the sources of the generators are in `code/s4-range` (`gen`, `layers.py`). In `RQGen.lean` and `TPThreeA.lean` a comment calls a building session by a role word, and in `TPThreeA.lean` a comment names a model. The argument that the headers of the hand-written modules refer to is written out in `NOTE.md`, Sections 3 to 7.

## Lean declarations of the note

The table "Lean correspondence" at the end of `NOTE.md` lists, for each lemma and theorem of the note, its Lean declaration and file, and whether the written proof is full or a sketch.
