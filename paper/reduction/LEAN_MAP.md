# LEAN_MAP: paper/reduction/main.tex

Lean project: `lean/` (Lean 4.30.0, Mathlib as pinned in `lean/lake-manifest.json`).
All modules listed are `LRSpectrumFull.<Module>` in `lean/LRSpectrumFull/<Module>.lean`.

Axioms checked 2026-09-24 without building anything (all `.olean` files present and newer than
their sources):

```
cd lean && lake env lean ../code/reduction/axioms/ax.lean
```

Output: `code/reduction/axioms/ax.out` (35 declarations; every one reports exactly
`[propext, Classical.choice, Quot.sound]`). Section 7 (added 2026-09-24):
`lake env lean ../code/reduction/axioms/ax_t2sub.lean`, output `code/reduction/axioms/ax_t2sub.out`, 5 declarations
(`oneEntry_ML_ge`, `oneEntry_T2`, `oneEntry_ML_ge_inv`, `oneEntry_T2_inv`,
`ML_ge_two_div_of_unit`), all `[propext, Classical.choice, Quot.sound]`; `T2Sub.lean` has no
`sorry`; its `.olean` is newer than the source. `grep sorry|native_decide` over the 12 modules below:
the only hit is a docstring in `RoomFCU_erdos.lean` (T2Sub.lean: no hit) (`LemmaP_statement` is a `def`, proved in
`RoomFCU_lemmaP.lean` and `RoomFCU_compress.lean`).

Index convention: the paper's m (number of speeds) is Lean's `k + 1`; the paper's target
1/(m+1) is Lean's `1 / ((k : ℝ) + 2)`. `UniversalFloor` is LRC(m) for all m >= 3 (Lean `n >= 2`).

## Theorems, propositions, lemmas

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| Def 2.1(4) strongly free | `StrongFree` (def) | Delta2FreeGrowth.lean | n/a |
| Def 2.1(5) two-free | `TwoFree` (def) | Delta2SeparationWindow.lean | n/a |
| Def 2.2 B_i, U_D | `RoomA4Compress.badSet`, `rieszWeight`, `UDFires` (defs) | RoomA4_compress.lean | n/a |
| Def 3.1 A1 | `StrongFreeWindowTiny` (def, UNPROVED) | Delta2SeparationWindow.lean | n/a |
| Def 3.1 A2 | `DissociatedOctetWitness` (def, UNPROVED) | Delta2Connect.lean | n/a |
| Def 3.1 A3 | hypothesis `hwinB` of Thm 3.3 (UNPROVED) | RoomA4_compress.lean | n/a |
| Def 3.2 crux | `RoomA4Compress.FloorCruxU` (def, OPEN) | RoomA4_compress.lean | n/a |
| Thm 3.3 | `RoomA4Compress.universalFloor_of_four_atoms_U` | RoomA4_compress.lean | standard |
| Thm 3.4 | `RoomFCUErdos.floorCruxU_iff_universalFloor` | RoomFCU_erdos.lean | standard |
| Prop 3.5 | `strongFreeWindowTiny_of_456` | Delta2WindowK3.lean | standard |
| Rem 3.6 (case ML > delta) | `RoomFCUCompress.rational_point_of_lt` | RoomFCU_compress.lean | standard |
| Lem 3.7 | `RoomA4Rosenfeld.witness_of_missing_divisor`, `RoomFCUErdos.floor_of_not_D` | RoomA4_rosenfeld.lean, RoomFCU_erdos.lean | standard |
| Lem 3.8 | `RoomA4Rosenfeld.floor_of_leaveOneOut_imprimitive` | RoomA4_rosenfeld.lean | standard |
| Prop 3.9 | `RoomFCUErdos.universalFloor_iff_divisible` | RoomFCU_erdos.lean | standard |
| Prop 3.10 | `RoomFCUModerator.strictFloorD_false` | RoomFCU_moderator.lean | standard |
| Rem 3.11 | `RoomA4Rosenfeld.bridgeDisjunctionQPrimInd_of_QPrim`, `RoomA4Rosenfeld.ind_of_ind2`, `RoomA4Compress.floorCruxU_of_ind2`; older top theorems `universalFloor_of_four_atoms_QWprim`, `RoomA4Rosenfeld.universalFloor_of_four_atoms_ind2` | Delta2Connect.lean, RoomA4_rosenfeld.lean, RoomA4_compress.lean | standard (floorCruxU_of_ind2, both top theorems; the two small implications were not separately printed) |
| Prop 4.1 | `RoomA4Compress.floor_of_measure_certificate` | RoomA4_compress.lean | standard |
| Prop 4.2 | `RoomA4Compress.floor_of_integral_unionBound`, `RoomA4Compress.floor_of_UD` | RoomA4_compress.lean | standard |
| Thm 4.3 | `floor_of_rieszSharpFiresQ` (hypothesis `rieszSharpFiresQ`, masses `webMassQ`, `webMassDelQ`, `webSections`) | Delta2Connect.lean, Delta2BridgeDisjunction.lean | standard |
| Cor 4.4 | `rieszSharpFiresQ_of_subfamilySum_le` | Delta2Connect.lean | standard |
| Rem 4.5 | NOT formalized (W(v) empty for strongly free v; one line) | | |
| Thm 4.6(1) | `RoomA4Barrier.goodSet_countable` | RoomA4_barrier.lean | standard |
| Thm 4.6(2) | `RoomA4Barrier.integral_le_sum_badSet` | RoomA4_barrier.lean | standard |
| Thm 4.6(3) | `RoomA4Barrier.lt_ML_of_UDFires` | RoomA4_barrier.lean | standard |
| Thm 4.6(4) | `RoomA4Barrier.not_UDFires_of_tight` | RoomA4_barrier.lean | standard |
| Thm 4.6(5) | `RoomA4Barrier.not_UDFires_consec` | RoomA4_barrier.lean | standard |
| Prop 5.1 | `RoomFCUModerator.ML_ge_of_escape` | RoomFCU_moderator.lean | standard |
| after Prop 5.1 | `RoomFCUCompress.ML_ge_of_residues`, `RoomFCUCompress.lonely_iff_escape` | RoomFCU_compress.lean | standard |
| Thm 5.2 (Lemma P) | `RoomFCUCompress.lemmaP_quant` (bound 2W/(q(2W-1))); `RoomFCULemmaP.lemmaP` and `RoomFCUCompress.lemmaP_via_escape` (strict form, `RoomFCUErdos.LemmaP_statement`) | RoomFCU_compress.lean, RoomFCU_lemmaP.lean | standard |
| Thm 5.3 | `RoomFCUCompress.famF_via_escape` (ML form), `RoomFCURamanujan.famF_lonely` (residue form, the time (sD+1)/(jD)); `famF` (def) | RoomFCU_compress.lean, RoomFCU_ramanujan.lean | standard |
| Conj 5.4 | CONJECTURE, no Lean | | |
| Prop 5.5 | `RoomFCUGoddyn.fast_runner_floor`, `RoomFCUGoddyn.cruxU_fast` | RoomFCU_goddyn.lean | standard |
| Conj 6.1, 6.2, 6.4 | CONJECTURES, no Lean | | |
| Prop 6.3 | `RoomFCUHilbert.gw_not_dvd`, `RoomFCUHilbert.gw_family_not_dvd` | RoomFCU_hilbert.lean | standard (gw_not_dvd printed; gw_family_not_dvd not separately printed) |
| Rem 6.5 (T2 => LRC) | NOT formalized (PROVED, short) | | |
| Thm 7.1 | `T2Sub.oneEntry_ML_ge` (family `T2Sub.oneEntry`, def; engine `T2Sub.ML_ge_two_div_of_unit`) | T2Sub.lean | standard |
| Cor 7.2 | `T2Sub.oneEntry_T2` | T2Sub.lean | standard |
| Thm 7.3 | `T2Sub.oneEntry_ML_ge_inv`, `T2Sub.oneEntry_T2_inv` | T2Sub.lean | standard |
| Prop 8.3 | `RoomFCUMss.halfShift_not_lonely` | RoomFCU_mss.lean | standard |

"standard" = `[propext, Classical.choice, Quot.sound]`, as printed in `code/reduction/axioms/ax.out`.

## Statements in the paper that are NOT formalized

- Remark 3.6: A2 from LRC(8) needs "ML attained at a rational time"; only the strict case is Lean.
- Remark 3.6: A1 (m = 5..7), A2, A3 themselves (cited from the literature, not formalized).
- Remark 4.5: W(v) empty for strongly free v.
- Remark 6.5: T2 implies LRC.
- Prop 6.3 applied to the Goddyn-Wong instances (rests on Goddyn-Wong Thms 2.3, 3.1).
- Section 6 and the computations: the fact that ML is attained at c/(v_i+v_j) (standard; used by all programs).
- Remark 8.2 (level drift): computed, exact integer arithmetic, not formalized.
- Section 7: the application of Zhang Thm 1.2 + Prop 6.3 to (T) on one-entry families; the sweep
  of 15,307 families and the 42 uncovered values (computed).
- ML(1,5,6,11,16,17) = 5/33 and ML(4,8,12)-type values other than Prop 3.10: computed.

## Computational ground (Rule 9). All paths relative to the archive root

Sources (source + Cargo.toml/Cargo.lock only) are in `code/reduction/<name>/`; exact commands in
`code/reduction/README.md`.

| Paper item | Program |
|---|---|
| Table 1 (boxes m = 3..10), maximiser denominators, T2 minima m <= 10 | `code/reduction/fcuspec` (`fcuspec sweep M H`) |
| Independent enumeration (4,400) ... (10,38) | `code/reduction/gdn` (`gdn tight M H 0`) |
| Third enumeration m <= 8 | `code/reduction/ecalc` (`ecalc enum M H OUT`) |
| Table 2 (T2 hunts) | `code/reduction/t2hunt` (`driver.sh`, seeds 101m+1, 101m+2) |
| T2 equality at m = 12 (WITHDRAWN: the exact value is ML = 1/9, see CLAIMS.tsv) | `code/reduction/mdr` (`mdr ml ...`, corrected; `code/obstructions/mlcheck.rs`) |
| Conj 5.4 (499 pairs, m <= 56) | `code/reduction/rmj` (`rmj thmF 2 400 40`, `rmj thmF 41 56 56`) |
| Remark 8.2 families | `code/reduction/mdr` (`mdr certv 60 V`; m = 16 with `MDR_QMIN=18`), `code/reduction/modchk`, `code/reduction/levelfit` |
| ML(1,5,6,11,16,17) = 5/33 | `code/reduction/fcuspec` (`fcuspec eval 1,5,6,11,16,17`) |
| Section 7: 15,307 families, min, equality cases, Table 3 | `code/reduction/t2sweep` (`t2sweep 3 40 20 > full.txt; t2sweep cover < full.txt`); `uncovered.txt` |

Re-run 2026-09-24: `t2sweep 3 40 20` output byte-identical to the original; `rmj thmF 41 56 56`,
`mdr ml`/`certv` on the Remark 8.2 families and the m = 12 T2 family reproduce the paper values.

