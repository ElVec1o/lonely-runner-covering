# LEAN_MAP: paper/eight/main.tex

Lean project: `lean/` (Lean 4.30.0, Mathlib as pinned in `lean/lake-manifest.json`).
Modules are `LRSpectrumFull.<Module>` in `lean/LRSpectrumFull/<Module>.lean`. Names below
omit the prefix `LRSpectrumFull.`.

## Main theorem (Thm 1.1)

`EightRunners.eight_runners_unconditional` in `EightRunners.lean` (imports only `EightE5`). Built
2026-09-27 with `bash code/lean_build/gbound_build.sh EightRunners` (EXIT 0). Axiom check:

```
cd lean && lake env lean ../code/eight/print_axioms.lean
```

Literal output for the main theorem:

```
'LRSpectrumFull.EightRunners.eight_runners_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p101_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p103_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p107_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p109_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p113_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p127_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p131_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p137_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p139_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p149_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p151_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p157_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p163_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p31_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p37_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p43_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p47_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p53_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p59_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p61_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p67_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p71_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p73_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p79_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p83_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p89_verified,
 LRSpectrumFull.EightCert27.lemma7Check_seven_p97_verified]
```

"standard" below means a subset of `[propext, Classical.choice, Quot.sound]` (some finite tables
report fewer, e.g. `Sec5Fin.F1a` none, `Card4Table.combo` `[propext, Quot.sound]`). "C27" means
standard plus the 27 axioms `EightCert27.lemma7Check_seven_p<p>_verified`, p in {31, 37, 43, 47,
53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
163}. No declaration in the tables depends on `sorryAx`. No `Lean.ofReduceBool` (native_decide)
appears. Rows marked (2026-09-27) were printed by `code/eight/print_axioms.lean`; the others by the
2026-09-26 axiom files (not shipped; same `.olean` files; the 2026-09-27 build rebuilt only `EightRunners` and
`EightRunnersFinal`, so the 2026-09-26 caveat about `BarajasSerraLRC6M1.lean` is void: lake found
its source hash unchanged).

### Real-proof variant (added 2026-09-30)

`EightRunnersReal.eight_runners_unconditional_real` and `EightRunnersReal.hchk_all_real` in
`EightRunnersReal.lean`. Not in the default lake build. It imports `E8Stage.P<p>.Asm` for the 27
primes (kept oleans in `code/eight/stage/work/olean`, produced by `code/eight/stage/real27_driver.sh`,
about 12 h and 2.6 GB) and is compiled with raw `lean` by `code/eight/stage/assemble_real.sh`.
Output on 2026-09-30: both declarations depend on `[propext, Classical.choice, Quot.sound]` only.
Control: `EightRunners.eight_runners_unconditional` in the same environment still lists the 27
`EightCert27` axioms. The `E8Stage.P<p>.Asm` theorems are `EightV4.Cert<p>.lemma7Check_seven_p<p>`.

Reproduction material: `code/eight/` (see `code/eight/README.md`).

## Statements

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| Thm 1.1 (eight runners) | `EightRunners.eight_runners_unconditional` | EightRunners.lean | C27 (2026-09-27) |
| Thm 1.1, same proof | `EightE5.eight_runners_unconditional` | EightE5.lean | C27 (2026-09-27) |
| Thm 1.2 (seven runners) | `BarajasSerra.LRC6_barajasSerra`; `BarajasSerra.Sec5.lrc6` | BarajasSerraLRC6Plan.lean, BarajasSerraLRC6.lean | standard (2026-09-27) |
| Table 1, all 27 primes | `EightCert27.hchk_all` | EightCert27.lean | C27 (2026-09-27) |
| Sec 3.2, the 27 axioms | `EightCert27.lemma7Check_seven_p<p>_verified` (docstrings carry the SHA-256) | EightCert27.lean | are axioms |

## Section 2 (Rosenfeld's reduction)

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| E0 | `EightPlan.e0_primitive` | EightPlan.lean | standard (2026-09-27) |
| E4 | `EightPlan.e4_leaveOneOut`, `EightPlan.e4_parity` | EightPlan.lean | standard |
| E2 | `EightPlan.e2_prime_dvd` | EightPlan.lean | standard (2026-09-27) |
| E3 | `EightPlan.e3_lcm_dvd` | EightPlan.lean | standard (2026-09-27) |
| NUM | `EightPlan.numeric`, `EightPlan.e5_amgm` | EightPlan.lean | standard (2026-09-27) |
| assembly | `EightE5.eight_runners_of` (LRC6 and the prime checks as hypotheses) | EightE5.lean | standard (2026-09-27) |

## Section 3 (prime campaign)

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| checker | `EightCheckV4` (definitions) | EightCheckV4.lean | n/a |
| soundness | `EightV4.lemma7Check_of_checkRootH`, `EightV4.go_sound` | EightCheckSound.lean | standard (2026-09-26; not imported by `EightRunners`, see Sec 3.1 of the paper) |
| reproduction | records `code/eight/records/P<p>/record.txt`; scripts `code/eight/stage/` | | 27/27 hashes reproduced 2026-09-27 |

## Section 4 (height bound E5)

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| Lemma 4.1 (pigeonhole) | `EightMSS.e5b_staircase` | EightMSS.lean | standard (2026-09-27) |
| Prop 4.2 (rounding step) | `EightE5.mssGap7_holds`; adjacent pair `EightE5.exists_adjacent_pair`; statement `EightMSS.MSSGap7` (def) | EightE5.lean, EightMSS.lean | standard (2026-09-27) |
| E5 | `EightMSS.e5_sum_of_gap`, `EightE5.e5_sum`, `EightE5.e5_prod` | EightMSS.lean, EightE5.lean | standard (2026-09-27) |

## Superseded, kept as records (not in the closure of Thm 1.1)

| Declaration | File | Axioms |
|---|---|---|
| `EightRunnersFinal.eight_runners` | EightRunnersFinal.lean (docstring marks it superseded) | C27 + `EightMSSImport.mss_theorem_A_n7` |
| `EightRunnersFinal.eight_runners_unconditional` | EightRunnersFinal.lean | C27 (duplicate of Thm 1.1; module imports EightMSSImport) |
| `EightMSSImport.mss_theorem_A_n7` (axiom), `eight_runners_mss`, `e5_sum_via_mss_axiom` | EightMSSImport.lean | standard + mss axiom |
| `EightMSSImport.eight_runners_conditional` | EightMSSImport.lean | standard + `chen_lrc7_int` + mss axiom |
| `Chen7RunnerImport.LRC6_holds` | Chen7RunnerImport.lean | standard + `Chen7RunnerImport.chen_lrc7_int` |
| `Chen7RunnerImport.eight_runners_via_chen` | Chen7RunnerImport.lean | standard + `sorryAx` + `chen_lrc7_int` |
| `EightPlan.eight_runners`, `EightPlan.e5_sum` | EightPlan.lean | standard + `sorryAx` (E5 placeholder) |
| MSS zonotope route B1-B6; `sorry`: `EightZonotope.projT_image_eq_LRZ6`, `EightZonotope.bridge31_pullback`, `EightMSS.bridge31` | EightZonotope.lean, EightMSS.lean | the `sorry` declarations are not used by any declaration above |

Import graph (checked 2026-09-27 by grep): `EightMSSImport` and `Chen7RunnerImport` are imported
only by `EightRunnersFinal` (and `EightMSSImport` imports `Chen7RunnerImport`); nothing imports
`EightRunnersFinal` or `EightZonotope`. `EightMSS` stays on the main path because `EightE5` uses
`e5b_staircase` and `MSSGap7` from it; its `bridge31` `sorry` is not in the closure of Thm 1.1
(verified by `#print axioms` above).

## Section 5 (Barajas and Serra)

Namespace prefix `BarajasSerra.` omitted.

| Paper | Lean declaration | File | Axioms |
|---|---|---|---|
| BS Lemma 2 (prime filtering) | `primeFiltering` | BarajasSerra.lean | standard |
| filtering variants | `primeFilteringCor3Top`; `G.primeFilteringBelow`, `G.primeFilteringSlack` | BarajasSerra.lean, BarajasSerraG.lean | standard |
| n = 4, finite model | `barajasSerra_card4_hard`; table `Card4Table.combo` | BarajasSerraCard4.lean, BarajasSerraCard4Table.lean | standard |
| level split | `Sec5.lrc6_nat`, `Sec5.lrc6` | BarajasSerraLRC6.lean | standard |
| cases (b), (c), (d) | `Sec5.case_b0`, `Sec5.case_c0`, `Sec5.case_d0` | BarajasSerraLRC6BCD.lean | standard |
| BS Section 5 core | `Sec5.sec5`; tables `Sec5Fin.F1a`, `F1b`, `F2`, `F3`, `Z1`-`Z3` | BarajasSerraSec5.lean, BarajasSerraSec5Fin.lean | standard |
| case (a), m = 1 | `lrc6_m1_scaled`; tables in `LRC6M1Table` | BarajasSerraLRC6M1.lean, BarajasSerraLRC6M1Table.lean | standard |
| case (a), m >= 2 | `Sec6.case_a_ge2`; reduction to seven patterns `Sec6.g4` | BarajasSerraSec6G4.lean | standard |
| case (a) | `case_a` | BarajasSerraCaseA.lean | standard |
| BS Lemma 4 | `Sec6.lemma4_i`, `Sec6.lemma4_ii`, `Sec6.lemma4_ii_eq` | BarajasSerraSec6.lean | standard |
| BS Lemma 5 | `Z7.lemma5`; `Z7.lemma5_as_printed_false` | BarajasSerraZ7.lean | standard |
| BS Lemma 6 | `Z7.lemma6_i`, `Z7.lemma6_ii`, `Z7.lemma6_iii` | BarajasSerraZ7.lean | standard |
| BS Lemma 7 | `Sec6.lemma7_i`, `Sec6.lemma7_ii` | BarajasSerraSec6.lean | standard |
| BS Lemma 9 | `Sec6.lemma9_i`, `Sec6.lemma9_ii_two`, `Sec6.lemma9_ii_three` | BarajasSerraSec6L9.lean | standard |
| BS Lemma 10, 11 | `Sec6.lemma10`, `Sec6.lemma11` | BarajasSerraSec6L10.lean | standard |
| BS Lemma 12 | `Z7.lemma12_i`, `Z7.lemma12_ii` | BarajasSerraZ7.lean | standard |
| BS 6.1 | `Sec6.sec61`, `Sec6.sec61_witness` | BarajasSerraSec6_1.lean | standard |
| BS 6.2 | `Sec6.sec62`, `Sec6.sec62_witness` | BarajasSerraSec6_2.lean | standard |
| BS 6.3 | `Sec6.sec63`, `Sec6.sec63_witness` | BarajasSerraSec6_3.lean, BarajasSerraSec6_3a.lean | standard |
| BS 6.4 | `Sec6.sec64`, `Sec6.sec64_witness` | BarajasSerraSec6_4.lean | standard |
| BS 6.5 | `Sec6.sec65`, `Sec6.sec65_witness` | BarajasSerraSec6_5.lean | standard |
| BS 6.6 | `Sec6.sec66`, `Sec6.sec66_witness`; `Z7.sec66b` | BarajasSerraSec6_6.lean, BarajasSerraZ7.lean | standard |

## Section 6 (errata)

Each erratum lists its Lean declarations in `paper/eight/errata_barajas_serra.md`.
