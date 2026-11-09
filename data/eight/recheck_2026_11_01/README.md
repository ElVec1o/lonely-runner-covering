# Re-observation of eight_runners_unconditional_real, 2026-11-01

Raw outputs of the run of 2026-11-01 (development machine, macOS, one `lean` process, no `lake build`):

* `assemble_real_2026_11_01.log`: `code/eight/stage/assemble_real.sh`; both `LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real` and `hchk_all_real` print `[propext, Classical.choice, Quot.sound]`; `/usr/bin/time -l` block: 50.43 s wall, maximum resident set 7,082,344,448 B, peak memory footprint 1,083,260,448 B.
* `chk_parsed.txt`: `#print axioms` of 50 declarations in the same environment, whitespace-normalised (the module prefix `LRSpectrumFull.` is cut): 47 print the three standard axioms only (the target, `hchk_all_real`, the intermediate theorems and the 27 theorems `EightV4.Cert<p>.lemma7Check_seven_p<p>`); the last three are controls for the detection of `sorry` and print `sorryAx` (`BarajasSerra.primeFilteringCor3`, `EightMSS.bridge31`, `EightPlan.e5_sum_STUB_SUPERSEDED`, declarations whose bodies are `sorry` and which are not used by the target).
* `lean_Ctl2.log`: negative control in the same environment: `EightRunners.eight_runners_unconditional` prints the three standard axioms and the 27 axioms `EightCert27.lemma7Check_seven_p<p>_verified`.

What this does not show: the 27 kernel proofs (about 11.5 h of kernel work, 2.6 GB of object files outside the lake package, not in this archive) were not rebuilt; the run loaded the kept object files and re-checked the final assembly. The hashes of the 27 regenerated certificate sources equal the recorded hashes (`code/eight/records`). No whole-lake rebuild was run for this release. Lean, Mathlib and the kernel are not audited. The Lean sources are provided as is.
