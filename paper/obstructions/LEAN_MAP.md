# Lean map for main.tex (live repository: programme/lean-mathlib, prefix LRSpectrumFull)

Status of every VERIFIED row: carried over from the repository where it built; not rebuilt in this archive.
Observed on 2026-10-18 in the live repository (not re-built): each module below has a compiled .olean whose timestamp matches its source, and `grep -c sorry` is 0 for all modules except RoomFCU_f5 (6) and RoomT2 (1), which hold only the CONJECTURE statements (T), (T'), (T2). Axiom prints recorded 2026-10-01: [propext, Classical.choice, Quot.sound]; RoomO6.not_divisorComplete: [propext, Quot.sound]. The axiom prints were not re-run.

| Paper item | Label | Lean declaration(s) (module) |
|---|---|---|
| Thm 1 (barrier), Lemma level sets | VERIFIED, carried over | RoomA4_barrier: nearestIntDist_eq_mem, goodSet_countable, goodSet_null, integral_le_sum_badSet, lt_ML_of_integral_unionBound; RoomA4_compress: floor_of_integral_unionBound |
| Cor 2 | VERIFIED, carried over | RoomA4_barrier: not_UDFires_of_tight, lt_ML_of_UDFires, not_UDFires_of_ML_le, not_UDFires_consec, ML_consec_le |
| Rem (scope) | HEURISTIC | none |
| Prop (escape) | VERIFIED, carried over | RoomFCU_moderator: ML_ge_of_escape; RoomFCU_compress: lonely_iff_escape, rational_point_of_lt, window_via_escape, famF_via_escape, lemmaP_via_escape |
| Prop (missing divisor) | VERIFIED, carried over (known) | RoomA4_rosenfeld: witness_of_missing_divisor |
| Prop (denominators of lonely times) | PROVED | none |
| Obs (level drift), Table | HEURISTIC | none (code/reduction/mdr; code/obstructions/repro_O4.sh, mlexact.py) |
| Thm (O6) | VERIFIED, carried over | RoomO6: not_dvd_speed, mul_sub_lt, exists_coprime_in_window (RoomFCU_hilbert) |
| Cor (GW not DC) | VERIFIED, carried over (family); HEURISTIC (listed vectors) | RoomO6: not_divisorComplete; listed vectors: code/obstructions/gwcheck.py |
| Prop (T') => (T) => no tight DC | PROVED | statements pinned in RoomFCU_f5 (TightNoDvd, TightMaximisersAtMp1); tightNoDvd_of_strong has sorry |
| Conj (T), (T') | CONJECTURE | RoomFCU_f5 definitions, no proof |
| E_m value, (2m+1)ML(E_m) > 2 | VERIFIED, carried over (known, Kravitz Thm 5.1) | RoomEm: ML_Em_m, thmB_gt |
| Conj (T2) | CONJECTURE | RoomT2: T2OnD, T2Weak (one sorry) |
| Prop (chain parity) | PROVED | none |
| Prop (half-phase) | VERIFIED, carried over | RoomFCU_mss: halfShift_not_lonely |
| Rem (covering radius) | known / cited | none |
