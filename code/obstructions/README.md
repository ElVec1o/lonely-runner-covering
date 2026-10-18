# code/obstructions

Reproduction of the finite computations quoted in `paper/obstructions/main.tex`.

| File | Role |
|---|---|
| `repro_O4.sh` | Builds `code/reduction/mdr`, `code/reduction/levelfit` and `mlcheck`; prints for each family of the table `tab:O4` the exact maximum loneliness (`mdr ml`, and `mlcheck`), the first certificate level (`certv`), `U1` with its a posteriori error bound (`u1`), `U1` and `U2` (`levelfit fitv`), controls for `U_D`, and the shifted supremum (`shift`). Output of the run for this snapshot: `data/obstructions/repro_O4.out`. |
| `mlcheck.rs` | Exact `ML(v)`, enumerating every numerator `k` of `k/(v_i+v_j)`; `mlcheck selftest` compares known values with a rational grid scan. Independent of `mdr`. |
| `shift_grid.py` | Exact rational scan (all `t = p/q`, `q <= 400`) of the shifted gap of the Proposition on phases, with a zero-phase control. Python, bounded loops, about 1 second. |

Other commands (inputs in `data/obstructions/`):

    mdr enumw M H                  # exhaustive supersets in the box; m = 6 H 50, 8 24, 10 30, 12 26, 14 24 (35 s, 4 s, 131 s, 63 s, 12 s)
    mdr cert 80 data/obstructions/census/resid_m12_h22.txt          # 98 census residuals
    mdr cert 80 data/obstructions/census/resid_m12_h26_gt24.txt     # 829
    mdr cert 80 data/obstructions/census/resid_m14_h22.txt          # 140
    mdr cert 80 data/obstructions/census/adversarial_147.txt        # 147 adversarial families
    MDR_WX=1 mdr hunt2 M 6000 SECONDS SEED 2M+2 data/obstructions/seeds/seed_mM.txt OUT    # time-limited hunt of the last table row

The hunt is a time-limited search: its outcome is UNRESOLVED whatever it prints, and its evaluation counts depend on the machine. The runs
of this snapshot (120 s per `m`, seed 1) and the recorded development run (480 s per `m`) are quoted in the manuscript. In the output of `hunt2` the figure after `WEq=` is
1000 times the certificate level, and `written=` counts families that reach the write threshold. In the output of `cert` the certificate kinds are those of `cert_m` in `mdr/src/main.rs` (mode 0: `WX`, exact scan over Z; mode 1: `WI`, point certificate or window; mode 2: `WE`); row 5 of the table quotes the `WI` level 39, for which `certv` prints `WX` level 6.

Correction of 2026-10-18: the function `ml` of `mdr` skipped numerators not coprime to the denominator (see `code/reduction/README.md`); the corrected source is archived,
and `mlcheck` agrees with it on all quoted values.

Added in 1.0.1: `python3 -I cornercheck.py` (exact check of the tight-corner proposition on boxes `m = 2..5`, output `data/obstructions/cornercheck.out`) and
`python3 -I chainparity.py 20001` (output `data/obstructions/chainparity.out`).

Added in 1.0.3: `descent_check.py`, the exact checks for Section 8 of the note (descent and topological obstructions). It contains the function `ml` and the control battery of the standard exact routine unchanged (every numerator `k` of `k/L`, `L = v_i + v_j`; earlier variants skipped numerators not coprime to `L`). Python glue, exact fractions, bounded memory, every mode under 2 minutes. From the archive root:

    python3 -I code/obstructions/descent_check.py controls > data/obstructions/descent_controls.out     # SELFTEST PASS (300 random vectors; 2000 if numpy is importable)
    python3 -I code/obstructions/descent_check.py d0 > data/obstructions/descent_d0.out                 # Lemma 20 on 1500 random vectors, with a negative control
    python3 -I code/obstructions/descent_check.py instances > data/obstructions/descent_instances.out   # m = 7 values, second-level witnesses m = 3..100, three near-tight sets (12 s)
    python3 -I code/obstructions/descent_check.py gw > data/obstructions/descent_gw.out                 # 66 Goddyn-Wong triples n <= 260 from the GCD condition, with a negative control
    python3 -I code/obstructions/descent_check.py table 73 > data/obstructions/descent_table.out        # the 70 tight vectors: full recomputation for m <= 73 (75 s), counts 11 / 59 / 46 / 13 / 0
    python3 -I code/obstructions/descent_check.py strict 151 > data/obstructions/descent_strict.out     # the eleven strict values of m (50 s)

Input: `data/obstructions/descent_gw_loo.tsv`, the leave-one-out values of the 67 Goddyn-Wong type tight vectors from an exact Rust job of 18 October 2026 (source not archived). Rows with `m > 73` are used from the table without recomputation (`table`), and in `strict` the vectors with `m > 151` are used from the table; the output files state which entries are recomputed. Exit status is 0 only if every check and control passes.
