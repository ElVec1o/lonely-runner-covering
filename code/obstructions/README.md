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
