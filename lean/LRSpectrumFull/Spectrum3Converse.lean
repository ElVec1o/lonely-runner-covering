/-
# Additional converse exclusion families for the n=3 spectrum

Two more "exclusion" families for the converse of the n=3 spectrum
classification, obtained by the *modular-witness method* packaged in
`Spectrum3.lean` as `D_lt_of_residues`. For a modulus `m`, if every
coordinate's residue mod `m` is "far from `0`" (the integer condition
`2m < 7·(n%m)` and `2m < 7·(m − n%m)`, i.e. `‖n/m‖ > 2/7`), then the
witness `t = 1/m` certifies `D < 3/14`.

Here we add the `m = 5` family (residues `2,3 mod 5`, giving `‖n/5‖ = 2/5`)
and the `m = 8` family (residues `3,4,5 mod 8`, giving `‖n/8‖ ∈ {3/8,1/2}`).
Each proof is a one-line `omega` over residues, following `D_lt_seven`
exactly. The mod-8 family genuinely extends coverage: e.g. `(5,11,12)` is
missed by the mod-3, mod-5, and mod-7 families. No `sorry`.
-/

import LRSpectrumFull.Spectrum3

namespace LRSpectrumFull

/-- Triples with every coordinate `≡ 2` or `3 (mod 5)` have `D < 3/14`.
Residues `2,3 mod 5` give `‖n/5‖ = 2/5 > 2/7`. -/
theorem D_lt_five (p q r : ℤ)
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3) : D (vtriple p q r) < 3 / 14 := by
  apply D_lt_of_residues (vtriple p q r) 5 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 5 < 7 * (p % 5) ∧ 2 * 5 < 7 * (5 - p % 5); omega
  · show 2 * 5 < 7 * (q % 5) ∧ 2 * 5 < 7 * (5 - q % 5); omega
  · show 2 * 5 < 7 * (r % 5) ∧ 2 * 5 < 7 * (5 - r % 5); omega

/-- Triples with every coordinate `≡ 3, 4` or `5 (mod 8)` have `D < 3/14`.
Residues `3,4,5 mod 8` give `‖n/8‖ ∈ {3/8, 1/2} > 2/7`. -/
theorem D_lt_eight (p q r : ℤ)
    (hp : p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5) (hq : q % 8 = 3 ∨ q % 8 = 4 ∨ q % 8 = 5)
    (hr : r % 8 = 3 ∨ r % 8 = 4 ∨ r % 8 = 5) : D (vtriple p q r) < 3 / 14 := by
  apply D_lt_of_residues (vtriple p q r) 8 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 8 < 7 * (p % 8) ∧ 2 * 8 < 7 * (8 - p % 8); omega
  · show 2 * 8 < 7 * (q % 8) ∧ 2 * 8 < 7 * (8 - q % 8); omega
  · show 2 * 8 < 7 * (r % 8) ∧ 2 * 8 < 7 * (8 - r % 8); omega

/-- Concrete instance of the `mod 5` exclusion: `D((2,3,7)) < 3/14`. -/
example : D (vtriple 2 3 7) < 3 / 14 := D_lt_five 2 3 7 (by omega) (by omega) (by omega)

/-- Concrete instance of the `mod 8` exclusion, missed by the mod-3, mod-5,
and mod-7 families: `D((5,11,12)) < 3/14`. -/
example : D (vtriple 5 11 12) < 3 / 14 := D_lt_eight 5 11 12 (by omega) (by omega) (by omega)

/-! ### The scaled-witness method: `t = a/m`

The unscaled exclusion (`D_lt_of_residues`, witness `t = 1/m`) cannot reach
triples like `(1,2,9)`: the coordinate `1` forces `m = 3` (only `‖1/3‖ > 2/7`
among `‖1/m‖`), but `9 ≡ 0 (mod 3)` then fails — and **no** single `1/m`
witness works. The **scaled** witness `t = a/m` removes this obstruction:
the runner becomes `‖(n·a)/m‖`, excluded when `n·a` is far from `0 mod m`.
Crucially this needs no new analysis — it reduces to the same helper
`two_sevenths_lt_nearestIntDist_div` applied to `v i · a`. -/

/-- **Scaled modular-witness exclusion.** With witness `t = a/m`: if every
`v i · a` is far from `0 (mod m)`, then `D v < 3/14`. Strictly generalizes
`D_lt_of_residues` (take `a = 1`). -/
theorem D_lt_of_scaled_residues {k : ℕ} (v : Fin (k + 1) → ℤ) (a m : ℤ) (hm : 0 < m)
    (h : ∀ i, 2 * m < 7 * (v i * a % m) ∧ 2 * m < 7 * (m - v i * a % m)) :
    D v < 3 / 14 := by
  apply D_lt_of_witness v ((a : ℝ) / (m : ℝ))
  intro i
  have key : (v i : ℝ) * ((a : ℝ) / (m : ℝ)) = ((v i * a : ℤ) : ℝ) * (1 / (m : ℝ)) := by
    push_cast; ring
  rw [key]
  exact two_sevenths_lt_nearestIntDist_div (v i * a) m hm (h i).1 (h i).2

/-- `(1,2,9)` — beyond `L₃`, but reachable by **no** unscaled modulus (the
coordinate `1` forces `m = 3`, killed by `9`). The scaled witness `t = 3/10`
catches it: `1,2,9` map to `3,6,27 ≡ 3,6,7 (mod 10)`, all far from `0`. -/
example : D (vtriple 1 2 9) < 3 / 14 := by
  apply D_lt_of_scaled_residues (vtriple 1 2 9) 3 10 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 10 < 7 * (1 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 1 * 3 % 10); omega
  · show 2 * 10 < 7 * (2 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 2 * 3 % 10); omega
  · show 2 * 10 < 7 * (9 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 9 * 3 % 10); omega

end LRSpectrumFull
