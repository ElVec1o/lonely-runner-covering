/-
# Milestone 34: Case-A exclusion via cascade ∘ converse

The paper's §3 Case A treats subtori in normal form `u = (a,a,b,c)`,
`v = (d,−d,e,f)` (the two columns of `jkForm a b c d e f`). The argument
is: the **cascade** (M31, `mD_le_col`) bounds `mD U` by the 1-dim D-value
of a generator column, and the `L₃` classification then forces the
column's abs-triple into `L₃` (coords `≤ 6`).

We mechanize the *clean half* of that step. The centerpiece is a single
general bridge composing the cascade with the **converse exclusion** (M33,
`D_lt_of_residues`, general over `Fin (k+1)` so it applies verbatim to a
4-runner column):

> `mD_lt_of_col_residues` — if some generator **column** of a subtorus has
> every residue far from `0` modulo some `m`, the whole subtorus is
> outside the band: `mD M < 3/14`.

The cascade does the geometric reduction; the modular witness `t = 1/m`
(lifted to the column) does the arithmetic. Every concrete Case-A
exclusion is then an `omega` over residues, for *any* of the moduli
`3, 5, 7, 8, …`. No `sorry`.
-/

import LRSpectrumFull.NormalForm
import LRSpectrumFull.Cascade
import LRSpectrumFull.Spectrum3
import LRSpectrumFull.Spectrum3Converse

namespace LRSpectrumFull

/-- **General Case-A bridge (cascade ∘ converse).** If a generator column
`j0` of a subtorus `M` has every residue far from `0` modulo `m`
(`2m < 7·(M i j0 % m)` and `2m < 7·(m − M i j0 % m)`), then `mD M < 3/14`.
Pure composition: the cascade `mD_le_col` reduces to the column's D-value,
and `D_lt_of_residues` bounds that. -/
theorem mD_lt_of_col_residues {k r : ℕ} (M : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r)
    (m : ℤ) (hm : 0 < m)
    (h : ∀ i, 2 * m < 7 * (M i j0 % m) ∧ 2 * m < 7 * (m - M i j0 % m)) :
    mD M < 3 / 14 :=
  lt_of_le_of_lt (mD_le_col M j0) (D_lt_of_residues (fun i => M i j0) m hm h)

/-- Column `0` of `jkForm` is the `u`-generator `(a, a, b, c)`. -/
theorem jkForm_col0 (a b c d e f : ℤ) :
    (fun i => jkForm a b c d e f i 0) = ![a, a, b, c] := by
  funext i; fin_cases i <;> rfl

/-- Column `1` of `jkForm` is the `v`-generator `(d, −d, e, f)`. -/
theorem jkForm_col1 (a b c d e f : ℤ) :
    (fun i => jkForm a b c d e f i 1) = ![d, -d, e, f] := by
  funext i; fin_cases i <;> rfl

/-- **Case-A exclusion via the `u`-generator, mod 3.** If the `u`-triple
`(a,b,c)` is coprime to `3`, the Case-A subtorus is outside the band. -/
theorem mD_jkForm_lt_of_u_not_three (a b c d e f : ℤ)
    (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) (hc : ¬ 3 ∣ c) :
    mD (jkForm a b c d e f) < 3 / 14 := by
  apply mD_lt_of_col_residues (jkForm a b c d e f) 0 3 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 3 < 7 * (a % 3) ∧ 2 * 3 < 7 * (3 - a % 3); omega
  · show 2 * 3 < 7 * (a % 3) ∧ 2 * 3 < 7 * (3 - a % 3); omega
  · show 2 * 3 < 7 * (b % 3) ∧ 2 * 3 < 7 * (3 - b % 3); omega
  · show 2 * 3 < 7 * (c % 3) ∧ 2 * 3 < 7 * (3 - c % 3); omega

/-- **Case-A exclusion via the `v`-generator, mod 3.** If the `v`-triple
`(d,e,f)` is coprime to `3`, the Case-A subtorus is outside the band. -/
theorem mD_jkForm_lt_of_v_not_three (a b c d e f : ℤ)
    (hd : ¬ 3 ∣ d) (he : ¬ 3 ∣ e) (hf : ¬ 3 ∣ f) :
    mD (jkForm a b c d e f) < 3 / 14 := by
  apply mD_lt_of_col_residues (jkForm a b c d e f) 1 3 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 3 < 7 * (d % 3) ∧ 2 * 3 < 7 * (3 - d % 3); omega
  · show 2 * 3 < 7 * ((-d) % 3) ∧ 2 * 3 < 7 * (3 - (-d) % 3); omega
  · show 2 * 3 < 7 * (e % 3) ∧ 2 * 3 < 7 * (3 - e % 3); omega
  · show 2 * 3 < 7 * (f % 3) ∧ 2 * 3 < 7 * (3 - f % 3); omega

/-- **Case-A exclusion via the `u`-generator, mod 7.** If the `u`-triple
`(a,b,c)` is `≡ 3,4 (mod 7)`, the Case-A subtorus is outside the band. This
reaches subtori the mod-3 exclusion cannot — e.g. `u`-triples containing a
multiple of `3`. -/
theorem mD_jkForm_lt_of_u_seven (a b c d e f : ℤ)
    (ha : a % 7 = 3 ∨ a % 7 = 4) (hb : b % 7 = 3 ∨ b % 7 = 4)
    (hc : c % 7 = 3 ∨ c % 7 = 4) :
    mD (jkForm a b c d e f) < 3 / 14 := by
  apply mD_lt_of_col_residues (jkForm a b c d e f) 0 7 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 7 < 7 * (a % 7) ∧ 2 * 7 < 7 * (7 - a % 7); omega
  · show 2 * 7 < 7 * (a % 7) ∧ 2 * 7 < 7 * (7 - a % 7); omega
  · show 2 * 7 < 7 * (b % 7) ∧ 2 * 7 < 7 * (7 - b % 7); omega
  · show 2 * 7 < 7 * (c % 7) ∧ 2 * 7 < 7 * (7 - c % 7); omega

/-- Concrete Case-A subtorus excluded by the mod-3 `u`-test: `u`-triple
`(1,2,4)` is coprime to `3`. -/
example : mD (jkForm 1 2 4 1 1 1) < 3 / 14 :=
  mD_jkForm_lt_of_u_not_three 1 2 4 1 1 1 (by omega) (by omega) (by omega)

/-- Concrete Case-A subtorus the mod-3 test **misses** but mod-7 catches:
`u`-triple `(3,4,10)` has `3 ≡ 0 (mod 3)` yet `3,4,10 ≡ 3,4,3 (mod 7)`. -/
example : mD (jkForm 3 4 10 1 1 1) < 3 / 14 :=
  mD_jkForm_lt_of_u_seven 3 4 10 1 1 1 (by omega) (by omega) (by omega)

/-- **General scaled Case-A bridge.** As `mD_lt_of_col_residues`, but with
the scaled witness `t = a/m` — if every `M i j0 · a` is far from `0 (mod m)`,
then `mD M < 3/14`. This reaches subtori **no unscaled modulus** can. -/
theorem mD_lt_of_col_scaled_residues {k r : ℕ} (M : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r)
    (a m : ℤ) (hm : 0 < m)
    (h : ∀ i, 2 * m < 7 * (M i j0 * a % m) ∧ 2 * m < 7 * (m - M i j0 * a % m)) :
    mD M < 3 / 14 :=
  lt_of_le_of_lt (mD_le_col M j0) (D_lt_of_scaled_residues (fun i => M i j0) a m hm h)

/-- A Case-A subtorus reachable by **no** unscaled modulus: the `u`-triple
`(1,2,9)` (coordinate `1` forces `m=3`, killed by `9`). The scaled witness
`t = 3/10` excludes it via column `0`. -/
example : mD (jkForm 1 2 9 1 1 1) < 3 / 14 := by
  apply mD_lt_of_col_scaled_residues (jkForm 1 2 9 1 1 1) 0 3 10 (by norm_num)
  intro i
  fin_cases i
  · show 2 * 10 < 7 * (1 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 1 * 3 % 10); omega
  · show 2 * 10 < 7 * (1 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 1 * 3 % 10); omega
  · show 2 * 10 < 7 * (2 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 2 * 3 % 10); omega
  · show 2 * 10 < 7 * (9 * 3 % 10) ∧ 2 * 10 < 7 * (10 - 9 * 3 % 10); omega

/-! ### Boundary side: connecting Case A to the exact `S₁(3)` values (M32)

The cascade also gives an *upper* bound `mD ≤ D(u-triple)`. Collapsing the
duplicated coordinate (`D(a,a,b,c) = D(a,b,c)`), the `u`-generator's
D-value is a genuine 3-runner value — so the **exact** `L₃` values from M32
(`D(1,2,6) = … = D(2,3,5) = 3/14`, `D(1,2,3) = 1/4`) bound Case A directly.
For the four `3/14`-triples this puts full-support Case-A subtori (any `v`)
*on the band boundary*: `mD ≤ 3/14`. -/

/-- Duplicating the first runner does not change the gap (a `min` over the
same value set). -/
theorem gap_dup (a b c : ℤ) (t : ℝ) :
    gap ![a, a, b, c] t = gap ![a, b, c] t := by
  apply le_antisymm
  · apply le_gap; intro j; fin_cases j
    · exact gap_le ![a, a, b, c] t 0
    · exact gap_le ![a, a, b, c] t 2
    · exact gap_le ![a, a, b, c] t 3
  · apply le_gap; intro i; fin_cases i
    · exact gap_le ![a, b, c] t 0
    · exact gap_le ![a, b, c] t 0
    · exact gap_le ![a, b, c] t 1
    · exact gap_le ![a, b, c] t 2

/-- Hence the D-value is unchanged: `D(a,a,b,c) = D(a,b,c)`. -/
theorem D_dup (a b c : ℤ) : D ![a, a, b, c] = D ![a, b, c] := by
  have hg : gap ![a, a, b, c] = gap ![a, b, c] := funext (gap_dup a b c)
  unfold D ML
  rw [hg]

/-- **Cascade upper bound in terms of the `u`-triple's 3-runner D-value.** -/
theorem mD_jkForm_le_D_utriple (a b c d e f : ℤ) :
    mD (jkForm a b c d e f) ≤ D ![a, b, c] := by
  have h := mD_le_col (jkForm a b c d e f) 0
  rw [jkForm_col0, D_dup] at h
  exact h

/-- Boundary members from M32's `3/14`-triples: full-support Case-A subtori
with `u`-triple `(1,2,6)` / `(1,3,4)` / `(1,5,6)` / `(2,3,5)` satisfy
`mD ≤ 3/14`, for **any** `v`-generator. -/
example (d e f : ℤ) : mD (jkForm 1 2 6 d e f) ≤ 3 / 14 :=
  (mD_jkForm_le_D_utriple 1 2 6 d e f).trans_eq D_v126_eq
example (d e f : ℤ) : mD (jkForm 1 3 4 d e f) ≤ 3 / 14 :=
  (mD_jkForm_le_D_utriple 1 3 4 d e f).trans_eq D_v134_eq
example (d e f : ℤ) : mD (jkForm 1 5 6 d e f) ≤ 3 / 14 :=
  (mD_jkForm_le_D_utriple 1 5 6 d e f).trans_eq D_v156_eq
example (d e f : ℤ) : mD (jkForm 2 3 5 d e f) ≤ 3 / 14 :=
  (mD_jkForm_le_D_utriple 2 3 5 d e f).trans_eq D_v235_eq

/-- The `u`-triple `(1,2,3)` caps Case A at the band **top** `1/4` (the
allowed endpoint, not in the open band `(3/14, 1/4)`). -/
example (d e f : ℤ) : mD (jkForm 1 2 3 d e f) ≤ 1 / 4 :=
  (mD_jkForm_le_D_utriple 1 2 3 d e f).trans_eq D_v123_eq

end LRSpectrumFull
