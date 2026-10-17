/-
# Attacking research lemma R2 (covering-radius bound) — the explicit-witness fragment

R2 is `ML(p,q,r) ≥ 1/3 − 3/(4·s)` (primitive `s = p+q+r`); via `sum_le_of_ML_bound` it gives the
n=3 absolute coordinate bound. The natural decomposition is **R2-by-cases**: for a triple caught by a
modular witness `t = 1/m`, an explicit lower bound on `ML` clears the inequality outright.

This file proves the **mod-3 witness, sharpened to `ML ≥ 1/3`** (the existing `D_lt_three` only gives
`ML > 2/7`, which is `< 1/3 − 3/(4s)` once `s ≥ 16` — so the sharp `1/3` is genuinely needed for the
large-sum tail of R2, not just the spectrum bound). When no coordinate is divisible by `3`, the
witness `t = 1/3` puts every runner at distance exactly `1/3` from the integers, so `ML ≥ 1/3`, which
dominates `1/3 − 3/(4s)` for *every* `s`.

The residual of R2 — triples that evade the modular witnesses for *all* small moduli — is exactly
where the genuine covering-radius argument (Averkov–Codenotti–Schymura) is required, and is NOT
provided here. Axiom-clean. -/
import LRSpectrumFull.DValue
import LRSpectrumFull.CoordSumBound
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- **The witness engine.** Any single time `t` at which every runner stays `≥ c` from the integers
lower-bounds the maximum loneliness: `c ≤ ML v`. Every modular witness family is an instance. -/
theorem ML_ge_of_witness {k : ℕ} (v : Fin (k + 1) → ℤ) (t c : ℝ)
    (h : ∀ i, c ≤ nearestIntDist ((v i : ℝ) * t)) : c ≤ ML v :=
  (le_gap v t c h).trans (gap_le_ML v t)

/-- For odd `n`, the witness `t = 1/2` puts `n·t` at distance exactly `1/2`: `1/2 ≤ ‖n/2‖`. -/
theorem one_half_le_nid_div2 (n : ℤ) (h : ¬ (2 ∣ n)) :
    (1 / 2 : ℝ) ≤ nearestIntDist ((n : ℝ) * (1 / 2)) := by
  have h1 : n % 2 = 1 := by
    have : n % 2 ≠ 0 := fun hc => h (Int.dvd_of_emod_eq_zero hc)
    have hge : 0 ≤ n % 2 := Int.emod_nonneg n (by norm_num)
    have hlt : n % 2 < 2 := Int.emod_lt_of_pos n (by norm_num)
    omega
  have hdecomp : (n : ℝ) * (1 / 2) = ((n % 2 : ℤ) : ℝ) * (1 / 2) + ((n / 2 : ℤ) : ℝ) := by
    have he : (n % 2 : ℤ) + 2 * (n / 2) = n := Int.emod_add_ediv n 2
    have hc : (n : ℝ) = ((n % 2 : ℤ) : ℝ) + 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast he.symm
    rw [hc]; ring
  rw [hdecomp, nearestIntDist_add_int, h1]
  rw [show ((1 : ℤ) : ℝ) * (1 / 2) = 1 / 2 by norm_num]
  apply nearestIntDist_ge <;> norm_num

/-- **R2, mod-2 case (strongest witness).** If every coordinate is odd, then `ML v ≥ 1/2` — the
maximum possible. A fortiori R2 holds. -/
theorem ML_ge_half_of_all_odd {k : ℕ} (v : Fin (k + 1) → ℤ) (h : ∀ i, ¬ (2 ∣ v i)) :
    (1 / 2 : ℝ) ≤ ML v :=
  ML_ge_of_witness v (1 / 2) (1 / 2) (fun i => one_half_le_nid_div2 (v i) (h i))

/-- For `n` not divisible by `3`, the witness `t = 1/3` puts `n·t` at distance exactly `1/3` from
the integers: `1/3 ≤ ‖n/3‖`. (Sharper than the `2/7` modular bound.) -/
theorem one_third_le_nid_div3 (n : ℤ) (h : ¬ (3 ∣ n)) :
    (1 / 3 : ℝ) ≤ nearestIntDist ((n : ℝ) * (1 / 3)) := by
  have h0 : n % 3 ≠ 0 := fun hc => h (Int.dvd_of_emod_eq_zero hc)
  have hge : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hr1 : (1 : ℝ) ≤ ((n % 3 : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ n % 3)
  have hr2 : ((n % 3 : ℤ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : n % 3 ≤ 2)
  -- shift `n/3` by the integer `n / 3`, leaving the residue part `(n % 3)/3`
  have hdecomp : (n : ℝ) * (1 / 3) = ((n % 3 : ℤ) : ℝ) * (1 / 3) + ((n / 3 : ℤ) : ℝ) := by
    have he : (n % 3 : ℤ) + 3 * (n / 3) = n := Int.emod_add_ediv n 3
    have hc : (n : ℝ) = ((n % 3 : ℤ) : ℝ) + 3 * ((n / 3 : ℤ) : ℝ) := by exact_mod_cast he.symm
    rw [hc]; ring
  rw [hdecomp, nearestIntDist_add_int, mul_one_div]
  -- all four `nearestIntDist_ge` obligations are linear in `(n%3)/3 ∈ [1/3, 2/3]`
  apply nearestIntDist_ge <;> linarith

/-- **General modular witness.** If `n`'s residue mod `m` is "far from `0`" in the strong sense
`m ≤ 3·(n%m) ≤ 2m` (i.e. `‖(n%m)/m‖ ≥ 1/3`), the witness `t = 1/m` gives `‖n/m‖ ≥ 1/3`. This
unifies every modular family: mod-3 (res `1,2`), mod-5 (res `2,3`), mod-8 (res `3,4,5`), … -/
theorem nid_div_m_ge_third (n m : ℤ) (hm : 0 < m)
    (h1 : m ≤ 3 * (n % m)) (h2 : 3 * (n % m) ≤ 2 * m) :
    (1 / 3 : ℝ) ≤ nearestIntDist ((n : ℝ) * (1 / (m : ℝ))) := by
  have hge : 0 ≤ n % m := Int.emod_nonneg n (by omega)
  have hlt : n % m < m := Int.emod_lt_of_pos n hm
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdecomp : (n : ℝ) * (1 / (m : ℝ))
      = ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) + ((n / m : ℤ) : ℝ) := by
    have he : (n % m : ℤ) + m * (n / m) = n := Int.emod_add_ediv n m
    have hc : (n : ℝ) = ((n % m : ℤ) : ℝ) + (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast he.symm
    have hcast : ((n / m : ℤ) : ℝ) = ((n / m : ℤ) : ℝ) * ((m : ℝ) * (1 / (m : ℝ))) := by
      rw [mul_one_div, div_self (ne_of_gt hmr), mul_one]
    rw [hcast, hc]; ring
  rw [hdecomp, nearestIntDist_add_int, mul_one_div]
  apply nearestIntDist_ge
  · have : (0 : ℝ) ≤ ((n % m : ℤ) : ℝ) := by exact_mod_cast hge
    positivity
  · rw [div_lt_one hmr]; exact_mod_cast hlt
  · rw [le_div_iff₀ hmr]
    have : (m : ℝ) ≤ 3 * ((n % m : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  · have h2r : (3 : ℝ) * ((n % m : ℤ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h2
    have hym : ((n % m : ℤ) : ℝ) / (m : ℝ) ≤ 2 / 3 := by rw [div_le_iff₀ hmr]; linarith
    linarith

/-- **R2 via any modulus (unified).** If there is a modulus `m` at which every coordinate's residue
is far from `0` (`m ≤ 3·(vᵢ%m) ≤ 2m`), then `ML v ≥ 1/3` — clearing R2 outright. Subsumes the
mod-3/5/7/8 families in a single statement. -/
theorem ML_ge_third_of_residues {k : ℕ} (v : Fin (k + 1) → ℤ) (m : ℤ) (hm : 0 < m)
    (h : ∀ i, m ≤ 3 * (v i % m) ∧ 3 * (v i % m) ≤ 2 * m) :
    (1 / 3 : ℝ) ≤ ML v :=
  ML_ge_of_witness v (1 / (m : ℝ)) (1 / 3)
    (fun i => nid_div_m_ge_third (v i) m hm (h i).1 (h i).2)

/-- **R2 via a SCALED witness `t = a/m` (sharp, maximal coverage).** If every coordinate's *scaled*
residue `(vᵢ·a) % m` is far from `0` (`m ≤ 3·((vᵢ·a)%m) ≤ 2m`), then `ML v ≥ 1/3`. Strictly extends
`ML_ge_third_of_residues` (take `a = 1`) and reaches triples no unscaled `t = 1/m` witness can (a
small coordinate like `1` forces `m = 3` unscaled, but a scaled multiplier opens other moduli).
Reduces in one line to the unscaled lemma applied at `vᵢ·a`. -/
theorem ML_ge_third_of_scaled_residues {k : ℕ} (v : Fin (k + 1) → ℤ) (a m : ℤ) (hm : 0 < m)
    (h : ∀ i, m ≤ 3 * ((v i * a) % m) ∧ 3 * ((v i * a) % m) ≤ 2 * m) :
    (1 / 3 : ℝ) ≤ ML v := by
  apply ML_ge_of_witness v ((a : ℝ) / (m : ℝ)) (1 / 3)
  intro i
  have heq : (v i : ℝ) * ((a : ℝ) / (m : ℝ)) = ((v i * a : ℤ) : ℝ) * (1 / (m : ℝ)) := by
    push_cast; ring
  rw [heq]
  exact nid_div_m_ge_third (v i * a) m hm (h i).1 (h i).2

/-- **R2, mod-3 case (sharp).** If no coordinate of the speed vector is divisible by `3`, then
`ML v ≥ 1/3`, witnessed by `t = 1/3`. In particular `ML v ≥ 1/3 ≥ 1/3 − 3/(4s)` for every sum `s`,
so the covering-radius inequality R2 holds outright on this case. -/
theorem ML_ge_third_of_not_dvd3 {k : ℕ} (v : Fin (k + 1) → ℤ) (h : ∀ i, ¬ (3 ∣ v i)) :
    (1 / 3 : ℝ) ≤ ML v := by
  refine le_trans ?_ (gap_le_ML v (1 / 3))
  apply le_gap
  intro i
  exact one_third_le_nid_div3 (v i) (h i)

/-- **R2 holds on the mod-3 case.** For a positive triple with no coordinate divisible by `3`, the
covering-radius inequality `ML ≥ 1/3 − 3/(4s)` follows from `ML ≥ 1/3`. -/
theorem R2_of_not_dvd3 (p q r : ℤ) (hs : 0 < p + q + r)
    (h : ¬ (3 ∣ p) ∧ ¬ (3 ∣ q) ∧ ¬ (3 ∣ r)) :
    (1 : ℝ) / 3 - 3 / (4 * ((p + q + r : ℤ) : ℝ)) ≤ ML ![p, q, r] := by
  have hsr : (0 : ℝ) < ((p + q + r : ℤ) : ℝ) := by exact_mod_cast hs
  obtain ⟨hp, hq, hr⟩ := h
  have hnd : ∀ i, ¬ (3 ∣ (![p, q, r] : Fin 3 → ℤ) i) := by
    intro i; fin_cases i
    · simpa using hp
    · simpa using hq
    · simpa using hr
  have hML : (1 / 3 : ℝ) ≤ ML ![p, q, r] := ML_ge_third_of_not_dvd3 _ hnd
  have hpos : (0 : ℝ) ≤ 3 / (4 * ((p + q + r : ℤ) : ℝ)) := by positivity
  linarith

end LRSpectrumFull
