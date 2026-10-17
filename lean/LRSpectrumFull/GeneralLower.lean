/-
# Milestone 9: the general two-runner lower bound `D(p,q) ≤ 1/(2(p+q))`

For *every* coprime pair `(p, q)` with `p` odd and `p+q` odd, the
view-obstruction D-value satisfies

    D(p, q) ≤ 1 / (2(p+q))

(equivalently `ML(p,q) ≥ (p+q−1)/(2(p+q))`). This is the "achievability"
half of the Cusick–Pomerance value `D₂(p,q) = 1/(2(p+q))`: a single
well-chosen time witnesses loneliness at least `(p+q−1)/(2(p+q))`.

The witness time is `t* = s/(2(p+q))`, where `s` is the residue making
both runners land at distance exactly `(p+q−1)/(2(p+q))` from the
integers — i.e. `p·s ≡ p+q−1` and `q·s ≡ p+q+1  (mod 2(p+q))`.
Such `s` exists because `gcd(p, 2(p+q)) = 1` (as `p` is odd and coprime
to `q`): Bézout gives `a·p + b·2(p+q) = 1`, and `s := a·(p+q−1)` works.

(For pairs with `q` odd instead, apply the result to `(q, p)` —
`gap`/`ML`/`D` are symmetric in the two speeds.)
-/

import LRSpectrumFull.DValue
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull

/-- **Witness residue.** For `p` odd, `p+q` odd, `gcd(p,q)=1`, there is an
integer `s` with `p·s ≡ p+q−1` and `q·s ≡ p+q+1` modulo `2(p+q)`. -/
theorem two_runner_witness (p q : ℕ) (hpodd : Odd p) (hmodd : Odd (p + q))
    (hcop : Nat.Coprime p q) :
    ∃ s : ℤ, (2 * ((p : ℤ) + q)) ∣ ((p : ℤ) * s - ((p : ℤ) + q - 1)) ∧
             (2 * ((p : ℤ) + q)) ∣ ((q : ℤ) * s - ((p : ℤ) + q + 1)) := by
  -- coprimality of p with 2(p+q)
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hcop2 : IsCoprime (p : ℤ) 2 := by
    obtain ⟨k, hk⟩ := hpodd
    refine ⟨1, -(k : ℤ), ?_⟩
    have hpk : (p : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
    rw [hpk]; ring
  have hcopm : IsCoprime (p : ℤ) ((p : ℤ) + q) := by
    have h := hcopZ.add_mul_left_right 1
    rwa [mul_one, add_comm] at h
  obtain ⟨a, b, hab⟩ := hcop2.mul_right hcopm
  -- p+q-1 is even
  obtain ⟨c, hc⟩ := hmodd
  have he : (p : ℤ) + q - 1 = 2 * (c : ℤ) := by
    have hpc : ((p : ℤ) + q) = 2 * (c : ℤ) + 1 := by exact_mod_cast hc
    rw [hpc]; ring
  refine ⟨a * ((p : ℤ) + q - 1), ?_, ?_⟩
  · -- p·s ≡ p+q-1
    exact ⟨-b * ((p : ℤ) + q - 1), by linear_combination ((p : ℤ) + q - 1) * hab⟩
  · -- q·s ≡ p+q+1, via div1 and (p+q)·s divisibility
    have div1 : (2 * ((p : ℤ) + q)) ∣ ((p : ℤ) * (a * ((p : ℤ) + q - 1)) - ((p : ℤ) + q - 1)) :=
      ⟨-b * ((p : ℤ) + q - 1), by linear_combination ((p : ℤ) + q - 1) * hab⟩
    have divM : (2 * ((p : ℤ) + q)) ∣ (((p : ℤ) + q) * (a * ((p : ℤ) + q - 1))) :=
      ⟨a * (c : ℤ), by rw [he]; ring⟩
    have key : (q : ℤ) * (a * ((p : ℤ) + q - 1)) - ((p : ℤ) + q + 1)
        = (((p : ℤ) + q) * (a * ((p : ℤ) + q - 1)))
          - ((p : ℤ) * (a * ((p : ℤ) + q - 1)) - ((p : ℤ) + q - 1))
          - 2 * ((p : ℤ) + q) := by ring
    rw [key]
    exact dvd_sub (dvd_sub divM div1) (dvd_refl _)

/-- The speed pair `(p, q)` as `Fin 2 → ℤ`. -/
def vpair (p q : ℕ) : Fin 2 → ℤ := ![(p : ℤ), (q : ℤ)]

@[simp] theorem vpair_zero (p q : ℕ) : ((vpair p q 0 : ℤ) : ℝ) = (p : ℝ) := by simp [vpair]
@[simp] theorem vpair_one (p q : ℕ) : ((vpair p q 1 : ℤ) : ℝ) = (q : ℝ) := by simp [vpair]

/-- **General two-runner lower bound.** For coprime `(p, q)` with `p` odd
and `p+q` odd, `D(p, q) ≤ 1/(2(p+q))` — the achievability half of
Cusick–Pomerance `D₂(p,q) = 1/(2(p+q))`. -/
theorem exists_gap_ge_general (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpodd : Odd p) (hmodd : Odd (p + q)) (hcop : Nat.Coprime p q) :
    ∃ t : ℝ, ((p : ℝ) + q - 1) / (2 * ((p : ℝ) + q)) ≤ gap (vpair p q) t := by
  obtain ⟨s, hd1, hd2⟩ := two_runner_witness p q hpodd hmodd hcop
  obtain ⟨w1, hw1⟩ := hd1
  obtain ⟨w2, hw2⟩ := hd2
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hMpos : (0 : ℝ) < (p : ℝ) + q := by linarith
  have hMne : (2 * ((p : ℝ) + q)) ≠ 0 := by positivity
  -- cast the two divisibility witnesses to ℝ
  have hc1 : (p : ℝ) * (s : ℝ) = ((p : ℝ) + q - 1) + 2 * ((p : ℝ) + q) * (w1 : ℝ) := by
    have : (p : ℤ) * s = ((p : ℤ) + q - 1) + 2 * ((p : ℤ) + q) * w1 := by linarith [hw1]
    exact_mod_cast this
  have hc2 : (q : ℝ) * (s : ℝ) = ((p : ℝ) + q + 1) + 2 * ((p : ℝ) + q) * (w2 : ℝ) := by
    have : (q : ℤ) * s = ((p : ℤ) + q + 1) + 2 * ((p : ℤ) + q) * w2 := by linarith [hw2]
    exact_mod_cast this
  -- evaluate both runners at t* = s / (2(p+q))
  have e0 : (p : ℝ) * ((s : ℝ) / (2 * ((p : ℝ) + q)))
      = ((p : ℝ) + q - 1) / (2 * ((p : ℝ) + q)) + (w1 : ℝ) := by
    field_simp
    linear_combination hc1
  have e1 : (q : ℝ) * ((s : ℝ) / (2 * ((p : ℝ) + q)))
      = ((p : ℝ) + q + 1) / (2 * ((p : ℝ) + q)) + (w2 : ℝ) := by
    field_simp
    linear_combination hc2
  refine ⟨(s : ℝ) / (2 * ((p : ℝ) + q)), ?_⟩
  apply le_gap
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [vpair_zero, e0, nearestIntDist_add_int]
    apply nearestIntDist_ge
    · apply div_nonneg (by linarith) (by positivity)
    · rw [div_lt_one (by positivity)]; linarith
    · exact le_refl _
    · rw [le_sub_iff_add_le, ← add_div, div_le_one (by positivity)]; linarith
  · rw [vpair_one, e1, nearestIntDist_add_int]
    apply nearestIntDist_ge
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
    · gcongr; linarith
    · rw [le_sub_iff_add_le, ← add_div, div_le_one (by positivity)]; linarith

theorem D_le_general (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpodd : Odd p) (hmodd : Odd (p + q)) (hcop : Nat.Coprime p q) :
    D (vpair p q) ≤ 1 / (2 * ((p : ℝ) + q)) := by
  have hMpos : (0 : ℝ) < (p : ℝ) + q := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  obtain ⟨t, hgap⟩ := exists_gap_ge_general p q hp hq hpodd hmodd hcop
  have hML : ((p : ℝ) + q - 1) / (2 * ((p : ℝ) + q)) ≤ ML (vpair p q) :=
    le_trans hgap (gap_le_ML _ _)
  have hval : (1 : ℝ) / 2 - ((p : ℝ) + q - 1) / (2 * ((p : ℝ) + q)) = 1 / (2 * ((p : ℝ) + q)) := by
    have : (2 * ((p : ℝ) + q)) ≠ 0 := by positivity
    field_simp; ring
  simp only [D]
  linarith

end LRSpectrumFull
