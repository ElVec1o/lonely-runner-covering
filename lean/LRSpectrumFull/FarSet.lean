/-
# The "far set" and the odd-relation loneliness bound (formalization nucleus)

This file formalizes the elementary nucleus of the character-sum argument
behind the effective-wall lemma. The argument shows

    v₁,…,vₙ nonzero with no all-odd integer relation  ⟹  ML(v) ≥ 1/4

via the identity `|{t : ∀i ‖vᵢt‖ ≥ 1/4}| = 2⁻ⁿ + Σ(odd-relation corrections)`,
whose full proof (a finite Fourier/character sum over `ℤ/4L`) is a larger
effort. Here we bank the *completable* atoms it rests on:

* `IsFar x` — the predicate `1/4 ≤ ‖x‖` ("runner `x` is far from the origin");
* `le_nearestIntDist_iff` — the exact reformulation of `c ≤ ‖x‖` via `Int.fract`;
* `isFar_iff` — `IsFar x ↔ Int.fract x ∈ [1/4, 3/4]`;
* `nearestIntDist_half`, `isFar_half` — the "parking" value `‖1/2‖ = 1/2`;
* `exists_far_single` — the `n = 1` case (one runner parks at `1/2`).

The general theorem is stated as `OddRelationBound` for reference; its proof
(the counting core) is not discharged here. No `sorry`.
-/
import LRSpectrumFull.NearestInteger
import LRSpectrumFull.Subtorus
import Mathlib.Tactic.Linarith

namespace LRSpectrumFull

/-- Runner value `x` is **far**: at least `1/4` from the nearest integer. -/
def IsFar (x : ℝ) : Prop := (1 : ℝ) / 4 ≤ nearestIntDist x

/-- Exact reformulation of a lower bound `c ≤ ‖x‖` (for `c ≤ 1/2`) in terms of
the fractional part: `x` is `≥ c` from `ℤ` iff `fract x ∈ [c, 1 − c]`. -/
theorem le_nearestIntDist_iff {x c : ℝ} :
    c ≤ nearestIntDist x ↔ c ≤ Int.fract x ∧ c ≤ 1 - Int.fract x := by
  unfold nearestIntDist
  exact le_min_iff

/-- `IsFar x ↔ fract x ∈ [1/4, 3/4]`. -/
theorem isFar_iff (x : ℝ) :
    IsFar x ↔ (1 : ℝ) / 4 ≤ Int.fract x ∧ Int.fract x ≤ 3 / 4 := by
  unfold IsFar
  rw [le_nearestIntDist_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- `‖1/2‖ = 1/2`: the deepest hole, where a free runner parks. -/
theorem nearestIntDist_half : nearestIntDist (1 / 2 : ℝ) = 1 / 2 := by
  have h1 : (1 / 2 : ℝ) ≤ nearestIntDist (1 / 2) :=
    nearestIntDist_ge (by norm_num) (by norm_num) (le_refl _) (by norm_num)
  have h2 := nearestIntDist_le_half (1 / 2 : ℝ)
  linarith

/-- The parking point is far. -/
theorem isFar_half : IsFar (1 / 2 : ℝ) := by
  unfold IsFar; rw [nearestIntDist_half]; norm_num

/-- Integer shifts preserve farness (`‖·‖` depends only on `fract`). -/
theorem isFar_add_int (x : ℝ) (k : ℤ) : IsFar (x + k) ↔ IsFar x := by
  unfold IsFar; rw [nearestIntDist_add_int]

/-- **`n = 1` case.** A single nonzero runner is far at `t = 1/(2v)` (it parks
at `1/2`), so `ML ≥ 1/4` trivially. The base case of the odd-relation bound. -/
theorem exists_far_single (v : ℤ) (hv : v ≠ 0) :
    ∃ t : ℝ, IsFar ((v : ℝ) * t) := by
  refine ⟨1 / (2 * v), ?_⟩
  have hvR : (v : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hv
  have : (v : ℝ) * (1 / (2 * v)) = 1 / 2 := by
    field_simp
  rw [this]; exact isFar_half

/-! ### The 2-adic parking core

The odd-relation bound is proven by a dyadic construction: one seeks `t = j/2^m`
(`j` odd) placing every `vᵢt` in the "middle half" mod `2^m`, where the runner is
far. The atom is `‖(odd)/4‖ = 1/4` — the deepest a runner of odd valuation parks
at level `m = 2`. When *all* speeds are odd this already gives a common far time
`t = 1/4`, the base case; the general case chooses `j` by a finite character sum
over `ℤ/2^m` (the counting core, not formalized here). -/

/-- `‖1/4‖ = 1/4`. -/
theorem nearestIntDist_quarter : nearestIntDist (1 / 4 : ℝ) = 1 / 4 := by
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]; norm_num

/-- `‖3/4‖ = 1/4`. -/
theorem nearestIntDist_three_quarter : nearestIntDist (3 / 4 : ℝ) = 1 / 4 := by
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]; norm_num

/-- **The parking atom:** an odd integer over `4` is exactly `1/4` from `ℤ`, hence
far. (`(4j+1)/4` has fractional part `1/4`; `(4j+3)/4` has `3/4`.) -/
theorem isFar_odd_div_four (w : ℤ) (hw : Odd w) : IsFar ((w : ℝ) / 4) := by
  unfold IsFar
  obtain ⟨k, rfl⟩ := hw
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · subst hj
    rw [show ((2 * (2 * j) + 1 : ℤ) : ℝ) / 4 = 1 / 4 + ((j : ℤ) : ℝ) by push_cast; ring,
      nearestIntDist_add_int]
    exact le_of_eq nearestIntDist_quarter.symm
  · subst hj
    rw [show ((2 * (2 * j + 1) + 1 : ℤ) : ℝ) / 4 = 3 / 4 + ((j : ℤ) : ℝ) by push_cast; ring,
      nearestIntDist_add_int]
    exact le_of_eq nearestIntDist_three_quarter.symm

/-- **All-odd speeds ⟹ `ML ≥ 1/4`.** If every runner speed is odd, the common
time `t = 1/4` places every runner exactly `1/4` from the integers. This is the
`m = 2` base case of the 2-adic construction behind the odd-relation bound (and,
by rescaling `t ↦ t/2^E`, extends to speeds of a common `2`-adic valuation). -/
theorem exists_far_of_forall_odd {n : ℕ} (v : Fin n → ℤ) (h : ∀ i, Odd (v i)) :
    ∃ t : ℝ, ∀ i, IsFar ((v i : ℝ) * t) := by
  refine ⟨1 / 4, fun i => ?_⟩
  rw [show (v i : ℝ) * (1 / 4) = (v i : ℝ) / 4 by ring]
  exact isFar_odd_div_four (v i) (h i)

/-- **The parking atom, sharpened.** `v/4` is far whenever `4 ∤ v` (i.e. `v mod 4 ∈ {1,2,3}`,
giving fractional part `1/4`, `1/2`, or `3/4`). -/
theorem isFar_of_not_dvd_four (v : ℤ) (h : ¬ ((4 : ℤ) ∣ v)) : IsFar ((v : ℝ) / 4) := by
  have hsplit : (v : ℝ) / 4 = ((v % 4 : ℤ) : ℝ) / 4 + ((v / 4 : ℤ) : ℝ) := by
    have key : (v : ℝ) = 4 * ((v / 4 : ℤ) : ℝ) + ((v % 4 : ℤ) : ℝ) := by
      have h4 : v = 4 * (v / 4) + v % 4 := by omega
      exact_mod_cast h4
    rw [key]; ring
  rw [hsplit, isFar_add_int]
  have hr : v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by
    have h0 : 0 ≤ v % 4 := Int.emod_nonneg v (by norm_num)
    have h1 : v % 4 < 4 := Int.emod_lt_of_pos v (by norm_num)
    have h2 : v % 4 ≠ 0 := fun hc => h (Int.dvd_of_emod_eq_zero hc)
    omega
  unfold IsFar
  rcases hr with hr | hr | hr
  · rw [hr, show (((1 : ℤ) : ℝ) / 4) = (1 : ℝ) / 4 by norm_num]
    exact le_of_eq nearestIntDist_quarter.symm
  · rw [hr, show (((2 : ℤ) : ℝ) / 4) = (1 : ℝ) / 2 by norm_num, nearestIntDist_half]; norm_num
  · rw [hr, show (((3 : ℤ) : ℝ) / 4) = (3 : ℝ) / 4 by norm_num]
    exact le_of_eq nearestIntDist_three_quarter.symm

/-- **No runner divisible by `4` ⟹ `ML ≥ 1/4`.** The common time `t = 1/4` works; every `ML < 1/4`
configuration must therefore contain a runner `≡ 0 (mod 4)`. Generalizes `exists_far_of_forall_odd`. -/
theorem exists_far_of_no_mul_four {n : ℕ} (v : Fin n → ℤ) (h : ∀ i, ¬ ((4 : ℤ) ∣ v i)) :
    ∃ t : ℝ, ∀ i, IsFar ((v i : ℝ) * t) := by
  refine ⟨1 / 4, fun i => ?_⟩
  rw [show (v i : ℝ) * (1 / 4) = (v i : ℝ) / 4 by ring]
  exact isFar_of_not_dvd_four (v i) (h i)

/-- **Mod-3 parking atom.** `v/3` is far whenever `3 ∤ v` (`v mod 3 ∈ {1,2}`, fractional part
`1/3` or `2/3`, both `1/3 ≥ 1/4` from the integers). -/
theorem isFar_of_not_dvd_three (v : ℤ) (h : ¬ ((3 : ℤ) ∣ v)) : IsFar ((v : ℝ) / 3) := by
  have hsplit : (v : ℝ) / 3 = ((v % 3 : ℤ) : ℝ) / 3 + ((v / 3 : ℤ) : ℝ) := by
    have key : (v : ℝ) = 3 * ((v / 3 : ℤ) : ℝ) + ((v % 3 : ℤ) : ℝ) := by
      have h3 : v = 3 * (v / 3) + v % 3 := by omega
      exact_mod_cast h3
    rw [key]; ring
  rw [hsplit, isFar_add_int]
  have hr : v % 3 = 1 ∨ v % 3 = 2 := by
    have h0 : 0 ≤ v % 3 := Int.emod_nonneg v (by norm_num)
    have h1 : v % 3 < 3 := Int.emod_lt_of_pos v (by norm_num)
    have h2 : v % 3 ≠ 0 := fun hc => h (Int.dvd_of_emod_eq_zero hc)
    omega
  unfold IsFar
  rcases hr with hr | hr
  · rw [hr, show (((1 : ℤ) : ℝ) / 3) = (1 : ℝ) / 3 by norm_num]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [hr, show (((2 : ℤ) : ℝ) / 3) = (2 : ℝ) / 3 by norm_num]
    exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **No runner divisible by `3` ⟹ `ML ≥ 1/4`** (in fact `≥ 1/3`), via `t = 1/3`. So every
`ML < 1/4` configuration contains a runner `≡ 0 (mod 3)` — jointly with `exists_far_of_no_mul_four`,
a runner `≡ 0 (mod 3)` *and* one `≡ 0 (mod 4)`. -/
theorem exists_far_of_no_mul_three {n : ℕ} (v : Fin n → ℤ) (h : ∀ i, ¬ ((3 : ℤ) ∣ v i)) :
    ∃ t : ℝ, ∀ i, IsFar ((v i : ℝ) * t) := by
  refine ⟨1 / 3, fun i => ?_⟩
  rw [show (v i : ℝ) * (1 / 3) = (v i : ℝ) / 3 by ring]
  exact isFar_of_not_dvd_three (v i) (h i)

/-! ### The general 1/4-band parking engine

Every "parking" bound is a special case of a single scaled-residue witness: with `t = a/m`, a runner
`vᵢ` is far exactly when the residue `vᵢ·a mod m` lands in the closed middle band `[m/4, 3m/4]`.
This is the `1/4`-analogue of `D_lt_of_scaled_residues` (the `2/7`-band engine). The clean parkings
`(a,m) = (1,3), (1,4)` are instances; so are the next tier `(2,7), (3,8)`. -/

/-- **General 1/4-band parking atom.** If the residue `n mod m` lies in `[m/4, 3m/4]` — encoded as
`m ≤ 4·(n mod m)` and `m ≤ 4·(m − n mod m)` — then `n/m` is far. -/
theorem quarter_le_nearestIntDist_div (n m : ℤ) (hm : 0 < m)
    (h1 : m ≤ 4 * (n % m)) (h2 : m ≤ 4 * (m - n % m)) :
    IsFar ((n : ℝ) * (1 / (m : ℝ))) := by
  have hmne : (m : ℤ) ≠ 0 := by omega
  have hs0 : 0 ≤ n % m := Int.emod_nonneg n hmne
  have hs1 : n % m < m := Int.emod_lt_of_pos n hm
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne' : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hdecomp : (n : ℝ) * (1 / (m : ℝ))
      = ((n % m : ℤ) : ℝ) * (1 / (m : ℝ)) + ((n / m : ℤ) : ℝ) := by
    have he : (n % m : ℤ) + m * (n / m) = n := Int.emod_add_mul_ediv n m
    have hc : (n : ℝ) = ((n % m : ℤ) : ℝ) + (m : ℝ) * ((n / m : ℤ) : ℝ) := by
      exact_mod_cast he.symm
    have hcast : ((n / m : ℤ) : ℝ) = ((n / m : ℤ) : ℝ) * ((m : ℝ) * (1 / (m : ℝ))) := by
      rw [mul_one_div, div_self hmne', mul_one]
    rw [hcast, hc]; ring
  unfold IsFar
  rw [hdecomp, nearestIntDist_add_int, mul_one_div]
  have hr0 : (0 : ℝ) ≤ ((n % m : ℤ) : ℝ) := by exact_mod_cast hs0
  refine nearestIntDist_ge (div_nonneg hr0 hm'.le) ?_ ?_ ?_
  · rw [div_lt_one hm']; exact_mod_cast hs1
  · rw [le_div_iff₀ hm']
    have hcast1 : (m : ℝ) ≤ 4 * ((n % m : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  · have hb : ((n % m : ℤ) : ℝ) / (m : ℝ) ≤ 3 / 4 := by
      rw [div_le_iff₀ hm']
      have hcast2 : (m : ℝ) ≤ 4 * ((m : ℝ) - ((n % m : ℤ) : ℝ)) := by exact_mod_cast h2
      linarith
    linarith

/-- **Scaled parking family.** With witness `t = a/m`, if every `vᵢ·a mod m` lies in the middle band
`[m/4, 3m/4]` then `t` is a common far time. This single lemma subsumes all clean and second-tier
parkings; the `mod-3`, `mod-4`, `t = 2/7`, `t = 3/8` bounds are the instances `(a,m) =
(1,3),(1,4),(2,7),(3,8)`. -/
theorem exists_far_of_scaled_residues {n : ℕ} (v : Fin n → ℤ) (a m : ℤ) (hm : 0 < m)
    (h : ∀ i, m ≤ 4 * (v i * a % m) ∧ m ≤ 4 * (m - v i * a % m)) :
    ∃ t : ℝ, ∀ i, IsFar ((v i : ℝ) * t) := by
  refine ⟨(a : ℝ) / (m : ℝ), fun i => ?_⟩
  have key : (v i : ℝ) * ((a : ℝ) / (m : ℝ)) = ((v i * a : ℤ) : ℝ) * (1 / (m : ℝ)) := by
    push_cast; ring
  rw [key]
  exact quarter_le_nearestIntDist_div (v i * a) m hm (h i).1 (h i).2

/-- **The general statement** (the odd-relation loneliness bound), recorded for
reference. `a` ranges over integer relation vectors whose nonzero entries are
all odd; the hypothesis is that no nonzero such relation holds. The conclusion
is a common far time, i.e. `ML(v) ≥ 1/4`. The full proof (the `ℤ/2^m` counting
core) is not discharged in this file; `exists_far_of_forall_odd` is its base
case. -/
def OddRelationBound {n : ℕ} (v : Fin n → ℤ) : Prop :=
  (∀ a : Fin n → ℤ, (∀ i, a i ≠ 0 → Odd (a i)) → (∑ i, a i * v i) = 0 →
      (∀ i, a i = 0)) →
    ∃ t : ℝ, ∀ i, IsFar ((v i : ℝ) * t)

end LRSpectrumFull
