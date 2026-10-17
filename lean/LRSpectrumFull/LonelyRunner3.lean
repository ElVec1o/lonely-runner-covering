/-
# The Lonely Runner Conjecture for three moving runners (machine-checked)

Assembles the library's spectral machinery into the classical statement: for any
three nonzero integer speeds there is a time at which all three runners are at
distance `≥ 1/4` from the stationary runner — `ML v ≥ 1/4`, i.e. `D v ≤ 1/4`.
This is the Lonely Runner Conjecture for four runners (three moving), proved by
Betke–Wills (1972) and Cusick (1974); the integer-speed form is the standard
combinatorial statement (the real-speed case reduces to it classically).

Also included, as the sharp companion (Chen's classification, cf. paper_DELTA2
Prop 2.2): the *only* value of `D` above `3/14` is `1/4`, attained exactly on the
`(g, 2g, 3g)`-shaped triples — so `1/4` is an isolated point of the three-runner
spectrum, with the gap `(3/14, 1/4)` empty.

No `sorry`.
-/
import LRSpectrumFull.Delta2CaseRoute
import LRSpectrumFull.PermInvariance
import LRSpectrumFull.SpectrumSymmetry
import LRSpectrumFull.WeylNormalize
import LRSpectrumFull.Spectrum3
import LRSpectrumFull.Delta2Boundary

namespace LRSpectrumFull

/-- A `(g,2g,3g)`-shaped triple has `D = 1/4` exactly: scale down by `g`
(`D_scale`), reduce to absolute values (`D_abs3`), and permute to `(1,2,3)`
(`D_swap*` + `D_v123_eq`). -/
theorem shaped123_D_eq (a b c : ℤ) (h : Shaped123 a b c) : D ![a, b, c] = 1 / 4 := by
  obtain ⟨g, hg, ga, gb, gc, habc⟩ := shaped123_factor h
  set a' := a / g with ha'def
  set b' := b / g with hb'def
  set c' := c / g with hc'def
  have hae : a = g * a' := (Int.mul_ediv_cancel' ga).symm
  have hbe : b = g * b' := (Int.mul_ediv_cancel' gb).symm
  have hce : c = g * c' := (Int.mul_ediv_cancel' gc).symm
  rw [hae, hbe, hce]
  have hfun : (![g * a', g * b', g * c'] : Fin 3 → ℤ) = fun i => g * (![a', b', c'] i) := by
    funext i; fin_cases i <;> rfl
  rw [hfun, D_scale _ g hg, ← D_abs3]
  have hmema : |a'| = 1 ∨ |a'| = 2 ∨ |a'| = 3 := by
    have hm : |a'| ∈ ({|a'|, |b'|, |c'|} : Multiset ℤ) := by simp
    rw [habc] at hm
    simpa using hm
  have hmemb : |b'| = 1 ∨ |b'| = 2 ∨ |b'| = 3 := by
    have hm : |b'| ∈ ({|a'|, |b'|, |c'|} : Multiset ℤ) := by simp
    rw [habc] at hm
    simpa using hm
  have hmemc : |c'| = 1 ∨ |c'| = 2 ∨ |c'| = 3 := by
    have hm : |c'| ∈ ({|a'|, |b'|, |c'|} : Multiset ℤ) := by simp
    rw [habc] at hm
    simpa using hm
  rcases hmema with h1 | h1 | h1 <;> rcases hmemb with h2 | h2 | h2 <;>
    rcases hmemc with h3 | h3 | h3 <;> rw [h1, h2, h3] at habc ⊢ <;>
    first
      | exact absurd habc (by decide)
      | exact D_v123_eq
      | (rw [D_swap12 1 2 3]; exact D_v123_eq)
      | (rw [D_swap01 1 2 3]; exact D_v123_eq)
      | (rw [D_swap02 1 2 3]; exact D_v123_eq)
      | (rw [D_swap02 1 3 2, D_swap12 1 2 3]; exact D_v123_eq)
      | (rw [D_swap02 2 1 3, D_swap01 1 2 3]; exact D_v123_eq)

/-- Every full-support integer triple has `D ≤ 1/4`. -/
theorem D_triple_le_quarter (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    D ![a, b, c] ≤ 1 / 4 := by
  by_cases h : Shaped123 a b c
  · exact le_of_eq (shaped123_D_eq a b c h)
  · exact (D_triple_le a b c ha hb hc h).trans (by norm_num)

/-- **The Lonely Runner Conjecture for three moving runners.** For any nonzero
integer speeds `v : Fin 3 → ℤ` there is a time at which all three runners are at
distance `≥ 1/4` from the origin: `ML v ≥ 1/4`. -/
theorem lonely_runner_three (v : Fin 3 → ℤ) (hv : ∀ i, v i ≠ 0) : 1 / 4 ≤ ML v := by
  have hv3 : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  have hD : D v ≤ 1 / 4 := by
    rw [hv3]; exact D_triple_le_quarter _ _ _ (hv 0) (hv 1) (hv 2)
  unfold D at hD
  linarith

/-- Sharpness: the bound `1/4` is attained by the speeds `(1,2,3)`. -/
theorem lonely_runner_three_sharp : ML v123 = 1 / 4 := by
  have h := D_v123_eq
  unfold D at h
  linarith

/-- **The top of the three-runner spectrum (Chen's classification).** Every
full-support triple has `D = 1/4` (exactly the `(g,2g,3g)`-shaped ones) or
`D ≤ 3/14`: the value `1/4` is isolated, with the gap `(3/14, 1/4)` empty. -/
theorem spectrum3_top (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    D ![a, b, c] = 1 / 4 ∨ D ![a, b, c] ≤ 3 / 14 := by
  by_cases h : Shaped123 a b c
  · exact Or.inl (shaped123_D_eq a b c h)
  · exact Or.inr (D_triple_le a b c ha hb hc h)

/-- **Three-runner rigidity — the stability-lemma base case.** A full-support triple attains the
extremal value `D = 1/4` **iff** it is `(1,2,3)`-shaped (`{|a|,|b|,|c|} = {g,2g,3g}`). Immediate from
Chen's isolation: the gap `(3/14, 1/4)` being empty turns `¬Shaped123 ⟹ D ≤ 3/14` (`D_triple_le`)
into `D = 1/4 ⟹ Shaped123`. For coprime speeds this pins the extremal uniquely to `(1,2,3)`. -/
theorem D_quarter_iff_shaped123 (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    D ![a, b, c] = 1 / 4 ↔ Shaped123 a b c := by
  refine ⟨fun h => ?_, shaped123_D_eq a b c⟩
  by_contra hne
  have hle := D_triple_le a b c ha hb hc hne
  rw [h] at hle
  norm_num at hle

/-- The maximum-loneliness form of three-runner rigidity: `ML ![a,b,c] = 1/4 ↔ Shaped123 a b c`
(via `D = 1/2 − ML`). So the three-runner Lonely Runner bound is met **with equality** exactly by
the `(g,2g,3g)` configurations. -/
theorem ML_quarter_iff_shaped123 (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ML ![a, b, c] = 1 / 4 ↔ Shaped123 a b c := by
  rw [← D_quarter_iff_shaped123 a b c ha hb hc]
  unfold D
  constructor <;> intro h <;> linarith

-- axiom audit
#print axioms lonely_runner_three
#print axioms spectrum3_top
#print axioms D_quarter_iff_shaped123
#print axioms ML_quarter_iff_shaped123

/-- **Four runners, in the form the conjecture actually asserts.**  `lonely_runner_three` bounds a
supremum; the conjecture asserts that a time exists.  The two differ without attainment, which
`exists_gap_eq_ML` supplies: `gap v` is continuous and `[0,1]` is compact, so the supremum is met at
some `t`. -/
theorem four_runners_exists (v : Fin 3 → ℤ) (hv : ∀ i, v i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) := by
  obtain ⟨t, _, ht⟩ := exists_gap_eq_ML v
  have key : ∀ i, (1 : ℝ) / 4 ≤ nearestIntDist ((v i : ℝ) * t) := by
    intro i
    have hle : (1 : ℝ) / 4 ≤ gap v t := by rw [ht]; exact lonely_runner_three v hv
    exact le_trans hle (Finset.inf'_le _ (Finset.mem_univ i))
  -- `t = 0` is impossible: every speed sits exactly on an integer there
  have ht0 : t ≠ 0 := by
    intro h
    have := key 0
    rw [h, mul_zero, show (0:ℝ) = ((0:ℤ):ℝ) by norm_num, nearestIntDist_intCast] at this
    linarith
  refine ⟨|t|, abs_pos.mpr ht0, fun i => ?_⟩
  rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact key i
  · rw [he, show (v i : ℝ) * -t = -((v i : ℝ) * t) by ring, nearestIntDist_neg]
    exact key i

end LRSpectrumFull
