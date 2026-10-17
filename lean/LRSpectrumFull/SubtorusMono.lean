/-
# Milestone 15: rank-r monotonicity and runner-permutation invariance

Lifts the multi-runner monotonicity of Milestone 11 from the rank-1 tower
to the rank-`r` subtorus tower, and derives that the rank-`r` D-value
depends only on the *multiset* of runner speed-vectors (coordinate order
is irrelevant):

* `mgap_comp_le`, `mML_comp_le`, `mD_comp_le` — adding runners increases
  the rank-`r` D-value;
* `mD_perm` — `mD (v ∘ σ) = mD v` for any permutation `σ` of the runners.

No `sorry`.
-/

import LRSpectrumFull.Subtorus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

variable {k m r : ℕ}

/-- The rank-`r` gap is at most any single runner's nearest-integer distance. -/
theorem mgap_le (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) (i : Fin (k + 1)) :
    mgap v t ≤ nearestIntDist (∑ j, (v i j : ℝ) * t j) := by
  simp only [mgap]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- Adding runners can only decrease the rank-`r` gap. -/
theorem mgap_comp_le (v : Fin (m + 1) → Fin r → ℤ) (ι : Fin (k + 1) → Fin (m + 1))
    (t : Fin r → ℝ) : mgap v t ≤ mgap (v ∘ ι) t := by
  apply le_mgap
  intro i
  exact mgap_le v t (ι i)

/-- Maximum loneliness is antitone under adding runners. -/
theorem mML_comp_le (v : Fin (m + 1) → Fin r → ℤ) (ι : Fin (k + 1) → Fin (m + 1)) :
    mML v ≤ mML (v ∘ ι) := by
  unfold mML
  apply csSup_le (Set.range_nonempty (mgap v))
  rintro y ⟨t, rfl⟩
  exact le_trans (mgap_comp_le v ι t) (le_csSup (bddAbove_range_mgap (v ∘ ι)) ⟨t, rfl⟩)

/-- The rank-`r` D-value is monotone under adding runners. -/
theorem mD_comp_le (v : Fin (m + 1) → Fin r → ℤ) (ι : Fin (k + 1) → Fin (m + 1)) :
    mD (v ∘ ι) ≤ mD v := by
  have := mML_comp_le v ι; simp only [mD]; linarith

/-- **Permutation invariance (runners).** Permuting the runners leaves
the rank-`r` D-value unchanged — it depends only on the multiset of
speed-vectors. -/
theorem mD_perm (v : Fin (k + 1) → Fin r → ℤ) (σ : Equiv.Perm (Fin (k + 1))) :
    mD (v ∘ ⇑σ) = mD v := by
  apply le_antisymm
  · exact mD_comp_le v ⇑σ
  · have h := mD_comp_le (v ∘ ⇑σ) ⇑σ.symm
    rwa [show ((v ∘ ⇑σ) ∘ ⇑σ.symm) = v from by funext i; simp] at h

/-! ## A general reparametrization tool

Whenever one subtorus `w` is a bijective reparametrization of another `v`
(`mgap w t = mgap v (φ t)` for an equiv `φ` of the parameter space),
their D-values agree. The generator-permutation and shear invariances
below are instances of this. -/

/-- If `mgap w = mgap v ∘ φ` for a parameter-space equiv `φ`, then
`mML w = mML v`. -/
theorem mML_reparam (v w : Fin (k + 1) → Fin r → ℤ)
    (φ : (Fin r → ℝ) ≃ (Fin r → ℝ)) (h : ∀ t, mgap w t = mgap v (φ t)) :
    mML w = mML v := by
  unfold mML
  congr 1
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨φ t, (h t).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨φ.symm s, by rw [h, Equiv.apply_symm_apply]⟩

/-- The D-value version of `mML_reparam`. -/
theorem mD_reparam (v w : Fin (k + 1) → Fin r → ℤ)
    (φ : (Fin r → ℝ) ≃ (Fin r → ℝ)) (h : ∀ t, mgap w t = mgap v (φ t)) :
    mD w = mD v := by
  unfold mD
  rw [mML_reparam v w φ h]

/-! ## Generator-permutation invariance

Reindexing the `r` generators by a permutation `e` of `Fin r`
reparametrizes the subtorus; the D-value is unchanged. -/

/-- Reindexing the generators by `e` reparametrizes the gap by `e.symm`. -/
theorem mgap_gen_perm (v : Fin (k + 1) → Fin r → ℤ) (e : Equiv.Perm (Fin r))
    (t : Fin r → ℝ) :
    mgap (fun i j => v i (e j)) t = mgap v (fun j => t (e.symm j)) := by
  unfold mgap
  congr 1
  funext i
  congr 1
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

/-- Maximum loneliness is invariant under permuting the generators. -/
theorem mML_gen_perm (v : Fin (k + 1) → Fin r → ℤ) (e : Equiv.Perm (Fin r)) :
    mML (fun i j => v i (e j)) = mML v := by
  unfold mML
  congr 1
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fun j => t (e.symm j), (mgap_gen_perm v e t).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨fun j => s (e j), ?_⟩
    rw [mgap_gen_perm]
    congr 1
    funext j
    simp

/-- **Generator-permutation invariance.** The rank-`r` D-value does not
depend on the order of the `r` generators of the subtorus. -/
theorem mD_gen_perm (v : Fin (k + 1) → Fin r → ℤ) (e : Equiv.Perm (Fin r)) :
    mD (fun i j => v i (e j)) = mD v := by
  unfold mD
  rw [mML_gen_perm]

/-! ## Coordinate sign-flips (the `W(Bₙ)` hyperoctahedral symmetry)

Negating a single coordinate (runner) leaves `mD` unchanged, since
`‖-x‖ = ‖x‖`. With `mD_perm` (coordinate permutations) this gives the
full hyperoctahedral `W(Bₙ)` symmetry of the spectrum that the paper's
classification uses to reduce to a normal form. -/

/-- Negating the `i`-th runner leaves the gap unchanged. -/
theorem mgap_sign_flip (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) (τ : Fin r → ℝ) :
    mgap (Function.update v i (-(v i))) τ = mgap v τ := by
  unfold mgap
  congr 1
  funext c
  rcases eq_or_ne c i with h | h
  · subst h
    have hsum : (∑ j, (((Function.update v c (-(v c)) c) j : ℤ) : ℝ) * τ j)
        = -(∑ j, ((v c j : ℤ) : ℝ) * τ j) := by
      rw [Function.update_self, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Pi.neg_apply]
    rw [hsum, nearestIntDist_neg]
  · rw [Function.update_of_ne h]

/-- Maximum loneliness is invariant under negating a runner. -/
theorem mML_sign_flip (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) :
    mML (Function.update v i (-(v i))) = mML v := by
  unfold mML
  rw [funext (mgap_sign_flip v i)]

/-- **Sign-flip invariance.** `mD` is unchanged by negating any single
coordinate; with `mD_perm` this is full `W(Bₙ)` hyperoctahedral
invariance. -/
theorem mD_sign_flip (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) :
    mD (Function.update v i (-(v i))) = mD v := by
  unfold mD
  rw [mML_sign_flip]

/-! ## A degenerate exclusion: a zero coordinate-runner pins `mD = 1/2`

If some runner has the zero speed-vector, it sits at `0` for all
parameters, so the gap is identically `0`, `mML = 0`, and `mD = 1/2`.
Such a subtorus is trivially outside the band `(3/14, 1/4)` (a degenerate
sub-case of the `δ₂` classification). -/

/-- A zero coordinate-runner makes the gap identically `0`. -/
theorem mgap_zero_runner (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1))
    (h : v i = 0) (t : Fin r → ℝ) : mgap v t = 0 := by
  refine le_antisymm ?_ (mgap_nonneg v t)
  have hle := mgap_le v t i
  have hsum : (∑ j, ((v i j : ℝ)) * t j) = 0 := by simp [h]
  rw [hsum] at hle
  have h0 : nearestIntDist (0 : ℝ) = 0 := by simpa using nearestIntDist_intCast 0
  rwa [h0] at hle

theorem mML_zero_runner (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) (h : v i = 0) :
    mML v = 0 := by
  unfold mML
  rw [show Set.range (mgap v) = {0} from by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩; exact mgap_zero_runner v i h t
    · rintro rfl; exact ⟨0, mgap_zero_runner v i h 0⟩]
  exact csSup_singleton 0

/-- **Zero-runner exclusion.** A subtorus with a zero coordinate-runner
has `mD = 1/2`, hence is not in the band `(3/14, 1/4)`. -/
theorem mD_zero_runner (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) (h : v i = 0) :
    mD v = 1 / 2 := by
  unfold mD; rw [mML_zero_runner v i h]; ring

/-! ## A second degenerate exclusion: a constant generator column

If one generator column is constant `(a, …, a)` with `a ≠ 0`, then at the
parameter putting that generator at `1/(2a)` (others `0`) every runner is
at the deep hole `1/2`, so `mML = 1/2` and `mD = 0`. Such subtori are
trivially outside the band. (This is exactly why the `u = (1,1,1,1)`
representatives of Cases B, C have `mD = 0`.) -/

/-- A constant nonzero generator column forces `mD = 0` (the deep hole). -/
theorem mD_const_col (v : Fin (k + 1) → Fin r → ℤ) (j0 : Fin r) (a : ℤ) (ha : a ≠ 0)
    (h : ∀ i, v i j0 = a) : mD v = 0 := by
  have haR : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hge : (1 / 2 : ℝ) ≤ mML v := by
    refine le_trans ?_
      (mgap_le_mML v (Function.update (0 : Fin r → ℝ) j0 (1 / (2 * (a : ℝ)))))
    apply le_mgap
    intro i
    have e : (∑ j, ((v i j : ℝ)) * (Function.update (0 : Fin r → ℝ) j0 (1 / (2 * (a : ℝ)))) j)
        = 1 / 2 := by
      rw [Finset.sum_eq_single j0
        (fun j _ hj => by rw [Function.update_of_ne hj]; simp)
        (fun h0 => absurd (Finset.mem_univ j0) h0)]
      rw [Function.update_self, h i]
      field_simp
    rw [e]
    have h2 : nearestIntDist (1 / 2 : ℝ) = 1 / 2 := by
      have hf : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr (by norm_num)
      simp only [nearestIntDist, hf]; rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, min_self]
    rw [h2]
  have hle := mML_le_half v
  unfold mD; linarith

/-! ## Shear invariance (the elementary basis change `a ↦ a + b`)

Replacing the first generator `a` by `a + b` (a column operation, the
`T` generator of `SL₂(ℤ)`) reparametrizes the rank-2 subtorus and leaves
the D-value unchanged. With the generator swap (`mD_gen_perm`), these
establish that `mD` of a rank-2 subtorus is a basis-independent
invariant of the subtorus itself. -/

/-- The shear `a ↦ a + b` reparametrizes the gap by `t ↦ (t₀, t₀+t₁)`. -/
theorem mgap_shear (v : Fin (k + 1) → Fin 2 → ℤ) (t : Fin 2 → ℝ) :
    mgap (fun i => ![v i 0 + v i 1, v i 1]) t = mgap v ![t 0, t 0 + t 1] := by
  unfold mgap
  congr 1
  funext i
  congr 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

/-- Maximum loneliness is invariant under the shear `a ↦ a + b`. -/
theorem mML_shear (v : Fin (k + 1) → Fin 2 → ℤ) :
    mML (fun i => ![v i 0 + v i 1, v i 1]) = mML v := by
  unfold mML
  congr 1
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨![t 0, t 0 + t 1], (mgap_shear v t).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨![s 0, s 1 - s 0], ?_⟩
    rw [mgap_shear]
    congr 1
    funext j
    fin_cases j
    · simp
    · simp

/-- **Shear invariance.** The rank-2 D-value is unchanged by the basis
change `(a, b) ↦ (a + b, b)`. -/
theorem mD_shear (v : Fin (k + 1) → Fin 2 → ℤ) :
    mD (fun i => ![v i 0 + v i 1, v i 1]) = mD v := by
  unfold mD
  rw [mML_shear]

/-- The parameter-space involution `(t₀, t₁) ↦ (−t₀, t₁)`. -/
def negParam : (Fin 2 → ℝ) ≃ (Fin 2 → ℝ) where
  toFun t := ![-t 0, t 1]
  invFun t := ![-t 0, t 1]
  left_inv t := by funext j; fin_cases j <;> simp
  right_inv t := by funext j; fin_cases j <;> simp

/-- **Negation invariance.** The rank-2 D-value is unchanged by negating
the first generator, `(a, b) ↦ (−a, b)`. Demonstrates `mD_reparam`.

Together with `mD_gen_perm` (swap) and `mD_shear`, these are the
generators of `GL₂(ℤ)`, so `mD` of a rank-2 subtorus is invariant under
arbitrary integer basis change of the generators. -/
theorem mD_neg (v : Fin (k + 1) → Fin 2 → ℤ) :
    mD (fun i => ![-(v i 0), v i 1]) = mD v := by
  refine mD_reparam v (fun i => ![-(v i 0), v i 1]) negParam ?_
  intro t
  unfold mgap
  congr 1
  funext i
  congr 1
  simp only [negParam, Equiv.coe_fn_mk, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

end LRSpectrumFull
