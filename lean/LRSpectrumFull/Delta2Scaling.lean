/-
# Scaling invariance of the maximal loneliness

`ML (g • v) = ML v` for any positive integer scale `g`.  The loneliness spectrum of a velocity
family depends only on the family up to a common scale: substituting `t ↦ g·t` (a bijection of
`ℝ`) carries `gap (g • v)` onto `gap v` with the same range, hence the same supremum.

**Consequence for the programme.**  Every family is a positive-integer multiple of a *primitive*
family (`gcd = 1`), and loneliness is scale-invariant, so the Lonely-Runner floor for all families
is equivalent to the floor for primitive families.  This matters because the Bridge-disjunction
erosion is driven entirely by non-primitive (`gcd > 1`) champions: the hardest measured families
are scaled copies whose residue witnesses are pushed past the height-relative cap.  With scaling
invariance, the disjunction only needs to hold on primitive families.
-/
import LRSpectrumFull.MaxLoneliness
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.GCD

namespace LRSpectrumFull

variable {k : ℕ}

/-- `gap` of a scaled family is `gap` reparametrised: `gap (g • v) t = gap v (g·t)`. -/
theorem gap_smul (g : ℤ) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => g * v i) t = gap v ((g : ℝ) * t) := by
  simp only [gap]
  refine Finset.inf'_congr _ rfl (fun i _ => ?_)
  congr 1
  push_cast
  ring

/-- **Scaling invariance of maximal loneliness.**  For a positive integer scale `g`,
`ML (g • v) = ML v`. -/
theorem ML_smul (g : ℤ) (hg : 0 < g) (v : Fin (k + 1) → ℤ) :
    ML (fun i => g * v i) = ML v := by
  simp only [ML]
  congr 1
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hsurj : Function.Surjective (fun t : ℝ => (g : ℝ) * t) := fun s =>
    ⟨s / (g : ℝ), by field_simp⟩
  have hcomp : (fun t => gap v ((g : ℝ) * t)) = gap v ∘ (fun t : ℝ => (g : ℝ) * t) := rfl
  calc Set.range (gap (fun i => g * v i))
      = Set.range (fun t => gap v ((g : ℝ) * t)) := by
        refine congrArg Set.range ?_; funext t; exact gap_smul g v t
    _ = Set.range (gap v ∘ (fun t : ℝ => (g : ℝ) * t)) := by rw [hcomp]
    _ = Set.range (gap v) := hsurj.range_comp (gap v)

/-- **The Lonely-Runner floor reduces to primitive families.**  If the floor `1/(k+2) ≤ ML v`
holds for every positive family whose entries have `gcd = 1`, then it holds for *every* positive
family: write `v = g · (v / g)` with `g = gcd v > 0`, note `v / g` is positive and primitive, and
apply scale invariance `ML v = ML (v / g)`. -/
theorem floor_of_primitive_floor {k : ℕ}
    (hp : ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
        Finset.univ.gcd v = 1 → 1 / ((k : ℝ) + 2) ≤ ML v)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  set g : ℤ := Finset.univ.gcd v with hgdef
  have hnorm : normalize g = g := by rw [hgdef]; exact Finset.normalize_gcd
  have hgnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self hnorm
  have hg0 : g ≠ 0 := by
    rw [hgdef, Ne, Finset.gcd_eq_zero_iff]; push_neg
    exact ⟨0, Finset.mem_univ 0, (hv 0).ne'⟩
  have hgpos : 0 < g := lt_of_le_of_ne hgnn (Ne.symm hg0)
  have hdvd : ∀ i, g ∣ v i := fun i => by rw [hgdef]; exact Finset.gcd_dvd (Finset.mem_univ i)
  set w : Fin (k + 1) → ℤ := fun i => v i / g with hwdef
  have hvw : v = fun i => g * w i := by
    funext i; rw [hwdef]; exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have h1 : 0 < g * w i := by have := hv i; rwa [hvw] at this
    exact (mul_pos_iff_of_pos_left hgpos).mp h1
  have hwprim : Finset.univ.gcd w = 1 := by
    have hmul : Finset.univ.gcd (fun i => g * w i) = normalize g * Finset.univ.gcd w :=
      Finset.gcd_mul_left
    rw [Int.normalize_of_nonneg hgnn, ← hvw, ← hgdef] at hmul
    exact (mul_left_cancel₀ hg0 ((mul_one g).trans hmul)).symm
  calc 1 / ((k : ℝ) + 2) ≤ ML w := hp w hwpos hwprim
    _ = ML v := by rw [hvw]; exact (ML_smul g hgpos w).symm

/-- **Predicate-carrying primitive reduction.**  For a predicate `P` that *descends to the
primitive part* (`hPdesc`: if `P (g • w)` then `P w`), the floor for any positive family
satisfying `P` follows from the floor on primitive `P`-families.  Instantiated at
`P = ¬ StrongFree` (which descends because a common factor cannot create or destroy a relation),
this lets the Bridge disjunction be assumed on primitive families only. -/
theorem floor_of_primitive_floor_pred {k : ℕ} (P : (Fin (k + 1) → ℤ) → Prop)
    (hPdesc : ∀ g : ℤ, 0 < g → ∀ w : Fin (k + 1) → ℤ, P (fun i => g * w i) → P w)
    (hp : ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 → P v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hP : P v) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  set g : ℤ := Finset.univ.gcd v with hgdef
  have hnorm : normalize g = g := by rw [hgdef]; exact Finset.normalize_gcd
  have hgnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self hnorm
  have hg0 : g ≠ 0 := by
    rw [hgdef, Ne, Finset.gcd_eq_zero_iff]; push_neg
    exact ⟨0, Finset.mem_univ 0, (hv 0).ne'⟩
  have hgpos : 0 < g := lt_of_le_of_ne hgnn (Ne.symm hg0)
  have hdvd : ∀ i, g ∣ v i := fun i => by rw [hgdef]; exact Finset.gcd_dvd (Finset.mem_univ i)
  set w : Fin (k + 1) → ℤ := fun i => v i / g with hwdef
  have hvw : v = fun i => g * w i := by
    funext i; rw [hwdef]; exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have h1 : 0 < g * w i := by have := hv i; rwa [hvw] at this
    exact (mul_pos_iff_of_pos_left hgpos).mp h1
  have hwprim : Finset.univ.gcd w = 1 := by
    have hmul : Finset.univ.gcd (fun i => g * w i) = normalize g * Finset.univ.gcd w :=
      Finset.gcd_mul_left
    rw [Int.normalize_of_nonneg hgnn, ← hvw, ← hgdef] at hmul
    exact (mul_left_cancel₀ hg0 ((mul_one g).trans hmul)).symm
  have hPw : P w := hPdesc g hgpos w (by rw [← hvw]; exact hP)
  calc 1 / ((k : ℝ) + 2) ≤ ML w := hp w hwpos hwprim hPw
    _ = ML v := by rw [hvw]; exact (ML_smul g hgpos w).symm

end LRSpectrumFull
