/-
# TP'(4), module M1: Lemma 1(b), the bad residues of a free runner

Write the time as `t = (j + x) / 5` with `j ∈ ℤ/5` and `x` real.  A runner of speed `v` with `5 ∤ v` and phase
`s / 5` has `5 t v + s = v j + β` with `β = s + v x`.  It is bad iff `v j + β` is within `1` of a multiple of `5`,
i.e. iff `k = 5 n - v j` satisfies `|β - k| < 1`.  The integers `k` in `(β - 1, β + 1)` lie in `[⌊β⌋, ⌈β⌉]`,
which has at most two elements, and one element when `β` is an integer.  Hence the set of bad residues `j`
is inside the image of `[⌊β⌋, ⌈β⌉]` under `k ↦ -v⁻¹ k`.

* `card_badImg_le_two`, `card_badImg_le_one` : at most 2 bad residues, at most 1 for integral `β`.
* `good_of_not_mem_badImg` : every residue outside `badImg` is good.
* `exists_res` : a union bound; if the bad-set sizes sum to less than 5, a common good residue exists.
Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 1(b); LEAN_PORT_PLAN.md module M1.
-/
import LRSpectrumFull.TPFourBridge

namespace LRSpectrumFull

instance fact_prime_five_tp4 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The residues `j` that can be bad for a free runner of speed `v` when `β = s + v x`. -/
noncomputable def badImg (v : ℕ) (β : ℝ) : Finset (ZMod 5) :=
  (Finset.Icc ⌊β⌋ ⌈β⌉).image (fun k : ℤ => -((v : ZMod 5)⁻¹ * (k : ZMod 5)))

lemma card_badImg_le_two (v : ℕ) (β : ℝ) : (badImg v β).card ≤ 2 := by
  unfold badImg
  refine Finset.card_image_le.trans ?_
  rw [Int.card_Icc]
  have h1 : ⌈β⌉ ≤ ⌊β⌋ + 1 := Int.ceil_le_floor_add_one β
  omega

lemma card_badImg_le_one (v : ℕ) (m : ℤ) : (badImg v (m : ℝ)).card ≤ 1 := by
  unfold badImg
  rw [Int.floor_intCast, Int.ceil_intCast]
  refine Finset.card_image_le.trans ?_
  simp

lemma good_of_not_mem_badImg {v : ℕ} (hv : ¬ 5 ∣ v) (s : ℤ) (x : ℝ) (j : ZMod 5)
    (hj : j ∉ badImg v ((s : ℝ) + v * x)) :
    Good v s ((((j.val : ℕ) : ℝ) + x) / 5) := by
  by_contra hbad
  unfold Good at hbad
  obtain ⟨n, hn⟩ := exists_near_of_not_good hbad
  set J : ℕ := j.val with hJ
  set β : ℝ := (s : ℝ) + v * x with hβ
  have hy : (v : ℝ) * (((J : ℝ) + x) / 5) + (s : ℝ) / 5 = ((v : ℝ) * J + β) / 5 := by
    rw [hβ]; ring
  rw [hy] at hn
  set k : ℤ := 5 * n - (v : ℤ) * J with hk
  have hdiff : β - (k : ℝ) = 5 * (((v : ℝ) * J + β) / 5 - n) := by
    rw [hk]; push_cast; ring
  have habs : |β - (k : ℝ)| < 1 := by
    rw [hdiff, abs_mul]
    have : |(5 : ℝ)| = 5 := abs_of_pos (by norm_num)
    rw [this]
    linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hk1 : ⌊β⌋ ≤ k := by
    have : ⌊β⌋ < k + 1 := by
      rw [Int.floor_lt]; push_cast; linarith
    omega
  have hk2 : k ≤ ⌈β⌉ := by
    have : k - 1 < ⌈β⌉ := by
      rw [Int.lt_ceil]; push_cast; linarith
    omega
  apply hj
  unfold badImg
  rw [Finset.mem_image]
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
  have hv0 : (v : ZMod 5) ≠ 0 := fun h => hv ((ZMod.natCast_eq_zero_iff v 5).mp h)
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hkz : (k : ZMod 5) = -((v : ZMod 5) * j) := by
    rw [hk]
    push_cast
    rw [h5, hJ, ZMod.natCast_zmod_val]
    ring
  rw [hkz, mul_neg, neg_neg, ← mul_assoc, inv_mul_cancel₀ hv0, one_mul]

/-- Union bound: if the bad-set sizes sum to less than `5` there is a common good residue. -/
lemma exists_res {ι : Type*} [DecidableEq ι] (A : Finset ι) (v : ι → ℕ) (s : ι → ℤ) (x : ℝ)
    (b : ι → ℕ) (hv : ∀ i ∈ A, ¬ 5 ∣ v i)
    (hb : ∀ i ∈ A, (badImg (v i) ((s i : ℝ) + v i * x)).card ≤ b i)
    (hsum : ∑ i ∈ A, b i < 5) :
    ∃ j : ZMod 5, ∀ i ∈ A, Good (v i) (s i) ((((j.val : ℕ) : ℝ) + x) / 5) := by
  classical
  have hcard : (A.biUnion fun i => badImg (v i) ((s i : ℝ) + v i * x)).card
      < Fintype.card (ZMod 5) := by
    rw [ZMod.card]
    calc (A.biUnion fun i => badImg (v i) ((s i : ℝ) + v i * x)).card
        ≤ ∑ i ∈ A, (badImg (v i) ((s i : ℝ) + v i * x)).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ A, b i := Finset.sum_le_sum hb
      _ < 5 := hsum
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := A.biUnion fun i => badImg (v i) ((s i : ℝ) + v i * x))
    (t := (Finset.univ : Finset (ZMod 5))) (by rwa [Finset.card_univ])
  refine ⟨j, fun i hi => good_of_not_mem_badImg (hv i hi) (s i) x j ?_⟩
  intro hmem
  exact hj (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)

end LRSpectrumFull
