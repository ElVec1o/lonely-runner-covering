/-
# Theorem R5 (real phases), module B: the runner predicate with a real phase and the decomposition

Paper proof: INVENTION_2026_11/ROOMS/OPUS_REAL_PHASES_2026_11_12.md, Lemma 1, with the self-contained version in
ROOMS/R5_LEAN_BLOCK1_2026_11_12.md.  New real-phase twins of the `TPFourBridge` / `TPFourLocal` / `TPFourReduce`
lemmas (those files are not edited): the phase is a real `φ` instead of an integer `s / 5`.

* `GoodR v φ t`            : `1/5 ≤ tpDist (v t + φ)`.
* `goodR_mul5`             : Lemma 1(a), a speed `5 w` at time `(j + x)/5` behaves as speed `w` at time `x`.
* `goodR_of_not_mem_badImg`: Lemma 1(b): `β = 5 φ + v x`; `badImg v β` is reused unchanged (`β` was already real).
* `exists_resR`, `step_le2R`: union bound and the "at most two free runners" step.
* `dvd5_class`, `exists_coincide`: two free runners of one class: the choice `x = (ε φ_b - φ_a)/D` makes
  the centres coincide exactly, hence equal bad sets.
-/
import LRSpectrumFull.TPFourReduce
import LRSpectrumFull.TPFourWindow

namespace LRSpectrumFull

/-- The runner of speed `v` and real phase `φ` is good at time `t` (threshold `1/5`). -/
def GoodR (v : ℕ) (φ : ℝ) (t : ℝ) : Prop :=
  1 / 5 ≤ tpDist ((v : ℝ) * t + φ)

lemma goodR_mul5 (w : ℕ) (φ : ℝ) (j : ℕ) (x : ℝ) :
    GoodR (5 * w) φ (((j : ℝ) + x) / 5) ↔ GoodR w φ x := by
  unfold GoodR
  have h : ((5 * w : ℕ) : ℝ) * (((j : ℝ) + x) / 5) + φ
      = ((w : ℝ) * x + φ) + ((w * j : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, tpDist_add_int]

lemma goodR_of_not_mem_badImg {v : ℕ} (hv : ¬ 5 ∣ v) (φ : ℝ) (x : ℝ) (j : ZMod 5)
    (hj : j ∉ badImg v (5 * φ + v * x)) :
    GoodR v φ ((((j.val : ℕ) : ℝ) + x) / 5) := by
  by_contra hbad
  unfold GoodR at hbad
  obtain ⟨n, hn⟩ := exists_near_of_not_good hbad
  set J : ℕ := j.val with hJ
  set β : ℝ := 5 * φ + v * x with hβ
  have hy : (v : ℝ) * (((J : ℝ) + x) / 5) + φ = ((v : ℝ) * J + β) / 5 := by
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
lemma exists_resR {ι : Type*} [DecidableEq ι] (A : Finset ι) (v : ι → ℕ) (φ : ι → ℝ) (x : ℝ)
    (b : ι → ℕ) (hv : ∀ i ∈ A, ¬ 5 ∣ v i)
    (hb : ∀ i ∈ A, (badImg (v i) (5 * φ i + v i * x)).card ≤ b i)
    (hsum : ∑ i ∈ A, b i < 5) :
    ∃ j : ZMod 5, ∀ i ∈ A, GoodR (v i) (φ i) ((((j.val : ℕ) : ℝ) + x) / 5) := by
  classical
  have hcard : (A.biUnion fun i => badImg (v i) (5 * φ i + v i * x)).card
      < Fintype.card (ZMod 5) := by
    rw [ZMod.card]
    calc (A.biUnion fun i => badImg (v i) (5 * φ i + v i * x)).card
        ≤ ∑ i ∈ A, (badImg (v i) (5 * φ i + v i * x)).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ A, b i := Finset.sum_le_sum hb
      _ < 5 := hsum
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := A.biUnion fun i => badImg (v i) (5 * φ i + v i * x))
    (t := (Finset.univ : Finset (ZMod 5))) (by rwa [Finset.card_univ])
  refine ⟨j, fun i hi => goodR_of_not_mem_badImg (hv i hi) (φ i) x j ?_⟩
  intro hmem
  exact hj (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)

/-- The step of Lemma S / Lemma 3': at most two runners of `F` are free and the slow ones (at speed `v/5`) are
good at `x`; then some time works for all of `F`. -/
lemma step_le2R {ι : Type*} [DecidableEq ι] (F : Finset ι) (v : ι → ℕ) (φ : ι → ℝ)
    (h2 : (F.filter (fun i => ¬ 5 ∣ v i)).card ≤ 2) (x : ℝ)
    (hx : ∀ i ∈ F.filter (fun i => 5 ∣ v i), GoodR (v i / 5) (φ i) x) :
    ∃ t : ℝ, ∀ i ∈ F, GoodR (v i) (φ i) t := by
  obtain ⟨j, hj⟩ := exists_resR (F.filter (fun i => ¬ 5 ∣ v i)) v φ x (fun _ => 2)
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i _ => card_badImg_le_two _ _)
    (by simp only [Finset.sum_const, smul_eq_mul]; omega)
  refine ⟨(((j.val : ℕ) : ℝ) + x) / 5, fun i hi => ?_⟩
  by_cases h5 : 5 ∣ v i
  · obtain ⟨w, hw⟩ := h5
    have hx' := hx i (Finset.mem_filter.mpr ⟨hi, ⟨w, hw⟩⟩)
    rw [show v i / 5 = w by omega] at hx'
    rw [hw]
    exact (goodR_mul5 w (φ i) j.val x).2 hx'
  · exact hj i (Finset.mem_filter.mpr ⟨hi, h5⟩)

lemma dvd5_class (va vx : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : (vx : ZMod 5) = (ε : ZMod 5) * va) : (5 : ℤ) ∣ (va : ℤ) - ε * vx := by
  have h0 : (((va : ℤ) - ε * vx : ℤ) : ZMod 5) = 0 := by
    push_cast
    rw [h]
    rcases hε with rfl | rfl <;> push_cast <;> ring
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h0

/-- Two free runners of one class (`v_b ≡ ε v_a`) have equal bad sets at `x = (ε φ_b - φ_a)/D`, `5 D = v_a - ε v_b`. -/
lemma exists_coincide (va vb : ℕ) (φa φb : ℝ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (ha : ¬ 5 ∣ va)
    (hb : (vb : ZMod 5) = (ε : ZMod 5) * va) (hne : (va : ℤ) ≠ ε * vb) :
    ∃ x : ℝ, badImg vb (5 * φb + vb * x) = badImg va (5 * φa + va * x) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  obtain ⟨D, hD⟩ := dvd5_class va vb ε hε hb
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply hne
    omega
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
  have hDe : ((va : ℤ) : ℝ) - (ε : ℝ) * (vb : ℝ) = 5 * (D : ℝ) := by exact_mod_cast hD
  refine ⟨((ε : ℝ) * φb - φa) / D, ?_⟩
  have hx : (D : ℝ) * (((ε : ℝ) * φb - φa) / D) = (ε : ℝ) * φb - φa := mul_div_cancel₀ _ hDR
  refine badImg_eq_of_class va vb _ _ ε 0 hε ha0 hb ?_
  push_cast at hDe ⊢
  linear_combination (((ε : ℝ) * φb - φa) / D) * hDe + 5 * hx

end LRSpectrumFull
