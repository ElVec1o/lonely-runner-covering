/-
# Free families grow exponentially

**W5, lower-bound side.**  A strongly `±1`-free family (no nontrivial `{−1,0,1}`
combination vanishes) has all `2^k` subset sums distinct, hence its maximum is
at least `(2^k − 1)/k`.  Bounded free families are logarithmically small — the
quantitative seed of the anti-emulation direction for the separation pillar.
-/
import LRSpectrumFull.Delta2Boundary

namespace LRSpectrumFull

/-- Strong `±1`-freeness: no nontrivial `{−1,0,1}`-combination vanishes. -/
def StrongFree {k : ℕ} (v : Fin k → ℤ) : Prop :=
  ∀ c : Fin k → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) →
    (∑ i, c i * v i) = 0 → ∀ i, c i = 0

/-- Subset sums are injective on a strongly free family. -/
theorem subsetSum_injective {k : ℕ} (v : Fin k → ℤ) (hf : StrongFree v) :
    Function.Injective (fun A : Finset (Fin k) => ∑ i ∈ A, v i) := by
  intro A B hAB
  simp only at hAB
  set c : Fin k → ℤ :=
    fun i => (if i ∈ A then (1 : ℤ) else 0) - (if i ∈ B then (1 : ℤ) else 0) with hc
  have hcoef : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1 := by
    intro i
    simp only [hc]
    split_ifs <;> norm_num
  have hA : (∑ i, (if i ∈ A then (1 : ℤ) else 0) * v i) = ∑ i ∈ A, v i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [ite_mul, one_mul, zero_mul]),
      Finset.sum_ite_mem, Finset.univ_inter]
  have hB : (∑ i, (if i ∈ B then (1 : ℤ) else 0) * v i) = ∑ i ∈ B, v i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [ite_mul, one_mul, zero_mul]),
      Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : (∑ i, c i * v i) = 0 := by
    simp only [hc, sub_mul]
    rw [Finset.sum_sub_distrib, hA, hB, hAB, sub_self]
  have hzero := hf c hcoef hsum
  ext i
  have hci := hzero i
  simp only [hc] at hci
  constructor
  · intro hiA
    by_contra hiB
    rw [if_pos hiA, if_neg hiB] at hci
    norm_num at hci
  · intro hiB
    by_contra hiA
    rw [if_neg hiA, if_pos hiB] at hci
    norm_num at hci

/-- **Exponential growth.** A positive strongly free family bounded by `M`
satisfies `2^k ≤ k·M + 1`; equivalently `max ≥ (2^k − 1)/k`. -/
theorem free_forces_growth {k : ℕ} (v : Fin k → ℤ) (hpos : ∀ i, 0 < v i)
    (hf : StrongFree v) (M : ℤ) (hM : ∀ i, v i ≤ M) :
    (2 : ℤ) ^ k ≤ (k : ℤ) * M + 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    norm_num
  · have hM0 : (0 : ℤ) < M := lt_of_lt_of_le (hpos ⟨0, hk0⟩) (hM ⟨0, hk0⟩)
    have hmaps : ∀ A : Finset (Fin k), (∑ i ∈ A, v i) ∈ Finset.Icc (0 : ℤ) ((k : ℤ) * M) := by
      intro A
      rw [Finset.mem_Icc]
      refine ⟨Finset.sum_nonneg (fun i _ => (hpos i).le), ?_⟩
      calc (∑ i ∈ A, v i) ≤ ∑ _i ∈ A, M := Finset.sum_le_sum (fun i _ => hM i)
      _ = (A.card : ℤ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℤ) * M := by
          have hcard : (A.card : ℤ) ≤ (k : ℤ) := by
            have h := A.card_le_univ
            rw [Fintype.card_fin] at h
            exact_mod_cast h
          exact mul_le_mul_of_nonneg_right hcard hM0.le
    have hcount := Finset.card_le_card_of_injOn
      (s := (Finset.univ : Finset (Finset (Fin k))))
      (t := Finset.Icc (0 : ℤ) ((k : ℤ) * M))
      (f := fun A : Finset (Fin k) => ∑ i ∈ A, v i)
      (fun A _ => hmaps A) ((subsetSum_injective v hf).injOn)
    have hdom : (Finset.univ : Finset (Finset (Fin k))).card = 2 ^ k := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    have hcod : (Finset.Icc (0 : ℤ) ((k : ℤ) * M)).card = ((k : ℤ) * M + 1).toNat := by
      rw [Int.card_Icc]
      norm_num
    rw [hdom, hcod] at hcount
    have hcastLe : ((2 ^ k : ℕ) : ℤ) ≤ ((((k : ℤ) * M + 1).toNat : ℕ) : ℤ) := by
      exact_mod_cast hcount
    have htn : ((((k : ℤ) * M + 1).toNat : ℕ) : ℤ) = (k : ℤ) * M + 1 :=
      Int.toNat_of_nonneg (by positivity)
    rw [htn] at hcastLe
    calc (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
    _ ≤ (k : ℤ) * M + 1 := hcastLe

-- axiom audit
#print axioms free_forces_growth

end LRSpectrumFull
