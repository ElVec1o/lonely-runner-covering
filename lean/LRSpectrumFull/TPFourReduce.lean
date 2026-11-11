/-
# TP'(4), module M3: reduction of `TPp 4` to the pinned case `CaseH`

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Sections 1-2 (Lemmas 0-3, 3'); LEAN_PORT_PLAN.md, M2 and M3.

`CaseH` is the single hard configuration of the hand proof: four distinct positive speeds, one of them
(index `z`) divisible by 5 with phase divisible by 5 (pinned at 0 for every time `j/5`), the other three not
divisible by 5.  This module proves

  `TPp_four_of_caseH : CaseH → TPp 4`.

Design choices (they differ from the hand-proof wording, and why):
* Lemma 0 (gcd rescale) is replaced by strong induction on the sum of the speeds: if every speed is divisible
  by 5, divide all of them by 5 (REVIEW2 section 8, risk 2).
* Sub-instances are `Finset`s of one fixed index type, with the speed function replaced by `v i / 5`, so no
  `Fin k` re-indexing equivalences are needed.
* The pigeonhole at `x = 0` (Lemma 2) is proved from the count lemmas of `TPFourLocal`, which are needed anyway
  for Lemma 1(b); it needs no distinctness and no padding of `Fin k` to `Fin 4`.  `TP_prime_free` is therefore
  not used (it is the same statement for the full family only).
* Distinctness enters only through `CaseH` (and through its preservation by `v ↦ v / 5`).
-/
import LRSpectrumFull.TPFourLocal

namespace LRSpectrumFull

/-- The pinned case of the hand proof (HANDPROOF_v2 Section 2, "Case H"). -/
def CaseH : Prop :=
  ∀ (v : Fin 4 → ℕ) (s : Fin 4 → ℤ) (z : Fin 4), (∀ i, 0 < v i) → Function.Injective v →
    5 ∣ v z → (5 : ℤ) ∣ s z → (∀ i, i ≠ z → ¬ 5 ∣ v i) →
    ∃ t : ℝ, ∀ i, Good (v i) (s i) t

/-- Lemma 2: if no runner of `F` is pinned (`5 ∣ v` and `5 ∣ s`) and `|F| ≤ 4`, take `t = j / 5`. -/
lemma z0 {ι : Type*} [DecidableEq ι] (F : Finset ι) (v : ι → ℕ) (s : ι → ℤ) (hF : F.card ≤ 4)
    (hnp : ∀ i ∈ F, ¬ (5 ∣ v i ∧ (5 : ℤ) ∣ s i)) :
    ∃ t : ℝ, ∀ i ∈ F, Good (v i) (s i) t := by
  set A : Finset ι := F.filter (fun i => ¬ 5 ∣ v i) with hA
  have hAF : A.card ≤ F.card := Finset.card_filter_le _ _
  obtain ⟨j, hj⟩ := exists_res A v s 0 (fun _ => 1)
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i _ => by
      have h0 : (s i : ℝ) + (v i : ℝ) * 0 = ((s i : ℤ) : ℝ) := by ring
      rw [h0]
      exact card_badImg_le_one _ _)
    (by simp only [Finset.sum_const, smul_eq_mul, mul_one]; omega)
  refine ⟨(((j.val : ℕ) : ℝ) + 0) / 5, fun i hi => ?_⟩
  by_cases h5 : 5 ∣ v i
  · obtain ⟨w, hw⟩ := h5
    have hs : ¬ (5 : ℤ) ∣ s i := fun h => hnp i hi ⟨⟨w, hw⟩, h⟩
    have hs' : s i % 5 ≠ 0 := by omega
    rw [hw, good_mul5]
    unfold Good
    have h := tp_residue 5 (by norm_num) (s i) hs'
    simpa using h
  · exact hj i (Finset.mem_filter.mpr ⟨hi, h5⟩)

/-- The common step of Lemma 3 and Lemma 3': if at most two runners of `F` have speed not divisible by 5 and
the runners with speed divisible by 5 (at speed `v / 5`) are good at `x`, then some time works for all of `F`. -/
lemma step_le2 {ι : Type*} [DecidableEq ι] (F : Finset ι) (v : ι → ℕ) (s : ι → ℤ)
    (h2 : (F.filter (fun i => ¬ 5 ∣ v i)).card ≤ 2) (x : ℝ)
    (hx : ∀ i ∈ F.filter (fun i => 5 ∣ v i), Good (v i / 5) (s i) x) :
    ∃ t : ℝ, ∀ i ∈ F, Good (v i) (s i) t := by
  obtain ⟨j, hj⟩ := exists_res (F.filter (fun i => ¬ 5 ∣ v i)) v s x (fun _ => 2)
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i _ => card_badImg_le_two _ _)
    (by simp only [Finset.sum_const, smul_eq_mul]; omega)
  refine ⟨(((j.val : ℕ) : ℝ) + x) / 5, fun i hi => ?_⟩
  by_cases h5 : 5 ∣ v i
  · obtain ⟨w, hw⟩ := h5
    have hx' := hx i (Finset.mem_filter.mpr ⟨hi, ⟨w, hw⟩⟩)
    rw [show v i / 5 = w by omega] at hx'
    rw [hw]
    exact (good_mul5 w (s i) j.val x).2 hx'
  · exact hj i (Finset.mem_filter.mpr ⟨hi, h5⟩)

/-- Sum of `v / 5` over a subset is smaller than the sum of `v` (positive speeds, nonempty `F`). -/
lemma sum_div5_lt {ι : Type*} [DecidableEq ι] (F C : Finset ι) (v : ι → ℕ) (hC : C ⊆ F)
    (hne : F.Nonempty) (hpos : ∀ i ∈ F, 0 < v i) :
    ∑ i ∈ C, v i / 5 < ∑ i ∈ F, v i := by
  calc ∑ i ∈ C, v i / 5 ≤ ∑ i ∈ F, v i / 5 :=
        Finset.sum_le_sum_of_subset hC
    _ < ∑ i ∈ F, v i :=
        Finset.sum_lt_sum_of_nonempty hne (fun i hi => by have := hpos i hi; omega)

/-- Lemma 3, `S(k)` for `k ≤ 3`: any three runners (any phases, no distinctness) have a good time. -/
theorem lemS {ι : Type*} [DecidableEq ι] :
    ∀ (N : ℕ) (v : ι → ℕ) (s : ι → ℤ) (F : Finset ι), (∀ i ∈ F, 0 < v i) → F.card ≤ 3 →
      ∑ i ∈ F, v i ≤ N → ∃ t : ℝ, ∀ i ∈ F, Good (v i) (s i) t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v s F hpos hcard hN
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ⟨0, by simp [hF]⟩
    by_cases ha : (F.filter (fun i => ¬ 5 ∣ v i)).card ≤ 2
    · set C : Finset ι := F.filter (fun i => 5 ∣ v i) with hC
      have hCF : C ⊆ F := Finset.filter_subset _ _
      have hlt := sum_div5_lt F C v hCF hF hpos
      obtain ⟨x, hx⟩ := ih (∑ i ∈ C, v i / 5) (lt_of_lt_of_le hlt hN) (fun i => v i / 5) s C
        (fun i hi => by
          obtain ⟨hiF, ⟨w, hw⟩⟩ := Finset.mem_filter.mp hi
          have := hpos i hiF
          show 0 < v i / 5
          omega)
        ((Finset.card_le_card hCF).trans hcard) le_rfl
      exact step_le2 F v s ha x hx
    · apply z0 F v s (by omega)
      intro i hi ⟨h5, _⟩
      apply ha
      have hsub : F.filter (fun i => ¬ 5 ∣ v i) ⊆ F.erase i := by
        intro k hk
        obtain ⟨hkF, hk5⟩ := Finset.mem_filter.mp hk
        exact Finset.mem_erase.mpr ⟨fun h => hk5 (h ▸ h5), hkF⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi] at this
      omega

/-- The full reduction, by strong induction on the sum of the speeds. -/
theorem lemT (hH : CaseH) :
    ∀ (N : ℕ) (v : Fin 4 → ℕ) (s : Fin 4 → ℤ), (∀ i, 0 < v i) → Function.Injective v →
      ∑ i, v i ≤ N → ∃ t : ℝ, ∀ i, Good (v i) (s i) t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v s hpos hinj hN
    by_cases hP : ∃ z, 5 ∣ v z ∧ (5 : ℤ) ∣ s z
    · obtain ⟨z, hz5, hzs⟩ := hP
      set A : Finset (Fin 4) := Finset.univ.filter (fun i => ¬ 5 ∣ v i) with hA
      by_cases ha : A.card ≤ 2
      · by_cases ha0 : A.card = 0
        · -- every speed is divisible by 5: rescale
          have hall : ∀ i, 5 ∣ v i := by
            intro i
            by_contra h
            have : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            rw [Finset.card_eq_zero] at ha0
            simp [ha0] at this
          have hlt := sum_div5_lt Finset.univ Finset.univ v (Finset.Subset.refl _)
            Finset.univ_nonempty (fun i _ => hpos i)
          obtain ⟨x, hx⟩ := ih (∑ i, v i / 5) (by simpa using lt_of_lt_of_le hlt hN)
            (fun i => v i / 5) s
            (fun i => by
              have := hpos i; have := hall i
              show 0 < v i / 5
              omega)
            (fun i j hij => by
              have := hall i; have := hall j
              have hij' : v i / 5 = v j / 5 := hij
              exact hinj (by omega))
            le_rfl
          obtain ⟨t, ht⟩ := step_le2 Finset.univ v s ha x (fun i _ => hx i)
          exact ⟨t, fun i => ht i (Finset.mem_univ _)⟩
        · -- 1 ≤ |A| ≤ 2: the multiples of 5 form at most three runners
          set C : Finset (Fin 4) := Finset.univ.filter (fun i => 5 ∣ v i) with hC
          have hCcard : C.card ≤ 3 := by
            obtain ⟨a0, ha0'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero ha0)
            have hsub : C ⊆ Finset.univ.erase a0 := by
              intro k hk
              obtain ⟨-, hk5⟩ := Finset.mem_filter.mp hk
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
              intro h
              exact (Finset.mem_filter.mp ha0').2 (h ▸ hk5)
            have := Finset.card_le_card hsub
            simpa using this
          obtain ⟨x, hx⟩ := lemS (∑ i ∈ C, v i / 5) (fun i => v i / 5) s C
            (fun i hi => by
              obtain ⟨-, ⟨w, hw⟩⟩ := Finset.mem_filter.mp hi
              have := hpos i
              show 0 < v i / 5
              omega)
            hCcard le_rfl
          obtain ⟨t, ht⟩ := step_le2 Finset.univ v s ha x hx
          exact ⟨t, fun i => ht i (Finset.mem_univ _)⟩
      · -- |A| = 3 and the fourth runner is pinned: the hard case
        have hz : ∀ i, i ≠ z → ¬ 5 ∣ v i := by
          intro i hiz hi5
          apply ha
          have hsub : A ⊆ (Finset.univ.erase i).erase z := by
            intro k hk
            obtain ⟨-, hk5⟩ := Finset.mem_filter.mp hk
            refine Finset.mem_erase.mpr ⟨fun h => hk5 (h ▸ hz5), ?_⟩
            exact Finset.mem_erase.mpr ⟨fun h => hk5 (h ▸ hi5), Finset.mem_univ _⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (by simp [hiz.symm]), Finset.card_erase_of_mem (by simp)] at this
          simpa using this
        exact hH v s z hpos hinj hz5 hzs hz
    · push Not at hP
      exact (by
        obtain ⟨t, ht⟩ := z0 (Finset.univ : Finset (Fin 4)) v s (by simp) (fun i _ h => hP i h.1 h.2)
        exact ⟨t, fun i => ht i (Finset.mem_univ _)⟩)

/-- Reduction of `TP'(4)` to the pinned case. -/
theorem TPp_four_of_caseH (hH : CaseH) : TPp 4 := by
  intro v hv hinj s
  obtain ⟨t, ht⟩ := lemT hH (∑ i, v i) v s hv hinj le_rfl
  refine ⟨t, fun i => ?_⟩
  have e : ((4 : ℕ) : ℝ) + 1 = 5 := by norm_num
  rw [e]
  exact ht i

end LRSpectrumFull
