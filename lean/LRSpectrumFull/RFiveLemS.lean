/-
# Theorem R5 (real phases), module S: Lemma S (at most three runners) and Lemma 3'

Paper proof: ROOMS/OPUS_REAL_PHASES_2026_11_12.md, "Lemma S (k <= 3 runners, threshold 1/5, real phases, distinct
positive speeds)".  The grid proof used the pigeonhole at `x = 0`, which needs integer phases; for real phases
it is replaced by exact coincidence of two same-class free runners (`exists_coincide`, `x = (ε φ_b - φ_a)/D`).

* `good_of_eq3`  : three free runners, two with equal bad sets: a common good residue (`≤ 4 < 5`).
* `three_free`   : three pairwise distinct free speeds, any real phases: some `x` and `j` good for all three.
* `lemSR`        : Lemma S, by strong induction on the sum of the speeds.
-/
import LRSpectrumFull.RFiveBase
import LRSpectrumFull.TPFourGlue

namespace LRSpectrumFull

lemma good_of_eq3 {va vb vc : ℕ} {βa βb βc : ℝ} (h : badImg vb βb = badImg va βa) :
    ∃ j : ZMod 5, j ∉ badImg va βa ∧ j ∉ badImg vb βb ∧ j ∉ badImg vc βc := by
  have hlt : (badImg va βa ∪ badImg vc βc).card < Fintype.card (ZMod 5) := by
    rw [ZMod.card]
    have h1 := Finset.card_union_le (badImg va βa) (badImg vc βc)
    have h2 := card_badImg_le_two va βa
    have h3 := card_badImg_le_two vc βc
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := badImg va βa ∪ badImg vc βc)
    (t := (Finset.univ : Finset (ZMod 5))) (by rwa [Finset.card_univ])
  have hja : j ∉ badImg va βa := fun h' => hj (Finset.mem_union_left _ h')
  have hjc : j ∉ badImg vc βc := fun h' => hj (Finset.mem_union_right _ h')
  exact ⟨j, hja, by rw [h]; exact hja, hjc⟩

lemma same_class_pair (a b c : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (b = a ∨ b = -a) ∨ (c = a ∨ c = -a) ∨ (c = b ∨ c = -b) := by
  revert a b c; decide

lemma three_free (va vb vc : ℕ) (φa φb φc : ℝ) (ha : ¬ 5 ∣ va) (hb : ¬ 5 ∣ vb) (hc : ¬ 5 ∣ vc)
    (hpa : 0 < va) (hpb : 0 < vb) (hpc : 0 < vc) (hab : va ≠ vb) (hac : va ≠ vc) (hbc : vb ≠ vc) :
    ∃ x : ℝ, ∃ j : ZMod 5, j ∉ badImg va (5 * φa + va * x) ∧ j ∉ badImg vb (5 * φb + vb * x) ∧
      j ∉ badImg vc (5 * φc + vc * x) := by
  have a0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  have b0 : (vb : ZMod 5) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  have c0 : (vc : ZMod 5) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff _ 5).mp h)
  rcases same_class_pair _ _ _ a0 b0 c0 with s | s | s
  · obtain ⟨ε, hε, hrel⟩ := exists_eps _ _ s
    obtain ⟨x, hx⟩ := exists_coincide va vb φa φb ε hε ha hrel (hne_of va vb hpa hpb hab ε hε)
    obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := vc) (βc := 5 * φc + vc * x) hx
    exact ⟨x, j, j1, j2, j3⟩
  · obtain ⟨ε, hε, hrel⟩ := exists_eps _ _ s
    obtain ⟨x, hx⟩ := exists_coincide va vc φa φc ε hε ha hrel (hne_of va vc hpa hpc hac ε hε)
    obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := vb) (βc := 5 * φb + vb * x) hx
    exact ⟨x, j, j1, j3, j2⟩
  · obtain ⟨ε, hε, hrel⟩ := exists_eps _ _ s
    obtain ⟨x, hx⟩ := exists_coincide vb vc φb φc ε hε hb hrel (hne_of vb vc hpb hpc hbc ε hε)
    obtain ⟨j, j1, j2, j3⟩ := good_of_eq3 (vc := va) (βc := 5 * φa + va * x) hx
    exact ⟨x, j, j3, j1, j2⟩

/-- Lemma S: at most three runners with distinct positive speeds and arbitrary real phases have a good time. -/
theorem lemSR {ι : Type*} [DecidableEq ι] :
    ∀ (N : ℕ) (v : ι → ℕ) (φ : ι → ℝ) (F : Finset ι), (∀ i ∈ F, 0 < v i) →
      (∀ i ∈ F, ∀ k ∈ F, v i = v k → i = k) → F.card ≤ 3 → ∑ i ∈ F, v i ≤ N →
      ∃ t : ℝ, ∀ i ∈ F, GoodR (v i) (φ i) t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v φ F hpos hinj hcard hN
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ⟨0, by simp [hF]⟩
    by_cases ha : (F.filter (fun i => ¬ 5 ∣ v i)).card ≤ 2
    · set C : Finset ι := F.filter (fun i => 5 ∣ v i) with hC
      have hCF : C ⊆ F := Finset.filter_subset _ _
      have hlt := sum_div5_lt F C v hCF hF hpos
      obtain ⟨x, hx⟩ := ih (∑ i ∈ C, v i / 5) (lt_of_lt_of_le hlt hN) (fun i => v i / 5) φ C
        (fun i hi => by
          obtain ⟨hiF, ⟨w, hw⟩⟩ := Finset.mem_filter.mp hi
          have := hpos i hiF
          show 0 < v i / 5
          omega)
        (fun i hi k hk hik => by
          obtain ⟨hiF, h5i⟩ := Finset.mem_filter.mp hi
          obtain ⟨hkF, h5k⟩ := Finset.mem_filter.mp hk
          have hik' : v i / 5 = v k / 5 := hik
          exact hinj i hiF k hkF (by omega))
        ((Finset.card_le_card hCF).trans hcard) le_rfl
      exact step_le2R F v φ ha x hx
    · push Not at ha
      have hsub : F.filter (fun i => ¬ 5 ∣ v i) ⊆ F := Finset.filter_subset _ _
      have hle := Finset.card_le_card hsub
      have heq : F.filter (fun i => ¬ 5 ∣ v i) = F :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hfree : ∀ i ∈ F, ¬ 5 ∣ v i := by
        intro i hi
        have : i ∈ F.filter (fun i => ¬ 5 ∣ v i) := by rw [heq]; exact hi
        exact (Finset.mem_filter.mp this).2
      have hF3 : F.card = 3 := by omega
      obtain ⟨a, b, c, hab, hac, hbc, hFabc⟩ := Finset.card_eq_three.mp hF3
      have mA : a ∈ F := by rw [hFabc]; simp
      have mB : b ∈ F := by rw [hFabc]; simp
      have mC : c ∈ F := by rw [hFabc]; simp
      obtain ⟨x, j, j1, j2, j3⟩ := three_free (v a) (v b) (v c) (φ a) (φ b) (φ c)
        (hfree a mA) (hfree b mB) (hfree c mC) (hpos a mA) (hpos b mB) (hpos c mC)
        (fun h => hab (hinj a mA b mB h)) (fun h => hac (hinj a mA c mC h))
        (fun h => hbc (hinj b mB c mC h))
      refine ⟨(((j.val : ℕ) : ℝ) + x) / 5, fun i hi => ?_⟩
      rw [hFabc] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact goodR_of_not_mem_badImg (hfree _ mA) _ x j j1
      · exact goodR_of_not_mem_badImg (hfree _ mB) _ x j j2
      · exact goodR_of_not_mem_badImg (hfree _ mC) _ x j j3

end LRSpectrumFull
