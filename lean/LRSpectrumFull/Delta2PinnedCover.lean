/-
# Pinned cover-capacity certificates (branching on forced-in / forced-out speeds)

`floor_of_cover_capacity` bounds the complement `W` of the speed set inside `[1, 2(k+1)]` part by
part.  Here a set `I` of window elements is *pinned into* `W` (they are not speeds) and a set `O`
is *pinned out of* `W` (they are speeds).  Then `W \ I` lies in `[1, 2(k+1)] \ (I ∪ O)`, the parts
only have to cover that set, and the capacities are taken in the *link* form: more than `c i`
elements of `U i` always contain `bad j \ I` for some `j`.  The budget is `∑ c i + |I| < k + 1`.

`pinned_tree_three` is the exhaustive three-case split used for a state with two uncovered lows
`a`, `b`: `a` is not a speed; `a` is a speed and `b` is not; both are speeds.
-/
import LRSpectrumFull.Delta2CoverCapacity

namespace LRSpectrumFull

open Finset

/-- **Pinned cover-capacity certificate.** -/
theorem floor_of_pinned_cover {k t N : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 (2 * (k + 1)))
    (p q : Fin N → ℕ) (hq : ∀ j, 0 < q j) (bad : Fin N → Finset ℕ)
    (hbad : ∀ j, ∀ x, 1 ≤ x → x ≤ 2 * (k + 1) →
      goodAt k x (p j) (q j) = false → x ∈ bad j)
    (I O : Finset ℕ) (hIsub : I ⊆ Finset.Icc 1 (2 * (k + 1)))
    (hI : ∀ x ∈ I, ∀ i, (v i).toNat ≠ x) (hO : ∀ x ∈ O, ∃ i, (v i).toNat = x)
    (U : Fin t → Finset ℕ) (c : Fin t → ℕ)
    (hcover : Finset.Icc 1 (2 * (k + 1)) \ (I ∪ O) ⊆ Finset.univ.biUnion U)
    (hcap : ∀ i, ∀ T ∈ (U i).powerset, c i < T.card → ∃ j, bad j \ I ⊆ T)
    (hsum : ∑ i, c i + I.card < k + 1) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  by_contra hcon
  push_neg at hcon
  set Vs : Finset ℕ := Finset.univ.image fun i => (v i).toNat with hVs
  have hVmem : ∀ x, x ∈ Vs ↔ ∃ i, (v i).toNat = x := by
    intro x
    simp only [hVs, Finset.mem_image, Finset.mem_univ, true_and]
  -- every certificate time is defeated, so every `bad j` meets the velocity set
  have hmeet : ∀ j : Fin N, ∃ x ∈ bad j, x ∈ Vs := by
    intro j
    by_contra hno
    push_neg at hno
    refine absurd (cube_floor_of_witness v hv (p j) (q j) (hq j) (fun i => ?_)) (not_le.mpr hcon)
    by_contra hg
    have hmem : (v i).toNat ∈ Vs := (hVmem _).mpr ⟨i, rfl⟩
    have h1 := (Finset.mem_Icc.mp (hden i)).1
    have h2 := (Finset.mem_Icc.mp (hden i)).2
    have hfalse : goodAt k (v i).toNat (p j) (q j) = false := by
      simpa [goodAt, decide_eq_false_iff_not] using hg
    exact hno _ (hbad j _ h1 h2 hfalse) hmem
  -- the complement `W` has exactly `k+1` elements
  set W : Finset ℕ := Finset.Icc 1 (2 * (k + 1)) \ Vs with hW
  have hVsub : Vs ⊆ Finset.Icc 1 (2 * (k + 1)) := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hVmem x).mp hx
    exact hden i
  have hVcard : Vs.card = k + 1 := by
    rw [hVs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hWcard : W.card = k + 1 := by
    rw [hW, Finset.card_sdiff, Finset.inter_eq_left.mpr hVsub, hVcard, Nat.card_Icc]
    omega
  -- the pinned-in elements lie in `W`, the pinned-out ones do not
  have hIW : I ⊆ W := by
    intro x hx
    rw [hW, Finset.mem_sdiff]
    refine ⟨hIsub hx, fun hxV => ?_⟩
    obtain ⟨i, hi⟩ := (hVmem x).mp hxV
    exact hI x hx i hi
  set W' : Finset ℕ := W \ I with hW'
  -- each part contributes at most its capacity to `W \ I`
  have hpart : ∀ i, (W' ∩ U i).card ≤ c i := by
    intro i
    by_contra hgt
    push_neg at hgt
    obtain ⟨j, hj⟩ := hcap i (W' ∩ U i) (Finset.mem_powerset.mpr Finset.inter_subset_right) hgt
    obtain ⟨x, hxb, hxV⟩ := hmeet j
    have hxI : x ∉ I := fun hxI => by
      obtain ⟨i', hi'⟩ := (hVmem x).mp hxV
      exact hI x hxI i' hi'
    have hx1 : x ∈ W' := (Finset.mem_inter.mp (hj (Finset.mem_sdiff.mpr ⟨hxb, hxI⟩))).1
    have hx2 : x ∈ W := (Finset.mem_sdiff.mp hx1).1
    exact (Finset.mem_sdiff.mp hx2).2 hxV
  -- `W \ I` is covered by the parts
  have hW'cov : W' ⊆ Finset.univ.biUnion fun i => W' ∩ U i := by
    intro x hx
    have hxW : x ∈ W := (Finset.mem_sdiff.mp hx).1
    have hxI : x ∉ I := (Finset.mem_sdiff.mp hx).2
    have hxIcc : x ∈ Finset.Icc 1 (2 * (k + 1)) := (Finset.mem_sdiff.mp hxW).1
    have hxV : x ∉ Vs := (Finset.mem_sdiff.mp hxW).2
    have hxO : x ∉ O := fun hxO => hxV ((hVmem x).mpr (hO x hxO))
    have hxG : x ∈ Finset.Icc 1 (2 * (k + 1)) \ (I ∪ O) := by
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨hxIcc, fun h => h.elim hxI hxO⟩
    obtain ⟨i, _, hxU⟩ := Finset.mem_biUnion.mp (hcover hxG)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hxU⟩⟩
  have hbu : (Finset.univ.biUnion fun i => W' ∩ U i).card ≤ ∑ i, c i :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun i _ => hpart i)
  have hW'card : W'.card ≤ ∑ i, c i :=
    le_trans (Finset.card_le_card hW'cov) hbu
  have hWsub : W ⊆ I ∪ W' := by
    intro x hx
    by_cases hxI : x ∈ I
    · exact Finset.mem_union_left _ hxI
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxI⟩)
  have hfin : k + 1 ≤ I.card + W'.card :=
    calc k + 1 = W.card := hWcard.symm
      _ ≤ (I ∪ W').card := Finset.card_le_card hWsub
      _ ≤ I.card + W'.card := Finset.card_union_le _ _
  omega

/-- The unpinned certificate is the case `I = O = ∅` (consistency check of the statement). -/
theorem floor_of_cover_capacity_of_pinned {k t N : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 (2 * (k + 1)))
    (p q : Fin N → ℕ) (hq : ∀ j, 0 < q j) (bad : Fin N → Finset ℕ)
    (hbad : ∀ j, ∀ x, 1 ≤ x → x ≤ 2 * (k + 1) →
      goodAt k x (p j) (q j) = false → x ∈ bad j)
    (U : Fin t → Finset ℕ) (c : Fin t → ℕ)
    (hcover : Finset.Icc 1 (2 * (k + 1)) ⊆ Finset.univ.biUnion U)
    (hcap : ∀ i, ∀ T ∈ (U i).powerset, c i < T.card → ∃ j, bad j ⊆ T)
    (hsum : ∑ i, c i < k + 1) :
    1 / ((k : ℝ) + 2) ≤ ML v :=
  floor_of_pinned_cover v hv hinj hden p q hq bad hbad ∅ ∅ (Finset.empty_subset _)
    (by simp) (by simp) U c (by simpa using hcover)
    (by intro i T hT hc; obtain ⟨j, hj⟩ := hcap i T hT hc; exact ⟨j, by simpa using hj⟩)
    (by simpa using hsum)

/-- Exhaustive three-way split on two window elements `a`, `b` being speeds or not. -/
theorem pinned_tree_three (a b : ℕ) {n : ℕ} (v : Fin n → ℤ) (G : Prop)
    (hB : (∀ i, (v i).toNat ≠ a) → G)
    (hC : (∃ i, (v i).toNat = a) → (∀ i, (v i).toNat ≠ b) → G)
    (hA : (∃ i, (v i).toNat = a) → (∃ i, (v i).toNat = b) → G) : G := by
  by_cases ha : ∃ i, (v i).toNat = a
  · by_cases hb : ∃ i, (v i).toNat = b
    · exact hA ha hb
    · exact hC ha (by push_neg at hb; exact hb)
  · exact hB (by push_neg at ha; exact ha)

end LRSpectrumFull
