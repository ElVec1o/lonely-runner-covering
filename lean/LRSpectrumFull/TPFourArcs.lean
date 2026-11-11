/-
# TP'(4), module M4: arcs on `ZMod 5` and the covering core of Case 2+1

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Section 3 (common coordinate) and Lemma 5.

`arc γ` is the image in `ZMod 5` of the integers `k` with `⌊γ⌋ ≤ k ≤ ⌈γ⌉`; the bad residues of a free runner are
`badImg v β = -(v⁻¹) · arc β` (`badImg_eq`), equivalently `j ∈ badImg v β ↔ -(v j) ∈ arc β` (`mem_badImg_iff`).
So in the coordinate `z = -(v_a j)` the runner `a` is the arc around `β_a`, a runner with `v ≡ ε v_a` (`ε = ±1`)
is the arc around `ε β` (`neg_mem_arc_iff` handles `ε = -1`), and a runner with `v ≡ λ v_a`, `λ ∈ {2, 3}`, is a set
of at most two residues no two of which are consecutive.

* `core5`            : two arcs whose centres are within 1 of each other, plus a set `P` of at most two residues
  without consecutive pair, miss a common residue.  (Lemma 5, the window `|c_b - c_a| ≤ 1`.)
* `exists_good_21`   : the same statement for three runners, in terms of `badImg`.
-/
import LRSpectrumFull.TPFourLocal

namespace LRSpectrumFull

/-- The residues mod 5 of the integers in the closed hull of the open interval `(γ - 1, γ + 1)`. -/
noncomputable def arc (γ : ℝ) : Finset (ZMod 5) :=
  (Finset.Icc ⌊γ⌋ ⌈γ⌉).image (fun k : ℤ => (k : ZMod 5))

lemma badImg_eq (v : ℕ) (β : ℝ) :
    badImg v β = (arc β).image (fun u => -((v : ZMod 5)⁻¹ * u)) := by
  unfold badImg arc
  rw [Finset.image_image]
  rfl

lemma mem_badImg_iff {v : ℕ} (hv : (v : ZMod 5) ≠ 0) (β : ℝ) (j : ZMod 5) :
    j ∈ badImg v β ↔ -((v : ZMod 5) * j) ∈ arc β := by
  rw [badImg_eq, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : -((v : ZMod 5) * -((v : ZMod 5)⁻¹ * u)) = u := by
      rw [mul_neg, neg_neg, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    rw [this]
    exact hu
  · intro h
    refine ⟨-((v : ZMod 5) * j), h, ?_⟩
    rw [mul_neg, neg_neg, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

lemma neg_mem_arc_iff (z : ZMod 5) (β : ℝ) : -z ∈ arc β ↔ z ∈ arc (-β) := by
  unfold arc
  rw [Int.floor_neg, Int.ceil_neg]
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, hk⟩
    exact ⟨-k, ⟨by omega, by omega⟩, by push_cast; simp [hk]⟩
  · rintro ⟨k, ⟨h1, h2⟩, hk⟩
    exact ⟨-k, ⟨by omega, by omega⟩, by push_cast; simp [hk]⟩

lemma arc_int_card (m : ℤ) : (arc (m : ℝ)).card ≤ 1 := by
  unfold arc
  rw [Int.floor_intCast, Int.ceil_intCast]
  refine Finset.card_image_le.trans ?_
  simp

lemma arc_add_int (γ : ℝ) (m : ℤ) : arc (γ + ((5 * m : ℤ) : ℝ)) = arc γ := by
  ext z
  have h5 : (5 : ZMod 5) = 0 := by decide
  simp only [arc, Finset.mem_image, Finset.mem_Icc, Int.floor_add_intCast, Int.ceil_add_intCast]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, hk⟩
    refine ⟨k - 5 * m, ⟨by omega, by omega⟩, ?_⟩
    push_cast
    rw [h5, zero_mul, sub_zero]
    rw [← hk]
  · rintro ⟨k, ⟨h1, h2⟩, hk⟩
    refine ⟨k + 5 * m, ⟨by omega, by omega⟩, ?_⟩
    push_cast
    rw [h5, zero_mul, add_zero]
    exact hk

/-- Two elements of one arc are equal or consecutive. -/
lemma arc_adj (β : ℝ) (p q : ZMod 5) (hp : p ∈ arc β) (hq : q ∈ arc β) :
    q = p ∨ q = p + 1 ∨ p = q + 1 := by
  unfold arc at hp hq
  simp only [Finset.mem_image, Finset.mem_Icc] at hp hq
  obtain ⟨k1, ⟨a1, a2⟩, rfl⟩ := hp
  obtain ⟨k2, ⟨b1, b2⟩, rfl⟩ := hq
  have hc := Int.ceil_le_floor_add_one β
  rcases (by omega : k2 = k1 ∨ k2 = k1 + 1 ∨ k1 = k2 + 1) with h | h | h
  · left; rw [h]
  · right; left; rw [h]; push_cast; ring
  · right; right; rw [h]; push_cast; ring

/-- A residue `k + 2` or `k + 3` is not in an arc that contains the integer `k` in its integer range. -/
lemma arc_far (g : ℝ) (k : ℤ) (h1 : k ≤ ⌈g⌉) (h2 : ⌊g⌋ ≤ k) (c : ZMod 5) (hc : c = 2 ∨ c = 3) :
    (k : ZMod 5) + c ∉ arc g := by
  intro hmem
  unfold arc at hmem
  simp only [Finset.mem_image, Finset.mem_Icc] at hmem
  obtain ⟨k', ⟨l1, l2⟩, hk'⟩ := hmem
  have hc' := Int.ceil_le_floor_add_one g
  have hd : ((k' - k : ℤ) : ZMod 5) = c := by
    push_cast
    rw [hk']
    ring
  rcases (by omega : k' - k = -1 ∨ k' - k = 0 ∨ k' - k = 1) with h | h | h <;>
    rw [h] at hd <;> push_cast at hd <;> rcases hc with rfl | rfl <;> revert hd <;> decide

lemma core_inter (g1 g2 : ℝ) (h1 : g1 ≤ g2) (h2 : g2 ≤ g1 + 1) :
    (∃ k : ℤ, (⌊g1⌋ ≤ k ∧ k ≤ ⌈g1⌉) ∧ (⌊g2⌋ ≤ k ∧ k ≤ ⌈g2⌉)) ∨
      (∃ m1 m2 : ℤ, g1 = m1 ∧ g2 = m2) := by
  have f12 : ⌊g1⌋ ≤ ⌊g2⌋ := Int.floor_mono h1
  have c12 : ⌈g1⌉ ≤ ⌈g2⌉ := Int.ceil_mono h1
  have fc2 := Int.floor_le_ceil g2
  have fc1 := Int.floor_le_ceil g1
  have fle : ⌊g2⌋ ≤ ⌊g1⌋ + 1 := by
    have := Int.floor_mono h2
    rwa [Int.floor_add_one] at this
  by_cases hg1 : g1 = (⌊g1⌋ : ℝ)
  · by_cases hg2 : g2 = (⌊g2⌋ : ℝ)
    · exact Or.inr ⟨⌊g1⌋, ⌊g2⌋, hg1, hg2⟩
    · left
      refine ⟨⌊g1⌋, ⟨le_refl _, fc1⟩, ?_, by omega⟩
      have hlt : (⌊g2⌋ : ℝ) < g2 := lt_of_le_of_ne (Int.floor_le g2) (Ne.symm hg2)
      have : (⌊g2⌋ : ℝ) < (⌊g1⌋ : ℝ) + 1 := by linarith
      have : ⌊g2⌋ < ⌊g1⌋ + 1 := by exact_mod_cast this
      omega
  · left
    have hlt : (⌊g1⌋ : ℝ) < g1 := lt_of_le_of_ne (Int.floor_le g1) (Ne.symm hg1)
    have hlt2 : (⌊g1⌋ : ℝ) < (⌈g1⌉ : ℝ) := lt_of_lt_of_le hlt (Int.le_ceil g1)
    have : ⌊g1⌋ < ⌈g1⌉ := by exact_mod_cast hlt2
    exact ⟨⌈g1⌉, ⟨by omega, le_refl _⟩, by omega, c12⟩

/-- Case 2+1, covering core: two arcs with centres within 1 and a pentagram-type set. -/
lemma core5 (g1 g2 : ℝ) (h : |g1 - g2| ≤ 1) (P : Finset (ZMod 5)) (hP : P.card ≤ 2)
    (hadj : ∀ p ∈ P, ∀ q ∈ P, q ≠ p + 1) :
    ∃ z : ZMod 5, z ∉ arc g1 ∧ z ∉ arc g2 ∧ z ∉ P := by
  suffices H : ∀ g1 g2 : ℝ, g1 ≤ g2 → g2 ≤ g1 + 1 →
      ∃ z : ZMod 5, z ∉ arc g1 ∧ z ∉ arc g2 ∧ z ∉ P by
    rcases le_total g1 g2 with h' | h'
    · exact H g1 g2 h' (by have := abs_le.mp h; linarith)
    · obtain ⟨z, a, b, c⟩ := H g2 g1 h' (by have := abs_le.mp h; linarith)
      exact ⟨z, b, a, c⟩
  intro g1 g2 h1 h2
  rcases core_inter g1 g2 h1 h2 with ⟨k, ⟨a1, a2⟩, ⟨b1, b2⟩⟩ | ⟨m1, m2, e1, e2⟩
  · by_cases hP2 : ((k : ZMod 5) + 2) ∈ P
    · refine ⟨(k : ZMod 5) + 3, arc_far g1 k a2 a1 3 (Or.inr rfl),
        arc_far g2 k b2 b1 3 (Or.inr rfl), fun hP3 => ?_⟩
      exact hadj _ hP2 _ hP3 (by ring)
    · exact ⟨(k : ZMod 5) + 2, arc_far g1 k a2 a1 2 (Or.inl rfl),
        arc_far g2 k b2 b1 2 (Or.inl rfl), hP2⟩
  · by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset (ZMod 5)) ⊆ arc g1 ∪ arc g2 ∪ P := by
      intro z _
      by_cases a : z ∈ arc g1
      · simp [a]
      · by_cases b : z ∈ arc g2
        · simp [b]
        · simp [hno z a b]
    have c1 : (arc g1).card ≤ 1 := by rw [e1]; exact arc_int_card m1
    have c2 : (arc g2).card ≤ 1 := by rw [e2]; exact arc_int_card m2
    have := Finset.card_le_card hsub
    have u1 := Finset.card_union_le (arc g1 ∪ arc g2) P
    have u2 := Finset.card_union_le (arc g1) (arc g2)
    rw [Finset.card_univ, ZMod.card] at this
    omega

/-- Case 2+1 for `badImg`: runner `a` free, runner `b` with `v_b ≡ ε v_a` (`ε = ±1`) whose centre `ε β_b` is
within `1` of `β_a` after a shift by `5 m`, runner `c` with `v_c ≡ λ v_a`, `λ ∈ {2, 3}`. -/
lemma exists_good_21 (va vb vc : ℕ) (βa βb βc : ℝ) (ε m : ℤ) (hε : ε = 1 ∨ ε = -1)
    (lc : ZMod 5) (hlc : lc = 2 ∨ lc = 3) (ha : (va : ZMod 5) ≠ 0)
    (hb : (vb : ZMod 5) = (ε : ZMod 5) * va) (hc : (vc : ZMod 5) = lc * va)
    (h : |βa - (ε * βb + ((5 * m : ℤ) : ℝ))| ≤ 1) :
    ∃ j : ZMod 5, j ∉ badImg va βa ∧ j ∉ badImg vb βb ∧ j ∉ badImg vc βc := by
  have hb0 : (vb : ZMod 5) ≠ 0 := by
    intro h0
    rw [hb] at h0
    rcases hε with rfl | rfl <;> simp at h0 <;> exact ha h0
  have hlc0 : lc ≠ 0 := by rcases hlc with rfl | rfl <;> decide
  have hc0 : (vc : ZMod 5) ≠ 0 := by
    rw [hc]; exact mul_ne_zero hlc0 ha
  set Pz : Finset (ZMod 5) := (badImg vc βc).image (fun j : ZMod 5 => -((va : ZMod 5) * j)) with hPz
  have hP : Pz.card ≤ 2 := Finset.card_image_le.trans (card_badImg_le_two vc βc)
  have key : ∀ (l p : ZMod 5), (l = 2 ∨ l = 3) →
      ¬ (l * (p + 1) = l * p ∨ l * (p + 1) = l * p + 1 ∨ l * p = l * (p + 1) + 1) := by decide
  have hadj : ∀ p ∈ Pz, ∀ q ∈ Pz, q ≠ p + 1 := by
    intro p hp q hq hqp
    rw [hPz, Finset.mem_image] at hp hq
    obtain ⟨j1, hj1, rfl⟩ := hp
    obtain ⟨j2, hj2, rfl⟩ := hq
    rw [mem_badImg_iff hc0] at hj1 hj2
    have e1 : -((vc : ZMod 5) * j1) = lc * -((va : ZMod 5) * j1) := by rw [hc]; ring
    have e2 : -((vc : ZMod 5) * j2) = lc * -((va : ZMod 5) * j2) := by rw [hc]; ring
    rw [e1] at hj1
    rw [e2] at hj2
    have := arc_adj βc _ _ hj1 hj2
    rw [hqp] at this
    exact key lc _ hlc this
  obtain ⟨z, hz1, hz2, hz3⟩ := core5 βa (ε * βb + ((5 * m : ℤ) : ℝ)) h Pz hP hadj
  have hj : -((va : ZMod 5) * (-((va : ZMod 5)⁻¹ * z))) = z := by
    rw [mul_neg, neg_neg, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨-((va : ZMod 5)⁻¹ * z), ?_, ?_, ?_⟩
  · rw [mem_badImg_iff ha, hj]; exact hz1
  · have e : -((vb : ZMod 5) * -((va : ZMod 5)⁻¹ * z)) = (ε : ZMod 5) * z := by
      rw [hb]
      have h1 : (va : ZMod 5) * (va : ZMod 5)⁻¹ = 1 := mul_inv_cancel₀ ha
      calc -((ε : ZMod 5) * va * -((va : ZMod 5)⁻¹ * z))
          = (ε : ZMod 5) * ((va : ZMod 5) * (va : ZMod 5)⁻¹) * z := by ring
        _ = (ε : ZMod 5) * z := by rw [h1]; ring
    rw [mem_badImg_iff hb0, e]
    intro hmem
    apply hz2
    rcases hε with rfl | rfl
    · have h1 : arc ((((1 : ℤ)) : ℝ) * βb + ((5 * m : ℤ) : ℝ)) = arc βb := by
        rw [Int.cast_one, one_mul]; exact arc_add_int βb m
      rw [h1]
      simpa using hmem
    · have h1 : arc ((((-1 : ℤ)) : ℝ) * βb + ((5 * m : ℤ) : ℝ)) = arc (-βb) := by
        rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact arc_add_int (-βb) m
      rw [h1]
      have h2 : ((((-1 : ℤ)) : ZMod 5) * z) = -z := by push_cast; ring
      rw [h2] at hmem
      exact (neg_mem_arc_iff z βb).mp hmem
  · intro hmem
    apply hz3
    rw [hPz, Finset.mem_image]
    exact ⟨_, hmem, hj⟩

end LRSpectrumFull
