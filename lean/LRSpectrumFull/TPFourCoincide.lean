/-
# TP'(4), module M5c: Lemma 6 (coincidence of two centres)

Hand proof: INVENTION_2026_11/tp4/HANDPROOF_v2.md, Lemma 6.

* `exists_exact`  : for `D ≠ 0`, `w ≥ 1`, `σ`, unless `D ∣ w` and `5 ∣ (w / D) σ`, there are `x` and an integer
  `m` with `D x + σ/5 = m` exactly and `1/5 ≤ tpDist (w x)` (coset `x_k = (k - σ/5)/D`; the case `D ∣ w` is the
  single value `-(w/D) σ / 5`, handled by `tp_residue`).
* `case6`         : if the centres of runners `a`, `b` (with `v_b ≡ ε v_a`) coincide exactly, their bad sets are
  equal, so with any third free runner at most `2 + 2 < 5` residues are bad.
-/
import LRSpectrumFull.TPFourCoset
import LRSpectrumFull.TPFourArcs

namespace LRSpectrumFull

lemma exists_exact_pos (D : ℤ) (hD : 0 < D) (w : ℕ) (σ : ℤ)
    (hnot : ¬ (D ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / D) * σ)) :
    ∃ x : ℝ, ∃ m : ℤ, (D : ℝ) * x + σ / 5 = m ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hdvd : D ∣ (w : ℤ)
  · obtain ⟨w2, hw2⟩ := hdvd
    have h5 : ¬ (5 : ℤ) ∣ w2 * σ := by
      intro h
      apply hnot
      refine ⟨⟨w2, hw2⟩, ?_⟩
      rw [hw2, Int.mul_ediv_cancel_left _ hD.ne']
      exact h
    have key : ∀ N : ℤ, ¬ (5 : ℤ) ∣ N → (-N) % 5 ≠ 0 := by
      intro N hN h
      apply hN
      omega
    have hres := tp_residue 5 (by norm_num) (-(w2 * σ)) (key _ h5)
    refine ⟨(0 - (σ : ℝ) / 5) / D, 0, by push_cast; field_simp; ring, ?_⟩
    have hwR : (w : ℝ) = D * w2 := by exact_mod_cast hw2
    have e : (w : ℝ) * ((0 - (σ : ℝ) / 5) / D) = ((-(w2 * σ) : ℤ) : ℝ) / ((5 : ℕ) : ℝ) := by
      rw [hwR]; push_cast; field_simp; ring
    rw [e]
    simpa using hres
  · obtain ⟨k, hk⟩ := coset_branch D hD w hdvd σ
    exact ⟨((k : ℝ) - σ / 5) / D, k, by field_simp; ring, hk⟩

lemma exists_exact (D : ℤ) (hD : D ≠ 0) (w : ℕ) (σ : ℤ)
    (hnot : ¬ (D ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / D) * σ)) :
    ∃ x : ℝ, ∃ m : ℤ, (D : ℝ) * x + σ / 5 = m ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x) := by
  rcases lt_or_gt_of_ne hD with h | h
  · obtain ⟨x, m, h1, h2⟩ := exists_exact_pos (-D) (by omega) w (-σ) (by
      intro ⟨a, b⟩
      apply hnot
      refine ⟨(neg_dvd).mp a, ?_⟩
      rw [Int.ediv_neg, neg_mul, mul_neg, neg_neg] at b
      exact b)
    refine ⟨x, -m, ?_, h2⟩
    push_cast at h1 ⊢
    linarith
  · exact exists_exact_pos D h w σ hnot

/-- The membership `ε z ∈ arc β` is `z ∈ arc (ε β + 5 m)`. -/
lemma mem_arc_eps (ε m : ℤ) (hε : ε = 1 ∨ ε = -1) (z : ZMod 5) (β : ℝ) :
    (ε : ZMod 5) * z ∈ arc β ↔ z ∈ arc ((ε : ℝ) * β + ((5 * m : ℤ) : ℝ)) := by
  rcases hε with rfl | rfl
  · simp only [Int.cast_one, one_mul]
    rw [arc_add_int β m]
  · have h1 : arc (((-1 : ℤ) : ℝ) * β + ((5 * m : ℤ) : ℝ)) = arc (-β) := by
      rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact arc_add_int (-β) m
    rw [h1, ← neg_mem_arc_iff]
    have h2 : ((-1 : ℤ) : ZMod 5) * z = -z := by push_cast; ring
    rw [h2]

/-- Runners `a`, `b` with `v_b ≡ ε v_a` and `β_a = ε β_b + 5 m` have the same bad residues. -/
lemma badImg_eq_of_class (va vb : ℕ) (βa βb : ℝ) (ε m : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ha : (va : ZMod 5) ≠ 0) (hb : (vb : ZMod 5) = (ε : ZMod 5) * va)
    (h : βa = (ε : ℝ) * βb + ((5 * m : ℤ) : ℝ)) : badImg vb βb = badImg va βa := by
  have hb0 : (vb : ZMod 5) ≠ 0 := by
    intro h0
    rw [hb] at h0
    rcases hε with rfl | rfl <;> simp at h0 <;> exact ha h0
  ext j
  rw [mem_badImg_iff hb0, mem_badImg_iff ha, h, ← mem_arc_eps ε m hε, hb]
  have : -((ε : ZMod 5) * va * j) = (ε : ZMod 5) * -((va : ZMod 5) * j) := by ring
  rw [this]

lemma case6 (w : ℕ) (va vb vc : ℕ) (sa sb sc : ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ha : ¬ 5 ∣ va) (hc5 : ¬ 5 ∣ vc) (hb : (vb : ZMod 5) = (ε : ZMod 5) * va)
    (D : ℤ) (hD : (va : ℤ) - ε * vb = 5 * D) (hne : (va : ℤ) ≠ ε * vb)
    (hnot : ¬ (D ∣ (w : ℤ) ∧ (5 : ℤ) ∣ ((w : ℤ) / D) * (sa - ε * sb))) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x) ∧ ∃ j : ZMod 5,
      Good va sa ((((j.val : ℕ) : ℝ) + x) / 5) ∧ Good vb sb ((((j.val : ℕ) : ℝ) + x) / 5) ∧
        Good vc sc ((((j.val : ℕ) : ℝ) + x) / 5) := by
  have ha0 : (va : ZMod 5) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff va 5).mp h)
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply hne
    omega
  obtain ⟨x, m, hx, hfar⟩ := exists_exact D hD0 w (sa - ε * sb) hnot
  have hDR : ((va : ℤ) : ℝ) - (ε : ℝ) * (vb : ℝ) = 5 * (D : ℝ) := by exact_mod_cast hD
  have hcen : ((sa : ℝ) + va * x) = (ε : ℝ) * ((sb : ℝ) + vb * x) + ((5 * m : ℤ) : ℝ) := by
    push_cast at hx hDR ⊢
    linear_combination x * hDR + 5 * hx
  have hb5 : ¬ 5 ∣ vb := by
    intro h5
    have : (vb : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff vb 5).mpr h5
    rw [hb] at this
    rcases hε with rfl | rfl <;> simp at this <;> exact ha0 this
  have heq := badImg_eq_of_class va vb _ _ ε m hε ha0 hb hcen
  have hlt : (badImg va ((sa : ℝ) + va * x) ∪ badImg vc ((sc : ℝ) + vc * x)).card
      < Fintype.card (ZMod 5) := by
    rw [ZMod.card]
    have h1 := Finset.card_union_le (badImg va ((sa : ℝ) + va * x)) (badImg vc ((sc : ℝ) + vc * x))
    have h2 := card_badImg_le_two va ((sa : ℝ) + va * x)
    have h3 := card_badImg_le_two vc ((sc : ℝ) + vc * x)
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := badImg va ((sa : ℝ) + va * x) ∪ badImg vc ((sc : ℝ) + vc * x))
    (t := (Finset.univ : Finset (ZMod 5))) (by rwa [Finset.card_univ])
  have hja : j ∉ badImg va ((sa : ℝ) + va * x) := fun h => hj (Finset.mem_union_left _ h)
  have hjc : j ∉ badImg vc ((sc : ℝ) + vc * x) := fun h => hj (Finset.mem_union_right _ h)
  have hjb : j ∉ badImg vb ((sb : ℝ) + vb * x) := by rw [heq]; exact hja
  exact ⟨x, hfar, j, good_of_not_mem_badImg ha sa x j hja, good_of_not_mem_badImg hb5 sb x j hjb,
    good_of_not_mem_badImg hc5 sc x j hjc⟩

end LRSpectrumFull
