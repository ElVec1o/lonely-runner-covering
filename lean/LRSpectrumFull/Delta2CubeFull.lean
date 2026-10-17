/-
# The full-support cube-single bridge

`bridge_cube_single_full` — the `s = k+1` edge of the single-line bridge: a
`(k+1)`-family (`k ≥ 4`) carrying a `±1` relation of **full** support whose
only vanishing `[-3,3]`-combinations are the seven multiples `λ·r`,
`|λ| ≤ 3`, meets the floor `1/(k+2)`.

This is the case `bridge_cube_single_general` cannot reach: its factorization
splits the mass off `(5/2)^{k-s}`, which is ℕ-truncated at `s = k+1`.  Full
support makes the computation *shorter* instead: no runner is exempt, so
every weight product is a plain power `a^{k+1}`, and every subfamily is
`ThreeDissoc` — deleting any runner destroys all seven multiples at once —
so each `Msub i = Q(5/2)^k` with no correction term.  The union close is the
same `u³(k+1) < 7/8` as the general case.
-/
import LRSpectrumFull.Delta2DisjointTriples

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- Deleting a runner from a full-support single-line family leaves a
`ThreeDissoc` subfamily: a vanishing cube-combination of the subfamily lifts
(by `insertNth 0`) to a vanishing cube-combination of the family, hence to a
multiple `λ·r`; but the lift is `0` at the deleted coordinate while `r` is
not, so `λ = 0`. -/
theorem subfamily_dissoc_of_full {k : ℕ} (v : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hr : ∀ w, r w = -1 ∨ r w = 1)
    (hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = (fun w => 2 * r w) ∨ c = (fun w => -(2 * r w))
          ∨ c = (fun w => 3 * r w) ∨ c = (fun w => -(3 * r w)))
    (i : Fin (k + 1)) :
    ThreeDissoc (fun j' : Fin k => v (i.succAbove j')) := by
  intro d hd hdv
  have hri : r i ≠ 0 := by rcases hr i with h | h <;> rw [h] <;> omega
  set c : Fin (k + 1) → ℤ := i.insertNth 0 d with hcdef
  have hci : c i = 0 := by rw [hcdef, Fin.insertNth_apply_same]
  have hcs : ∀ j' : Fin k, c (i.succAbove j') = d j' := by
    intro j'
    rw [hcdef, Fin.insertNth_apply_succAbove]
  have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
    intro w
    rcases Fin.eq_self_or_eq_succAbove i w with rfl | ⟨j', rfl⟩
    · rw [hci]; omega
    · rw [hcs j']; exact hd j'
  have hcv : (∑ w, c w * v w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hci, zero_mul, zero_add]
    rw [Finset.sum_congr rfl (fun j' _ => by rw [hcs j'])]
    exact hdv
  -- a nonzero multiple of `r` is nonzero at `i`; the lift is not
  have hz : ∀ (f : Fin (k + 1) → ℤ), c = f → f i ≠ 0 → False := by
    intro f hf hfi
    exact hfi (hci ▸ congrFun hf i).symm
  rcases hcube c hcb hcv with h | h | h | h | h | h | h
  · funext j'
    have := congrFun h (i.succAbove j')
    rw [hcs j'] at this
    simpa using this
  · exact (hz r h hri).elim
  · exact (hz (-r) h (by simp [hri])).elim
  · exact (hz _ h (by simpa using mul_ne_zero two_ne_zero hri)).elim
  · exact (hz _ h (by simp only [neg_ne_zero]; exact mul_ne_zero two_ne_zero hri)).elim
  · exact (hz _ h (by simpa using mul_ne_zero three_ne_zero hri)).elim
  · exact (hz _ h (by simp only [neg_ne_zero]; exact mul_ne_zero three_ne_zero hri)).elim

/-- Deleting a runner does not increase the `ℓ¹` size of a family. -/
theorem subfamily_l1_le {k : ℕ} (v : Fin (k + 1) → ℤ) (i : Fin (k + 1)) :
    (∑ j' : Fin k, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
  rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
  omega

/-- At full support every weight product is a plain power: `∏ cubeWtR (λ r w) = a^{k+1}`. -/
theorem full_prod_eval {k : ℕ} (r : Fin (k + 1) → ℤ) (hr : ∀ w, r w = -1 ∨ r w = 1)
    (lam : ℤ) (a : ℝ) (hval : ∀ ρ : ℤ, (ρ = -1 ∨ ρ = 1) → cubeWtR (lam * ρ) = a) :
    (∏ w : Fin (k + 1), cubeWtR (lam * r w)) = a ^ (k + 1) := by
  rw [Finset.prod_congr rfl (fun w _ => hval (r w) (hr w))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The full-support relation mass factor is at least `(7/20)(5/2)^{k+1}`: the
`±1` and `±3` weights are the only negative ones and both are dominated. -/
theorem full_mass_lower {n : ℕ} (hn : 5 ≤ n) :
    (7/20 : ℝ) * (5/2 : ℝ) ^ n
      ≤ (5/2 : ℝ) ^ n + 2 * (-15/8 : ℝ) ^ n + 2 * (3/4 : ℝ) ^ n + 2 * (-1/8 : ℝ) ^ n := by
  have hX : (0 : ℝ) < (5/2 : ℝ) ^ n := by positivity
  have hT : (15/8 : ℝ) ^ n = (3/4 : ℝ) ^ n * (5/2 : ℝ) ^ n := by
    rw [← mul_pow]; norm_num
  have hV : (1/8 : ℝ) ^ n = (1/20 : ℝ) ^ n * (5/2 : ℝ) ^ n := by
    rw [← mul_pow]; norm_num
  have h34 : (3/4 : ℝ) ^ n ≤ (3/4 : ℝ) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h120 : (1/20 : ℝ) ^ n ≤ (1/20 : ℝ) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hTneg : -((15/8 : ℝ) ^ n) ≤ (-15/8 : ℝ) ^ n := by
    have h := neg_abs_le ((-15/8 : ℝ) ^ n)
    rw [abs_pow, show |(-15/8 : ℝ)| = 15/8 from by
      rw [abs_of_neg (by norm_num : (-15/8 : ℝ) < 0)]; norm_num] at h
    exact h
  have hVneg : -((1/8 : ℝ) ^ n) ≤ (-1/8 : ℝ) ^ n := by
    have h := neg_abs_le ((-1/8 : ℝ) ^ n)
    rw [abs_pow, show |(-1/8 : ℝ)| = 1/8 from by
      rw [abs_of_neg (by norm_num : (-1/8 : ℝ) < 0)]; norm_num] at h
    exact h
  have hUpos : (0 : ℝ) ≤ (3/4 : ℝ) ^ n := by positivity
  have h1320 : (15/8 : ℝ) ^ n + (1/8 : ℝ) ^ n ≤ (13/40) * (5/2 : ℝ) ^ n := by
    rw [hT, hV]
    have hpa := mul_le_mul_of_nonneg_right h34 (le_of_lt hX)
    have hpb := mul_le_mul_of_nonneg_right h120 (le_of_lt hX)
    nlinarith [hpa, hpb]
  linarith [hTneg, hVneg, hUpos, h1320]

/-- **The uniform union close**, shared with the general case: at `δ = 1/(k+2)`
and `k ≥ 4`, `(1 - cos 2πδ)³ · (k+1) < 7/8`. -/
theorem cube_union_close {k : ℕ} (hk : 4 ≤ k) :
    (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * ((k : ℝ) + 1) < 7/8 := by
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  have hδ61 : δ ^ 6 * ((k : ℝ) + 2) ^ 6 = 1 := by
    rw [← mul_pow, hδval, one_pow]
  have hkey : 64 * π ^ 6 * ((k : ℝ) + 1) < 7 * ((k : ℝ) + 2) ^ 6 := by
    have h64 : (1296 : ℝ) ≤ ((k : ℝ) + 2) ^ 4 := by
      calc (1296 : ℝ) = 6 ^ 4 := by norm_num
        _ ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h6b : 1296 * ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 6 := by
      have hsplit : ((k : ℝ) + 2) ^ 6 = ((k : ℝ) + 2) ^ 4 * ((k : ℝ) + 2) ^ 2 := by ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right h64 (by positivity)
    have hπk : π ^ 6 * ((k : ℝ) + 1) < 961.51 * ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hπ6 (by linarith)
    nlinarith [hπk, h6b, hkR,
      mul_le_mul_of_nonneg_left hkR (by linarith : (0 : ℝ) ≤ (k : ℝ))]
  calc (1 - Real.cos (2 * π * δ)) ^ 3 * ((k : ℝ) + 1)
      < (2 * (π * δ) ^ 2) ^ 3 * ((k : ℝ) + 1) :=
        mul_lt_mul_of_pos_right hu3 (by linarith)
    _ = (8 * π ^ 6 * ((k : ℝ) + 1)) * δ ^ 6 := by ring
    _ < ((7/8) * ((k : ℝ) + 2) ^ 6) * δ ^ 6 := by
        refine mul_lt_mul_of_pos_right ?_ (pow_pos hδ0 6)
        nlinarith [hkey]
    _ = (7/8) * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by ring
    _ = 7/8 := by rw [hδ61, mul_one]

set_option maxHeartbeats 1600000 in
/-- **The full-support cube-single bridge** (`s = k+1`).  A `(k+1)`-family
(`k ≥ 4`) carrying a `±1` relation `r` of full support, whose only vanishing
`[-3,3]`-combinations are the seven multiples `λ·r` with `|λ| ≤ 3`, meets the
floor `1/(k+2)`.

The mass is `Q·((5/2)^{k+1} + 2(-15/8)^{k+1} + 2(3/4)^{k+1} + 2(-1/8)^{k+1})`;
every subfamily is `ThreeDissoc` (`subfamily_dissoc_of_full`), so the union
side is exactly `(k+1)·Q(5/2)^k` with no correction, and the close is
`u³(k+1) < 7/8` against the `(7/20)(5/2)^{k+1} = (7/8)(5/2)^k` mass floor. -/
theorem bridge_cube_single_full {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hr : ∀ w, r w = -1 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = (fun w => 2 * r w) ∨ c = (fun w => -(2 * r w))
          ∨ c = (fun w => 3 * r w) ∨ c = (fun w => -(3 * r w))) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set w₀ : Fin (k + 1) := ⟨0, by omega⟩ with hw₀def
  have hρ : r w₀ = -1 ∨ r w₀ = 1 := hr w₀
  have hval_ne : ∀ (f g : Fin (k + 1) → ℤ), f w₀ ≠ g w₀ → f ≠ g :=
    fun f g h hc => h (congrFun hc w₀)
  have hrb : ∀ (lam : ℤ), (-3 ≤ lam) → (lam ≤ 3) → ∀ w, -3 ≤ lam * r w ∧ lam * r w ≤ 3 := by
    intro lam h1 h3 w
    rcases hr w with h | h <;> rw [h] <;> constructor <;> nlinarith
  -- the seven weight products, plain powers at full support
  have hP1 : (∏ w : Fin (k + 1), cubeWtR (1 * r w)) = (-15/8 : ℝ) ^ (k + 1) :=
    full_prod_eval r hr 1 _ (fun ρ hρ' => by rcases hρ' with h | h <;> rw [h] <;>
      norm_num [cubeWtR])
  have hP2 : (∏ w : Fin (k + 1), cubeWtR (2 * r w)) = (3/4 : ℝ) ^ (k + 1) :=
    full_prod_eval r hr 2 _ (fun ρ hρ' => by rcases hρ' with h | h <;> rw [h] <;>
      norm_num [cubeWtR])
  have hP3 : (∏ w : Fin (k + 1), cubeWtR (3 * r w)) = (-1/8 : ℝ) ^ (k + 1) :=
    full_prod_eval r hr 3 _ (fun ρ hρ' => by rcases hρ' with h | h <;> rw [h] <;>
      norm_num [cubeWtR])
  -- the vanishing cube-set is exactly the seven multiples
  have hvan : ∀ (lam : ℤ), (∑ w, (lam * r w) * v w) = 0 := by
    intro lam
    have h1 : (∑ w, (lam * r w) * v w) = lam * ∑ w, r w * v w := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [h1, hrel, mul_zero]
  have hbox : ∀ (d : Fin (k + 1) → ℤ), (∀ w, -3 ≤ d w ∧ d w ≤ 3) →
      d ∈ Fintype.piFinset (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
    intro d hd
    rw [Fintype.mem_piFinset]
    intro w
    have := hd w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hfilter : (Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0)
      = {0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
         fun w => 3 * r w, fun w => -(3 * r w)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      rcases hcube c hcb hcv with h|h|h|h|h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right; left; exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · right; right; right; right; left; rw [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · right; right; right; right; right; right; rw [h]
    · intro hmem
      rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · exact ⟨hbox _ (fun w => by rcases hr w with h|h <;> rw [h] <;> omega), hrel⟩
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          rcases hr w with h|h <;> rw [h] <;> omega), ?_⟩
        have h1 : (∑ w, (-r) w * v w) = -(∑ w, r w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
      · exact ⟨hbox _ (hrb 2 (by norm_num) (by norm_num)), hvan 2⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 2 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(2 * r w)) * v w) = -(∑ w, (2 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 2, neg_zero]
      · exact ⟨hbox _ (hrb 3 (by norm_num) (by norm_num)), hvan 3⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 3 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(3 * r w)) * v w) = -(∑ w, (3 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 3, neg_zero]
  -- the seven-element mass sum
  have hsum7 : (∑ c ∈ ({0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
        fun w => 3 * r w, fun w => -(3 * r w)} : Finset (Fin (k + 1) → ℤ)),
        ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
        + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1) := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 : (∏ w : Fin (k + 1), cubeWtR (r w)) = (-15/8 : ℝ) ^ (k + 1) := by
      have := hP1; simp only [one_mul] at this; exact this
    have e1n : (∏ w : Fin (k + 1), cubeWtR ((-r) w)) = (-15/8 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])]
      exact e1
    have e2 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 2 * r w) w)) = (3/4 : ℝ) ^ (k + 1) := hP2
    have e2n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(2 * r w)) w)) = (3/4 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP2
    have e3 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 3 * r w) w)) = (-1/8 : ℝ) ^ (k + 1) := hP3
    have e3n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(3 * r w)) w)) = (-1/8 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP3
    have d01 : (0 : Fin (k + 1) → ℤ) ≠ r := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d02 : (0 : Fin (k + 1) → ℤ) ≠ -r := hval_ne _ _ (by
      simp only [Pi.zero_apply, Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d03 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d04 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d05 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d06 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d12 : r ≠ -r := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d13 : r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d14 : r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d15 : r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d16 : r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d23 : -r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d24 : -r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d25 : -r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d26 : -r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d34 : (fun w => 2 * r w) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d35 : (fun w => 2 * r w) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d36 : (fun w => 2 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d45 : (fun w => -(2 * r w)) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d46 : (fun w => -(2 * r w)) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d56 : (fun w : Fin (k + 1) => 3 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d01, d02, d03, d04, d05, d06⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14, d15, d16⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24, d25, d26⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d34, d35, d36⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d45, d46⟩),
      Finset.sum_insert (by simpa using d56), Finset.sum_singleton,
      e0, e1, e1n, e2, e2n, e3, e3n]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
        + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1)) := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum7] at h
    exact h
  -- every subfamily is dissociated: the union side is bare
  have hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (5/2 : ℝ) ^ k := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    exact riesz_mass_cube_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
      (subfamily_dissoc_of_full v r hr hcube i)
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
      + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1)))
    (fun _ => (Q : ℝ) * (5/2 : ℝ) ^ k) hM hMsub ?_
  -- the union arithmetic: (k+1) bare subfamily masses against the relation mass
  have hXk : (0 : ℝ) < (5/2 : ℝ) ^ k := by positivity
  have hsumsub : (∑ _i : Fin (k + 1), (Q : ℝ) * (5/2 : ℝ) ^ k)
      = ((k : ℝ) + 1) * ((Q : ℝ) * (5/2 : ℝ) ^ k) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumsub]
  have hlow := full_mass_lower (n := k + 1) (by omega)
  have hpow : (5/2 : ℝ) ^ (k + 1) = (5/2 : ℝ) ^ k * (5/2) := by rw [pow_succ]
  have hfloor : (7/8 : ℝ) * ((Q : ℝ) * (5/2 : ℝ) ^ k)
      ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
        + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1)) := by
    have h1 : (7/8 : ℝ) * (5/2 : ℝ) ^ k = (7/20 : ℝ) * (5/2 : ℝ) ^ (k + 1) := by
      rw [hpow]; ring
    have h2 : (7/8 : ℝ) * (5/2 : ℝ) ^ k
        ≤ (5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
          + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1) := by
      rw [h1]; exact hlow
    calc (7/8 : ℝ) * ((Q : ℝ) * (5/2 : ℝ) ^ k)
        = (Q : ℝ) * ((7/8 : ℝ) * (5/2 : ℝ) ^ k) := by ring
      _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
            + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hQR)
  calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * (((k : ℝ) + 1) * ((Q : ℝ) * (5/2 : ℝ) ^ k))
      = ((1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * ((k : ℝ) + 1))
        * ((Q : ℝ) * (5/2 : ℝ) ^ k) := by ring
    _ < (7/8 : ℝ) * ((Q : ℝ) * (5/2 : ℝ) ^ k) :=
        mul_lt_mul_of_pos_right (cube_union_close hk) (mul_pos hQR hXk)
    _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * (-15/8 : ℝ) ^ (k + 1)
          + 2 * (3/4 : ℝ) ^ (k + 1) + 2 * (-1/8 : ℝ) ^ (k + 1)) := hfloor

/-- **The support-complete `±1` single-line dispatcher.**  A `(k+1)`-family
(`k ≥ 4`) carrying a `±1`-valued relation `d` of support `≥ 3` whose only
vanishing `[-3,3]`-combinations lie on the line `ℤ·d` meets the floor
`1/(k+2)` — with **no upper bound on the support**.  The support `≤ k` branch
is `bridge_cube_single_pm1`; the remaining full-support branch `s = k+1` is
`bridge_cube_single_full`.  This closes the `±1` single-line case for every
support `3 ≤ s ≤ k+1`; only the support-two collision (`v_i = ±v_j`) stays
outside, and it is handled by `ML_dedup`. -/
theorem bridge_cube_single_pm1' {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (d : Fin (k + 1) → ℤ)
    (hd1 : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1)
    (hrel : (∑ w, d w * v w) = 0)
    (hs3 : 3 ≤ (Finset.univ.filter (fun w => d w ≠ 0)).card)
    (hline : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        ∃ lam : ℤ, c = fun w => lam * d w) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  by_cases hsk : (Finset.univ.filter (fun w => d w ≠ 0)).card ≤ k
  · exact bridge_cube_single_pm1 hk v d hd1 hrel hs3 hsk hline
  · -- full support: every coordinate carries the relation
    push_neg at hsk
    have hle : (Finset.univ.filter (fun w => d w ≠ 0)).card ≤ k + 1 := by
      have h := Finset.card_filter_le (Finset.univ : Finset (Fin (k + 1))) (fun w => d w ≠ 0)
      simpa using h
    have hcard : (Finset.univ.filter (fun w => d w ≠ 0)).card = k + 1 := by omega
    have hfull : (Finset.univ.filter (fun w => d w ≠ 0)) = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [hcard, Fintype.card_fin]
    have hne : ∀ w, d w ≠ 0 := by
      intro w
      have hw : w ∈ Finset.univ.filter (fun w => d w ≠ 0) := by
        rw [hfull]; exact Finset.mem_univ w
      exact (Finset.mem_filter.mp hw).2
    have hr : ∀ w, d w = -1 ∨ d w = 1 := by
      intro w
      rcases hd1 w with h | h | h
      · exact Or.inl h
      · exact absurd h (hne w)
      · exact Or.inr h
    -- the seven-multiple hypothesis, from the single-line property
    have hw₀ : d ⟨0, by omega⟩ ≠ 0 := hne _
    have hρ : d ⟨0, by omega⟩ = -1 ∨ d ⟨0, by omega⟩ = 1 := hr _
    have hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = d ∨ c = -d ∨ c = (fun w => 2 * d w) ∨ c = (fun w => -(2 * d w))
          ∨ c = (fun w => 3 * d w) ∨ c = (fun w => -(3 * d w)) := by
      intro c hcb hcv
      obtain ⟨lam, hc⟩ := hline c hcb hcv
      have hbound : -3 ≤ lam ∧ lam ≤ 3 := by
        have hcw := congrFun hc ⟨0, by omega⟩
        simp only at hcw
        have hb := hcb ⟨0, by omega⟩
        rcases hρ with h | h <;> rw [h] at hcw <;> omega
      obtain ⟨hlo, hhi⟩ := hbound
      have hlam : lam = 0 ∨ lam = 1 ∨ lam = -1 ∨ lam = 2 ∨ lam = -2 ∨ lam = 3 ∨ lam = -3 := by
        omega
      rcases hlam with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by funext w; rw [congrFun hc w]; simp)
      · exact Or.inr (Or.inl (by funext w; rw [congrFun hc w]; simp))
      · refine Or.inr (Or.inr (Or.inl ?_))
        funext w
        rw [congrFun hc w, Pi.neg_apply]
        ring
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by funext w; rw [congrFun hc w]))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        funext w
        rw [congrFun hc w]
        ring
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by funext w; rw [congrFun hc w]))))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        funext w
        rw [congrFun hc w]
        ring
    exact bridge_cube_single_full hk v d hr hrel hcube

end LRSpectrumFull
