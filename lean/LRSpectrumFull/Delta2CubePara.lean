/-
# The parallelogram cube floor: the last three-direction stratum

`torsion_para_cube_floor` — a StrongFree positive family (`k ≥ 4`) whose
`[-3,3]`-vanishing set is `{0, ±r₁, ±r₂, ±(r₁+r₂)}` meets the floor
`1/(k+2)`.  Together with the escaping-triple floor this closes every
three-direction vanishing set; the residual becomes four or more directions
(`denseTorsion_of_fourDir`).

Two new devices.  **The parity identity**: `odd(a+b) = odd(a) ⊕ odd(b)`
coordinate-wise, and the negative cube weights are exactly the odd ones, so
`P₁P₂P₃ ≥ 0` (`para_parity`) — the number of negative weights is never one
or three.  **The signed inexact masses**: subfamily masses only pay for
*positive* candidate weights (`mass_upper_signed`), the mass only for
*negative* ones (`mass_lower_signed`); with the parity split and the
one-generic bound the three sign scenarios close against
`u³(59k+41) < 185/4` (`cube_para_close`) and `u³(k+1) < 7/8`.
-/
import LRSpectrumFull.Delta2CubeTriple

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- Sum over an inserted element is at least the value plus the rest, for
nonpositive weights (duplicates only help downward). -/
theorem sum_insert_ge_of_nonpos {α : Type*} [DecidableEq α] (f : α → ℝ)
    (hf : ∀ x, f x ≤ 0) (a : α) (s : Finset α) :
    f a + ∑ x ∈ s, f x ≤ ∑ x ∈ insert a s, f x := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_self.mpr h]
    have := hf a
    linarith
  · rw [Finset.sum_insert h]

/-- **Signed mass lower bound**: only negative candidate weights can pull the
mass below `(5/2)^n`. -/
theorem mass_lower_signed {n : ℕ} (F S : Finset (Fin n → ℤ))
    (h0 : (0 : Fin n → ℤ) ∈ F) (hFS : F ⊆ insert 0 S) (T : ℝ)
    (hT : T ≤ ∑ c ∈ S, min (∏ w, cubeWtR (c w)) 0) :
    (5/2 : ℝ) ^ n + T ≤ ∑ c ∈ F, ∏ w, cubeWtR (c w) := by
  have hsplit : (∑ c ∈ F, ∏ w, cubeWtR (c w))
      = (∏ w, cubeWtR ((0 : Fin n → ℤ) w)) + ∑ c ∈ F.erase 0, ∏ w, cubeWtR (c w) :=
    (Finset.add_sum_erase F _ h0).symm
  have hsub : F.erase 0 ⊆ S := by
    intro c hc
    have h1 := Finset.mem_erase.mp hc
    have h2 := hFS h1.2
    rcases Finset.mem_insert.mp h2 with h | h
    · exact absurd h h1.1
    · exact h
  have hptw : (∑ c ∈ F.erase 0, min (∏ w, cubeWtR (c w)) 0)
      ≤ ∑ c ∈ F.erase 0, ∏ w, cubeWtR (c w) :=
    Finset.sum_le_sum (fun c _ => min_le_left _ _)
  have hmono : (∑ c ∈ F.erase 0, -(min (∏ w, cubeWtR (c w)) 0))
      ≤ ∑ c ∈ S, -(min (∏ w, cubeWtR (c w)) 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun c _ _ => by simp [min_le_right (∏ w, cubeWtR (c w)) 0])
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at hmono
  rw [hsplit, cubeWtR_prod_zero]
  linarith

/-- **Signed mass upper bound**: only positive candidate weights can push the
mass above `(5/2)^n`. -/
theorem mass_upper_signed {n : ℕ} (F S : Finset (Fin n → ℤ))
    (hFS : F ⊆ insert 0 S) (T : ℝ)
    (hT : (∑ c ∈ S, max (∏ w, cubeWtR (c w)) 0) ≤ T) :
    (∑ c ∈ F, ∏ w, cubeWtR (c w)) ≤ (5/2 : ℝ) ^ n + T := by
  have h1 : (∑ c ∈ F, ∏ w, cubeWtR (c w)) ≤ ∑ c ∈ F, max (∏ w, cubeWtR (c w)) 0 :=
    Finset.sum_le_sum (fun c _ => le_max_left _ _)
  have h2 : (∑ c ∈ F, max (∏ w, cubeWtR (c w)) 0)
      ≤ ∑ c ∈ insert 0 S, max (∏ w, cubeWtR (c w)) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg hFS (fun c _ _ => le_max_right _ _)
  have h3 : (∑ c ∈ insert (0 : Fin n → ℤ) S, max (∏ w, cubeWtR (c w)) 0)
      ≤ max (∏ w, cubeWtR ((0 : Fin n → ℤ) w)) 0 + ∑ c ∈ S, max (∏ w, cubeWtR (c w)) 0 :=
    sum_insert_le_of_nonneg _ (fun c => le_max_right _ _) _ _
  rw [cubeWtR_prod_zero] at h3
  have h4 : max ((5/2 : ℝ) ^ n) 0 = (5/2 : ℝ) ^ n := max_eq_left (by positivity)
  rw [h4] at h3
  linarith

/-- **The coordinate parity identity**: the product of the three cube weights
along a parallelogram column is nonnegative — the negative weights sit exactly
on the odd values, and `a + b` is odd iff exactly one of `a, b` is. -/
theorem cubeWtR_triple_nonneg (a b : ℤ) (ha : -3 ≤ a ∧ a ≤ 3) (hb : -3 ≤ b ∧ b ≤ 3)
    (hab : -3 ≤ a + b ∧ a + b ≤ 3) :
    0 ≤ cubeWtR a * cubeWtR b * cubeWtR (a + b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;>
    first
      | (exfalso; omega)
      | norm_num [cubeWtR]

/-- **The parallelogram parity**: `P₁ P₂ P₃ ≥ 0` — the number of negative
weight products among the three generators is never odd. -/
theorem para_parity {n : ℕ} (r₁ r₂ : Fin n → ℤ)
    (h13 : ∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) (h23 : ∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3)
    (h33 : ∀ w, -3 ≤ r₁ w + r₂ w ∧ r₁ w + r₂ w ≤ 3) :
    0 ≤ (∏ w, cubeWtR (r₁ w)) * (∏ w, cubeWtR (r₂ w)) * (∏ w, cubeWtR (r₁ w + r₂ w)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_nonneg
    (fun w _ => cubeWtR_triple_nonneg _ _ (h13 w) (h23 w) (h33 w))

/-- Positive scaling commutes with the positive part. -/
theorem max_two_fifths (x : ℝ) : max ((2/5) * x) 0 = (2/5) * max x 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right (by linarith), max_eq_right h, mul_zero]
  · rw [max_eq_left (by linarith), max_eq_left h]

/-- **The parallelogram close**: `u³(59k+41) < 185/4` at `δ = 1/(k+2)` for
`k ≥ 4` — exact cosine at the five-runner corner, the sextic chain beyond. -/
theorem cube_para_close {k : ℕ} (hk : 4 ≤ k) :
    (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * (59 * (k : ℝ) + 41) < 185/4 := by
  rcases eq_or_lt_of_le hk with hk4 | hk5
  · subst hk4
    have harg : 2 * π * (1 / ((4 : ℕ) + 2 : ℝ)) = π / 3 := by
      push_cast
      ring
    rw [harg, Real.cos_pi_div_three]
    push_cast
    norm_num
  · have hk5' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
    set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
    have hδ0 : 0 < δ := by rw [hδdef]; positivity
    have hδ2 : δ ≤ 1 / 2 := by
      rw [hδdef]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
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
      have := Real.cos_le_one (2 * π * δ)
      linarith
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
    have hkey : 8 * π ^ 6 * (59 * (k : ℝ) + 41) < (185/4) * ((k : ℝ) + 2) ^ 6 := by
      have h74 : (2401 : ℝ) ≤ ((k : ℝ) + 2) ^ 4 := by
        calc (2401 : ℝ) = 7 ^ 4 := by norm_num
          _ ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      have h6b : 2401 * ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 6 := by
        have hsplit : ((k : ℝ) + 2) ^ 6 = ((k : ℝ) + 2) ^ 4 * ((k : ℝ) + 2) ^ 2 := by ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right h74 (by positivity)
      have h59 : 59 * (k : ℝ) + 41 ≤ 59 * ((k : ℝ) + 2) := by linarith
      have hgrow : 8 * 961.51 * (59 * ((k : ℝ) + 2)) < (185/4) * (2401 * ((k : ℝ) + 2) ^ 2) := by
        nlinarith [hk5']
      have hstep : 8 * π ^ 6 * (59 * (k : ℝ) + 41) < 8 * 961.51 * (59 * ((k : ℝ) + 2)) := by
        have hpos : (0:ℝ) < 59 * (k : ℝ) + 41 := by positivity
        have h1 : 8 * π ^ 6 * (59 * (k : ℝ) + 41) < 8 * 961.51 * (59 * (k : ℝ) + 41) := by
          nlinarith [hπ6, hpos]
        have h2 : 8 * 961.51 * (59 * (k : ℝ) + 41) ≤ 8 * 961.51 * (59 * ((k : ℝ) + 2)) := by
          nlinarith [h59]
        linarith
      calc 8 * π ^ 6 * (59 * (k : ℝ) + 41)
          < 8 * 961.51 * (59 * ((k : ℝ) + 2)) := hstep
        _ < (185/4) * (2401 * ((k : ℝ) + 2) ^ 2) := hgrow
        _ ≤ (185/4) * ((k : ℝ) + 2) ^ 6 := by nlinarith [h6b]
    calc (1 - Real.cos (2 * π * δ)) ^ 3 * (59 * (k : ℝ) + 41)
        < (2 * (π * δ) ^ 2) ^ 3 * (59 * (k : ℝ) + 41) := by
          refine mul_lt_mul_of_pos_right hu3 ?_
          positivity
      _ = (8 * π ^ 6 * (59 * (k : ℝ) + 41)) * δ ^ 6 := by ring
      _ < ((185/4) * ((k : ℝ) + 2) ^ 6) * δ ^ 6 :=
          mul_lt_mul_of_pos_right hkey (pow_pos hδ0 6)
      _ = (185/4) * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by ring
      _ = 185/4 := by rw [hδ61, mul_one]

/-- The positive and negative parts reassemble the absolute value. -/
theorem max_add_max_neg (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring

/-- The negative part is at most the absolute value. -/
theorem max_neg_le_abs (x : ℝ) : max (-x) 0 ≤ |x| :=
  max_le (neg_le_abs x) (abs_nonneg x)

set_option maxHeartbeats 6400000 in
/-- **The parallelogram cube floor.**  A StrongFree positive family (`k ≥ 4`)
whose `[-3,3]`-vanishing set lies in `{0, ±r₁, ±r₂, ±(r₁+r₂)}` (with the sum
in the box) meets the floor `1/(k+2)`.  The forced escapes `r₁-r₂`, `2r₁+r₂`,
`r₁+2r₂` kill second generic-heavy generators; the parity identity leaves at
most two negative weights; the signed masses and `u³(59k+41) < 185/4`
close. -/
theorem torsion_para_cube_floor {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hSF : StrongFree v)
    (r₁ r₂ : Fin (k + 1) → ℤ)
    (h13 : ∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) (h23 : ∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3)
    (h33 : ∀ w, -3 ≤ r₁ w + r₂ w ∧ r₁ w + r₂ w ≤ 3)
    (h10 : r₁ ≠ 0) (h20 : r₂ ≠ 0) (hne' : r₂ ≠ -r₁)
    (hrel1 : (∑ w, r₁ w * v w) = 0) (hrel2 : (∑ w, r₂ w * v w) = 0)
    (hclass : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r₁ ∨ c = -r₁ ∨ c = r₂ ∨ c = -r₂
          ∨ c = (fun w => r₁ w + r₂ w) ∨ c = (fun w => -(r₁ w + r₂ w))) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hB0 : (0 : ℝ) < (5/2 : ℝ) ^ k := by positivity
  -- the sum generator
  have hrel3 : (∑ w, (r₁ w + r₂ w) * v w) = 0 := by
    have h1 : (∑ w, (r₁ w + r₂ w) * v w) = (∑ w, r₁ w * v w) + (∑ w, r₂ w * v w) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [h1, hrel1, hrel2, add_zero]
  have h30 : (fun w => r₁ w + r₂ w) ≠ (0 : Fin (k + 1) → ℤ) := by
    intro h
    apply hne'
    funext w
    have := congrFun h w
    simp only [Pi.zero_apply] at this
    simp only [Pi.neg_apply]
    omega
  -- bigness and support for all three
  obtain ⟨wb1, hwb1⟩ := strongfree_cube_two v hSF r₁ h10 hrel1
  obtain ⟨wb2, hwb2⟩ := strongfree_cube_two v hSF r₂ h20 hrel2
  obtain ⟨wb3, hwb3'⟩ := strongfree_cube_two v hSF (fun w => r₁ w + r₂ w) h30 hrel3
  have hwb3 : r₁ wb3 + r₂ wb3 ≤ -2 ∨ 2 ≤ r₁ wb3 + r₂ wb3 := hwb3'
  have hs1 : ∀ w, r₁ w ≠ 0 → ∃ w', w' ≠ w ∧ r₁ w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r₁ hrel1 w hw
  have hs2 : ∀ w, r₂ w ≠ 0 → ∃ w', w' ≠ w ∧ r₂ w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r₂ hrel2 w hw
  have hs3' := fun w hw => cube_supp_two v hv (fun w => r₁ w + r₂ w) hrel3 w hw
  have hs3 : ∀ w, r₁ w + r₂ w ≠ 0 → ∃ w', w' ≠ w ∧ r₁ w' + r₂ w' ≠ 0 := hs3'
  set P₁ : ℝ := ∏ w, cubeWtR (r₁ w) with hP1def
  set P₂ : ℝ := ∏ w, cubeWtR (r₂ w) with hP2def
  set P₃ : ℝ := ∏ w, cubeWtR (r₁ w + r₂ w) with hP3def
  -- the three escapes
  have hE1 : ∃ w, r₁ w - r₂ w ≤ -4 ∨ 4 ≤ r₁ w - r₂ w := by
    by_contra h
    push_neg at h
    have hbox : ∀ w, -3 ≤ r₁ w - r₂ w ∧ r₁ w - r₂ w ≤ 3 := by
      intro w
      have := h w
      have := h13 w
      have := h23 w
      omega
    have hvan : (∑ w, (r₁ w - r₂ w) * v w) = 0 := by
      have h1 : (∑ w, (r₁ w - r₂ w) * v w) = (∑ w, r₁ w * v w) - (∑ w, r₂ w * v w) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [h1, hrel1, hrel2, sub_zero]
    rcases hclass (fun w => r₁ w - r₂ w) hbox hvan with hc|hc|hc|hc|hc|hc|hc
    · -- r₁ = r₂: then the sum is 2r₁, too big at wb1
      have h1 : ∀ w, r₁ w = r₂ w := by
        intro w
        have := congrFun hc w
        simp only [Pi.zero_apply] at this
        omega
      have := h33 wb1
      have := h1 wb1
      omega
    · -- r₂ = 0
      refine h20 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- r₂ = 2r₁: kills at wb1
      have h1 := congrFun hc wb1
      simp only [Pi.neg_apply] at h1
      have := h23 wb1
      omega
    · -- r₁ = 2r₂: kills at wb2
      have h1 := congrFun hc wb2
      simp only at h1
      have := h13 wb2
      omega
    · -- r₁ = 0
      refine h10 (funext fun w => ?_)
      have := congrFun hc w
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    · -- r₁ - r₂ = r₁ + r₂: r₂ = 0
      refine h20 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- r₁ - r₂ = -(r₁ + r₂): r₁ = 0
      refine h10 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
  -- the halving kill: 3x = -2y with x vanishing forces an SF violation
  have hhalf : ∀ (x y : Fin (k + 1) → ℤ), x ≠ 0 → (∑ w, x w * v w) = 0 →
      (∀ w, -3 ≤ y w ∧ y w ≤ 3) → (∀ w, 3 * x w = -(2 * y w)) → False := by
    intro x y hx0 hxv hy3 heq
    have heven : ∀ w, x w = 2 * (x w / 2) := by
      intro w
      have := heq w
      omega
    have hbnd : ∀ w, (x w / 2) = -1 ∨ (x w / 2) = 0 ∨ (x w / 2) = 1 := by
      intro w
      have h1 := heq w
      have h2 := hy3 w
      have h3 := heven w
      omega
    have hvan : (∑ w, (x w / 2) * v w) = 0 := by
      have h1 : (∑ w, x w * v w) = 2 * (∑ w, (x w / 2) * v w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        linear_combination (v w) * (heven w)
      rw [h1] at hxv
      linarith
    have hz := hSF (fun w => x w / 2) hbnd hvan
    apply hx0
    funext w
    have h1 : x w / 2 = 0 := hz w
    have h2 := heven w
    simp only [Pi.zero_apply]
    omega
  have hE2 : ∃ w, 2 * r₁ w + r₂ w ≤ -4 ∨ 4 ≤ 2 * r₁ w + r₂ w := by
    by_contra h
    push_neg at h
    have hbox : ∀ w, -3 ≤ 2 * r₁ w + r₂ w ∧ 2 * r₁ w + r₂ w ≤ 3 := by
      intro w
      have := h w
      have := h13 w
      have := h23 w
      omega
    have hvan : (∑ w, (2 * r₁ w + r₂ w) * v w) = 0 := by
      have h1 : (∑ w, (2 * r₁ w + r₂ w) * v w)
          = 2 * (∑ w, r₁ w * v w) + (∑ w, r₂ w * v w) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [h1, hrel1, hrel2]
      ring
    rcases hclass (fun w => 2 * r₁ w + r₂ w) hbox hvan with hc|hc|hc|hc|hc|hc|hc
    · -- r₂ = -2r₁: kills at wb1
      have h1 := congrFun hc wb1
      simp only [Pi.zero_apply] at h1
      have := h23 wb1
      omega
    · -- r₁ + r₂ = 0: contradicts h30
      apply hne'
      funext w
      have := congrFun hc w
      simp only at this
      simp only [Pi.neg_apply]
      omega
    · -- 3r₁ + r₂ = 0: r₂ = -3r₁, kills at wb1
      have h1 := congrFun hc wb1
      simp only [Pi.neg_apply] at h1
      have := h23 wb1
      omega
    · -- 2r₁ = 0
      refine h10 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- 2r₁ + 2r₂ = 0: r₂ = -r₁
      apply hne'
      funext w
      have := congrFun hc w
      simp only [Pi.neg_apply] at this
      simp only [Pi.neg_apply]
      omega
    · -- r₁ = 0
      refine h10 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- 3r₁ + 2r₂ = 0: the halving kill on r₁
      refine hhalf r₁ r₂ h10 hrel1 h23 (fun w => ?_)
      have := congrFun hc w
      simp only at this
      omega
  have hE3 : ∃ w, r₁ w + 2 * r₂ w ≤ -4 ∨ 4 ≤ r₁ w + 2 * r₂ w := by
    by_contra h
    push_neg at h
    have hbox : ∀ w, -3 ≤ r₁ w + 2 * r₂ w ∧ r₁ w + 2 * r₂ w ≤ 3 := by
      intro w
      have := h w
      have := h13 w
      have := h23 w
      omega
    have hvan : (∑ w, (r₁ w + 2 * r₂ w) * v w) = 0 := by
      have h1 : (∑ w, (r₁ w + 2 * r₂ w) * v w)
          = (∑ w, r₁ w * v w) + 2 * (∑ w, r₂ w * v w) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [h1, hrel1, hrel2]
      ring
    rcases hclass (fun w => r₁ w + 2 * r₂ w) hbox hvan with hc|hc|hc|hc|hc|hc|hc
    · -- r₁ = -2r₂: kills at wb2
      have h1 := congrFun hc wb2
      simp only [Pi.zero_apply] at h1
      have := h13 wb2
      omega
    · -- 2r₂ = 0
      refine h20 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- 2r₁ + 2r₂ = 0: r₂ = -r₁
      apply hne'
      funext w
      have := congrFun hc w
      simp only [Pi.neg_apply] at this
      simp only [Pi.neg_apply]
      omega
    · -- r₁ + r₂ = 0
      apply hne'
      funext w
      have := congrFun hc w
      simp only at this
      simp only [Pi.neg_apply]
      omega
    · -- r₁ + 3r₂ = 0: r₁ = -3r₂, kills at wb2
      have h1 := congrFun hc wb2
      simp only [Pi.neg_apply] at h1
      have := h13 wb2
      omega
    · -- r₂ = 0
      refine h20 (funext fun w => ?_)
      have := congrFun hc w
      simp only at this
      simp only [Pi.zero_apply]
      omega
    · -- 2r₁ + 3r₂ = 0: the halving kill on r₂
      refine hhalf r₂ r₁ h20 hrel2 h13 (fun w => ?_)
      have := congrFun hc w
      simp only at this
      omega
  -- generic unpacking: a single ±2 coordinate, everything else small
  have hgen_unpack : ∀ (x : Fin (k + 1) → ℤ), (∀ w, -3 ≤ x w ∧ x w ≤ 3) →
      (∃ w, x w ≤ -2 ∨ 2 ≤ x w) → (∀ w, x w ≠ 0 → ∃ w', w' ≠ w ∧ x w' ≠ 0) →
      ¬ TwoBig x → ¬ ThreeBig x →
      ∃ b, (x b = -2 ∨ x b = 2) ∧ ∀ w, w ≠ b → -1 ≤ x w ∧ x w ≤ 1 := by
    intro x hx3 hbig hsup hnt hn3
    obtain ⟨b, hb⟩ := hbig
    have hno3 : ∀ w, x w ≠ -3 ∧ x w ≠ 3 := by
      intro w
      by_contra hc
      push_neg at hc
      have h3w : x w = -3 ∨ x w = 3 := by
        by_cases h : x w = -3
        · exact Or.inl h
        · exact Or.inr (hc h)
      have hwne : x w ≠ 0 := by rcases h3w with h | h <;> omega
      obtain ⟨w', hw'ne, hw'⟩ := hsup w hwne
      exact hn3 ⟨w, w', hw'ne.symm, h3w, hw'⟩
    have hsmall : ∀ w, w ≠ b → -1 ≤ x w ∧ x w ≤ 1 := by
      intro w hw
      by_contra hc
      have hbw : x w ≤ -2 ∨ 2 ≤ x w := by
        have := hx3 w
        omega
      exact hnt ⟨w, b, hw, hbw, hb⟩
    have hb2 : x b = -2 ∨ x b = 2 := by
      have := hx3 b
      have := hno3 b
      omega
    exact ⟨b, hb2, hsmall⟩
  -- kill shape A: generic pair with a difference escape and a 2x+y escape
  have hkillA : ∀ (x y : Fin (k + 1) → ℤ), (∀ w, -3 ≤ x w ∧ x w ≤ 3) →
      (∀ w, -3 ≤ y w ∧ y w ≤ 3) →
      (∃ w, x w ≤ -2 ∨ 2 ≤ x w) → (∃ w, y w ≤ -2 ∨ 2 ≤ y w) →
      (∀ w, x w ≠ 0 → ∃ w', w' ≠ w ∧ x w' ≠ 0) →
      (∀ w, y w ≠ 0 → ∃ w', w' ≠ w ∧ y w' ≠ 0) →
      (∃ w, x w - y w ≤ -4 ∨ 4 ≤ x w - y w) →
      (∃ w, 2 * x w + y w ≤ -4 ∨ 4 ≤ 2 * x w + y w) →
      ¬ TwoBig x → ¬ ThreeBig x → ¬ TwoBig y → ¬ ThreeBig y → False := by
    intro x y hx3 hy3 hbx hby hsx hsy hEd hEs hntx hn3x hnty hn3y
    obtain ⟨bx, hbx2, hsmx⟩ := hgen_unpack x hx3 hbx hsx hntx hn3x
    obtain ⟨by', hby2, hsmy⟩ := hgen_unpack y hy3 hby hsy hnty hn3y
    obtain ⟨wd, hwd⟩ := hEd
    have hdbx : wd = bx := by
      by_contra hne
      have h1 := hsmx wd hne
      by_cases h2 : wd = by'
      · subst h2
        omega
      · have := hsmy wd h2
        omega
    subst hdbx
    have hdby : wd = by' := by
      by_contra hne
      have := hsmy wd hne
      omega
    subst hdby
    obtain ⟨ws, hws⟩ := hEs
    by_cases hsw : ws = wd
    · rw [hsw] at hws
      omega
    · have h1 := hsmx ws hsw
      have h2 := hsmy ws hsw
      omega
  -- kill shape B: generic pair with a sum escape and a 2z−x escape
  have hkillB : ∀ (x z : Fin (k + 1) → ℤ), (∀ w, -3 ≤ x w ∧ x w ≤ 3) →
      (∀ w, -3 ≤ z w ∧ z w ≤ 3) →
      (∃ w, x w ≤ -2 ∨ 2 ≤ x w) → (∃ w, z w ≤ -2 ∨ 2 ≤ z w) →
      (∀ w, x w ≠ 0 → ∃ w', w' ≠ w ∧ x w' ≠ 0) →
      (∀ w, z w ≠ 0 → ∃ w', w' ≠ w ∧ z w' ≠ 0) →
      (∃ w, x w + z w ≤ -4 ∨ 4 ≤ x w + z w) →
      (∃ w, 2 * z w - x w ≤ -4 ∨ 4 ≤ 2 * z w - x w) →
      ¬ TwoBig x → ¬ ThreeBig x → ¬ TwoBig z → ¬ ThreeBig z → False := by
    intro x z hx3 hz3 hbx hbz hsx hsz hEp hEs hntx hn3x hntz hn3z
    obtain ⟨bx, hbx2, hsmx⟩ := hgen_unpack x hx3 hbx hsx hntx hn3x
    obtain ⟨bz, hbz2, hsmz⟩ := hgen_unpack z hz3 hbz hsz hntz hn3z
    obtain ⟨wp, hwp⟩ := hEp
    have hpbx : wp = bx := by
      by_contra hne
      have h1 := hsmx wp hne
      by_cases h2 : wp = bz
      · subst h2
        omega
      · have := hsmz wp h2
        omega
    subst hpbx
    have hpbz : wp = bz := by
      by_contra hne
      have := hsmz wp hne
      omega
    subst hpbz
    obtain ⟨ws, hws⟩ := hEs
    by_cases hsw : ws = wp
    · rw [hsw] at hws
      omega
    · have h1 := hsmx ws hsw
      have h2 := hsmz ws hsw
      omega
  -- class bounds with at most one generic generator
  have hgenline : ∀ (x : Fin (k + 1) → ℤ), (∃ w, x w ≤ -2 ∨ 2 ≤ x w) →
      (∀ w, x w ≠ 0 → ∃ w', w' ≠ w ∧ x w' ≠ 0) →
      |∏ w, cubeWtR (x w)| ≤ (9/16) * (5/2 : ℝ) ^ k := by
    intro x hb hs
    obtain ⟨w₀, hw₀⟩ := hb
    obtain ⟨w₁, hw₁ne, hw₁⟩ := hs w₀ (by rcases hw₀ with h | h <;> omega)
    exact line_weight_bound (by omega) x w₀ w₁ hw₁ne hw₀ hw₁
  obtain ⟨b₁, b₂, b₃, hb1, hb2, hb3, hp12, hp13, hp23, hpsum⟩ :
      ∃ b₁ b₂ b₃ : ℝ, |P₁| ≤ b₁ * (5/2 : ℝ) ^ k ∧ |P₂| ≤ b₂ * (5/2 : ℝ) ^ k
        ∧ |P₃| ≤ b₃ * (5/2 : ℝ) ^ k ∧ b₁ + b₂ ≤ 63/80 ∧ b₁ + b₃ ≤ 63/80
        ∧ b₂ + b₃ ≤ 63/80 ∧ b₁ + b₂ + b₃ ≤ 81/80 := by
    have hcls : ∀ (x : Fin (k + 1) → ℤ), TwoBig x ∨ ThreeBig x →
        |∏ w, cubeWtR (x w)| ≤ (9/40) * (5/2 : ℝ) ^ k :=
      fun x hx => class_bound (by omega) x hx
    by_cases hc1 : TwoBig r₁ ∨ ThreeBig r₁ <;>
      by_cases hc2 : TwoBig r₂ ∨ ThreeBig r₂ <;>
      by_cases hc3 : TwoBig (fun w => r₁ w + r₂ w) ∨ ThreeBig (fun w => r₁ w + r₂ w)
    · exact ⟨9/40, 9/40, 9/40, hcls r₁ hc1, hcls r₂ hc2, hcls _ hc3,
        by norm_num, by norm_num, by norm_num, by norm_num⟩
    · push_neg at hc3
      refine ⟨9/40, 9/40, 9/16, hcls r₁ hc1, hcls r₂ hc2,
        hgenline _ ⟨wb3, hwb3'⟩ hs3', by norm_num, by norm_num, by norm_num, by norm_num⟩
    · push_neg at hc2
      exact ⟨9/40, 9/16, 9/40, hcls r₁ hc1, hgenline r₂ ⟨wb2, hwb2⟩ hs2, hcls _ hc3,
        by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- r₂ and the sum both generic: killed by shape B on (r₂, sum)
      push_neg at hc2
      push_neg at hc3
      exfalso
      refine hkillB r₂ (fun w => r₁ w + r₂ w) h23
        (fun w => h33 w) ⟨wb2, hwb2⟩ ⟨wb3, hwb3'⟩ hs2 hs3'
        ?_ ?_ hc2.1 hc2.2 hc3.1 hc3.2
      · obtain ⟨w, hw⟩ := hE3
        refine ⟨w, ?_⟩
        show r₂ w + (r₁ w + r₂ w) ≤ -4 ∨ 4 ≤ r₂ w + (r₁ w + r₂ w)
        omega
      · obtain ⟨w, hw⟩ := hE2
        refine ⟨w, ?_⟩
        show 2 * (r₁ w + r₂ w) - r₂ w ≤ -4 ∨ 4 ≤ 2 * (r₁ w + r₂ w) - r₂ w
        omega
    · push_neg at hc1
      exact ⟨9/16, 9/40, 9/40, hgenline r₁ ⟨wb1, hwb1⟩ hs1, hcls r₂ hc2, hcls _ hc3,
        by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- r₁ and the sum both generic: killed by shape B on (r₁, sum)
      push_neg at hc1
      push_neg at hc3
      exfalso
      refine hkillB r₁ (fun w => r₁ w + r₂ w) h13
        (fun w => h33 w) ⟨wb1, hwb1⟩ ⟨wb3, hwb3'⟩ hs1 hs3'
        ?_ ?_ hc1.1 hc1.2 hc3.1 hc3.2
      · obtain ⟨w, hw⟩ := hE2
        refine ⟨w, ?_⟩
        show r₁ w + (r₁ w + r₂ w) ≤ -4 ∨ 4 ≤ r₁ w + (r₁ w + r₂ w)
        omega
      · obtain ⟨w, hw⟩ := hE3
        refine ⟨w, ?_⟩
        show 2 * (r₁ w + r₂ w) - r₁ w ≤ -4 ∨ 4 ≤ 2 * (r₁ w + r₂ w) - r₁ w
        omega
    · -- r₁ and r₂ both generic: killed by shape A
      push_neg at hc1
      push_neg at hc2
      exfalso
      exact hkillA r₁ r₂ h13 h23 ⟨wb1, hwb1⟩ ⟨wb2, hwb2⟩ hs1 hs2 hE1 hE2
        hc1.1 hc1.2 hc2.1 hc2.2
    · push_neg at hc1
      push_neg at hc2
      exfalso
      exact hkillA r₁ r₂ h13 h23 ⟨wb1, hwb1⟩ ⟨wb2, hwb2⟩ hs1 hs2 hE1 hE2
        hc1.1 hc1.2 hc2.1 hc2.2
  -- parity and the two uniform caps
  have hpar : (0:ℝ) ≤ P₁ * P₂ * P₃ := para_parity r₁ r₂ h13 h23 h33
  have habs1 : max P₁ 0 + max (-P₁) 0 = |P₁| := max_add_max_neg P₁
  have habs2 : max P₂ 0 + max (-P₂) 0 = |P₂| := max_add_max_neg P₂
  have habs3 : max P₃ 0 + max (-P₃) 0 = |P₃| := max_add_max_neg P₃
  have hsum_abs : (max P₁ 0 + max P₂ 0 + max P₃ 0)
      + (max (-P₁) 0 + max (-P₂) 0 + max (-P₃) 0) ≤ (81/80) * (5/2 : ℝ) ^ k := by
    have h1 : |P₁| + |P₂| + |P₃| ≤ (b₁ + b₂ + b₃) * (5/2 : ℝ) ^ k := by
      nlinarith [hb1, hb2, hb3]
    have h2 : (b₁ + b₂ + b₃) * (5/2 : ℝ) ^ k ≤ (81/80) * (5/2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hpsum (le_of_lt hB0)
    linarith [habs1, habs2, habs3]
  have hsome : 0 ≤ P₁ ∨ 0 ≤ P₂ ∨ 0 ≤ P₃ := by
    by_contra hall
    push_neg at hall
    obtain ⟨h1, h2, h3⟩ := hall
    nlinarith [hpar, mul_pos_of_neg_of_neg h1 h2]
  have hN : max (-P₁) 0 + max (-P₂) 0 + max (-P₃) 0 ≤ (63/80) * (5/2 : ℝ) ^ k := by
    have hm1 : max (-P₁) 0 ≤ |P₁| := max_neg_le_abs P₁
    have hm2 : max (-P₂) 0 ≤ |P₂| := max_neg_le_abs P₂
    have hm3 : max (-P₃) 0 ≤ |P₃| := max_neg_le_abs P₃
    rcases hsome with h | h | h
    · have hz : max (-P₁) 0 = 0 := max_eq_right (by linarith)
      have hpair23 : |P₂| + |P₃| ≤ (b₂ + b₃) * (5/2 : ℝ) ^ k := by
        nlinarith [hb2, hb3]
      have := mul_le_mul_of_nonneg_right hp23 (le_of_lt hB0)
      linarith
    · have hz : max (-P₂) 0 = 0 := max_eq_right (by linarith)
      have hpair13 : |P₁| + |P₃| ≤ (b₁ + b₃) * (5/2 : ℝ) ^ k := by
        nlinarith [hb1, hb3]
      have := mul_le_mul_of_nonneg_right hp13 (le_of_lt hB0)
      linarith
    · have hz : max (-P₃) 0 = 0 := max_eq_right (by linarith)
      have hpair12 : |P₁| + |P₂| ≤ (b₁ + b₂) * (5/2 : ℝ) ^ k := by
        nlinarith [hb1, hb2]
      have := mul_le_mul_of_nonneg_right hp12 (le_of_lt hB0)
      linarith
  -- the signed main-mass lower bound
  have hbox0 : (0 : Fin (k + 1) → ℤ) ∈ Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
    rw [Fintype.mem_piFinset]
    intro w
    simp
  have hprod_neg : ∀ (t : Fin (k + 1) → ℤ),
      (∏ w : Fin (k + 1), cubeWtR ((-t) w)) = ∏ w : Fin (k + 1), cubeWtR (t w) :=
    fun t => Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])
  have hP3neg : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(r₁ w + r₂ w)) w)) = P₃ :=
    Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])
  have hMlow : (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1)
      - 2 * (max (-P₁) 0 + max (-P₂) 0 + max (-P₃) 0))
      ≤ (∑ j ∈ Finset.range Q,
        (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3) := by
    have hgrid := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hgrid]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
    have h0F : (0 : Fin (k + 1) → ℤ) ∈ (Fintype.piFinset
        (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
        (fun c => (∑ w, c w * v w) = 0) :=
      Finset.mem_filter.mpr ⟨hbox0, Finset.sum_eq_zero (fun w _ => by simp)⟩
    have hFS : (Fintype.piFinset
        (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
        (fun c => (∑ w, c w * v w) = 0)
        ⊆ insert 0 ({r₁, -r₁, r₂, -r₂, (fun w => r₁ w + r₂ w),
            (fun w => -(r₁ w + r₂ w))} : Finset (Fin (k + 1) → ℤ)) := by
      intro c hc
      obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      rcases hclass c hcb hcv with h|h|h|h|h|h|h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))
    refine mass_lower_signed _ _ h0F hFS _ ?_
    have hstepG : ∀ (a : Fin (k + 1) → ℤ) (t : Finset (Fin (k + 1) → ℤ)) (T : ℝ),
        (T ≤ ∑ c ∈ t, min (∏ w, cubeWtR (c w)) 0) →
        min (∏ w, cubeWtR (a w)) 0 + T ≤ ∑ c ∈ insert a t, min (∏ w, cubeWtR (c w)) 0 := by
      intro a t T hT
      have := sum_insert_ge_of_nonpos (fun c => min (∏ w, cubeWtR (c w)) 0)
        (fun c => min_le_right _ _) a t
      linarith
    have e1 : min (∏ w, cubeWtR (r₁ w)) 0 = min P₁ 0 := rfl
    have e1n : min (∏ w, cubeWtR ((-r₁) w)) 0 = min P₁ 0 := by rw [hprod_neg r₁]
    have e2n : min (∏ w, cubeWtR ((-r₂) w)) 0 = min P₂ 0 := by rw [hprod_neg r₂]
    have e3 : min (∏ w, cubeWtR ((fun w => r₁ w + r₂ w) w)) 0 = min P₃ 0 := rfl
    have e3n : min (∏ w, cubeWtR ((fun w => -(r₁ w + r₂ w)) w)) 0 = min P₃ 0 := by
      rw [hP3neg]
    have h6 : min P₃ 0 ≤ ∑ c ∈ ({(fun w => -(r₁ w + r₂ w))} : Finset (Fin (k + 1) → ℤ)),
        min (∏ w, cubeWtR (c w)) 0 := by
      rw [Finset.sum_singleton, e3n]
    have h5 := hstepG (fun w => r₁ w + r₂ w) _ _ h6
    rw [e3] at h5
    have h4 := hstepG (-r₂) _ _ h5
    rw [e2n] at h4
    have h3 := hstepG r₂ _ _ h4
    have h2 := hstepG (-r₁) _ _ h3
    rw [e1n] at h2
    have h1 := hstepG r₁ _ _ h2
    have hmm : ∀ x : ℝ, min x 0 = -(max (-x) 0) := by
      intro x
      rcases le_total x 0 with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
        ring
      · rw [min_eq_right h, max_eq_right (by linarith)]
        ring
    calc -(2 * (max (-P₁) 0 + max (-P₂) 0 + max (-P₃) 0))
        = min P₁ 0 + (min P₁ 0 + (min P₂ 0 + (min P₂ 0 + (min P₃ 0 + min P₃ 0)))) := by
          rw [hmm P₁, hmm P₂, hmm P₃]
          ring
      _ ≤ _ := h1
  -- the subfamily upper bounds, only positive weights pay
  have hMsub_le : ∀ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      ≤ (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (4/5) * ((if r₁ i = 0 then max P₁ 0 else 0) + (if r₂ i = 0 then max P₂ 0 else 0)
          + (if r₁ i + r₂ i = 0 then max P₃ 0 else 0))) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    have hgrid := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    rw [hgrid]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r₁
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r₁
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r₂
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r₂
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => r₁ w + r₂ w)
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => -(r₁ w + r₂ w)) := by
      intro c hc hcv
      have hdi : (i.insertNth 0 c : Fin (k + 1) → ℤ) i = 0 := by
        rw [Fin.insertNth_apply_same]
      have hds : ∀ j', (i.insertNth 0 c : Fin (k + 1) → ℤ) (i.succAbove j') = c j' := by
        intro j'
        rw [Fin.insertNth_apply_succAbove]
      have hdb : ∀ w, -3 ≤ (i.insertNth 0 c : Fin (k + 1) → ℤ) w
          ∧ (i.insertNth 0 c : Fin (k + 1) → ℤ) w ≤ 3 := by
        intro w
        rcases Fin.eq_self_or_eq_succAbove i w with rfl | ⟨j', rfl⟩
        · rw [hdi]; omega
        · rw [hds j']; exact hc j'
      have hdv : (∑ w, (i.insertNth 0 c : Fin (k + 1) → ℤ) w * v w) = 0 := by
        rw [Fin.sum_univ_succAbove _ i, hdi, zero_mul, zero_add]
        rw [Finset.sum_congr rfl (fun j' _ => by rw [hds j'])]
        exact hcv
      exact hclass _ hdb hdv
    have hcb_of_mem : ∀ (c : Fin k → ℤ), c ∈ Fintype.piFinset
        (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) →
        ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
      intro c hcm j'
      have := (Fintype.mem_piFinset.mp hcm) j'
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h <;> omega
    have hzero_c : ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0 → c = 0 := by
      intro c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      simpa using this
    have hrestr : ∀ (t : Fin (k + 1) → ℤ), ∀ (c : Fin k → ℤ),
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = t →
        c = fun j' => t (i.succAbove j') := by
      intro t c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      exact this
    have hkill : ∀ (t : Fin (k + 1) → ℤ), t i ≠ 0 →
        ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = t → False := by
      intro t ht c hcs
      have := congrFun hcs i
      rw [Fin.insertNth_apply_same] at this
      exact ht this.symm
    have hP52 : ∀ (t : Fin (k + 1) → ℤ), t i = 0 →
        (∏ w, cubeWtR (t w)) = (5/2) * (∏ j' : Fin k, cubeWtR (t (i.succAbove j'))) := by
      intro t ht
      rw [Fin.prod_univ_succAbove (fun w => cubeWtR (t w)) i, ht]
      norm_num [cubeWtR]
    have hstepM : ∀ (a : Fin k → ℤ) (t : Finset (Fin k → ℤ)) (T : ℝ),
        (∑ c ∈ t, max (∏ j', cubeWtR (c j')) 0) ≤ T →
        (∑ c ∈ insert a t, max (∏ j', cubeWtR (c j')) 0)
          ≤ max (∏ j', cubeWtR (a j')) 0 + T := by
      intro a t T hT
      have := sum_insert_le_of_nonneg (fun c => max (∏ j', cubeWtR (c j')) 0)
        (fun c => le_max_right _ _) a t
      linarith
    by_cases hri1 : r₁ i = 0 <;> by_cases hri2 : r₂ i = 0 <;>
      by_cases hri3 : r₁ i + r₂ i = 0
    · -- all three survive
      rw [if_pos hri1, if_pos hri2, if_pos hri3]
      refine mass_upper_signed _ ({(fun j' => r₁ (i.succAbove j')),
        (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₂ (i.succAbove j')),
        (fun j' => -(r₂ (i.succAbove j'))),
        (fun j' => r₁ (i.succAbove j') + r₂ (i.succAbove j')),
        (fun j' => -(r₁ (i.succAbove j') + r₂ (i.succAbove j')))} : Finset (Fin k → ℤ))
        ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · rw [hrestr r₁ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₁ (i.succAbove j')) from by
            rw [hrestr (-r₁) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · rw [hrestr r₂ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
        · rw [hrestr _ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
        · rw [hrestr _ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_singleton_self _))))))
      · have e1p : max (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))) 0
            = (2/5) * max P₁ 0 := by
          have h := hP52 r₁ hri1
          have h2 : (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))) = (2/5) * P₁ := by
            linarith
          rw [h2, max_two_fifths]
        have e1n : max (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))) 0
            = (2/5) * max P₁ 0 := by
          have hn : (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact e1p
        have e2p : max (∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))) 0
            = (2/5) * max P₂ 0 := by
          have h := hP52 r₂ hri2
          have h2 : (∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))) = (2/5) * P₂ := by
            linarith
          rw [h2, max_two_fifths]
        have e2n : max (∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))) 0
            = (2/5) * max P₂ 0 := by
          have hn : (∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact e2p
        have e3p : max (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j'))) 0
            = (2/5) * max P₃ 0 := by
          have h := hP52 (fun w => r₁ w + r₂ w) hri3
          have h2 : (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')))
              = (2/5) * P₃ := by
            have h3 : (∏ j' : Fin k, cubeWtR ((fun w => r₁ w + r₂ w) (i.succAbove j')))
                = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')) := rfl
            rw [← h3]
            linarith
          rw [h2, max_two_fifths]
        have e3n : max (∏ j' : Fin k,
            cubeWtR (-(r₁ (i.succAbove j') + r₂ (i.succAbove j')))) 0
            = (2/5) * max P₃ 0 := by
          have hn : (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j') + r₂ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact e3p
        have hc6 : (∑ c ∈ ({(fun j' => -(r₁ (i.succAbove j') + r₂ (i.succAbove j')))} :
            Finset (Fin k → ℤ)), max (∏ j', cubeWtR (c j')) 0) ≤ (2/5) * max P₃ 0 := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq e3n
        have hc5 := hstepM (fun j' => r₁ (i.succAbove j') + r₂ (i.succAbove j')) _ _ hc6
        have hc4 := hstepM (fun j' => -(r₂ (i.succAbove j'))) _ _ hc5
        have hc3 := hstepM (fun j' => r₂ (i.succAbove j')) _ _ hc4
        have hc2 := hstepM (fun j' => -(r₁ (i.succAbove j'))) _ _ hc3
        have hc1 := hstepM (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc _ ≤ _ := hc1
          _ ≤ (4/5) * (max P₁ 0 + max P₂ 0 + max P₃ 0) := by
              simp only
              rw [e1p, e1n, e2p, e2n, e3p]
              linarith
    · exact absurd (by omega : r₁ i + r₂ i = 0) hri3
    · exact absurd (by omega : r₂ i = 0) hri2
    · -- only r₁ survives
      rw [if_pos hri1, if_neg hri2, if_neg hri3]
      refine mass_upper_signed _ ({(fun j' => r₁ (i.succAbove j')),
        (fun j' => -(r₁ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · rw [hrestr r₁ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₁ (i.succAbove j')) from by
            rw [hrestr (-r₁) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill (-r₂) (by simpa using hri2) c h).elim
        · exact (hkill _ (by simpa using hri3) c h).elim
        · exact (hkill _ (by
            show -(r₁ i + r₂ i) ≠ 0
            omega) c h).elim
      · have e1p : max (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))) 0
            = (2/5) * max P₁ 0 := by
          have h := hP52 r₁ hri1
          have h2 : (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))) = (2/5) * P₁ := by
            linarith
          rw [h2, max_two_fifths]
        have e1n : max (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))) 0
            = (2/5) * max P₁ 0 := by
          have hn : (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact e1p
        have hc2 : (∑ c ∈ ({(fun j' => -(r₁ (i.succAbove j')))} : Finset (Fin k → ℤ)),
            max (∏ j', cubeWtR (c j')) 0) ≤ (2/5) * max P₁ 0 := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq e1n
        have hc1 := hstepM (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc _ ≤ _ := hc1
          _ ≤ (4/5) * (max P₁ 0 + 0 + 0) := by
              simp only
              rw [e1p]
              have : (0:ℝ) ≤ max P₁ 0 := le_max_right _ _
              linarith
    · exact absurd (by omega : r₁ i = 0) hri1
    · -- only r₂ survives
      rw [if_neg hri1, if_pos hri2, if_neg hri3]
      refine mass_upper_signed _ ({(fun j' => r₂ (i.succAbove j')),
        (fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill (-r₁) (by simpa using hri1) c h).elim
        · rw [hrestr r₂ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact (hkill _ (by simpa using hri3) c h).elim
        · exact (hkill _ (by
            show -(r₁ i + r₂ i) ≠ 0
            omega) c h).elim
      · have e2p : max (∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))) 0
            = (2/5) * max P₂ 0 := by
          have h := hP52 r₂ hri2
          have h2 : (∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))) = (2/5) * P₂ := by
            linarith
          rw [h2, max_two_fifths]
        have e2n : max (∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))) 0
            = (2/5) * max P₂ 0 := by
          have hn : (∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact e2p
        have hc2 : (∑ c ∈ ({(fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)),
            max (∏ j', cubeWtR (c j')) 0) ≤ (2/5) * max P₂ 0 := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq e2n
        have hc1 := hstepM (fun j' => r₂ (i.succAbove j')) _ _ hc2
        calc _ ≤ _ := hc1
          _ ≤ (4/5) * (0 + max P₂ 0 + 0) := by
              simp only
              rw [e2p]
              have : (0:ℝ) ≤ max P₂ 0 := le_max_right _ _
              linarith
    · -- only the sum survives (r₁ i = -r₂ i ≠ 0)
      rw [if_neg hri1, if_neg hri2, if_pos hri3]
      refine mass_upper_signed _
        ({(fun j' => r₁ (i.succAbove j') + r₂ (i.succAbove j')),
          (fun j' => -(r₁ (i.succAbove j') + r₂ (i.succAbove j')))} : Finset (Fin k → ℤ))
        ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill (-r₁) (by simpa using hri1) c h).elim
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill (-r₂) (by simpa using hri2) c h).elim
        · rw [hrestr _ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [hrestr _ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · have e3p : max (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j'))) 0
            = (2/5) * max P₃ 0 := by
          have h := hP52 (fun w => r₁ w + r₂ w) hri3
          have h2 : (∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')))
              = (2/5) * P₃ := by
            have h3 : (∏ j' : Fin k, cubeWtR ((fun w => r₁ w + r₂ w) (i.succAbove j')))
                = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')) := rfl
            rw [← h3]
            linarith
          rw [h2, max_two_fifths]
        have hc2 : (∑ c ∈ ({(fun j' => -(r₁ (i.succAbove j') + r₂ (i.succAbove j')))} :
            Finset (Fin k → ℤ)), max (∏ j', cubeWtR (c j')) 0) ≤ (2/5) * max P₃ 0 := by
          rw [Finset.sum_singleton]
          simp only
          have hn : (∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j') + r₂ (i.succAbove j'))))
              = ∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j') + r₂ (i.succAbove j')) :=
            Finset.prod_congr rfl (fun j' _ => by rw [cubeWtR_neg])
          rw [hn]
          exact le_of_eq e3p
        have hc1 := hstepM (fun j' => r₁ (i.succAbove j') + r₂ (i.succAbove j')) _ _ hc2
        calc _ ≤ _ := hc1
          _ ≤ (4/5) * (0 + 0 + max P₃ 0) := by
              simp only
              rw [e3p]
              have : (0:ℝ) ≤ max P₃ 0 := le_max_right _ _
              linarith
    · -- nothing survives
      rw [if_neg hri1, if_neg hri2, if_neg hri3]
      refine mass_upper_signed _ (∅ : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill (-r₁) (by simpa using hri1) c h).elim
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill (-r₂) (by simpa using hri2) c h).elim
        · exact (hkill _ (by simpa using hri3) c h).elim
        · exact (hkill _ (by
            show -(r₁ i + r₂ i) ≠ 0
            omega) c h).elim
      · simp
  -- assemble via the union engine on the raw grid sums
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith)
    ((∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
    (fun i => (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
    rfl (fun i => rfl) ?_
  have hu0 : (0 : ℝ) ≤ 1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2))) := by
    have := Real.cos_le_one (2 * π * (1 / ((k : ℝ) + 2)))
    linarith
  have hu30 : (0 : ℝ) ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 := pow_nonneg hu0 3
  -- the zero-count bound, inline for each of the three predicates
  have hzc : ∀ (p : Fin (k + 1) → Prop) (_ : DecidablePred p) (w₀ w₁ : Fin (k + 1)),
      w₁ ≠ w₀ → ¬ p w₀ → ¬ p w₁ →
      ((Finset.univ.filter p).card : ℝ) ≤ (k : ℝ) - 1 := by
    intro p hdec w₀ w₁ hne hp₀ hp₁
    have hsub : Finset.univ.filter p ⊆ (Finset.univ.erase w₀).erase w₁ := by
      intro c hc
      have hc0 := (Finset.mem_filter.mp hc).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ c⟩⟩
      · intro h
        rw [h] at hc0
        exact hp₁ hc0
      · intro h
        rw [h] at hc0
        exact hp₀ hc0
    have hcard : ((Finset.univ.erase w₀).erase w₁).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ w₀), Finset.card_univ, Fintype.card_fin]
      omega
    have h1 : (Finset.univ.filter p).card ≤ k - 1 := by
      have := Finset.card_le_card hsub
      omega
    have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      ring
    calc ((Finset.univ.filter p).card : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (k : ℝ) - 1 := h2
  have hw1ne : r₁ wb1 ≠ 0 := by rcases hwb1 with h | h <;> omega
  obtain ⟨w₁1, hw₁1ne, hw₁1⟩ := hs1 wb1 hw1ne
  have hw2ne : r₂ wb2 ≠ 0 := by rcases hwb2 with h | h <;> omega
  obtain ⟨w₁2, hw₁2ne, hw₁2⟩ := hs2 wb2 hw2ne
  have hw3ne : r₁ wb3 + r₂ wb3 ≠ 0 := by rcases hwb3 with h | h <;> omega
  obtain ⟨w₁3, hw₁3ne, hw₁3⟩ := hs3 wb3 hw3ne
  have hz1 : ((Finset.univ.filter (fun i : Fin (k + 1) => r₁ i = 0)).card : ℝ)
      ≤ (k : ℝ) - 1 :=
    hzc _ _ wb1 w₁1 hw₁1ne hw1ne hw₁1
  have hz2 : ((Finset.univ.filter (fun i : Fin (k + 1) => r₂ i = 0)).card : ℝ)
      ≤ (k : ℝ) - 1 :=
    hzc _ _ wb2 w₁2 hw₁2ne hw2ne hw₁2
  have hz3 : ((Finset.univ.filter (fun i : Fin (k + 1) => r₁ i + r₂ i = 0)).card : ℝ)
      ≤ (k : ℝ) - 1 :=
    hzc _ _ wb3 w₁3 hw₁3ne hw3ne hw₁3
  have hite : ∀ (p : Fin (k + 1) → Prop) (_ : DecidablePred p) (Pv : ℝ),
      (∑ i : Fin (k + 1), (if p i then Pv else 0))
        = ((Finset.univ.filter p).card : ℝ) * Pv := by
    intro p hdec Pv
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hSbound : (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
      + (4/5) * ((if r₁ i = 0 then max P₁ 0 else 0) + (if r₂ i = 0 then max P₂ 0 else 0)
        + (if r₁ i + r₂ i = 0 then max P₃ 0 else 0))))
      = (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * (((Finset.univ.filter (fun i : Fin (k + 1) => r₁ i = 0)).card : ℝ) * max P₁ 0
          + ((Finset.univ.filter (fun i : Fin (k + 1) => r₂ i = 0)).card : ℝ) * max P₂ 0
          + ((Finset.univ.filter (fun i : Fin (k + 1) => r₁ i + r₂ i = 0)).card : ℝ)
            * max P₃ 0)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hite _ _ (max P₁ 0), hite _ _ (max P₂ 0), hite _ _ (max P₃ 0)]
    push_cast
    ring
  have hm10 : (0:ℝ) ≤ max P₁ 0 := le_max_right _ _
  have hm20 : (0:ℝ) ≤ max P₂ 0 := le_max_right _ _
  have hm30 : (0:ℝ) ≤ max P₃ 0 := le_max_right _ _
  have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hsum_le : (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
      ≤ (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * (((k : ℝ) - 1) * (max P₁ 0 + max P₂ 0 + max P₃ 0))) := by
    calc (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
        (∏ j' : Fin k,
          (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
        ≤ ∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
          + (4/5) * ((if r₁ i = 0 then max P₁ 0 else 0) + (if r₂ i = 0 then max P₂ 0 else 0)
            + (if r₁ i + r₂ i = 0 then max P₃ 0 else 0))) :=
          Finset.sum_le_sum (fun i _ => hMsub_le i)
      _ = _ := hSbound
      _ ≤ (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * (((k : ℝ) - 1) * (max P₁ 0 + max P₂ 0 + max P₃ 0))) := by
          have t1 := mul_le_mul_of_nonneg_right hz1 hm10
          have t2 := mul_le_mul_of_nonneg_right hz2 hm20
          have t3 := mul_le_mul_of_nonneg_right hz3 hm30
          nlinarith [hQR]
  -- the staged close
  set u3 : ℝ := (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 with hu3def
  set PiP : ℝ := max P₁ 0 + max P₂ 0 + max P₃ 0 with hPidef
  set NN : ℝ := max (-P₁) 0 + max (-P₂) 0 + max (-P₃) 0 with hNdef
  set C : ℝ := u3 * ((4/5) * ((k : ℝ) - 1)) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have : (0:ℝ) ≤ (4/5) * ((k : ℝ) - 1) := by positivity
    exact mul_nonneg hu30 this
  have hPi0 : 0 ≤ PiP := by rw [hPidef]; positivity
  have hN0 : 0 ≤ NN := by
    rw [hNdef]
    have : (0:ℝ) ≤ max (-P₁) 0 := le_max_right _ _
    have : (0:ℝ) ≤ max (-P₂) 0 := le_max_right _ _
    have : (0:ℝ) ≤ max (-P₃) 0 := le_max_right _ _
    linarith
  have hCu : C < 2 := by
    have h1 := cube_union_close hk
    rw [hCdef]
    nlinarith [hu30, hkm1, h1]
  have hPile : PiP ≤ (81/80) * (5/2 : ℝ) ^ k - NN := by
    rw [hPidef, hNdef]
    linarith [hsum_abs]
  have hfin : u3 * ((k : ℝ) + 1) + (9/40) * C < 37/40 := by
    have h1 := cube_para_close hk
    have h2 : u3 * ((k : ℝ) + 1) + (9/40) * C = u3 * (59 * (k : ℝ) + 41) / 50 := by
      rw [hCdef]
      ring
    rw [h2]
    linarith
  calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
      * (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
        (∏ j' : Fin k,
          (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
      ≤ u3 * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k + (4/5) * (((k : ℝ) - 1) * PiP))) := by
        rw [hu3def]
        exact mul_le_mul_of_nonneg_left hsum_le hu30
    _ = (Q : ℝ) * (u3 * ((k : ℝ) + 1) * (5/2 : ℝ) ^ k + C * PiP) := by
        rw [hCdef]
        ring
    _ ≤ (Q : ℝ) * (u3 * ((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + C * ((81/80) * (5/2 : ℝ) ^ k - NN)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
        have := mul_le_mul_of_nonneg_left hPile hC0
        linarith
    _ < (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) - 2 * NN) := by
        refine mul_lt_mul_of_pos_left ?_ hQR
        have hNle : NN ≤ (63/80) * (5/2 : ℝ) ^ k := by
          rw [hNdef]
          exact hN
        have hstep : (C - 2) * NN ≥ (C - 2) * ((63/80) * (5/2 : ℝ) ^ k) := by
          have hc2 : C - 2 ≤ 0 := by linarith
          nlinarith [hNle, hc2]
        have hpow : (5/2 : ℝ) ^ (k + 1) = (5/2) * (5/2 : ℝ) ^ k := by
          rw [pow_succ]
          ring
        have hcore : (u3 * ((k : ℝ) + 1) + (9/40) * C) * (5/2 : ℝ) ^ k
            < (37/40) * (5/2 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hfin hB0
        nlinarith [hstep, hcore, hpow.le, hpow.ge]
    _ ≤ _ := hMlow

/-- **The four-direction residual**: the dense-web families admitting neither
an escaping-triple classification nor a parallelogram classification — since
every three-direction vanishing set is one or the other, this is the
four-or-more-direction web. -/
def CubeFourDirResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ATorsionFree v → ¬ SingleTorsionData v →
    (k = 4 ∨ ¬ BoundedResonance v) →
    ¬ ThreeDissoc v →
    (¬ ∃ r : Fin (k + 1) → ℤ, (∀ w, -3 ≤ r w ∧ r w ≤ 3) ∧ r ≠ 0 ∧
        (∑ w, r w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r ∨ c = -r)) →
    (¬ ∃ r r' : Fin (k + 1) → ℤ, (∀ w, -3 ≤ r w ∧ r w ≤ 3) ∧ (∀ w, -3 ≤ r' w ∧ r' w ≤ 3) ∧
        r ≠ 0 ∧ r' ≠ 0 ∧ r' ≠ r ∧ r' ≠ -r ∧
        (∑ w, r w * v w) = 0 ∧ (∑ w, r' w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r ∨ c = -r ∨ c = r' ∨ c = -r')) →
    (¬ ∃ r₁ r₂ r₃ : Fin (k + 1) → ℤ,
        (∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) ∧ (∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3) ∧
        (∀ w, -3 ≤ r₃ w ∧ r₃ w ≤ 3) ∧
        r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₃ ≠ 0 ∧
        (∑ w, r₁ w * v w) = 0 ∧ (∑ w, r₂ w * v w) = 0 ∧ (∑ w, r₃ w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r₁ ∨ c = -r₁ ∨ c = r₂ ∨ c = -r₂ ∨ c = r₃ ∨ c = -r₃) ∧
        (∃ w, r₁ w + r₂ w ≤ -4 ∨ 4 ≤ r₁ w + r₂ w) ∧
        (∃ w, r₁ w - r₂ w ≤ -4 ∨ 4 ≤ r₁ w - r₂ w) ∧
        (∃ w, r₁ w + r₃ w ≤ -4 ∨ 4 ≤ r₁ w + r₃ w) ∧
        (∃ w, r₁ w - r₃ w ≤ -4 ∨ 4 ≤ r₁ w - r₃ w) ∧
        (∃ w, r₂ w + r₃ w ≤ -4 ∨ 4 ≤ r₂ w + r₃ w) ∧
        (∃ w, r₂ w - r₃ w ≤ -4 ∨ 4 ≤ r₂ w - r₃ w)) →
    (¬ ∃ r₁ r₂ : Fin (k + 1) → ℤ,
        (∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) ∧ (∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3) ∧
        (∀ w, -3 ≤ r₁ w + r₂ w ∧ r₁ w + r₂ w ≤ 3) ∧
        r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₂ ≠ -r₁ ∧
        (∑ w, r₁ w * v w) = 0 ∧ (∑ w, r₂ w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r₁ ∨ c = -r₁ ∨ c = r₂ ∨ c = -r₂
            ∨ c = (fun w => r₁ w + r₂ w) ∨ c = (fun w => -(r₁ w + r₂ w)))) →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **The dense web shrinks to four directions**: parallelogram
classifications go to the parallelogram floor. -/
theorem denseWeb_of_fourDir (h : CubeFourDirResidual) : CubeDenseWebResidual := by
  intro k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin hpair htresc
  by_cases hpara : ∃ r₁ r₂ : Fin (k + 1) → ℤ,
      (∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) ∧ (∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3) ∧
      (∀ w, -3 ≤ r₁ w + r₂ w ∧ r₁ w + r₂ w ≤ 3) ∧
      r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₂ ≠ -r₁ ∧
      (∑ w, r₁ w * v w) = 0 ∧ (∑ w, r₂ w * v w) = 0 ∧
      (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r₁ ∨ c = -r₁ ∨ c = r₂ ∨ c = -r₂
          ∨ c = (fun w => r₁ w + r₂ w) ∨ c = (fun w => -(r₁ w + r₂ w)))
  · obtain ⟨r₁, r₂, h13, h23, h33, h10, h20, hne', hrel1, hrel2, hcl⟩ := hpara
    exact torsion_para_cube_floor hk4 v hv hSF r₁ r₂ h13 h23 h33 h10 h20 hne' hrel1 hrel2 hcl
  · exact h k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin hpair htresc hpara

/-- The dense-torsion shard reduces to the four-direction core: the free side
of the all-`N` program now rests on webs of four or more directions. -/
theorem denseTorsion_of_fourDir (h : CubeFourDirResidual) : DenseTorsionResidual :=
  denseTorsion_of_denseWeb (denseWeb_of_fourDir h)

end LRSpectrumFull
