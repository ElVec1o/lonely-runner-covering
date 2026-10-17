/-
# The torsion-line cube floor and the rank-two reduction

`torsion_line_cube_floor` — a StrongFree positive family (`k ≥ 4`) whose
`[-3,3]`-vanishing set is a single line `{0, r, -r}` meets the floor
`1/(k+2)`.  StrongFree forces the generator to carry a coordinate of
absolute value `≥ 2` (`strongfree_cube_two`), which caps its weight product
at `(9/16)(5/2)^k`; the mass is exactly `Q((5/2)^{k+1} + 2P)` and every
subfamily is either three-dissociated (the deleted runner meets the line)
or carries the restricted line with `P_sub = (2/5)P`.  The union close needs
only `u³(k+1) < 7/8` (`cube_union_close`).

This subsumes the visible single-torsion case at every `k ≥ 4` and every
support — in particular the `k = 4` support-two hole left by
`riesz_clears_floor_torsion_single`.  Together with the banked
`riesz_clears_floor_threediss`, it shrinks `DenseTorsionResidual` to
`CubeRankTwoResidual`: families whose `[-3,3]`-vanishing set contains two
essentially independent directions (`denseTorsion_of_cubeRankTwo`).
-/
import LRSpectrumFull.Delta2CubeFull

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- Under StrongFree, any nonzero vanishing cube vector has a coordinate of
absolute value at least `2`. -/
theorem strongfree_cube_two {m : ℕ} (v : Fin m → ℤ) (hSF : StrongFree v)
    (r : Fin m → ℤ) (hr0 : r ≠ 0) (hrel : (∑ w, r w * v w) = 0) :
    ∃ w, r w ≤ -2 ∨ 2 ≤ r w := by
  by_contra h
  push_neg at h
  have h1 : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1 := by
    intro w
    have := h w
    omega
  exact hr0 (funext (hSF r h1 hrel))

/-- A vanishing cube vector of a positive family has support at least two:
a second nonzero coordinate exists besides any given one. -/
theorem cube_supp_two {m : ℕ} (v : Fin m → ℤ) (hv : ∀ i, 0 < v i)
    (r : Fin m → ℤ) (hrel : (∑ w, r w * v w) = 0) (w₀ : Fin m) (hw₀ : r w₀ ≠ 0) :
    ∃ w₁, w₁ ≠ w₀ ∧ r w₁ ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum : (∑ w, r w * v w) = r w₀ * v w₀ := by
    refine Finset.sum_eq_single w₀ (fun b _ hb => ?_) (fun h' => absurd (Finset.mem_univ w₀) h')
    rw [h b hb, zero_mul]
  rw [hsum] at hrel
  rcases mul_eq_zero.mp hrel with h' | h'
  · exact hw₀ h'
  · exact absurd h' (by have := hv w₀; omega)

/-- Every cube weight is at most `5/2` in absolute value. -/
theorem cubeWtR_abs_le (a : ℤ) : |cubeWtR a| ≤ 5/2 := by
  unfold cubeWtR
  split_ifs <;> (rw [abs_le]; constructor <;> norm_num)

/-- Nonzero cube weights are at most `15/8` in absolute value. -/
theorem cubeWtR_abs_le_ne (a : ℤ) (ha : a ≠ 0) : |cubeWtR a| ≤ 15/8 := by
  unfold cubeWtR
  rw [if_neg ha]
  split_ifs <;> (rw [abs_le]; constructor <;> norm_num)

/-- Cube weights at coordinates of absolute value `≥ 2` are at most `3/4`. -/
theorem cubeWtR_abs_le_two (a : ℤ) (ha : a ≤ -2 ∨ 2 ≤ a) : |cubeWtR a| ≤ 3/4 := by
  unfold cubeWtR
  rw [if_neg (by omega), if_neg (by omega)]
  split_ifs <;> (rw [abs_le]; constructor <;> norm_num)

/-- **The line weight cap.**  A cube vector with a `≥ 2` coordinate and a
second nonzero coordinate has weight product at most `(9/16)(5/2)^k`. -/
theorem line_weight_bound {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1) → ℤ)
    (w₀ w₁ : Fin (k + 1)) (hne : w₁ ≠ w₀)
    (h₀ : r w₀ ≤ -2 ∨ 2 ≤ r w₀) (h₁ : r w₁ ≠ 0) :
    |∏ w, cubeWtR (r w)| ≤ (9/16) * (5/2 : ℝ) ^ k := by
  rw [Finset.abs_prod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase w₀) _
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w₁⟩)]
  have hcard : ((Finset.univ.erase w₀).erase w₁).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w₁⟩),
      Finset.card_erase_of_mem (Finset.mem_univ w₀), Finset.card_univ, Fintype.card_fin]
    omega
  have hrest : (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
      ≤ (5/2 : ℝ) ^ (k - 1) := by
    calc (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
        ≤ ∏ _w ∈ (Finset.univ.erase w₀).erase w₁, (5/2 : ℝ) :=
          Finset.prod_le_prod (fun w _ => abs_nonneg _) (fun w _ => cubeWtR_abs_le _)
      _ = (5/2 : ℝ) ^ (k - 1) := by rw [Finset.prod_const, hcard]
  have hrest0 : (0 : ℝ) ≤ ∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)| :=
    Finset.prod_nonneg (fun w _ => abs_nonneg _)
  have h1 : |cubeWtR (r w₁)| * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
      ≤ (15/8) * (5/2 : ℝ) ^ (k - 1) := by
    have := cubeWtR_abs_le_ne _ h₁
    calc |cubeWtR (r w₁)| * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
        ≤ (15/8) * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
          mul_le_mul_of_nonneg_right this hrest0
      _ ≤ (15/8) * (5/2 : ℝ) ^ (k - 1) := by
          have h158 : (0:ℝ) ≤ 15/8 := by norm_num
          exact mul_le_mul_of_nonneg_left hrest h158
  have h158pos : (0:ℝ) ≤ |cubeWtR (r w₁)| * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
    mul_nonneg (abs_nonneg _) hrest0
  have h0 := cubeWtR_abs_le_two _ h₀
  calc |cubeWtR (r w₀)| * (|cubeWtR (r w₁)| * ∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
      ≤ (3/4) * (|cubeWtR (r w₁)| * ∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
        mul_le_mul_of_nonneg_right h0 h158pos
    _ ≤ (3/4) * ((15/8) * (5/2 : ℝ) ^ (k - 1)) := by
        have h34 : (0:ℝ) ≤ 3/4 := by norm_num
        exact mul_le_mul_of_nonneg_left h1 h34
    _ = (45/32) * (5/2 : ℝ) ^ (k - 1) := by ring
    _ = (9/16) * (5/2 : ℝ) ^ k := by
        have hp : (5/2 : ℝ) ^ k = (5/2) ^ (k - 1) * (5/2) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hp]
        ring

set_option maxHeartbeats 1600000 in
/-- **The torsion-line cube floor.**  A StrongFree positive family of `k+1`
runners (`k ≥ 4`) whose only vanishing `[-3,3]`-combinations are `{0, r, -r}`
meets the floor `1/(k+2)`.  StrongFree caps the line's weight product at
`(9/16)(5/2)^k`, each subfamily is exact (three-dissociated or the restricted
line), and `u³(k+1) < 7/8` closes with margin `203/160 < 220/160`. -/
theorem torsion_line_cube_floor {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hSF : StrongFree v)
    (r : Fin (k + 1) → ℤ) (hr3 : ∀ w, -3 ≤ r w ∧ r w ≤ 3) (hr0 : r ≠ 0)
    (hrel : (∑ w, r w * v w) = 0)
    (hline : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  obtain ⟨w₀, hw₀2⟩ := strongfree_cube_two v hSF r hr0 hrel
  have hw₀ne : r w₀ ≠ 0 := by rcases hw₀2 with h | h <;> omega
  obtain ⟨w₁, hw₁ne, hw₁⟩ := cube_supp_two v hv r hrel w₀ hw₀ne
  have hPabs : |∏ w, cubeWtR (r w)| ≤ (9/16) * (5/2 : ℝ) ^ k :=
    line_weight_bound (by omega) r w₀ w₁ hw₁ne hw₀2 hw₁
  set P : ℝ := ∏ w, cubeWtR (r w) with hPdef
  -- the box and the filter
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
      (fun c => (∑ w, c w * v w) = 0) = {0, r, -r} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      exact hline c hcb hcv
    · intro hmem
      rcases hmem with rfl | rfl | rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · exact ⟨hbox _ hr3, hrel⟩
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          have := hr3 w
          omega), ?_⟩
        have h1 : (∑ w, (-r) w * v w) = -(∑ w, r w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
  -- the three-element mass sum
  have hsum3 : (∑ c ∈ ({0, r, -r} : Finset (Fin (k + 1) → ℤ)), ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ (k + 1) + 2 * P := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1n : (∏ w : Fin (k + 1), cubeWtR ((-r) w)) = P := by
      rw [Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])]
    have d01 : (0 : Fin (k + 1) → ℤ) ≠ r := by
      intro h
      exact hw₀ne (congrFun h w₀).symm
    have d02 : (0 : Fin (k + 1) → ℤ) ≠ -r := by
      intro h
      have := congrFun h w₀
      simp only [Pi.zero_apply, Pi.neg_apply] at this
      omega
    have d12 : r ≠ -r := by
      intro h
      have := congrFun h w₀
      simp only [Pi.neg_apply] at this
      omega
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d01, d02⟩),
      Finset.sum_insert (by simpa using d12), Finset.sum_singleton, e0, e1n]
    ring
  have hM : (∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P) := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum3] at h
    exact h
  -- subfamily masses
  have hMsub : ∀ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      = (Q : ℝ) * (if r i = 0 then (5/2 : ℝ) ^ k + (4/5) * P else (5/2 : ℝ) ^ k) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    -- the insertNth lift, shared by both branches
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r := by
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
      exact hline _ hdb hdv
    by_cases hri : r i = 0
    · rw [if_pos hri]
      -- the restricted line
      have hw₀i : w₀ ≠ i := by
        intro h
        rw [h] at hw₀ne
        exact hw₀ne hri
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hrsj₀ : r (i.succAbove j₀) ≠ 0 := by rw [hj₀]; exact hw₀ne
      have hsbox : ∀ (d : Fin k → ℤ), (∀ j', -3 ≤ d j' ∧ d j' ≤ 3) →
          d ∈ Fintype.piFinset (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
        intro d hd
        rw [Fintype.mem_piFinset]
        intro j'
        have := hd j'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hsrel : (∑ j' : Fin k, r (i.succAbove j') * v (i.succAbove j')) = 0 := by
        have h := hrel
        rw [Fin.sum_univ_succAbove (fun w => r w * v w) i, hri, zero_mul, zero_add] at h
        exact h
      have hsfilter : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, fun j' => r (i.succAbove j'), fun j' => -(r (i.succAbove j'))} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          rcases hlift c hcb hcv with h | h | h
          · left
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · right; left
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            exact this
          · right; right
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
        · intro hmem
          rcases hmem with rfl | rfl | rfl
          · exact ⟨hsbox _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · exact ⟨hsbox _ (fun j' => hr3 _), hsrel⟩
          · refine ⟨hsbox _ (fun j' => by
              show -3 ≤ -(r (i.succAbove j')) ∧ -(r (i.succAbove j')) ≤ 3
              have := hr3 (i.succAbove j')
              omega), ?_⟩
            have h1 : (∑ j', (-(r (i.succAbove j'))) * v (i.succAbove j'))
                = -(∑ j', r (i.succAbove j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hsrel, neg_zero]
      have hssum3 : (∑ c ∈ ({0, fun j' => r (i.succAbove j'),
            fun j' => -(r (i.succAbove j'))} : Finset (Fin k → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + 2 * (∏ j' : Fin k, cubeWtR (r (i.succAbove j'))) := by
        have e0 : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
          rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
            ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have e1n : (∏ j' : Fin k, cubeWtR ((fun j' => -(r (i.succAbove j'))) j'))
            = ∏ j' : Fin k, cubeWtR (r (i.succAbove j')) := by
          exact Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])
        have d01 : (0 : Fin k → ℤ) ≠ (fun j' => r (i.succAbove j')) := by
          intro h
          exact hrsj₀ (congrFun h j₀).symm
        have d02 : (0 : Fin k → ℤ) ≠ (fun j' => -(r (i.succAbove j'))) := by
          intro h
          have := congrFun h j₀
          simp only [Pi.zero_apply] at this
          omega
        have d12 : (fun j' => r (i.succAbove j')) ≠ (fun j' => -(r (i.succAbove j'))) := by
          intro h
          have := congrFun h j₀
          simp only at this
          omega
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨d01, d02⟩),
          Finset.sum_insert (by simpa using d12), Finset.sum_singleton, e0, e1n]
        ring
      have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
      rw [hsfilter, hssum3] at h
      rw [h]
      congr 1
      have hP52 : P = (5/2) * (∏ j' : Fin k, cubeWtR (r (i.succAbove j'))) := by
        rw [hPdef, Fin.prod_univ_succAbove (fun w => cubeWtR (r w)) i, hri]
        norm_num [cubeWtR]
      rw [hP52]
      ring
    · rw [if_neg hri]
      have hdiss : ThreeDissoc (fun j' => v (i.succAbove j')) := by
        intro c hc hcv
        rcases hlift c hc hcv with h | h | h
        · funext j'
          have := congrFun h (i.succAbove j')
          rw [Fin.insertNth_apply_succAbove] at this
          simpa using this
        · exfalso
          have h2 := congrFun h i
          rw [Fin.insertNth_apply_same] at h2
          exact hri h2.symm
        · exfalso
          have h2 := congrFun h i
          rw [Fin.insertNth_apply_same] at h2
          simp only [Pi.neg_apply] at h2
          omega
      exact riesz_mass_cube_real k _ Q hQ0 hsubQ hdiss
  -- assemble
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P))
    (fun i => (Q : ℝ) * (if r i = 0 then (5/2 : ℝ) ^ k + (4/5) * P else (5/2 : ℝ) ^ k))
    hM hMsub ?_
  -- the numeric close
  have hz : (Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card
      + (Finset.univ.filter (fun i : Fin (k + 1) => ¬ r i = 0)).card = k + 1 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0)
    simpa using this
  set z : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card with hzdef
  have hsum : (∑ i : Fin (k + 1), (Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ k + (4/5) * P else (5/2 : ℝ) ^ k))
      = (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k + (4/5) * (z : ℝ) * P) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hzk : ((Finset.univ.filter (fun i : Fin (k + 1) => ¬ r i = 0)).card : ℝ)
        = ((k : ℝ) + 1) - (z : ℝ) := by
      have : (Finset.univ.filter (fun i : Fin (k + 1) => ¬ r i = 0)).card = k + 1 - z := by
        omega
      rw [this]
      have hzle : z ≤ k + 1 := by omega
      push_cast [Nat.cast_sub hzle]
      ring
    rw [hzk]
    ring
  rw [hsum]
  -- bounds
  have hB0 : (0 : ℝ) < (5/2 : ℝ) ^ k := by positivity
  have hzle : (z : ℝ) ≤ (k : ℝ) + 1 := by
    have : z ≤ k + 1 := by omega
    exact_mod_cast this
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hu0 : (0 : ℝ) ≤ 1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2))) := by
    have := Real.cos_le_one (2 * π * (1 / ((k : ℝ) + 2)))
    linarith
  have hu30 : (0 : ℝ) ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 :=
    pow_nonneg hu0 3
  have hPle : P ≤ (9/16) * (5/2 : ℝ) ^ k := le_trans (le_abs_self P) hPabs
  have hPge : -((9/16) * (5/2 : ℝ) ^ k) ≤ P := neg_le_of_abs_le hPabs
  -- z·P ≤ (k+1)·(9/16)·B  regardless of the sign of P
  have hzP : (4/5) * (z : ℝ) * P ≤ (9/20) * ((k : ℝ) + 1) * (5/2 : ℝ) ^ k := by
    have h1 : (z : ℝ) * P ≤ ((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k) := by
      rcases le_total 0 P with hP0 | hP0
      · calc (z : ℝ) * P ≤ ((k : ℝ) + 1) * P := mul_le_mul_of_nonneg_right hzle hP0
          _ ≤ ((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k) := by
              have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
              exact mul_le_mul_of_nonneg_left hPle hk0
      · calc (z : ℝ) * P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz0 hP0
          _ ≤ ((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k) := by positivity
    nlinarith [h1]
  have hLnn : (0 : ℝ) ≤ ((k : ℝ) + 1) * (5/2 : ℝ) ^ k + (4/5) * (z : ℝ) * P := by
    have h1 : -(((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k)) ≤ (z : ℝ) * P := by
      rcases le_total 0 P with hP0 | hP0
      · calc -(((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k)) ≤ 0 :=
              neg_nonpos.mpr (by positivity)
          _ ≤ (z : ℝ) * P := mul_nonneg hz0 hP0
      · calc -(((k : ℝ) + 1) * ((9/16) * (5/2 : ℝ) ^ k))
            ≤ ((k : ℝ) + 1) * P := by
              have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hPabs)
                (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)
              nlinarith [this]
          _ ≤ (z : ℝ) * P := by
              nlinarith [mul_le_mul_of_nonneg_right hzle (neg_nonneg.mpr hP0)]
    nlinarith [h1]
  have hclose := cube_union_close hk
  calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
      * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k + (4/5) * (z : ℝ) * P))
      ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * ((Q : ℝ) * ((29/20) * ((k : ℝ) + 1) * (5/2 : ℝ) ^ k)) := by
        refine mul_le_mul_of_nonneg_left ?_ hu30
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
        linarith [hzP]
    _ = ((1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * ((k : ℝ) + 1))
        * ((29/20) * (Q : ℝ) * (5/2 : ℝ) ^ k) := by ring
    _ < (7/8) * ((29/20) * (Q : ℝ) * (5/2 : ℝ) ^ k) := by
        refine mul_lt_mul_of_pos_right hclose ?_
        positivity
    _ = (203/160) * (Q : ℝ) * (5/2 : ℝ) ^ k := by ring
    _ < (11/8) * (Q : ℝ) * (5/2 : ℝ) ^ k := by
        have : (203/160 : ℝ) < 11/8 := by norm_num
        nlinarith [hQR, hB0]
    _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P) := by
        have hpow : (5/2 : ℝ) ^ (k + 1) = (5/2) * (5/2 : ℝ) ^ k := by
          rw [pow_succ]; ring
        have h1 : (11/8) * (5/2 : ℝ) ^ k ≤ (5/2 : ℝ) ^ (k + 1) + 2 * P := by
          rw [hpow]
          linarith [hPge]
        calc (11/8) * (Q : ℝ) * (5/2 : ℝ) ^ k
            = (Q : ℝ) * ((11/8) * (5/2 : ℝ) ^ k) := by ring
          _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hQR)

/-- **The rank-two residual**: the dense-torsion shard families whose
`[-3,3]`-vanishing set is neither trivial nor a single line — at least two
essentially independent bounded directions.  This is the genuine
multi-relation core left open by the floor theorems. -/
def CubeRankTwoResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ATorsionFree v → ¬ SingleTorsionData v →
    (k = 4 ∨ ¬ BoundedResonance v) →
    ¬ ThreeDissoc v →
    (¬ ∃ r : Fin (k + 1) → ℤ, (∀ w, -3 ≤ r w ∧ r w ≤ 3) ∧ r ≠ 0 ∧
        (∑ w, r w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r ∨ c = -r)) →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **The dense-torsion shard shrinks to the rank-two core.**  Trivial
vanishing sets go to the three-dissociated floor, single lines to the
torsion-line floor; only genuinely multi-directional cube webs remain. -/
theorem denseTorsion_of_cubeRankTwo (h : CubeRankTwoResidual) : DenseTorsionResidual := by
  intro k hk4 hk7 v hv hSF hAT hST hdense
  by_cases hdiss : ThreeDissoc v
  · exact riesz_clears_floor_threediss (by omega) v hdiss
  · by_cases hlin : ∃ r : Fin (k + 1) → ℤ, (∀ w, -3 ≤ r w ∧ r w ≤ 3) ∧ r ≠ 0 ∧
        (∑ w, r w * v w) = 0 ∧
        (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = r ∨ c = -r)
    · obtain ⟨r, hr3, hr0, hrel, hl⟩ := hlin
      exact torsion_line_cube_floor hk4 v hv hSF r hr3 hr0 hrel hl
    · exact h k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin

end LRSpectrumFull
