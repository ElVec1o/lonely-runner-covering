/-
# The clean-pair cube floor and the three-direction reduction

`torsion_pair_cube_floor` — a StrongFree positive family (`k ≥ 4`) whose
`[-3,3]`-vanishing set is exactly two lines `{0, ±r, ±r'}` meets the floor
`1/(k+2)`.

The new structural input is the **obstruction dichotomy**: since `r ± r'`
lie in the lattice, the pair hypothesis forces them OUTSIDE the box, so at
some coordinate `|r_w + r'_w| ≥ 4` and at another `|r_w - r'_w| ≥ 4`.
Bookkeeping the (unique or not) big coordinates then shows: either one
generator carries two coordinates of absolute value `≥ 2`, or **both**
generators carry a `±3` (`pair_dichotomy`).  Either way the joint weight is
crushed: `|P_r| + |P_{r'}| ≤ (63/80)(5/2)^k`, while the union close only
needs `< (65/80)(5/2)^k` — the box geometry itself pays for the second
line.  (Numerically the worst clean pair reaches `0.27·(5/2)^{k+1}/2`;
among heavy pairs only five exist at `m = 5`.)

Together with the dissociated and line floors, this shrinks
`CubeRankTwoResidual` to `CubeThreeDirResidual`: vanishing sets containing
a third direction beyond two lines (`denseTorsion_of_cubeThreeDir`).
-/
import LRSpectrumFull.Delta2CubeLine

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- Cube weights at `±3` are `1/8` in absolute value. -/
theorem cubeWtR_abs_le_three (a : ℤ) (ha : a = -3 ∨ a = 3) : |cubeWtR a| ≤ 1/8 := by
  unfold cubeWtR
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [abs_le]
  constructor <;> norm_num

/-- **The two-slot product bound**: caps at two distinct coordinates and the
trivial cap `5/2` elsewhere. -/
theorem cube_prod_bound_two {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1) → ℤ)
    (w₀ w₁ : Fin (k + 1)) (hne : w₁ ≠ w₀) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₀ : |cubeWtR (r w₀)| ≤ a) (h₁ : |cubeWtR (r w₁)| ≤ b) :
    |∏ w, cubeWtR (r w)| ≤ a * b * (5/2 : ℝ) ^ (k - 1) := by
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
      ≤ b * (5/2 : ℝ) ^ (k - 1) := by
    calc |cubeWtR (r w₁)| * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
        ≤ b * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
          mul_le_mul_of_nonneg_right h₁ hrest0
      _ ≤ b * (5/2 : ℝ) ^ (k - 1) := mul_le_mul_of_nonneg_left hrest hb
  have h1nn : (0:ℝ) ≤ |cubeWtR (r w₁)| * (∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
    mul_nonneg (abs_nonneg _) hrest0
  calc |cubeWtR (r w₀)| * (|cubeWtR (r w₁)| * ∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|)
      ≤ a * (|cubeWtR (r w₁)| * ∏ w ∈ (Finset.univ.erase w₀).erase w₁, |cubeWtR (r w)|) :=
        mul_le_mul_of_nonneg_right h₀ h1nn
    _ ≤ a * (b * (5/2 : ℝ) ^ (k - 1)) := mul_le_mul_of_nonneg_left h1 ha
    _ = a * b * (5/2 : ℝ) ^ (k - 1) := by ring

/-- A generator has two coordinates of absolute value `≥ 2`. -/
def TwoBig {m : ℕ} (r : Fin m → ℤ) : Prop :=
  ∃ w w', w ≠ w' ∧ (r w ≤ -2 ∨ 2 ≤ r w) ∧ (r w' ≤ -2 ∨ 2 ≤ r w')

/-- A generator has a `±3` coordinate and a second nonzero coordinate. -/
def ThreeBig {m : ℕ} (r : Fin m → ℤ) : Prop :=
  ∃ w w', w ≠ w' ∧ (r w = -3 ∨ r w = 3) ∧ r w' ≠ 0

/-- **The pair obstruction dichotomy.**  If two box generators each carry a
`≥ 2` coordinate, their supports are `≥ 2`-recoverable, and both `r + r'`
and `r - r'` escape the box, then one generator is `TwoBig` or both are
`ThreeBig`. -/
theorem pair_dichotomy {m : ℕ} (r r' : Fin m → ℤ)
    (hr3 : ∀ w, -3 ≤ r w ∧ r w ≤ 3) (hr3' : ∀ w, -3 ≤ r' w ∧ r' w ≤ 3)
    (hbig : ∃ w, r w ≤ -2 ∨ 2 ≤ r w) (hbig' : ∃ w, r' w ≤ -2 ∨ 2 ≤ r' w)
    (hsup : ∀ w, r w ≠ 0 → ∃ w', w' ≠ w ∧ r w' ≠ 0)
    (hsup' : ∀ w, r' w ≠ 0 → ∃ w', w' ≠ w ∧ r' w' ≠ 0)
    (hplus : ∃ w, r w + r' w ≤ -4 ∨ 4 ≤ r w + r' w)
    (hminus : ∃ w, r w - r' w ≤ -4 ∨ 4 ≤ r w - r' w) :
    TwoBig r ∨ TwoBig r' ∨ (ThreeBig r ∧ ThreeBig r') := by
  classical
  by_cases h2r : TwoBig r
  · exact Or.inl h2r
  by_cases h2r' : TwoBig r'
  · exact Or.inr (Or.inl h2r')
  refine Or.inr (Or.inr ?_)
  obtain ⟨wr, hwr⟩ := hbig
  obtain ⟨wr', hwr'⟩ := hbig'
  have hsmall : ∀ w, w ≠ wr → -1 ≤ r w ∧ r w ≤ 1 := by
    intro w hw
    by_contra hc
    have hb : r w ≤ -2 ∨ 2 ≤ r w := by
      have := hr3 w
      omega
    exact h2r ⟨w, wr, hw, hb, hwr⟩
  have hsmall' : ∀ w, w ≠ wr' → -1 ≤ r' w ∧ r' w ≤ 1 := by
    intro w hw
    by_contra hc
    have hb : r' w ≤ -2 ∨ 2 ≤ r' w := by
      have := hr3' w
      omega
    exact h2r' ⟨w, wr', hw, hb, hwr'⟩
  obtain ⟨wp, hwp⟩ := hplus
  obtain ⟨wm, hwm⟩ := hminus
  have hpm : wp ≠ wm := by
    intro h
    rw [h] at hwp
    have h1 := hr3 wm
    have h2 := hr3' wm
    omega
  -- the plus obstruction sits on a big coordinate
  have hp_cases : (wp = wr ∧ wp ≠ wr') ∨ (wp = wr' ∧ wp ≠ wr) ∨ (wp = wr ∧ wp = wr') := by
    by_cases h1 : wp = wr <;> by_cases h2 : wp = wr'
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exfalso
      have := hsmall wp h1
      have := hsmall' wp h2
      omega
  -- shared big coordinate: the minus obstruction has nowhere to sit
  rcases hp_cases with ⟨hpr, hpr'⟩ | ⟨hpr', hpr⟩ | ⟨hpr, hpr'⟩
  · -- wp = wr: the plus obstruction forces r wp = ±3 (r' is small there)
    have hs' := hsmall' wp hpr'
    have hr3wp := hr3 wp
    have h3r : r wp = -3 ∨ r wp = 3 := by omega
    have hTr : ThreeBig r := by
      obtain ⟨w', hw'ne, hw'⟩ := hsup wp (by omega)
      exact ⟨wp, w', hw'ne.symm, h3r, hw'⟩
    -- the minus obstruction must sit at wr', forcing r' wm = ±3
    have hwm_ne_wr : wm ≠ wr := by
      intro h
      rw [← hpr] at h
      exact hpm h.symm
    have hwm_eq : wm = wr' := by
      by_contra h
      have := hsmall wm hwm_ne_wr
      have := hsmall' wm h
      omega
    have hs := hsmall wm hwm_ne_wr
    have hr3wm' := hr3' wm
    have h3r' : r' wm = -3 ∨ r' wm = 3 := by omega
    have hTr' : ThreeBig r' := by
      obtain ⟨w', hw'ne, hw'⟩ := hsup' wm (by omega)
      exact ⟨wm, w', hw'ne.symm, h3r', hw'⟩
    exact ⟨hTr, hTr'⟩
  · -- wp = wr': symmetric — the plus obstruction forces r' wp = ±3
    have hs := hsmall wp hpr
    have hr3wp' := hr3' wp
    have h3r' : r' wp = -3 ∨ r' wp = 3 := by omega
    have hTr' : ThreeBig r' := by
      obtain ⟨w', hw'ne, hw'⟩ := hsup' wp (by omega)
      exact ⟨wp, w', hw'ne.symm, h3r', hw'⟩
    have hwm_ne_wr' : wm ≠ wr' := by
      intro h
      rw [← hpr'] at h
      exact hpm h.symm
    have hwm_eq : wm = wr := by
      by_contra h
      have := hsmall wm h
      have := hsmall' wm hwm_ne_wr'
      omega
    have hs' := hsmall' wm hwm_ne_wr'
    have hr3wm := hr3 wm
    have h3r : r wm = -3 ∨ r wm = 3 := by omega
    have hTr : ThreeBig r := by
      obtain ⟨w', hw'ne, hw'⟩ := hsup wm (by omega)
      exact ⟨wm, w', hw'ne.symm, h3r, hw'⟩
    exact ⟨hTr, hTr'⟩
  · -- wp = wr = wr': both bigs spent at wp; the minus obstruction is stranded
    exfalso
    have h1 : wm ≠ wr := by
      intro h
      rw [← hpr] at h
      exact hpm h.symm
    have h2 : wm ≠ wr' := by
      intro h
      rw [← hpr'] at h
      exact hpm h.symm
    have := hsmall wm h1
    have := hsmall' wm h2
    omega

/-- **The joint weight cap for a clean pair**: the dichotomy crushes the two
weight products to a combined `(63/80)(5/2)^k`. -/
theorem pair_weight_cap {k : ℕ} (hk : 1 ≤ k) (r r' : Fin (k + 1) → ℤ)
    (hr3 : ∀ w, -3 ≤ r w ∧ r w ≤ 3) (hr3' : ∀ w, -3 ≤ r' w ∧ r' w ≤ 3)
    (hbig : ∃ w, r w ≤ -2 ∨ 2 ≤ r w) (hbig' : ∃ w, r' w ≤ -2 ∨ 2 ≤ r' w)
    (hsup : ∀ w, r w ≠ 0 → ∃ w', w' ≠ w ∧ r w' ≠ 0)
    (hsup' : ∀ w, r' w ≠ 0 → ∃ w', w' ≠ w ∧ r' w' ≠ 0)
    (hplus : ∃ w, r w + r' w ≤ -4 ∨ 4 ≤ r w + r' w)
    (hminus : ∃ w, r w - r' w ≤ -4 ∨ 4 ≤ r w - r' w) :
    |∏ w, cubeWtR (r w)| + |∏ w, cubeWtR (r' w)| ≤ (63/80) * (5/2 : ℝ) ^ k := by
  have hB1 : (0:ℝ) < (5/2 : ℝ) ^ (k - 1) := by positivity
  have hpow : (5/2 : ℝ) ^ k = (5/2) ^ (k - 1) * (5/2) := by
    rw [← pow_succ]
    congr 1
    omega
  -- the generic single-line cap, used for the partner of a TwoBig generator
  have hline : ∀ (s : Fin (k + 1) → ℤ), (∃ w, s w ≤ -2 ∨ 2 ≤ s w) →
      (∀ w, s w ≠ 0 → ∃ w', w' ≠ w ∧ s w' ≠ 0) →
      |∏ w, cubeWtR (s w)| ≤ (9/16) * (5/2 : ℝ) ^ k := by
    intro s hb hs
    obtain ⟨w₀, hw₀⟩ := hb
    obtain ⟨w₁, hw₁ne, hw₁⟩ := hs w₀ (by omega)
    calc |∏ w, cubeWtR (s w)|
        ≤ (3/4) * (15/8) * (5/2 : ℝ) ^ (k - 1) :=
          cube_prod_bound_two hk s w₀ w₁ hw₁ne _ _ (by norm_num) (by norm_num)
            (cubeWtR_abs_le_two _ hw₀) (cubeWtR_abs_le_ne _ hw₁)
      _ = (9/16) * (5/2 : ℝ) ^ k := by rw [hpow]; ring
  -- the TwoBig cap
  have htwo : ∀ (s : Fin (k + 1) → ℤ), TwoBig s →
      |∏ w, cubeWtR (s w)| ≤ (9/40) * (5/2 : ℝ) ^ k := by
    intro s hs
    obtain ⟨w₀, w₁, hne, hb₀, hb₁⟩ := hs
    calc |∏ w, cubeWtR (s w)|
        ≤ (3/4) * (3/4) * (5/2 : ℝ) ^ (k - 1) :=
          cube_prod_bound_two hk s w₀ w₁ (Ne.symm hne) _ _ (by norm_num) (by norm_num)
            (cubeWtR_abs_le_two _ hb₀) (cubeWtR_abs_le_two _ hb₁)
      _ = (9/40) * (5/2 : ℝ) ^ k := by rw [hpow]; ring
  -- the ThreeBig cap
  have hthree : ∀ (s : Fin (k + 1) → ℤ), ThreeBig s →
      |∏ w, cubeWtR (s w)| ≤ (3/32) * (5/2 : ℝ) ^ k := by
    intro s hs
    obtain ⟨w₀, w₁, hne, hb₀, hb₁⟩ := hs
    calc |∏ w, cubeWtR (s w)|
        ≤ (1/8) * (15/8) * (5/2 : ℝ) ^ (k - 1) :=
          cube_prod_bound_two hk s w₀ w₁ (Ne.symm hne) _ _ (by norm_num) (by norm_num)
            (cubeWtR_abs_le_three _ hb₀) (cubeWtR_abs_le_ne _ hb₁)
      _ = (3/32) * (5/2 : ℝ) ^ k := by rw [hpow]; ring
  have hBk : (0:ℝ) < (5/2 : ℝ) ^ k := by positivity
  rcases pair_dichotomy r r' hr3 hr3' hbig hbig' hsup hsup' hplus hminus with h | h | ⟨h, h'⟩
  · have h1 := htwo r h
    have h2 := hline r' hbig' hsup'
    nlinarith [h1, h2]
  · have h1 := htwo r' h
    have h2 := hline r hbig hsup
    nlinarith [h1, h2]
  · have h1 := hthree r h
    have h2 := hthree r' h'
    nlinarith [h1, h2]

set_option maxHeartbeats 3200000 in
/-- **The clean-pair cube floor.**  A StrongFree positive family (`k ≥ 4`)
whose `[-3,3]`-vanishing set is exactly `{0, r, -r, r', -r'}` meets the floor
`1/(k+2)`: the pair hypothesis pushes `r ± r'` out of the box, the resulting
dichotomy caps the joint weight at `(63/80)(5/2)^k`, every subfamily is exact
(both restricted lines, one, or none), and the sign-split union close needs
only `u³(k+1) < 7/8`. -/
theorem torsion_pair_cube_floor {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hSF : StrongFree v)
    (r r' : Fin (k + 1) → ℤ)
    (hr3 : ∀ w, -3 ≤ r w ∧ r w ≤ 3) (hr3' : ∀ w, -3 ≤ r' w ∧ r' w ≤ 3)
    (hr0 : r ≠ 0) (hr'0 : r' ≠ 0) (hne : r' ≠ r) (hne' : r' ≠ -r)
    (hrel : (∑ w, r w * v w) = 0) (hrel' : (∑ w, r' w * v w) = 0)
    (hpair : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = r' ∨ c = -r') :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  obtain ⟨w₀, hw₀2⟩ := strongfree_cube_two v hSF r hr0 hrel
  have hw₀ne : r w₀ ≠ 0 := by rcases hw₀2 with h | h <;> omega
  obtain ⟨w₀', hw₀2'⟩ := strongfree_cube_two v hSF r' hr'0 hrel'
  have hw₀ne' : r' w₀' ≠ 0 := by rcases hw₀2' with h | h <;> omega
  have hsup : ∀ w, r w ≠ 0 → ∃ w', w' ≠ w ∧ r w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r hrel w hw
  have hsup' : ∀ w, r' w ≠ 0 → ∃ w', w' ≠ w ∧ r' w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r' hrel' w hw
  -- the two escape obstructions
  have hsum_pm : ∀ (ε : ℤ), (∑ w, (r w + ε * r' w) * v w) = 0 := by
    intro ε
    have h1 : (∑ w, (r w + ε * r' w) * v w)
        = (∑ w, r w * v w) + ε * (∑ w, r' w * v w) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [h1, hrel, hrel', mul_zero, add_zero]
  have hplus : ∃ w, r w + r' w ≤ -4 ∨ 4 ≤ r w + r' w := by
    by_contra h
    push_neg at h
    have hbox : ∀ w, -3 ≤ r w + r' w ∧ r w + r' w ≤ 3 := by
      intro w
      have := h w
      have := hr3 w
      have := hr3' w
      omega
    have hvan : (∑ w, (r w + r' w) * v w) = 0 := by
      have := hsum_pm 1
      have h2 : (∑ w, (r w + 1 * r' w) * v w) = (∑ w, (r w + r' w) * v w) :=
        Finset.sum_congr rfl (fun w _ => by ring)
      rw [h2] at this
      exact this
    rcases hpair (fun w => r w + r' w) hbox hvan with hc | hc | hc | hc | hc
    · refine hne' (funext fun w => ?_)
      have h1 := congrFun hc w
      simp only [Pi.zero_apply] at h1
      simp only [Pi.neg_apply]
      omega
    · refine hr'0 (funext fun w => ?_)
      have h1 := congrFun hc w
      simp only at h1
      simp only [Pi.zero_apply]
      omega
    · have h1 := congrFun hc w₀
      simp only [Pi.neg_apply] at h1
      have h2 := hr3' w₀
      omega
    · refine hr0 (funext fun w => ?_)
      have h1 := congrFun hc w
      simp only at h1
      simp only [Pi.zero_apply]
      omega
    · have h1 := congrFun hc w₀'
      simp only [Pi.neg_apply] at h1
      have h2 := hr3 w₀'
      omega
  have hminus : ∃ w, r w - r' w ≤ -4 ∨ 4 ≤ r w - r' w := by
    by_contra h
    push_neg at h
    have hbox : ∀ w, -3 ≤ r w - r' w ∧ r w - r' w ≤ 3 := by
      intro w
      have := h w
      have := hr3 w
      have := hr3' w
      omega
    have hvan : (∑ w, (r w - r' w) * v w) = 0 := by
      have := hsum_pm (-1)
      have h2 : (∑ w, (r w + (-1) * r' w) * v w) = (∑ w, (r w - r' w) * v w) :=
        Finset.sum_congr rfl (fun w _ => by ring)
      rw [h2] at this
      exact this
    rcases hpair (fun w => r w - r' w) hbox hvan with hc | hc | hc | hc | hc
    · refine hne (funext fun w => ?_)
      have h1 := congrFun hc w
      simp only [Pi.zero_apply] at h1
      omega
    · refine hr'0 (funext fun w => ?_)
      have h1 := congrFun hc w
      simp only at h1
      simp only [Pi.zero_apply]
      omega
    · have h1 : r w₀ - r' w₀ = -(r w₀) := by
        have := congrFun hc w₀
        simpa using this
      have h2 := hr3' w₀
      omega
    · have h1 : r w₀' - r' w₀' = r' w₀' := by
        have := congrFun hc w₀'
        simpa using this
      have h2 := hr3 w₀'
      omega
    · refine hr0 (funext fun w => ?_)
      have h1 : r w - r' w = -(r' w) := by
        have := congrFun hc w
        simpa using this
      simp only [Pi.zero_apply]
      omega
  set P : ℝ := ∏ w, cubeWtR (r w) with hPdef
  set P' : ℝ := ∏ w, cubeWtR (r' w) with hP'def
  have hPP : |P| + |P'| ≤ (63/80) * (5/2 : ℝ) ^ k :=
    pair_weight_cap (by omega) r r' hr3 hr3' ⟨w₀, hw₀2⟩ ⟨w₀', hw₀2'⟩ hsup hsup' hplus hminus
  -- the ten pairwise distinctions
  have d0r : (0 : Fin (k + 1) → ℤ) ≠ r := fun h => hw₀ne (congrFun h w₀).symm
  have d0rn : (0 : Fin (k + 1) → ℤ) ≠ -r := fun h => by
    have := congrFun h w₀
    simp only [Pi.zero_apply, Pi.neg_apply] at this
    omega
  have d0r' : (0 : Fin (k + 1) → ℤ) ≠ r' := fun h => hw₀ne' (congrFun h w₀').symm
  have d0rn' : (0 : Fin (k + 1) → ℤ) ≠ -r' := fun h => by
    have := congrFun h w₀'
    simp only [Pi.zero_apply, Pi.neg_apply] at this
    omega
  have drrn : r ≠ -r := fun h => by
    have := congrFun h w₀
    simp only [Pi.neg_apply] at this
    omega
  have drr' : r ≠ r' := fun h => hne h.symm
  have drrn' : r ≠ -r' := fun h => hne' (by rw [h]; funext w; simp)
  have drnr' : -r ≠ r' := fun h => hne' h.symm
  have drnrn' : -r ≠ -r' := fun h => hne (by
    have : r = r' := by
      funext w
      have := congrFun h w
      simp only [Pi.neg_apply] at this
      omega
    exact this.symm)
  have dr'rn' : r' ≠ -r' := fun h => by
    have := congrFun h w₀'
    simp only [Pi.neg_apply] at this
    omega
  -- the box and the filter
  have hbox : ∀ (d : Fin (k + 1) → ℤ), (∀ w, -3 ≤ d w ∧ d w ≤ 3) →
      d ∈ Fintype.piFinset (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
    intro d hd
    rw [Fintype.mem_piFinset]
    intro w
    have := hd w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hnegsum : ∀ (s : Fin (k + 1) → ℤ), (∑ w, s w * v w) = 0 →
      (∑ w, (-s) w * v w) = 0 := by
    intro s hs
    have h1 : (∑ w, (-s) w * v w) = -(∑ w, s w * v w) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun w _ => by simp)
    rw [h1, hs, neg_zero]
  have hfilter : (Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0) = {0, r, -r, r', -r'} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      exact hpair c hcb hcv
    · intro hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · exact ⟨hbox _ hr3, hrel⟩
      · exact ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          have := hr3 w
          omega), hnegsum r hrel⟩
      · exact ⟨hbox _ hr3', hrel'⟩
      · exact ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          have := hr3' w
          omega), hnegsum r' hrel'⟩
  -- the five-element mass sum
  have hprod_neg : ∀ (s : Fin (k + 1) → ℤ),
      (∏ w : Fin (k + 1), cubeWtR ((-s) w)) = ∏ w : Fin (k + 1), cubeWtR (s w) :=
    fun s => Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])
  have hsum5 : (∑ c ∈ ({0, r, -r, r', -r'} : Finset (Fin (k + 1) → ℤ)),
      ∏ w, cubeWtR (c w)) = (5/2 : ℝ) ^ (k + 1) + 2 * P + 2 * P' := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d0r, d0rn, d0r', d0rn'⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨drrn, drr', drrn'⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨drnr', drnrn'⟩),
      Finset.sum_insert (by simpa using dr'rn'), Finset.sum_singleton,
      e0, hprod_neg r, hprod_neg r']
    rw [← hPdef, ← hP'def]
    ring
  have hM : (∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P + 2 * P') := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum5] at h
    exact h
  -- subfamily masses: the two restricted lines survive independently
  have hMsub : ∀ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      = (Q : ℝ) * ((5/2 : ℝ) ^ k + (if r i = 0 then (4/5) * P else 0)
          + (if r' i = 0 then (4/5) * P' else 0)) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r'
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r' := by
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
      exact hpair _ hdb hdv
    -- generic: a restriction sub-filter identity, one lemma-shaped `have` per case
    have hkill : ∀ (s : Fin (k + 1) → ℤ), s i ≠ 0 →
        ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = s → False := by
      intro s hs c hcs
      have := congrFun hcs i
      rw [Fin.insertNth_apply_same] at this
      exact hs this.symm
    have hkill_neg : ∀ (s : Fin (k + 1) → ℤ), s i ≠ 0 →
        ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = -s → False := by
      intro s hs c hcs
      have := congrFun hcs i
      rw [Fin.insertNth_apply_same] at this
      simp only [Pi.neg_apply] at this
      exact hs (by omega)
    have hrestr : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = s →
        c = fun j' => s (i.succAbove j') := by
      intro s hs c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      exact this
    have hrestr_neg : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = -s →
        c = fun j' => -(s (i.succAbove j')) := by
      intro s hs c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      simpa using this
    have hzero_c : ∀ (c : Fin k → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0 → c = 0 := by
      intro c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      simpa using this
    have hsbox : ∀ (d : Fin k → ℤ), (∀ j', -3 ≤ d j' ∧ d j' ≤ 3) →
        d ∈ Fintype.piFinset (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
      intro d hd
      rw [Fintype.mem_piFinset]
      intro j'
      have := hd j'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcb_of_mem : ∀ (c : Fin k → ℤ), c ∈ Fintype.piFinset
        (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) →
        ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
      intro c hcm j'
      have := (Fintype.mem_piFinset.mp hcm) j'
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h <;> omega
    have hsrel : ∀ (s : Fin (k + 1) → ℤ), s i = 0 → (∑ w, s w * v w) = 0 →
        (∑ j' : Fin k, s (i.succAbove j') * v (i.succAbove j')) = 0 := by
      intro s hs hsv
      have h := hsv
      rw [Fin.sum_univ_succAbove (fun w => s w * v w) i, hs, zero_mul, zero_add] at h
      exact h
    have hsneg : ∀ (s : Fin k → ℤ), (∑ j', s j' * v (i.succAbove j')) = 0 →
        (∑ j', (-(s j')) * v (i.succAbove j')) = 0 := by
      intro s hs
      have h1 : (∑ j', (-(s j')) * v (i.succAbove j'))
          = -(∑ j', s j' * v (i.succAbove j')) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun j' _ => by ring)
      rw [h1, hs, neg_zero]
    have hP52 : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        (∏ w, cubeWtR (s w)) = (5/2) * (∏ j' : Fin k, cubeWtR (s (i.succAbove j'))) := by
      intro s hs
      rw [Fin.prod_univ_succAbove (fun w => cubeWtR (s w)) i, hs]
      norm_num [cubeWtR]
    have hprod_negk : ∀ (s : Fin k → ℤ),
        (∏ j' : Fin k, cubeWtR ((fun j' => -(s j')) j')) = ∏ j' : Fin k, cubeWtR (s j') :=
      fun s => Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])
    have he0k : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
      rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
        ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases hri : r i = 0 <;> by_cases hri' : r' i = 0
    · -- both restricted lines survive
      rw [if_pos hri, if_pos hri']
      have hw₀i : w₀ ≠ i := fun h => hw₀ne (h ▸ hri)
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hw₀i' : w₀' ≠ i := fun h => hw₀ne' (h ▸ hri')
      obtain ⟨j₀', hj₀'⟩ := Fin.exists_succAbove_eq hw₀i'
      have hrs0 : r (i.succAbove j₀) ≠ 0 := by rw [hj₀]; exact hw₀ne
      have hrs0' : r' (i.succAbove j₀') ≠ 0 := by rw [hj₀']; exact hw₀ne'
      obtain ⟨wd, hwd⟩ := Function.ne_iff.mp (Ne.symm hne)
      have hwdi : wd ≠ i := fun h => hwd (by rw [h, hri, hri'])
      obtain ⟨jd, hjd⟩ := Fin.exists_succAbove_eq hwdi
      obtain ⟨wD, hwD⟩ := Function.ne_iff.mp hne'
      have hwDval : r wD ≠ -(r' wD) := by
        intro h
        apply hwD
        simp only [Pi.neg_apply]
        omega
      have hwDi : wD ≠ i := fun h => hwDval (by rw [h, hri, hri']; ring)
      obtain ⟨jD, hjD⟩ := Fin.exists_succAbove_eq hwDi
      have hsfilter : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, fun j' => r (i.succAbove j'), fun j' => -(r (i.succAbove j')),
             fun j' => r' (i.succAbove j'), fun j' => -(r' (i.succAbove j'))} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          rcases hlift c (hcb_of_mem c hcm) hcv with h | h | h | h | h
          · exact Or.inl (hzero_c c h)
          · exact Or.inr (Or.inl (hrestr r hri c h))
          · exact Or.inr (Or.inr (Or.inl (hrestr_neg r hri c h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hrestr r' hri' c h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hrestr_neg r' hri' c h))))
        · intro hmem
          rcases hmem with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hsbox _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · exact ⟨hsbox _ (fun j' => hr3 _), hsrel r hri hrel⟩
          · exact ⟨hsbox _ (fun j' => by
              show -3 ≤ -(r (i.succAbove j')) ∧ -(r (i.succAbove j')) ≤ 3
              have := hr3 (i.succAbove j')
              omega), hsneg _ (hsrel r hri hrel)⟩
          · exact ⟨hsbox _ (fun j' => hr3' _), hsrel r' hri' hrel'⟩
          · exact ⟨hsbox _ (fun j' => by
              show -3 ≤ -(r' (i.succAbove j')) ∧ -(r' (i.succAbove j')) ≤ 3
              have := hr3' (i.succAbove j')
              omega), hsneg _ (hsrel r' hri' hrel')⟩
      have sd0r : (0 : Fin k → ℤ) ≠ (fun j' => r (i.succAbove j')) :=
        fun h => hrs0 (congrFun h j₀).symm
      have sd0rn : (0 : Fin k → ℤ) ≠ (fun j' => -(r (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀
        simp only [Pi.zero_apply] at this
        omega
      have sd0r' : (0 : Fin k → ℤ) ≠ (fun j' => r' (i.succAbove j')) :=
        fun h => hrs0' (congrFun h j₀').symm
      have sd0rn' : (0 : Fin k → ℤ) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀'
        simp only [Pi.zero_apply] at this
        omega
      have sdrrn : (fun j' => r (i.succAbove j')) ≠ (fun j' => -(r (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀
        simp only at this
        omega
      have sdrr' : (fun j' => r (i.succAbove j')) ≠ (fun j' => r' (i.succAbove j')) := by
        intro h
        have := congrFun h jd
        simp only at this
        rw [hjd] at this
        exact hwd this
      have sdrrn' : (fun j' => r (i.succAbove j')) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h jD
        simp only at this
        rw [hjD] at this
        exact hwDval this
      have sdrnr' : (fun j' => -(r (i.succAbove j'))) ≠ (fun j' => r' (i.succAbove j')) := by
        intro h
        have := congrFun h jD
        simp only at this
        rw [hjD] at this
        omega
      have sdrnrn' : (fun j' => -(r (i.succAbove j'))) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h jd
        simp only at this
        rw [hjd] at this
        omega
      have sdr'rn' : (fun j' => r' (i.succAbove j')) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀'
        simp only at this
        omega
      have hssum : (∑ c ∈ ({0, fun j' => r (i.succAbove j'), fun j' => -(r (i.succAbove j')),
            fun j' => r' (i.succAbove j'), fun j' => -(r' (i.succAbove j'))} :
            Finset (Fin k → ℤ)), ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + (4/5) * P + (4/5) * P' := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨sd0r, sd0rn, sd0r', sd0rn'⟩),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨sdrrn, sdrr', sdrrn'⟩),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨sdrnr', sdrnrn'⟩),
          Finset.sum_insert (by simpa using sdr'rn'), Finset.sum_singleton, he0k,
          hprod_negk (fun j' => r (i.succAbove j')),
          hprod_negk (fun j' => r' (i.succAbove j'))]
        have hPr := hP52 r hri
        have hPr' := hP52 r' hri'
        rw [← hPdef] at hPr
        rw [← hP'def] at hPr'
        have e1 : (∏ j' : Fin k, cubeWtR (r (i.succAbove j'))) = (2/5) * P := by
          rw [hPr]; ring
        have e2 : (∏ j' : Fin k, cubeWtR (r' (i.succAbove j'))) = (2/5) * P' := by
          rw [hPr']; ring
        rw [e1, e2]
        ring
      have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
      rw [hsfilter, hssum] at h
      exact h
    · -- only the r-line survives
      rw [if_pos hri, if_neg hri']
      have hw₀i : w₀ ≠ i := fun h => hw₀ne (h ▸ hri)
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hrs0 : r (i.succAbove j₀) ≠ 0 := by rw [hj₀]; exact hw₀ne
      have hsfilter : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, fun j' => r (i.succAbove j'), fun j' => -(r (i.succAbove j'))} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          rcases hlift c (hcb_of_mem c hcm) hcv with h | h | h | h | h
          · exact Or.inl (hzero_c c h)
          · exact Or.inr (Or.inl (hrestr r hri c h))
          · exact Or.inr (Or.inr (hrestr_neg r hri c h))
          · exact absurd h (by intro hc; exact hkill r' hri' c hc)
          · exact absurd h (by intro hc; exact hkill_neg r' hri' c hc)
        · intro hmem
          rcases hmem with rfl | rfl | rfl
          · exact ⟨hsbox _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · exact ⟨hsbox _ (fun j' => hr3 _), hsrel r hri hrel⟩
          · exact ⟨hsbox _ (fun j' => by
              show -3 ≤ -(r (i.succAbove j')) ∧ -(r (i.succAbove j')) ≤ 3
              have := hr3 (i.succAbove j')
              omega), hsneg _ (hsrel r hri hrel)⟩
      have sd0r : (0 : Fin k → ℤ) ≠ (fun j' => r (i.succAbove j')) :=
        fun h => hrs0 (congrFun h j₀).symm
      have sd0rn : (0 : Fin k → ℤ) ≠ (fun j' => -(r (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀
        simp only [Pi.zero_apply] at this
        omega
      have sdrrn : (fun j' => r (i.succAbove j')) ≠ (fun j' => -(r (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀
        simp only at this
        omega
      have hssum : (∑ c ∈ ({0, fun j' => r (i.succAbove j'),
            fun j' => -(r (i.succAbove j'))} : Finset (Fin k → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + (4/5) * P := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨sd0r, sd0rn⟩),
          Finset.sum_insert (by simpa using sdrrn), Finset.sum_singleton, he0k,
          hprod_negk]
        have hPr := hP52 r hri
        rw [← hPdef] at hPr
        have e1 : (∏ j' : Fin k, cubeWtR (r (i.succAbove j'))) = (2/5) * P := by
          rw [hPr]; ring
        rw [e1]
        ring
      have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
      rw [hsfilter, hssum] at h
      rw [h]
      ring
    · -- only the r'-line survives
      rw [if_neg hri, if_pos hri']
      have hw₀i' : w₀' ≠ i := fun h => hw₀ne' (h ▸ hri')
      obtain ⟨j₀', hj₀'⟩ := Fin.exists_succAbove_eq hw₀i'
      have hrs0' : r' (i.succAbove j₀') ≠ 0 := by rw [hj₀']; exact hw₀ne'
      have hsfilter : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, fun j' => r' (i.succAbove j'), fun j' => -(r' (i.succAbove j'))} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          rcases hlift c (hcb_of_mem c hcm) hcv with h | h | h | h | h
          · exact Or.inl (hzero_c c h)
          · exact absurd h (by intro hc; exact hkill r hri c hc)
          · exact absurd h (by intro hc; exact hkill_neg r hri c hc)
          · exact Or.inr (Or.inl (hrestr r' hri' c h))
          · exact Or.inr (Or.inr (hrestr_neg r' hri' c h))
        · intro hmem
          rcases hmem with rfl | rfl | rfl
          · exact ⟨hsbox _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · exact ⟨hsbox _ (fun j' => hr3' _), hsrel r' hri' hrel'⟩
          · exact ⟨hsbox _ (fun j' => by
              show -3 ≤ -(r' (i.succAbove j')) ∧ -(r' (i.succAbove j')) ≤ 3
              have := hr3' (i.succAbove j')
              omega), hsneg _ (hsrel r' hri' hrel')⟩
      have sd0r' : (0 : Fin k → ℤ) ≠ (fun j' => r' (i.succAbove j')) :=
        fun h => hrs0' (congrFun h j₀').symm
      have sd0rn' : (0 : Fin k → ℤ) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀'
        simp only [Pi.zero_apply] at this
        omega
      have sdr'rn' : (fun j' => r' (i.succAbove j')) ≠ (fun j' => -(r' (i.succAbove j'))) := by
        intro h
        have := congrFun h j₀'
        simp only at this
        omega
      have hssum : (∑ c ∈ ({0, fun j' => r' (i.succAbove j'),
            fun j' => -(r' (i.succAbove j'))} : Finset (Fin k → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + (4/5) * P' := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨sd0r', sd0rn'⟩),
          Finset.sum_insert (by simpa using sdr'rn'), Finset.sum_singleton, he0k,
          hprod_negk]
        have hPr' := hP52 r' hri'
        rw [← hP'def] at hPr'
        have e1 : (∏ j' : Fin k, cubeWtR (r' (i.succAbove j'))) = (2/5) * P' := by
          rw [hPr']; ring
        rw [e1]
        ring
      have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
      rw [hsfilter, hssum] at h
      rw [h]
      ring
    · -- both lines killed: the subfamily is three-dissociated
      rw [if_neg hri, if_neg hri']
      have hdiss : ThreeDissoc (fun j' => v (i.succAbove j')) := by
        intro c hc hcv
        rcases hlift c hc hcv with h | h | h | h | h
        · exact hzero_c c h
        · exact absurd h (by intro hc'; exact hkill r hri c hc')
        · exact absurd h (by intro hc'; exact hkill_neg r hri c hc')
        · exact absurd h (by intro hc'; exact hkill r' hri' c hc')
        · exact absurd h (by intro hc'; exact hkill_neg r' hri' c hc')
      have h := riesz_mass_cube_real k _ Q hQ0 hsubQ hdiss
      rw [h]
      ring
  -- assemble
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * P + 2 * P'))
    (fun i => (Q : ℝ) * ((5/2 : ℝ) ^ k + (if r i = 0 then (4/5) * P else 0)
        + (if r' i = 0 then (4/5) * P' else 0)))
    hM hMsub ?_
  -- the numeric close
  set z : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card with hzdef
  set z' : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r' i = 0)).card with hz'def
  have hsum : (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
      + (if r i = 0 then (4/5) * P else 0) + (if r' i = 0 then (4/5) * P' else 0)))
      = (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * (z : ℝ) * P + (4/5) * (z' : ℝ) * P') := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : (∑ i : Fin (k + 1), (if r i = 0 then (4/5) * P else 0))
        = (4/5) * (z : ℝ) * P := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
        nsmul_eq_mul, ← hzdef]
      ring
    have h2 : (∑ i : Fin (k + 1), (if r' i = 0 then (4/5) * P' else 0))
        = (4/5) * (z' : ℝ) * P' := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
        nsmul_eq_mul, ← hz'def]
      ring
    rw [h1, h2]
    push_cast
    ring
  rw [hsum]
  have hB0 : (0 : ℝ) < (5/2 : ℝ) ^ k := by positivity
  have hzle : (z : ℝ) ≤ (k : ℝ) + 1 := by
    have h1 : z ≤ k + 1 := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin (k + 1)))
        (fun i => r i = 0)
      simpa using this
    exact_mod_cast h1
  have hz'le : (z' : ℝ) ≤ (k : ℝ) + 1 := by
    have h1 : z' ≤ k + 1 := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin (k + 1)))
        (fun i => r' i = 0)
      simpa using this
    exact_mod_cast h1
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hz'0 : (0 : ℝ) ≤ (z' : ℝ) := Nat.cast_nonneg z'
  have hu0 : (0 : ℝ) ≤ 1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2))) := by
    have := Real.cos_le_one (2 * π * (1 / ((k : ℝ) + 2)))
    linarith
  have hu30 : (0 : ℝ) ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 :=
    pow_nonneg hu0 3
  have hclose := cube_union_close hk
  have hPabs : |P| ≤ (63/80) * (5/2 : ℝ) ^ k := by
    have := abs_nonneg P'
    linarith [hPP]
  have hP'abs : |P'| ≤ (63/80) * (5/2 : ℝ) ^ k := by
    have := abs_nonneg P
    linarith [hPP]
  have hind : ∀ (zz PP : ℝ), 0 ≤ zz → zz ≤ (k : ℝ) + 1 →
      (4/5) * zz * PP ≤ (4/5) * ((k : ℝ) + 1) * max PP 0 := by
    intro zz PP hzz hzzle
    rcases le_total 0 PP with hP0 | hP0
    · rw [max_eq_left hP0]
      have h1 : zz * PP ≤ ((k : ℝ) + 1) * PP := mul_le_mul_of_nonneg_right hzzle hP0
      nlinarith [h1]
    · rw [max_eq_right hP0]
      have h1 : zz * PP ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hzz hP0
      nlinarith [h1]
  have hind1 := hind (z : ℝ) P hz0 hzle
  have hind2 := hind (z' : ℝ) P' hz'0 hz'le
  have hm1 : (0:ℝ) ≤ max P 0 := le_max_right P 0
  have hm2 : (0:ℝ) ≤ max P' 0 := le_max_right P' 0
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hLHS : (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
      * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * (z : ℝ) * P + (4/5) * (z' : ℝ) * P'))
      < (Q : ℝ) * ((7/8) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0)) := by
    have hinner : ((k : ℝ) + 1) * (5/2 : ℝ) ^ k + (4/5) * (z : ℝ) * P + (4/5) * (z' : ℝ) * P'
        ≤ ((k : ℝ) + 1) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0) := by
      nlinarith [hind1, hind2, hm1, hm2, hk1]
    have hpos_inner : (0:ℝ) < (5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0 := by
      positivity
    calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * (z : ℝ) * P + (4/5) * (z' : ℝ) * P'))
        ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
          * ((Q : ℝ) * (((k : ℝ) + 1) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0))) := by
          refine mul_le_mul_of_nonneg_left ?_ hu30
          exact mul_le_mul_of_nonneg_left hinner (le_of_lt hQR)
      _ = ((1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * ((k : ℝ) + 1))
          * ((Q : ℝ) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0)) := by
          ring
      _ < (7/8) * ((Q : ℝ) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0)) := by
          exact mul_lt_mul_of_pos_right hclose (mul_pos hQR hpos_inner)
      _ = (Q : ℝ) * ((7/8) * ((5/2 : ℝ) ^ k + (4/5) * max P 0 + (4/5) * max P' 0)) := by ring
  refine lt_of_lt_of_le hLHS ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
  have hpow : (5/2 : ℝ) ^ (k + 1) = (5/2) * (5/2 : ℝ) ^ k := by
    rw [pow_succ]; ring
  rw [hpow]
  rcases le_total 0 P with hP0 | hP0 <;> rcases le_total 0 P' with hP'0 | hP'0
  · rw [max_eq_left hP0, max_eq_left hP'0]
    nlinarith [hB0, hP0, hP'0]
  · rw [max_eq_left hP0, max_eq_right hP'0]
    have hP'ge : -((63/80) * (5/2 : ℝ) ^ k) + P ≤ P' := by
      have h1 : |P| = P := abs_of_nonneg hP0
      have h2 : |P'| = -P' := abs_of_nonpos hP'0
      have := hPP
      rw [h1, h2] at this
      linarith
    nlinarith [hB0, hP0, hP'ge]
  · rw [max_eq_right hP0, max_eq_left hP'0]
    have hPge : -((63/80) * (5/2 : ℝ) ^ k) + P' ≤ P := by
      have h1 : |P'| = P' := abs_of_nonneg hP'0
      have h2 : |P| = -P := abs_of_nonpos hP0
      have := hPP
      rw [h1, h2] at this
      linarith
    nlinarith [hB0, hP'0, hPge]
  · rw [max_eq_right hP0, max_eq_right hP'0]
    have hboth : -((63/80) * (5/2 : ℝ) ^ k) ≤ P + P' := by
      have h1 : |P| = -P := abs_of_nonpos hP0
      have h2 : |P'| = -P' := abs_of_nonpos hP'0
      have := hPP
      rw [h1, h2] at this
      linarith
    nlinarith [hB0, hboth]

/-- **The three-direction residual**: the dense-torsion shard families whose
`[-3,3]`-vanishing set is neither trivial, nor one line, nor two lines — at
least three essentially independent bounded directions. -/
def CubeThreeDirResidual : Prop :=
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
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **The rank-two core shrinks to the three-direction core**: clean pairs go
to the pair floor. -/
theorem cubeRankTwo_of_cubeThreeDir (h : CubeThreeDirResidual) : CubeRankTwoResidual := by
  intro k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin
  by_cases hpair : ∃ r r' : Fin (k + 1) → ℤ,
      (∀ w, -3 ≤ r w ∧ r w ≤ 3) ∧ (∀ w, -3 ≤ r' w ∧ r' w ≤ 3) ∧
      r ≠ 0 ∧ r' ≠ 0 ∧ r' ≠ r ∧ r' ≠ -r ∧
      (∑ w, r w * v w) = 0 ∧ (∑ w, r' w * v w) = 0 ∧
      (∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = r' ∨ c = -r')
  · obtain ⟨r, r', hr3, hr3', hr0, hr'0, hne, hne', hrel, hrel', hp⟩ := hpair
    exact torsion_pair_cube_floor hk4 v hv hSF r r' hr3 hr3' hr0 hr'0 hne hne' hrel hrel' hp
  · exact h k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin hpair

/-- The dense-torsion shard reduces to the three-direction core. -/
theorem denseTorsion_of_cubeThreeDir (h : CubeThreeDirResidual) : DenseTorsionResidual :=
  denseTorsion_of_cubeRankTwo (cubeRankTwo_of_cubeThreeDir h)

end LRSpectrumFull
