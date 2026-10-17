/-
# The escaping-triple cube floor and the dense-web reduction

`torsion_triple_cube_floor` — a StrongFree positive family (`k ≥ 4`) whose
`[-3,3]`-vanishing set is three lines `{0, ±r₁, ±r₂, ±r₃}` with all pairwise
sums and differences escaping the box meets the floor `1/(k+2)`.

Two new devices.  **The sharpened dichotomy** (`pair_heavy_partner`): if a
generator is generic-heavy — a single `±2` coordinate, no `±3` — then its two
escape coordinates against any partner cannot both sit on its big coordinate,
and an escape off it forces a `±3` on the partner.  Hence in an escaping
triple at most one generator is generic-heavy and the others carry `±3`s:
the joint weight is capped at exactly `(3/4)(5/2)^k` (`triple_weight_cap`),
against a close threshold of `(8k+2)/5 · u³ < 1` (`cube_triple_close`).

**The inexact-mass architecture**: the union close needs only a lower bound
on the mass and upper bounds on the subfamily masses, so instead of exact
filter identities the proof uses subset bounds — the vanishing filter sits
inside `{0} ∪ {±rᵢ}` and each subfamily filter inside the surviving
restrictions — eliminating all distinctness bookkeeping.  The union engine
is instantiated with the grid sums themselves (`hM := rfl`).
-/
import LRSpectrumFull.Delta2CubePair

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- The zero vector's weight product in dimension `n`. -/
theorem cubeWtR_prod_zero (n : ℕ) :
    (∏ w : Fin n, cubeWtR ((0 : Fin n → ℤ) w)) = (5/2 : ℝ) ^ n := by
  rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
    ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin n → ℤ) w) = 5/2)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum over an inserted element is at most the value plus the rest, for
nonnegative weights (duplicates only help). -/
theorem sum_insert_le_of_nonneg {α : Type*} [DecidableEq α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (a : α) (s : Finset α) :
    (∑ x ∈ insert a s, f x) ≤ f a + ∑ x ∈ s, f x := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_self.mpr h]
    have := hf a
    linarith
  · rw [Finset.sum_insert h]

/-- **Mass lower bound by candidates**: if a weight-sum's index set contains
`0` and is otherwise inside a candidate set of total absolute weight `≤ T`,
the sum is at least `(5/2)^n - T`. -/
theorem mass_lower_of_subset {n : ℕ} (F S : Finset (Fin n → ℤ))
    (h0 : (0 : Fin n → ℤ) ∈ F) (hFS : F ⊆ insert 0 S) (T : ℝ)
    (hT : (∑ c ∈ S, |∏ w, cubeWtR (c w)|) ≤ T) :
    (5/2 : ℝ) ^ n - T ≤ ∑ c ∈ F, ∏ w, cubeWtR (c w) := by
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
  have habs : -(∑ c ∈ F.erase 0, |∏ w, cubeWtR (c w)|)
      ≤ ∑ c ∈ F.erase 0, ∏ w, cubeWtR (c w) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun c _ => neg_abs_le _)
  have hmono : (∑ c ∈ F.erase 0, |∏ w, cubeWtR (c w)|)
      ≤ ∑ c ∈ S, |∏ w, cubeWtR (c w)| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => abs_nonneg _)
  rw [hsplit, cubeWtR_prod_zero]
  linarith

/-- **Mass upper bound by candidates**: a weight-sum whose index set sits
inside `{0} ∪ S` is at most `(5/2)^n` plus the candidate total. -/
theorem mass_upper_of_subset {n : ℕ} (F S : Finset (Fin n → ℤ))
    (hFS : F ⊆ insert 0 S) (T : ℝ)
    (hT : (∑ c ∈ S, |∏ w, cubeWtR (c w)|) ≤ T) :
    (∑ c ∈ F, ∏ w, cubeWtR (c w)) ≤ (5/2 : ℝ) ^ n + T := by
  have h1 : (∑ c ∈ F, ∏ w, cubeWtR (c w)) ≤ ∑ c ∈ F, |∏ w, cubeWtR (c w)| :=
    Finset.sum_le_sum (fun c _ => le_abs_self _)
  have h2 : (∑ c ∈ F, |∏ w, cubeWtR (c w)|)
      ≤ ∑ c ∈ insert 0 S, |∏ w, cubeWtR (c w)| :=
    Finset.sum_le_sum_of_subset_of_nonneg hFS (fun c _ _ => abs_nonneg _)
  have h3 : (∑ c ∈ insert (0 : Fin n → ℤ) S, |∏ w, cubeWtR (c w)|)
      ≤ |∏ w, cubeWtR ((0 : Fin n → ℤ) w)| + ∑ c ∈ S, |∏ w, cubeWtR (c w)| :=
    sum_insert_le_of_nonneg _ (fun c => abs_nonneg _) _ _
  rw [cubeWtR_prod_zero] at h3
  have h4 : |(5/2 : ℝ) ^ n| = (5/2 : ℝ) ^ n := abs_of_pos (by positivity)
  linarith [h1, h2, h3, h4.le]

/-- **The sharpened heavy-partner lemma.**  A generic-heavy generator — not
`TwoBig`, not `ThreeBig` — forces a `±3` on every escaping partner: the two
escape coordinates cannot share its unique big coordinate, and an escape off
it meets only `≤ 1` entries of the generator. -/
theorem pair_heavy_partner {m : ℕ} (r r' : Fin m → ℤ)
    (hr3 : ∀ w, -3 ≤ r w ∧ r w ≤ 3) (hr3' : ∀ w, -3 ≤ r' w ∧ r' w ≤ 3)
    (hbig : ∃ w, r w ≤ -2 ∨ 2 ≤ r w)
    (hsup : ∀ w, r w ≠ 0 → ∃ w', w' ≠ w ∧ r w' ≠ 0)
    (hsup' : ∀ w, r' w ≠ 0 → ∃ w', w' ≠ w ∧ r' w' ≠ 0)
    (hnt : ¬ TwoBig r) (hn3 : ¬ ThreeBig r)
    (hplus : ∃ w, r w + r' w ≤ -4 ∨ 4 ≤ r w + r' w)
    (hminus : ∃ w, r w - r' w ≤ -4 ∨ 4 ≤ r w - r' w) :
    ThreeBig r' := by
  classical
  obtain ⟨w₀, hw₀⟩ := hbig
  -- no ±3 anywhere on r
  have hno3 : ∀ w, r w ≠ -3 ∧ r w ≠ 3 := by
    intro w
    by_contra hc
    push_neg at hc
    have h3w : r w = -3 ∨ r w = 3 := by
      by_cases h : r w = -3
      · exact Or.inl h
      · exact Or.inr (hc h)
    have hwne : r w ≠ 0 := by rcases h3w with h | h <;> omega
    obtain ⟨w', hw'ne, hw'⟩ := hsup w hwne
    exact hn3 ⟨w, w', hw'ne.symm, h3w, hw'⟩
  -- all other coordinates of r are small
  have hsmall : ∀ w, w ≠ w₀ → -1 ≤ r w ∧ r w ≤ 1 := by
    intro w hw
    by_contra hc
    have hb : r w ≤ -2 ∨ 2 ≤ r w := by
      have := hr3 w
      omega
    exact hnt ⟨w, w₀, hw, hb, hw₀⟩
  obtain ⟨wp, hwp⟩ := hplus
  obtain ⟨wm, hwm⟩ := hminus
  have hpm : wp ≠ wm := by
    intro h
    rw [h] at hwp
    have h1 := hr3 wm
    have h2 := hr3' wm
    omega
  -- one of the two escapes is off the big coordinate
  have hoff : ∃ wx, wx ≠ w₀ ∧ (r wx + r' wx ≤ -4 ∨ 4 ≤ r wx + r' wx
      ∨ r wx - r' wx ≤ -4 ∨ 4 ≤ r wx - r' wx) := by
    by_cases hp0 : wp = w₀
    · refine ⟨wm, ?_, ?_⟩
      · intro h
        exact hpm (hp0.trans h.symm)
      · tauto
    · exact ⟨wp, hp0, by tauto⟩
  obtain ⟨wx, hwx₀, hwx⟩ := hoff
  have hsx := hsmall wx hwx₀
  have hr3x' := hr3' wx
  have h3' : r' wx = -3 ∨ r' wx = 3 := by omega
  have hxne : r' wx ≠ 0 := by rcases h3' with h | h <;> omega
  obtain ⟨w', hw'ne, hw'⟩ := hsup' wx hxne
  exact ⟨wx, w', hw'ne.symm, h3', hw'⟩

/-- The `TwoBig` weight cap `(9/40)(5/2)^k`, with the `ThreeBig` cap
`(3/32)(5/2)^k` folded in: any classed generator obeys `(9/40)(5/2)^k`. -/
theorem class_bound {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1) → ℤ)
    (h : TwoBig r ∨ ThreeBig r) :
    |∏ w, cubeWtR (r w)| ≤ (9/40) * (5/2 : ℝ) ^ k := by
  have hpow : (5/2 : ℝ) ^ k = (5/2) ^ (k - 1) * (5/2) := by
    rw [← pow_succ]
    congr 1
    omega
  rcases h with ⟨w₀, w₁, hne, hb₀, hb₁⟩ | ⟨w₀, w₁, hne, hb₀, hb₁⟩
  · calc |∏ w, cubeWtR (r w)|
        ≤ (3/4) * (3/4) * (5/2 : ℝ) ^ (k - 1) :=
          cube_prod_bound_two hk r w₀ w₁ (Ne.symm hne) _ _ (by norm_num) (by norm_num)
            (cubeWtR_abs_le_two _ hb₀) (cubeWtR_abs_le_two _ hb₁)
      _ ≤ (9/40) * (5/2 : ℝ) ^ k := by rw [hpow]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 5/2) (k-1)]
  · calc |∏ w, cubeWtR (r w)|
        ≤ (1/8) * (15/8) * (5/2 : ℝ) ^ (k - 1) :=
          cube_prod_bound_two hk r w₀ w₁ (Ne.symm hne) _ _ (by norm_num) (by norm_num)
            (cubeWtR_abs_le_three _ hb₀) (cubeWtR_abs_le_ne _ hb₁)
      _ ≤ (9/40) * (5/2 : ℝ) ^ k := by rw [hpow]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 5/2) (k-1)]

/-- The `ThreeBig` weight cap alone: `(3/32)(5/2)^k`. -/
theorem class_bound_three {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1) → ℤ)
    (h : ThreeBig r) :
    |∏ w, cubeWtR (r w)| ≤ (3/32) * (5/2 : ℝ) ^ k := by
  have hpow : (5/2 : ℝ) ^ k = (5/2) ^ (k - 1) * (5/2) := by
    rw [← pow_succ]
    congr 1
    omega
  obtain ⟨w₀, w₁, hne, hb₀, hb₁⟩ := h
  calc |∏ w, cubeWtR (r w)|
      ≤ (1/8) * (15/8) * (5/2 : ℝ) ^ (k - 1) :=
        cube_prod_bound_two hk r w₀ w₁ (Ne.symm hne) _ _ (by norm_num) (by norm_num)
          (cubeWtR_abs_le_three _ hb₀) (cubeWtR_abs_le_ne _ hb₁)
    _ = (3/32) * (5/2 : ℝ) ^ k := by rw [hpow]; ring

/-- **The escaping-triple weight cap**: three pairwise-escaping generators
have joint weight at most `(3/4)(5/2)^k` — at most one is generic-heavy, and
then the other two carry `±3`s: `9/16 + 3/32 + 3/32 = 3/4`. -/
theorem triple_weight_cap {k : ℕ} (hk : 1 ≤ k) (r₁ r₂ r₃ : Fin (k + 1) → ℤ)
    (h1 : ∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) (h2 : ∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3)
    (h3 : ∀ w, -3 ≤ r₃ w ∧ r₃ w ≤ 3)
    (hb1 : ∃ w, r₁ w ≤ -2 ∨ 2 ≤ r₁ w) (hb2 : ∃ w, r₂ w ≤ -2 ∨ 2 ≤ r₂ w)
    (hb3 : ∃ w, r₃ w ≤ -2 ∨ 2 ≤ r₃ w)
    (hs1 : ∀ w, r₁ w ≠ 0 → ∃ w', w' ≠ w ∧ r₁ w' ≠ 0)
    (hs2 : ∀ w, r₂ w ≠ 0 → ∃ w', w' ≠ w ∧ r₂ w' ≠ 0)
    (hs3 : ∀ w, r₃ w ≠ 0 → ∃ w', w' ≠ w ∧ r₃ w' ≠ 0)
    (e12p : ∃ w, r₁ w + r₂ w ≤ -4 ∨ 4 ≤ r₁ w + r₂ w)
    (e12m : ∃ w, r₁ w - r₂ w ≤ -4 ∨ 4 ≤ r₁ w - r₂ w)
    (e13p : ∃ w, r₁ w + r₃ w ≤ -4 ∨ 4 ≤ r₁ w + r₃ w)
    (e13m : ∃ w, r₁ w - r₃ w ≤ -4 ∨ 4 ≤ r₁ w - r₃ w)
    (e23p : ∃ w, r₂ w + r₃ w ≤ -4 ∨ 4 ≤ r₂ w + r₃ w)
    (e23m : ∃ w, r₂ w - r₃ w ≤ -4 ∨ 4 ≤ r₂ w - r₃ w) :
    |∏ w, cubeWtR (r₁ w)| + |∏ w, cubeWtR (r₂ w)| + |∏ w, cubeWtR (r₃ w)|
      ≤ (3/4) * (5/2 : ℝ) ^ k := by
  classical
  have hB0 : (0:ℝ) < (5/2 : ℝ) ^ k := by positivity
  -- the generic line bound (single big + second support)
  have hgen : ∀ (s : Fin (k + 1) → ℤ), (∃ w, s w ≤ -2 ∨ 2 ≤ s w) →
      (∀ w, s w ≠ 0 → ∃ w', w' ≠ w ∧ s w' ≠ 0) →
      |∏ w, cubeWtR (s w)| ≤ (9/16) * (5/2 : ℝ) ^ k := by
    intro s hb hs
    obtain ⟨w₀, hw₀⟩ := hb
    obtain ⟨w₁, hw₁ne, hw₁⟩ := hs w₀ (by rcases hw₀ with h | h <;> omega)
    exact line_weight_bound hk s w₀ w₁ hw₁ne hw₀ hw₁
  -- the negation of the pair escape dichotomy is impossible for two generics
  have hnogen2 : ∀ (a b : Fin (k + 1) → ℤ),
      (∀ w, -3 ≤ a w ∧ a w ≤ 3) → (∀ w, -3 ≤ b w ∧ b w ≤ 3) →
      (∃ w, a w ≤ -2 ∨ 2 ≤ a w) →
      (∀ w, a w ≠ 0 → ∃ w', w' ≠ w ∧ a w' ≠ 0) →
      (∀ w, b w ≠ 0 → ∃ w', w' ≠ w ∧ b w' ≠ 0) →
      (∃ w, a w + b w ≤ -4 ∨ 4 ≤ a w + b w) →
      (∃ w, a w - b w ≤ -4 ∨ 4 ≤ a w - b w) →
      ¬ (TwoBig a ∨ ThreeBig a) → ¬ (TwoBig b ∨ ThreeBig b) → False := by
    intro a b ha3 hb3 hba hsa hsb hep hem hna hnb
    push_neg at hna
    have := pair_heavy_partner a b ha3 hb3 hba hsa hsb hna.1 hna.2 hep hem
    exact hnb (Or.inr this)
  by_cases hc1 : TwoBig r₁ ∨ ThreeBig r₁ <;>
    by_cases hc2 : TwoBig r₂ ∨ ThreeBig r₂ <;>
    by_cases hc3 : TwoBig r₃ ∨ ThreeBig r₃
  · -- all classed
    have := class_bound hk r₁ hc1
    have := class_bound hk r₂ hc2
    have := class_bound hk r₃ hc3
    linarith
  · -- r₃ generic: r₁, r₂ forced ThreeBig by the sharpened lemma
    push_neg at hc3
    have hT1 : ThreeBig r₁ := by
      have hesc : ∃ w, r₃ w + r₁ w ≤ -4 ∨ 4 ≤ r₃ w + r₁ w := by
        obtain ⟨w, hw⟩ := e13p
        exact ⟨w, by omega⟩
      have hescm : ∃ w, r₃ w - r₁ w ≤ -4 ∨ 4 ≤ r₃ w - r₁ w := by
        obtain ⟨w, hw⟩ := e13m
        exact ⟨w, by omega⟩
      exact pair_heavy_partner r₃ r₁ h3 h1 hb3 hs3 hs1 hc3.1 hc3.2 hesc hescm
    have hT2 : ThreeBig r₂ := by
      have hesc : ∃ w, r₃ w + r₂ w ≤ -4 ∨ 4 ≤ r₃ w + r₂ w := by
        obtain ⟨w, hw⟩ := e23p
        exact ⟨w, by omega⟩
      have hescm : ∃ w, r₃ w - r₂ w ≤ -4 ∨ 4 ≤ r₃ w - r₂ w := by
        obtain ⟨w, hw⟩ := e23m
        exact ⟨w, by omega⟩
      exact pair_heavy_partner r₃ r₂ h3 h2 hb3 hs3 hs2 hc3.1 hc3.2 hesc hescm
    have := class_bound_three hk r₁ hT1
    have := class_bound_three hk r₂ hT2
    have := hgen r₃ hb3 hs3
    linarith
  · -- r₂ generic
    push_neg at hc2
    have hT1 : ThreeBig r₁ := by
      have hesc : ∃ w, r₂ w + r₁ w ≤ -4 ∨ 4 ≤ r₂ w + r₁ w := by
        obtain ⟨w, hw⟩ := e12p
        exact ⟨w, by omega⟩
      have hescm : ∃ w, r₂ w - r₁ w ≤ -4 ∨ 4 ≤ r₂ w - r₁ w := by
        obtain ⟨w, hw⟩ := e12m
        exact ⟨w, by omega⟩
      exact pair_heavy_partner r₂ r₁ h2 h1 hb2 hs2 hs1 hc2.1 hc2.2 hesc hescm
    have hT3 : ThreeBig r₃ := by
      exact pair_heavy_partner r₂ r₃ h2 h3 hb2 hs2 hs3 hc2.1 hc2.2 e23p e23m
    have := class_bound_three hk r₁ hT1
    have := class_bound_three hk r₃ hT3
    have := hgen r₂ hb2 hs2
    linarith
  · -- r₂ and r₃ generic: impossible
    exact absurd (hnogen2 r₂ r₃ h2 h3 hb2 hs2 hs3 e23p e23m hc2 hc3) (by simp)
  · -- r₁ generic
    push_neg at hc1
    have hT2 : ThreeBig r₂ :=
      pair_heavy_partner r₁ r₂ h1 h2 hb1 hs1 hs2 hc1.1 hc1.2 e12p e12m
    have hT3 : ThreeBig r₃ :=
      pair_heavy_partner r₁ r₃ h1 h3 hb1 hs1 hs3 hc1.1 hc1.2 e13p e13m
    have := class_bound_three hk r₂ hT2
    have := class_bound_three hk r₃ hT3
    have := hgen r₁ hb1 hs1
    linarith
  · -- r₁, r₃ generic: impossible
    exact absurd (hnogen2 r₁ r₃ h1 h3 hb1 hs1 hs3 e13p e13m hc1 hc3) (by simp)
  · -- r₁, r₂ generic: impossible
    exact absurd (hnogen2 r₁ r₂ h1 h2 hb1 hs1 hs2 e12p e12m hc1 hc2) (by simp)
  · -- all generic: impossible
    exact absurd (hnogen2 r₁ r₂ h1 h2 hb1 hs1 hs2 e12p e12m hc1 hc2) (by simp)

/-- **The triple close**: `u³(8k+2) < 5` at `δ = 1/(k+2)` for all `k ≥ 4` —
exact cosine at `k = 4` (`cos(π/3) = 1/2`, giving `34/8 < 5`), the sextic
`π`-chain beyond. -/
theorem cube_triple_close {k : ℕ} (hk : 4 ≤ k) :
    (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * (8 * (k : ℝ) + 2) < 5 := by
  rcases eq_or_lt_of_le hk with hk4 | hk5
  · -- k = 4: exact cosine
    subst hk4
    have harg : 2 * π * (1 / ((4 : ℕ) + 2 : ℝ)) = π / 3 := by
      push_cast
      ring
    rw [harg, Real.cos_pi_div_three]
    push_cast
    norm_num
  · -- k ≥ 5: the sextic chain
    have hk5' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
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
    have hkey : 8 * π ^ 6 * (8 * (k : ℝ) + 2) < 5 * ((k : ℝ) + 2) ^ 6 := by
      have h74 : (2401 : ℝ) ≤ ((k : ℝ) + 2) ^ 4 := by
        calc (2401 : ℝ) = 7 ^ 4 := by norm_num
          _ ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      have h6b : 2401 * ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 6 := by
        have hsplit : ((k : ℝ) + 2) ^ 6 = ((k : ℝ) + 2) ^ 4 * ((k : ℝ) + 2) ^ 2 := by ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right h74 (by positivity)
      have h8k : 8 * (k : ℝ) + 2 ≤ 8 * ((k : ℝ) + 2) := by linarith
      have hπk : 8 * π ^ 6 * (8 * (k : ℝ) + 2) ≤ 8 * π ^ 6 * (8 * ((k : ℝ) + 2)) := by
        have h8π : (0:ℝ) ≤ 8 * π ^ 6 := by positivity
        exact mul_le_mul_of_nonneg_left h8k h8π
      have hgrow : 64 * 961.51 * ((k : ℝ) + 2) < 5 * (2401 * ((k : ℝ) + 2) ^ 2) := by
        nlinarith [hk5']
      calc 8 * π ^ 6 * (8 * (k : ℝ) + 2)
          ≤ 64 * π ^ 6 * ((k : ℝ) + 2) := by nlinarith [hπk]
        _ < 64 * 961.51 * ((k : ℝ) + 2) := by
            have : (0:ℝ) < (k : ℝ) + 2 := by linarith
            nlinarith [hπ6, this]
        _ < 5 * (2401 * ((k : ℝ) + 2) ^ 2) := hgrow
        _ ≤ 5 * ((k : ℝ) + 2) ^ 6 := by nlinarith [h6b]
    calc (1 - Real.cos (2 * π * δ)) ^ 3 * (8 * (k : ℝ) + 2)
        < (2 * (π * δ) ^ 2) ^ 3 * (8 * (k : ℝ) + 2) := by
          refine mul_lt_mul_of_pos_right hu3 ?_
          have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
      _ = (8 * π ^ 6 * (8 * (k : ℝ) + 2)) * δ ^ 6 := by ring
      _ < (5 * ((k : ℝ) + 2) ^ 6) * δ ^ 6 := by
          refine mul_lt_mul_of_pos_right hkey (pow_pos hδ0 6)
      _ = 5 * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by ring
      _ = 5 := by rw [hδ61, mul_one]

set_option maxHeartbeats 3200000 in
/-- **The escaping-triple cube floor.**  A StrongFree positive family
(`k ≥ 4`) whose `[-3,3]`-vanishing set lies in three lines `{0, ±r₁, ±r₂, ±r₃}`
with all pairwise sums and differences escaping the box meets the floor
`1/(k+2)`.  Inexact masses: the mass is at least `Q((5/2)^{k+1} - 2T)` and
each subfamily mass at most `Q((5/2)^k + (4/5)·(surviving weights))` by the
candidate-subset bounds; the cap `T ≤ (3/4)(5/2)^k` and the close
`u³(8k+2) < 5` finish. -/
theorem torsion_triple_cube_floor {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hSF : StrongFree v)
    (r₁ r₂ r₃ : Fin (k + 1) → ℤ)
    (h13 : ∀ w, -3 ≤ r₁ w ∧ r₁ w ≤ 3) (h23 : ∀ w, -3 ≤ r₂ w ∧ r₂ w ≤ 3)
    (h33 : ∀ w, -3 ≤ r₃ w ∧ r₃ w ≤ 3)
    (h10 : r₁ ≠ 0) (h20 : r₂ ≠ 0) (h30 : r₃ ≠ 0)
    (hrel1 : (∑ w, r₁ w * v w) = 0) (hrel2 : (∑ w, r₂ w * v w) = 0)
    (hrel3 : (∑ w, r₃ w * v w) = 0)
    (hclass : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r₁ ∨ c = -r₁ ∨ c = r₂ ∨ c = -r₂ ∨ c = r₃ ∨ c = -r₃)
    (e12p : ∃ w, r₁ w + r₂ w ≤ -4 ∨ 4 ≤ r₁ w + r₂ w)
    (e12m : ∃ w, r₁ w - r₂ w ≤ -4 ∨ 4 ≤ r₁ w - r₂ w)
    (e13p : ∃ w, r₁ w + r₃ w ≤ -4 ∨ 4 ≤ r₁ w + r₃ w)
    (e13m : ∃ w, r₁ w - r₃ w ≤ -4 ∨ 4 ≤ r₁ w - r₃ w)
    (e23p : ∃ w, r₂ w + r₃ w ≤ -4 ∨ 4 ≤ r₂ w + r₃ w)
    (e23m : ∃ w, r₂ w - r₃ w ≤ -4 ∨ 4 ≤ r₂ w - r₃ w) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hB0 : (0 : ℝ) < (5/2 : ℝ) ^ k := by positivity
  -- bigness and support
  obtain ⟨wb1, hwb1⟩ := strongfree_cube_two v hSF r₁ h10 hrel1
  obtain ⟨wb2, hwb2⟩ := strongfree_cube_two v hSF r₂ h20 hrel2
  obtain ⟨wb3, hwb3⟩ := strongfree_cube_two v hSF r₃ h30 hrel3
  have hs1 : ∀ w, r₁ w ≠ 0 → ∃ w', w' ≠ w ∧ r₁ w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r₁ hrel1 w hw
  have hs2 : ∀ w, r₂ w ≠ 0 → ∃ w', w' ≠ w ∧ r₂ w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r₂ hrel2 w hw
  have hs3 : ∀ w, r₃ w ≠ 0 → ∃ w', w' ≠ w ∧ r₃ w' ≠ 0 :=
    fun w hw => cube_supp_two v hv r₃ hrel3 w hw
  set P₁ : ℝ := ∏ w, cubeWtR (r₁ w) with hP1def
  set P₂ : ℝ := ∏ w, cubeWtR (r₂ w) with hP2def
  set P₃ : ℝ := ∏ w, cubeWtR (r₃ w) with hP3def
  have hcap : |P₁| + |P₂| + |P₃| ≤ (3/4) * (5/2 : ℝ) ^ k :=
    triple_weight_cap (by omega) r₁ r₂ r₃ h13 h23 h33
      ⟨wb1, hwb1⟩ ⟨wb2, hwb2⟩ ⟨wb3, hwb3⟩ hs1 hs2 hs3
      e12p e12m e13p e13m e23p e23m
  -- the negation-invariance of weight products
  have hprod_neg : ∀ (s : Fin (k + 1) → ℤ),
      (∏ w : Fin (k + 1), cubeWtR ((-s) w)) = ∏ w : Fin (k + 1), cubeWtR (s w) :=
    fun s => Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])
  -- the main-mass lower bound
  have hbox0 : (0 : Fin (k + 1) → ℤ) ∈ Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
    rw [Fintype.mem_piFinset]
    intro w
    simp
  have hMlow : (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) - 2 * (|P₁| + |P₂| + |P₃|))
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
        ⊆ insert 0 ({r₁, -r₁, r₂, -r₂, r₃, -r₃} : Finset (Fin (k + 1) → ℤ)) := by
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
    have hS : (∑ c ∈ ({r₁, -r₁, r₂, -r₂, r₃, -r₃} : Finset (Fin (k + 1) → ℤ)),
        |∏ w, cubeWtR (c w)|) ≤ 2 * (|P₁| + |P₂| + |P₃|) := by
      have step : ∀ (a : Fin (k + 1) → ℤ) (s : Finset (Fin (k + 1) → ℤ)) (T : ℝ),
          (∑ c ∈ s, |∏ w, cubeWtR (c w)|) ≤ T →
          (∑ c ∈ insert a s, |∏ w, cubeWtR (c w)|) ≤ |∏ w, cubeWtR (a w)| + T := by
        intro a s T hT
        have := sum_insert_le_of_nonneg (fun c => |∏ w, cubeWtR (c w)|)
          (fun c => abs_nonneg _) a s
        linarith
      have habs_neg : ∀ (s : Fin (k + 1) → ℤ),
          |∏ w, cubeWtR ((-s) w)| = |∏ w, cubeWtR (s w)| :=
        fun s => by rw [hprod_neg]
      have h6 : (∑ c ∈ ({-r₃} : Finset (Fin (k + 1) → ℤ)), |∏ w, cubeWtR (c w)|)
          ≤ |P₃| := by
        rw [Finset.sum_singleton, habs_neg r₃]
      have h5 := step (-r₂) _ _ (step r₃ _ _ h6)
      have h4 := step (-r₁) _ _ (step r₂ _ _ h5)
      have h3 := step r₁ _ _ h4
      rw [habs_neg r₁, habs_neg r₂] at *
      calc (∑ c ∈ ({r₁, -r₁, r₂, -r₂, r₃, -r₃} : Finset (Fin (k + 1) → ℤ)),
          |∏ w, cubeWtR (c w)|) ≤ _ := h3
        _ ≤ 2 * (|P₁| + |P₂| + |P₃|) := by
            rw [← hP1def, ← hP2def, ← hP3def]
            linarith
    exact mass_lower_of_subset _ _ h0F hFS _ hS
  -- z-counts: each line vanishes on at most k-1 coordinates
  have hzcount : ∀ (r : Fin (k + 1) → ℤ), (∃ w, r w ≤ -2 ∨ 2 ≤ r w) →
      (∀ w, r w ≠ 0 → ∃ w', w' ≠ w ∧ r w' ≠ 0) →
      ((Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card : ℝ) ≤ (k : ℝ) - 1 := by
    intro r hb hs
    obtain ⟨w₀, hw₀⟩ := hb
    have hw₀ne : r w₀ ≠ 0 := by rcases hw₀ with h | h <;> omega
    obtain ⟨w₁, hw₁ne, hw₁⟩ := hs w₀ hw₀ne
    have hsub : (Finset.univ.filter (fun i : Fin (k + 1) => r i = 0))
        ⊆ (Finset.univ.erase w₀).erase w₁ := by
      intro c hc
      have hc0 := (Finset.mem_filter.mp hc).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ c⟩⟩
      · intro h
        rw [h] at hc0
        exact hw₁ hc0
      · intro h
        rw [h] at hc0
        exact hw₀ne hc0
    have hcard : ((Finset.univ.erase w₀).erase w₁).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hw₁ne, Finset.mem_univ w₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ w₀), Finset.card_univ, Fintype.card_fin]
      omega
    have h1 : (Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card ≤ k - 1 := by
      have := Finset.card_le_card hsub
      omega
    have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      ring
    calc ((Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card : ℝ)
        ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (k : ℝ) - 1 := h2
  -- per-subfamily upper bounds
  have hMsub_le : ∀ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3)
      ≤ (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (4/5) * ((if r₁ i = 0 then |P₁| else 0) + (if r₂ i = 0 then |P₂| else 0)
          + (if r₃ i = 0 then |P₃| else 0))) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle := subfamily_l1_le v i
      omega
    have hgrid := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    rw [hgrid]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
    -- the lift and its bookkeeping
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = 0
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r₁
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r₁
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r₂
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r₂
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r₃
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r₃ := by
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
    have hrestr : ∀ (s : Fin (k + 1) → ℤ), ∀ (c : Fin k → ℤ),
        (i.insertNth 0 c : Fin (k + 1) → ℤ) = s →
        c = fun j' => s (i.succAbove j') := by
      intro s c hcs
      funext j'
      have := congrFun hcs (i.succAbove j')
      rw [Fin.insertNth_apply_succAbove] at this
      exact this
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
    have hP52 : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        (∏ w, cubeWtR (s w)) = (5/2) * (∏ j' : Fin k, cubeWtR (s (i.succAbove j'))) := by
      intro s hs
      rw [Fin.prod_univ_succAbove (fun w => cubeWtR (s w)) i, hs]
      norm_num [cubeWtR]
    have habs_sub : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        (∏ w, cubeWtR (s w)) ≠ 0 ∨ True := fun _ _ => Or.inr trivial
    -- |restricted product| in terms of |P|
    have hsubval : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        |∏ j' : Fin k, cubeWtR (s (i.succAbove j'))| = (2/5) * |∏ w, cubeWtR (s w)| := by
      intro s hs
      have h := hP52 s hs
      have h2 : (∏ j' : Fin k, cubeWtR (s (i.succAbove j')))
          = (2/5) * (∏ w, cubeWtR (s w)) := by linarith
      rw [h2, abs_mul]
      norm_num
    have hsubval_neg : ∀ (s : Fin (k + 1) → ℤ), s i = 0 →
        |∏ j' : Fin k, cubeWtR ((fun j' => -(s (i.succAbove j'))) j')|
          = (2/5) * |∏ w, cubeWtR (s w)| := by
      intro s hs
      have hn : (∏ j' : Fin k, cubeWtR ((fun j' => -(s (i.succAbove j'))) j'))
          = ∏ j' : Fin k, cubeWtR (s (i.succAbove j')) :=
        Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])
      rw [hn]
      exact hsubval s hs
    have hstep : ∀ (a : Fin k → ℤ) (s : Finset (Fin k → ℤ)) (T : ℝ),
        (∑ c ∈ s, |∏ j', cubeWtR (c j')|) ≤ T →
        (∑ c ∈ insert a s, |∏ j', cubeWtR (c j')|) ≤ |∏ j', cubeWtR (a j')| + T := by
      intro a s T hT
      have := sum_insert_le_of_nonneg (fun c => |∏ j', cubeWtR (c j')|)
        (fun c => abs_nonneg _) a s
      linarith
    by_cases hri1 : r₁ i = 0 <;> by_cases hri2 : r₂ i = 0 <;> by_cases hri3 : r₃ i = 0
    · -- survivors: r₁, r₂, r₃
      rw [if_pos hri1, if_pos hri2, if_pos hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
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
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
        · rw [hrestr r₃ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
        · rw [show c = fun j' => -(r₃ (i.succAbove j')) from by
            rw [hrestr (-r₃) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))
      · have e1p : |∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))| = (2/5) * |P₁| :=
          hsubval r₁ hri1
        have e1n : |∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))| = (2/5) * |P₁| :=
          hsubval_neg r₁ hri1
        have e2p : |∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))| = (2/5) * |P₂| :=
          hsubval r₂ hri2
        have e2n : |∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))| = (2/5) * |P₂| :=
          hsubval_neg r₂ hri2
        have e3p : |∏ j' : Fin k, cubeWtR (r₃ (i.succAbove j'))| = (2/5) * |P₃| :=
          hsubval r₃ hri3
        have e3n : |∏ j' : Fin k, cubeWtR (-(r₃ (i.succAbove j')))| = (2/5) * |P₃| :=
          hsubval_neg r₃ hri3
        have hc6 : (∑ c ∈ ({(fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₃| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₃ hri3)
        have hc5 := hstep (fun j' => r₃ (i.succAbove j')) _ _ hc6
        have hc4 := hstep (fun j' => -(r₂ (i.succAbove j'))) _ _ hc5
        have hc3 := hstep (fun j' => r₂ (i.succAbove j')) _ _ hc4
        have hc2 := hstep (fun j' => -(r₁ (i.succAbove j'))) _ _ hc3
        have hc1 := hstep (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (|P₁| + |P₂| + |P₃|) := by
              simp only
              rw [e1p, e1n, e2p, e2n, e3p]
              linarith
    · -- survivors: r₁, r₂
      rw [if_pos hri1, if_pos hri2, if_neg hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
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
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
        · exact (hkill r₃ hri3 c h).elim
        · exact (hkill_neg r₃ hri3 c h).elim
      · have e1p : |∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))| = (2/5) * |P₁| :=
          hsubval r₁ hri1
        have e1n : |∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))| = (2/5) * |P₁| :=
          hsubval_neg r₁ hri1
        have e2p : |∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))| = (2/5) * |P₂| :=
          hsubval r₂ hri2
        have e2n : |∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))| = (2/5) * |P₂| :=
          hsubval_neg r₂ hri2
        have hc4 : (∑ c ∈ ({(fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₂| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₂ hri2)
        have hc3 := hstep (fun j' => r₂ (i.succAbove j')) _ _ hc4
        have hc2 := hstep (fun j' => -(r₁ (i.succAbove j'))) _ _ hc3
        have hc1 := hstep (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (|P₁| + |P₂| + 0) := by
              simp only
              rw [e1p, e1n, e2p]
              linarith
    · -- survivors: r₁, r₃
      rw [if_pos hri1, if_neg hri2, if_pos hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
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
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill_neg r₂ hri2 c h).elim
        · rw [hrestr r₃ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rw [show c = fun j' => -(r₃ (i.succAbove j')) from by
            rw [hrestr (-r₃) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      · have e1p : |∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))| = (2/5) * |P₁| :=
          hsubval r₁ hri1
        have e1n : |∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))| = (2/5) * |P₁| :=
          hsubval_neg r₁ hri1
        have e3p : |∏ j' : Fin k, cubeWtR (r₃ (i.succAbove j'))| = (2/5) * |P₃| :=
          hsubval r₃ hri3
        have e3n : |∏ j' : Fin k, cubeWtR (-(r₃ (i.succAbove j')))| = (2/5) * |P₃| :=
          hsubval_neg r₃ hri3
        have hc4 : (∑ c ∈ ({(fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₃| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₃ hri3)
        have hc3 := hstep (fun j' => r₃ (i.succAbove j')) _ _ hc4
        have hc2 := hstep (fun j' => -(r₁ (i.succAbove j'))) _ _ hc3
        have hc1 := hstep (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (|P₁| + 0 + |P₃|) := by
              simp only
              rw [e1p, e1n, e3p]
              linarith
    · -- survivors: r₁
      rw [if_pos hri1, if_neg hri2, if_neg hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
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
        · exact (hkill_neg r₂ hri2 c h).elim
        · exact (hkill r₃ hri3 c h).elim
        · exact (hkill_neg r₃ hri3 c h).elim
      · have e1p : |∏ j' : Fin k, cubeWtR (r₁ (i.succAbove j'))| = (2/5) * |P₁| :=
          hsubval r₁ hri1
        have e1n : |∏ j' : Fin k, cubeWtR (-(r₁ (i.succAbove j')))| = (2/5) * |P₁| :=
          hsubval_neg r₁ hri1
        have hc2 : (∑ c ∈ ({(fun j' => -(r₁ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₁| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₁ hri1)
        have hc1 := hstep (fun j' => r₁ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₁ (i.succAbove j')), (fun j' => -(r₁ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (|P₁| + 0 + 0) := by
              simp only
              rw [e1p]
              linarith
    · -- survivors: r₂, r₃
      rw [if_neg hri1, if_pos hri2, if_pos hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill_neg r₁ hri1 c h).elim
        · rw [hrestr r₂ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · rw [hrestr r₃ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rw [show c = fun j' => -(r₃ (i.succAbove j')) from by
            rw [hrestr (-r₃) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      · have e2p : |∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))| = (2/5) * |P₂| :=
          hsubval r₂ hri2
        have e2n : |∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))| = (2/5) * |P₂| :=
          hsubval_neg r₂ hri2
        have e3p : |∏ j' : Fin k, cubeWtR (r₃ (i.succAbove j'))| = (2/5) * |P₃| :=
          hsubval r₃ hri3
        have e3n : |∏ j' : Fin k, cubeWtR (-(r₃ (i.succAbove j')))| = (2/5) * |P₃| :=
          hsubval_neg r₃ hri3
        have hc4 : (∑ c ∈ ({(fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₃| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₃ hri3)
        have hc3 := hstep (fun j' => r₃ (i.succAbove j')) _ _ hc4
        have hc2 := hstep (fun j' => -(r₂ (i.succAbove j'))) _ _ hc3
        have hc1 := hstep (fun j' => r₂ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j'))), (fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (0 + |P₂| + |P₃|) := by
              simp only
              rw [e2p, e2n, e3p]
              linarith
    · -- survivors: r₂
      rw [if_neg hri1, if_pos hri2, if_neg hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill_neg r₁ hri1 c h).elim
        · rw [hrestr r₂ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₂ (i.succAbove j')) from by
            rw [hrestr (-r₂) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact (hkill r₃ hri3 c h).elim
        · exact (hkill_neg r₃ hri3 c h).elim
      · have e2p : |∏ j' : Fin k, cubeWtR (r₂ (i.succAbove j'))| = (2/5) * |P₂| :=
          hsubval r₂ hri2
        have e2n : |∏ j' : Fin k, cubeWtR (-(r₂ (i.succAbove j')))| = (2/5) * |P₂| :=
          hsubval_neg r₂ hri2
        have hc2 : (∑ c ∈ ({(fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₂| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₂ hri2)
        have hc1 := hstep (fun j' => r₂ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₂ (i.succAbove j')), (fun j' => -(r₂ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (0 + |P₂| + 0) := by
              simp only
              rw [e2p]
              linarith
    · -- survivors: r₃
      rw [if_neg hri1, if_neg hri2, if_pos hri3]
      refine mass_upper_of_subset _ ({(fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill_neg r₁ hri1 c h).elim
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill_neg r₂ hri2 c h).elim
        · rw [hrestr r₃ c h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [show c = fun j' => -(r₃ (i.succAbove j')) from by
            rw [hrestr (-r₃) c h]
            funext j'
            simp]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · have e3p : |∏ j' : Fin k, cubeWtR (r₃ (i.succAbove j'))| = (2/5) * |P₃| :=
          hsubval r₃ hri3
        have e3n : |∏ j' : Fin k, cubeWtR (-(r₃ (i.succAbove j')))| = (2/5) * |P₃| :=
          hsubval_neg r₃ hri3
        have hc2 : (∑ c ∈ ({(fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|) ≤ (2/5) * |P₃| := by
          rw [Finset.sum_singleton]
          simp only
          exact le_of_eq (hsubval_neg r₃ hri3)
        have hc1 := hstep (fun j' => r₃ (i.succAbove j')) _ _ hc2
        calc (∑ c ∈ ({(fun j' => r₃ (i.succAbove j')), (fun j' => -(r₃ (i.succAbove j')))} : Finset (Fin k → ℤ)), |∏ j', cubeWtR (c j')|)
            ≤ _ := hc1
          _ ≤ (4/5) * (0 + 0 + |P₃|) := by
              simp only
              rw [e3p]
              linarith
    · -- survivors: none
      rw [if_neg hri1, if_neg hri2, if_neg hri3]
      refine mass_upper_of_subset _ (∅ : Finset (Fin k → ℤ)) ?_ _ ?_
      · intro c hc
        obtain ⟨hcm, hcv⟩ := Finset.mem_filter.mp hc
        rcases hlift c (hcb_of_mem c hcm) hcv with h|h|h|h|h|h|h
        · rw [hzero_c c h]
          exact Finset.mem_insert_self _ _
        · exact (hkill r₁ hri1 c h).elim
        · exact (hkill_neg r₁ hri1 c h).elim
        · exact (hkill r₂ hri2 c h).elim
        · exact (hkill_neg r₂ hri2 c h).elim
        · exact (hkill r₃ hri3 c h).elim
        · exact (hkill_neg r₃ hri3 c h).elim
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
  set z₁ : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r₁ i = 0)).card with hz₁def
  set z₂ : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r₂ i = 0)).card with hz₂def
  set z₃ : ℕ := (Finset.univ.filter (fun i : Fin (k + 1) => r₃ i = 0)).card with hz₃def
  have hite : ∀ (r : Fin (k + 1) → ℤ) (Pv : ℝ),
      (∑ i : Fin (k + 1), (if r i = 0 then Pv else 0))
        = ((Finset.univ.filter (fun i : Fin (k + 1) => r i = 0)).card : ℝ) * Pv := by
    intro r Pv
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hSbound : (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
      + (4/5) * ((if r₁ i = 0 then |P₁| else 0) + (if r₂ i = 0 then |P₂| else 0)
        + (if r₃ i = 0 then |P₃| else 0))))
      = (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * ((z₁ : ℝ) * |P₁| + (z₂ : ℝ) * |P₂| + (z₃ : ℝ) * |P₃|)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hite r₁ |P₁|, hite r₂ |P₂|, hite r₃ |P₃|, ← hz₁def, ← hz₂def, ← hz₃def]
    push_cast
    ring
  have hz₁le : (z₁ : ℝ) ≤ (k : ℝ) - 1 := by
    rw [hz₁def]
    exact hzcount r₁ ⟨wb1, hwb1⟩ hs1
  have hz₂le : (z₂ : ℝ) ≤ (k : ℝ) - 1 := by
    rw [hz₂def]
    exact hzcount r₂ ⟨wb2, hwb2⟩ hs2
  have hz₃le : (z₃ : ℝ) ≤ (k : ℝ) - 1 := by
    rw [hz₃def]
    exact hzcount r₃ ⟨wb3, hwb3⟩ hs3
  have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hsum_le : (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
      ≤ (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
        + (4/5) * (((k : ℝ) - 1) * (|P₁| + |P₂| + |P₃|))) := by
    calc (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
        (∏ j' : Fin k,
          (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
        ≤ ∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
          + (4/5) * ((if r₁ i = 0 then |P₁| else 0) + (if r₂ i = 0 then |P₂| else 0)
            + (if r₃ i = 0 then |P₃| else 0))) :=
          Finset.sum_le_sum (fun i _ => hMsub_le i)
      _ = (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * ((z₁ : ℝ) * |P₁| + (z₂ : ℝ) * |P₂| + (z₃ : ℝ) * |P₃|)) := hSbound
      _ ≤ (Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * (((k : ℝ) - 1) * (|P₁| + |P₂| + |P₃|))) := by
          have h1 : (z₁ : ℝ) * |P₁| ≤ ((k : ℝ) - 1) * |P₁| :=
            mul_le_mul_of_nonneg_right hz₁le (abs_nonneg _)
          have h2 : (z₂ : ℝ) * |P₂| ≤ ((k : ℝ) - 1) * |P₂| :=
            mul_le_mul_of_nonneg_right hz₂le (abs_nonneg _)
          have h3 : (z₃ : ℝ) * |P₃| ≤ ((k : ℝ) - 1) * |P₃| :=
            mul_le_mul_of_nonneg_right hz₃le (abs_nonneg _)
          nlinarith [hQR]
  calc (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
      * (∑ i : Fin (k + 1), (∑ j ∈ Finset.range Q,
        (∏ j' : Fin k,
          (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3))
      ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * (((k : ℝ) - 1) * (|P₁| + |P₂| + |P₃|)))) :=
        mul_le_mul_of_nonneg_left hsum_le hu30
    _ ≤ (1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3
        * ((Q : ℝ) * (((k : ℝ) + 1) * (5/2 : ℝ) ^ k
          + (4/5) * (((k : ℝ) - 1) * ((3/4) * (5/2 : ℝ) ^ k)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hu30
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
        have := mul_le_mul_of_nonneg_left hcap hkm1
        nlinarith [this]
    _ = ((1 - Real.cos (2 * π * (1 / ((k : ℝ) + 2)))) ^ 3 * (8 * (k : ℝ) + 2))
        * ((Q : ℝ) * (5/2 : ℝ) ^ k / 5) := by ring
    _ < 5 * ((Q : ℝ) * (5/2 : ℝ) ^ k / 5) := by
        refine mul_lt_mul_of_pos_right (cube_triple_close hk) ?_
        positivity
    _ = (Q : ℝ) * (5/2 : ℝ) ^ k := by ring
    _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) - 2 * (|P₁| + |P₂| + |P₃|)) := by
        have hp : (5/2 : ℝ) ^ (k + 1) = (5/2) * (5/2 : ℝ) ^ k := by
          rw [pow_succ]; ring
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
        rw [hp]
        linarith [hcap]
    _ ≤ _ := hMlow

/-- **The dense-web residual**: the shard families whose vanishing set is
neither trivial, nor one line, nor two lines, nor an escaping triple —
a parallelogram triple or four or more directions. -/
def CubeDenseWebResidual : Prop :=
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
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **The three-direction core shrinks to the dense web**: escaping triples
go to the triple floor. -/
theorem cubeThreeDir_of_denseWeb (h : CubeDenseWebResidual) : CubeThreeDirResidual := by
  intro k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin hpair
  by_cases htrip : ∃ r₁ r₂ r₃ : Fin (k + 1) → ℤ,
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
      (∃ w, r₂ w - r₃ w ≤ -4 ∨ 4 ≤ r₂ w - r₃ w)
  · obtain ⟨r₁, r₂, r₃, h13, h23, h33, h10, h20, h30, hrel1, hrel2, hrel3, hclass,
      e12p, e12m, e13p, e13m, e23p, e23m⟩ := htrip
    exact torsion_triple_cube_floor hk4 v hv hSF r₁ r₂ r₃ h13 h23 h33 h10 h20 h30
      hrel1 hrel2 hrel3 hclass e12p e12m e13p e13m e23p e23m
  · exact h k hk4 hk7 v hv hSF hAT hST hdense hdiss hlin hpair htrip

/-- The dense-torsion shard reduces to the dense-web core. -/
theorem denseTorsion_of_denseWeb (h : CubeDenseWebResidual) : DenseTorsionResidual :=
  denseTorsion_of_cubeThreeDir (cubeThreeDir_of_denseWeb h)

end LRSpectrumFull
