/-
# Triple normalization: `D ![a,b,c] ≤ 3/14` unless `(a,b,c)` is `(1,2,3)`-shaped

The normalization glue for `WallCore`: a full-support integer triple whose sorted
primitive is not `(1,2,3)` has `D ≤ 3/14`. Cases: two equal absolute values reduce to a
2-runner (`≤ 1/6`); three distinct reduce — via abs, sort, and primitive scaling — to the
n=3 classification `D_le_of_not_123`. NO `sorry`, NO `native_decide`.
-/
import LRSpectrumFull.WeylNormalize
import LRSpectrumFull.KravitzPieceA
import LRSpectrumFull.TwoRunnerBound
import LRSpectrumFull.SpectrumSymmetry

namespace LRSpectrumFull

/-- Duplicating the first runner of a *pair* does not change the gap. -/
theorem gap_dup3 (a b : ℤ) (t : ℝ) : gap ![a, a, b] t = gap ![a, b] t := by
  apply le_antisymm
  · apply le_gap; intro j; fin_cases j
    · exact gap_le ![a, a, b] t 0
    · exact gap_le ![a, a, b] t 2
  · apply le_gap; intro i; fin_cases i
    · exact gap_le ![a, b] t 0
    · exact gap_le ![a, b] t 0
    · exact gap_le ![a, b] t 1

/-- `D ![a,a,b] = D ![a,b]` — the duplicated runner is redundant. -/
theorem D_dup3 (a b : ℤ) : D ![a, a, b] = D ![a, b] := by
  have hg : gap ![a, a, b] = gap ![a, b] := funext (gap_dup3 a b)
  unfold D ML; rw [hg]

/-! ## Fin-2 sign normalization and the 2-runner bound -/

theorem D_flip2_0 (a b : ℤ) : D ![-a, b] = D ![a, b] := by
  have h := D_sign_flip ![a, b] 0; simpa using h

theorem D_flip2_1 (a b : ℤ) : D ![a, -b] = D ![a, b] := by
  have h := D_sign_flip ![a, b] 1; simpa using h

/-- `D` of a pair is invariant under componentwise absolute value. -/
theorem D_abs2 (a b : ℤ) : D ![|a|, |b|] = D ![a, b] := by
  rcases abs_choice a with ha | ha <;> rcases abs_choice b with hb | hb <;>
    rw [ha, hb] <;> simp only [D_flip2_0, D_flip2_1]

/-- **2-runner bound.** Any pair of nonzero speeds has `D ≤ 1/6`. -/
theorem D_two_le (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : D ![a, b] ≤ 1 / 6 := by
  rw [← D_abs2 a b, Int.abs_eq_natAbs a, Int.abs_eq_natAbs b]
  set p := a.natAbs with hp
  set q := b.natAbs with hq
  have hp0 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (by simpa [hp] using Int.natAbs_ne_zero.mpr ha)
  have hq0 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (by simpa [hq] using Int.natAbs_ne_zero.mpr hb)
  set g := Nat.gcd p q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left q hp0
  have hdp : g ∣ p := Nat.gcd_dvd_left p q
  have hdq : g ∣ q := Nat.gcd_dvd_right p q
  -- divide out the gcd
  have hpe : p = g * (p / g) := (Nat.mul_div_cancel' hdp).symm
  have hqe : q = g * (q / g) := (Nat.mul_div_cancel' hdq).symm
  have hcop : Nat.Coprime (p / g) (q / g) := Nat.coprime_div_gcd_div_gcd hg0
  have hpg1 : 1 ≤ p / g := Nat.one_le_div_iff hg0 |>.mpr (Nat.le_of_dvd hp0 hdp)
  have hqg1 : 1 ≤ q / g := Nat.one_le_div_iff hg0 |>.mpr (Nat.le_of_dvd hq0 hdq)
  have epe : (p : ℤ) = (g : ℤ) * ((p / g : ℕ) : ℤ) := by rw [← Nat.cast_mul, ← hpe]
  have eqe : (q : ℤ) = (g : ℤ) * ((q / g : ℕ) : ℤ) := by rw [← Nat.cast_mul, ← hqe]
  have hscale : (![(p : ℤ), (q : ℤ)] : Fin 2 → ℤ)
      = (fun i => (g : ℤ) * (![((p / g : ℕ) : ℤ), ((q / g : ℕ) : ℤ)] : Fin 2 → ℤ) i) := by
    funext i
    fin_cases i
    · simp only [Matrix.cons_val_zero]; exact epe
    · simp only [Matrix.cons_val_one, Matrix.head_cons]; exact eqe
  rw [hscale, D_scale _ _ (by exact_mod_cast hg0)]
  exact D_le_one_sixth (p / g) (q / g) hpg1 hqg1 hcop

/-- A triple with a repeated runner is a 2-runner: `D ![a,a,b] ≤ 1/6`. -/
theorem D_aab_le (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : D ![a, a, b] ≤ 1 / 6 := by
  rw [D_dup3]; exact D_two_le a b ha hb

/-! ## The strict-distinct case via the n=3 classification -/

/-- **Strict-distinct normalization.** A sorted triple `0 < x < y < z` not of the form
`(x, 2x, 3x)` has `D ≤ 3/14`. (The excluded shape is exactly the scaled `(1,2,3)`.) -/
theorem D_sorted_strict_le (x y z : ℤ) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hne : ¬ (y = 2 * x ∧ z = 3 * x)) : D ![x, y, z] ≤ 3 / 14 := by
  set X := x.toNat with hXd
  set Y := y.toNat with hYd
  set Z := z.toNat with hZd
  have hxc : (X : ℤ) = x := Int.toNat_of_nonneg hx.le
  have hyc : (Y : ℤ) = y := Int.toNat_of_nonneg (by linarith)
  have hzc : (Z : ℤ) = z := Int.toNat_of_nonneg (by linarith)
  set H := Nat.gcd Y Z with hHd
  set G := Nat.gcd X H with hGd
  have hX0 : 0 < X := by have := hx; rw [← hxc] at this; exact_mod_cast this
  have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ hX0
  have hdX : G ∣ X := Nat.gcd_dvd_left _ _
  have hdH : G ∣ H := Nat.gcd_dvd_right _ _
  have hdY : G ∣ Y := hdH.trans (Nat.gcd_dvd_left _ _)
  have hdZ : G ∣ Z := hdH.trans (Nat.gcd_dvd_right _ _)
  set p := X / G with hpd
  set q := Y / G with hqd
  set r := Z / G with hrd
  have ex : x = (G : ℤ) * (p : ℤ) := by
    rw [← hxc, hpd, ← Nat.cast_mul, Nat.mul_div_cancel' hdX]
  have ey : y = (G : ℤ) * (q : ℤ) := by
    rw [← hyc, hqd, ← Nat.cast_mul, Nat.mul_div_cancel' hdY]
  have ez : z = (G : ℤ) * (r : ℤ) := by
    rw [← hzc, hrd, ← Nat.cast_mul, Nat.mul_div_cancel' hdZ]
  have hGc : (0 : ℤ) < (G : ℤ) := by exact_mod_cast hG0
  have hpq : (p : ℤ) < q := by
    have : (G : ℤ) * p < (G : ℤ) * q := by rw [← ex, ← ey]; exact hxy
    exact lt_of_mul_lt_mul_left this hGc.le
  have hqr : (q : ℤ) < r := by
    have : (G : ℤ) * q < (G : ℤ) * r := by rw [← ey, ← ez]; exact hyz
    exact lt_of_mul_lt_mul_left this hGc.le
  have hp0 : (0 : ℤ) < p := by
    have : (G : ℤ) * 0 < (G : ℤ) * p := by rw [mul_zero, ← ex]; exact hx
    exact lt_of_mul_lt_mul_left this hGc.le
  -- triple primitivity: gcd p (gcd q r) = 1
  have hqrg : Nat.gcd q r = H / G := by
    have e1 : Nat.gcd q r * G = H := by
      rw [← Nat.gcd_mul_right, hqd, hrd, Nat.div_mul_cancel hdY, Nat.div_mul_cancel hdZ]
    rw [← e1, Nat.mul_div_cancel _ hG0]
  have hcop3 : Nat.gcd p (Nat.gcd q r) = 1 := by
    rw [hqrg, hpd]; exact Nat.coprime_div_gcd_div_gcd hG0
  have hcop3' : Nat.gcd q (Nat.gcd p r) = 1 := by
    rw [← Nat.gcd_assoc, Nat.gcd_comm q p, Nat.gcd_assoc]; exact hcop3
  -- rescale to the primitive triple
  have hscale3 : (![x, y, z] : Fin 3 → ℤ)
      = (fun i => (G : ℤ) * (![(p : ℤ), (q : ℤ), (r : ℤ)] : Fin 3 → ℤ) i) := by
    funext i; fin_cases i
    · simp only [Matrix.cons_val_zero]; exact ex
    · simp only [Matrix.cons_val_one, Matrix.head_cons]; exact ey
    · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; exact ez
  rw [hscale3, D_scale _ _ hGc]
  -- coprimality in D_le_of_not_123's form
  have hgqr : Int.gcd (q : ℤ) (r : ℤ) = Nat.gcd q r := by simp [Int.gcd_natCast_natCast]
  have hgpr : Int.gcd (p : ℤ) (r : ℤ) = Nat.gcd p r := by simp [Int.gcd_natCast_natCast]
  have hcA : IsCoprime (p : ℤ) ((Int.gcd (q : ℤ) (r : ℤ) : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one, hgqr]
    simpa [Int.gcd_natCast_natCast] using hcop3
  have hcB : IsCoprime (q : ℤ) ((Int.gcd (p : ℤ) (r : ℤ) : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one, hgpr]
    simpa [Int.gcd_natCast_natCast] using hcop3'
  refine D_le_of_not_123 (p : ℤ) (q : ℤ) (r : ℤ) hp0 hpq hqr hcA hcB ?_
  rintro ⟨hp1, hq2, hr3⟩
  apply hne
  refine ⟨?_, ?_⟩
  · rw [ey, ex, hq2, hp1]; ring
  · rw [ez, ex, hr3, hp1]; ring

/-- **Sorted normalization.** A sorted positive triple `0 < x ≤ y ≤ z` not of the form
`(x, 2x, 3x)` has `D ≤ 3/14`. Combines the 2-runner bound (`x = y` or `y = z`) with the
strict-distinct classification. -/
theorem D_sorted_le (x y z : ℤ) (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hne : ¬ (y = 2 * x ∧ z = 3 * x)) : D ![x, y, z] ≤ 3 / 14 := by
  rcases eq_or_lt_of_le hxy with hxye | hxyl
  · -- x = y: `![x,x,z]`
    subst hxye
    exact le_trans (D_aab_le x z hx.ne' (by linarith)) (by norm_num)
  · rcases eq_or_lt_of_le hyz with hyze | hyzl
    · -- y = z: reorder to `![y,y,x]`
      subst hyze
      have hperm : D ![x, y, y] = D ![y, y, x] := by
        have he : (![y, y, x] : Fin 3 → ℤ) ∘ ⇑(Equiv.swap (0 : Fin 3) 2) = ![x, y, y] := by
          funext i; fin_cases i <;> rfl
        rw [← he, D_perm]
      rw [hperm]
      exact le_trans (D_aab_le y x (by linarith) hx.ne') (by norm_num)
    · -- strict 0 < x < y < z
      exact D_sorted_strict_le x y z hx hxyl hyzl hne

/-! ## Dropping a redundant (duplicate-up-to-sign) coordinate -/

/-- If coordinate `i` of `w` equals `±` coordinate `j`, the gap is unchanged by dropping
coordinate `i` (it is redundant). -/
theorem gap_drop (w : Fin 4 → ℤ) (i j : Fin 4) (hij : i ≠ j)
    (h : w i = w j ∨ w i = -w j) (t : ℝ) :
    gap w t = gap (fun b => w (Fin.succAbove i b)) t := by
  have hnid : nearestIntDist ((w i : ℝ) * t) = nearestIntDist ((w j : ℝ) * t) := by
    rcases h with h | h
    · rw [h]
    · rw [h]; push_cast; rw [neg_mul, nearestIntDist_neg]
  apply le_antisymm
  · apply le_gap; intro b; exact gap_le w t (Fin.succAbove i b)
  · apply le_gap; intro a
    rcases eq_or_ne a i with hai | ha
    · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hij.symm
      rw [hai, hnid, ← hb]; exact gap_le (fun b => w (Fin.succAbove i b)) t b
    · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq ha
      rw [← hb]; exact gap_le (fun b => w (Fin.succAbove i b)) t b

/-- `D` is unchanged by dropping a duplicate-up-to-sign coordinate. -/
theorem D_drop (w : Fin 4 → ℤ) (i j : Fin 4) (hij : i ≠ j)
    (h : w i = w j ∨ w i = -w j) :
    D w = D (fun b => w (Fin.succAbove i b)) := by
  unfold D ML; rw [funext (gap_drop w i j hij h)]

/-! ## The general triple normalization -/

/-- A triple is **`(1,2,3)`-shaped** iff its multiset of absolute values is `{g,2g,3g}`
for some `g > 0`. -/
def Shaped123 (a b c : ℤ) : Prop :=
  ∃ g : ℤ, 0 < g ∧ ({|a|, |b|, |c|} : Multiset ℤ) = {g, 2 * g, 3 * g}

/-- **General triple normalization.** Any full-support integer triple that is not
`(1,2,3)`-shaped has `D ≤ 3/14`. (Abs + sort reduce it to `D_sorted_le`.) -/
theorem D_triple_le (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hne : ¬ Shaped123 a b c) : D ![a, b, c] ≤ 3 / 14 := by
  have hA : 0 < |a| := abs_pos.mpr ha
  have hB : 0 < |b| := abs_pos.mpr hb
  have hC : 0 < |c| := abs_pos.mpr hc
  rw [← D_abs3 a b c]
  rcases le_total |a| |b| with hab | hab
  · rcases le_total |b| |c| with hbc | hbc
    · refine D_sorted_le |a| |b| |c| hA hab hbc (fun h => hne ⟨|a|, hA, ?_⟩)
      obtain ⟨h2, h3⟩ := h; rw [h2, h3]
    · rcases le_total |a| |c| with hac | hac
      · rw [← D_swap12]
        refine D_sorted_le |a| |c| |b| hA hac hbc (fun h => hne ⟨|a|, hA, ?_⟩)
        obtain ⟨h2, h3⟩ := h; rw [h2, h3]
        ext n; simp only [Multiset.count_cons, Multiset.count_singleton, Multiset.insert_eq_cons]; ring
      · rw [← D_swap02, D_swap12]
        refine D_sorted_le |c| |a| |b| hC hac hab (fun h => hne ⟨|c|, hC, ?_⟩)
        obtain ⟨h2, h3⟩ := h; rw [h2, h3]
        ext n; simp only [Multiset.count_cons, Multiset.count_singleton, Multiset.insert_eq_cons]; ring
  · rcases le_total |a| |c| with hac | hac
    · rw [← D_swap01]
      refine D_sorted_le |b| |a| |c| hB hab hac (fun h => hne ⟨|b|, hB, ?_⟩)
      obtain ⟨h2, h3⟩ := h; rw [h2, h3]
      ext n; simp only [Multiset.count_cons, Multiset.count_singleton, Multiset.insert_eq_cons]; ring
    · rcases le_total |b| |c| with hbc | hbc
      · rw [← D_swap01, D_swap12]
        refine D_sorted_le |b| |c| |a| hB hbc hac (fun h => hne ⟨|b|, hB, ?_⟩)
        obtain ⟨h2, h3⟩ := h; rw [h2, h3]
        ext n; simp only [Multiset.count_cons, Multiset.count_singleton, Multiset.insert_eq_cons]; ring
      · rw [← D_swap02]
        refine D_sorted_le |c| |b| |a| hC hbc hab (fun h => hne ⟨|c|, hC, ?_⟩)
        obtain ⟨h2, h3⟩ := h; rw [h2, h3]
        ext n; simp only [Multiset.count_cons, Multiset.count_singleton, Multiset.insert_eq_cons]; ring

end LRSpectrumFull
