/-
# R7-partial, module B: two free runners in one class, the third in another class (pattern (B)), modulus `q = 7`

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem R7-partial" case (B).
Base runner `b`, same-class runner `c` (`v_b - ε v_c = 7 D`), third runner `a` with `v_a ≡ μ v_b (mod 7)`, `μ ≠ ±1`.
The offset `x` makes the slow runner good and `r = D x + (φ_b - ε φ_c) - n` small:

* `ρ = 1/10` (`D ∤ w` or `2|D| ≤ w`, `lemma4R_tight`, RQG24, whose statement contains the sharper bound),
* `ρ = 1/5`  (`|D| = w`, `lemma4R`).

The bad integers of `b, c` (coordinate `z = v_b j`) then lie in `M < m < M + L` with `L = 5` resp. `6` (`bc_window`);
the free residues are `M + L, ..., M + 7`.  The runner `a` is bad at `z` only if `μ z` is one of three consecutive
residues; for `μ ≠ ±1` (three free residues, `ap3`) resp. `μ = ±3` (two free residues, `ap2`) one free `z` is good for `a`.
Both finite statements are kernel `decide` over `ZMod 7`.
-/
import LRSpectrumFull.RSevenCore
import LRSpectrumFull.RFiveCluster

namespace LRSpectrumFull

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
lemma ap3 : ∀ μ z k : ZMod 7, μ ≠ 0 → μ ≠ 1 → μ ≠ -1 →
    (μ * z ≠ k + 1 ∧ μ * z ≠ k + 2 ∧ μ * z ≠ k + 3) ∨
    (μ * (z + 1) ≠ k + 1 ∧ μ * (z + 1) ≠ k + 2 ∧ μ * (z + 1) ≠ k + 3) ∨
    (μ * (z + 2) ≠ k + 1 ∧ μ * (z + 2) ≠ k + 2 ∧ μ * (z + 2) ≠ k + 3) := by
  decide

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
lemma ap2 : ∀ μ z k : ZMod 7, (μ = 3 ∨ μ = -3) →
    (μ * z ≠ k + 1 ∧ μ * z ≠ k + 2 ∧ μ * z ≠ k + 3) ∨
    (μ * (z + 1) ≠ k + 1 ∧ μ * (z + 1) ≠ k + 2 ∧ μ * (z + 1) ≠ k + 3) := by
  decide

/-- the bad integers of two centres at distance `≤ 7 ρ` lie in a window `M < m < M + L` -/
lemma bc_window (q : ℕ) (hq7 : (q : ℝ) = 7) (ub uc ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℤ)
    (hL : (19 : ℝ) / 5 + 7 * ρ ≤ L) (hd : |uc - ub| ≤ 7 * ρ) :
    ∃ M : ℤ, ∀ m : ℤ, (|(m : ℝ) - ub| < (q : ℝ) / 5 ∨ |(m : ℝ) - uc| < (q : ℝ) / 5) →
      M < m ∧ m < M + L := by
  obtain ⟨lo, l1, l2, hmin⟩ : ∃ lo : ℝ, lo ≤ ub ∧ lo ≤ uc ∧ (lo = ub ∨ lo = uc) := by
    rcases le_total ub uc with h | h
    · exact ⟨ub, le_rfl, h, Or.inl rfl⟩
    · exact ⟨uc, h, le_rfl, Or.inr rfl⟩
  obtain ⟨a1, a2⟩ := abs_le.mp hd
  have hup : ub ≤ lo + 7 * ρ ∧ uc ≤ lo + 7 * ρ := by
    rcases hmin with h | h <;> rw [h] <;> constructor <;> linarith
  have f1 := Int.floor_le (lo - (q : ℝ) / 5)
  have f2 := Int.lt_floor_add_one (lo - (q : ℝ) / 5)
  refine ⟨⌊lo - (q : ℝ) / 5⌋, fun m hm => ?_⟩
  have hm' : lo - (q : ℝ) / 5 < m ∧ (m : ℝ) < lo + 7 * ρ + (q : ℝ) / 5 := by
    rcases hm with hm | hm
    · obtain ⟨c1, c2⟩ := abs_lt.mp hm
      constructor <;> linarith [hup.1]
    · obtain ⟨c1, c2⟩ := abs_lt.mp hm
      constructor <;> linarith [hup.2]
  constructor
  · have : ((⌊lo - (q : ℝ) / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
    exact_mod_cast this
  · have : (m : ℝ) < ((⌊lo - (q : ℝ) / 5⌋ : ℤ) : ℝ) + L := by linarith [hm'.2]
    exact_mod_cast this

/-- `b` and `c` are good at `j = N A` for every `N` in the free range `M + L ≤ N ≤ M + 7` -/
lemma bc_good (q : ℕ) (hq7 : q = 7) (vb vc : ℕ) (A B : ℤ) (hAB : A * (vb : ℤ) + B * q = 1)
    (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (vb : ℤ) - ε * vc = q * D) (φb φc x : ℝ) (n : ℤ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℤ) (hL : (19 : ℝ) / 5 + 7 * ρ ≤ L)
    (hr : |(D : ℝ) * x + (φb - ε * φc) - n| ≤ ρ) :
    ∃ M : ℤ, ∀ N : ℤ, M + L ≤ N → N ≤ M + 7 →
      GoodR vb φb ((((N * A : ℤ) : ℝ) + x) / q) ∧ GoodR vc φc ((((N * A : ℤ) : ℝ) + x) / q) := by
  have hq0 : 0 < q := by omega
  have hqR : (q : ℝ) = 7 := by rw [hq7]; norm_num
  have hqZ : (q : ℤ) = 7 := by exact_mod_cast hq7
  have hqpos : (0 : ℝ) < q := by rw [hqR]; norm_num
  obtain ⟨ub, hub⟩ : ∃ u : ℝ, u = -((vb : ℝ) * x + q * φb) := ⟨_, rfl⟩
  obtain ⟨uc, huc⟩ : ∃ u : ℝ, u = -((ε : ℝ) * ((vc : ℝ) * x + q * φc)) - q * (n : ℝ) := ⟨_, rfl⟩
  have ec : uc - ub = q * ((D : ℝ) * x + (φb - ε * φc) - n) := by
    rw [huc, hub]; exact centre_diff q vb vc φb φc x ε D hD n
  have hd : |uc - ub| ≤ 7 * ρ := by
    rw [ec, abs_mul, abs_of_pos hqpos, hqR]
    have := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 7)
    linarith
  obtain ⟨M, hM⟩ := bc_window q hqR ub uc ρ hρ L hL hd
  refine ⟨M, fun N hN1 hN2 => ?_⟩
  have hnd : ∀ u : ℝ, (∀ m : ℤ, |(m : ℝ) - u| < (q : ℝ) / 5 → M < m ∧ m < M + L) →
      ∀ m : ℤ, |(m : ℝ) - u| < (q : ℝ) / 5 → ¬ (q : ℤ) ∣ m - N := by
    intro u hu m hm h
    have h1 := hu m hm
    rw [hqZ] at h
    omega
  constructor
  · exact good_of_win q hq0 vb vb A B hAB 1 0 (Or.inl rfl) (by ring) φb x 0 N ub
      (by rw [hub]; push_cast; ring) (hnd ub (fun m hm => hM m (Or.inl hm)))
  · exact good_of_win q hq0 vb vc A B hAB ε D hε hD φc x n N uc huc
      (hnd uc (fun m hm => hM m (Or.inr hm)))

/-- the third runner `a` (`v_a ≡ μ v_b`) is good at `j = N A` unless `μ N` is one of three consecutive residues -/
lemma a_good (q : ℕ) (hq7 : q = 7) (va vb : ℕ) (A B : ℤ) (hAB : A * (vb : ℤ) + B * q = 1)
    (μ : ZMod 7) (hμ : (va : ZMod 7) = μ * (vb : ZMod 7)) (φa x : ℝ) (N k : ℤ)
    (hk : k = ⌊-((va : ℝ) * x + q * φa) - (q : ℝ) / 5⌋)
    (hne : μ * (N : ZMod 7) ≠ (k : ZMod 7) + 1 ∧ μ * (N : ZMod 7) ≠ (k : ZMod 7) + 2 ∧
      μ * (N : ZMod 7) ≠ (k : ZMod 7) + 3) :
    GoodR va φa ((((N * A : ℤ) : ℝ) + x) / q) := by
  have hq0 : 0 < q := by omega
  have hqR : (q : ℝ) = 7 := by rw [hq7]; norm_num
  by_contra hbad
  unfold GoodR at hbad
  obtain ⟨n2, hn2⟩ := exists_near_of_not_good hbad
  have h2 := near_to_int q hq0 va φa x (N * A) n2 hn2
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, m' = (va : ℤ) * (N * A) - q * n2 := ⟨_, rfl⟩
  rw [← hm'] at h2
  obtain ⟨h21, h22⟩ := abs_lt.mp h2
  have f1 : (k : ℝ) ≤ -((va : ℝ) * x + q * φa) - (q : ℝ) / 5 := by rw [hk]; exact Int.floor_le _
  have f2 : -((va : ℝ) * x + q * φa) - (q : ℝ) / 5 < (k : ℝ) + 1 := by
    rw [hk]; exact Int.lt_floor_add_one _
  have i1 : k < m' := by
    have : (k : ℝ) < m' := by linarith
    exact_mod_cast this
  have i2 : m' < k + 4 := by
    have : (m' : ℝ) < k + 4 := by linarith
    exact_mod_cast this
  have h7 : ((q : ℕ) : ZMod 7) = 0 := by rw [hq7]; exact ZMod.natCast_self 7
  have hA : (A : ZMod 7) * (vb : ZMod 7) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 7) hAB
    push_cast at this
    rw [h7, mul_zero, add_zero] at this
    exact this
  have hmod : (m' : ZMod 7) = μ * (N : ZMod 7) := by
    rw [hm']
    push_cast
    rw [h7, zero_mul, sub_zero, hμ]
    calc μ * (vb : ZMod 7) * ((N : ZMod 7) * (A : ZMod 7))
        = μ * (N : ZMod 7) * ((A : ZMod 7) * (vb : ZMod 7)) := by ring
      _ = μ * (N : ZMod 7) := by rw [hA, mul_one]
  have hcases : m' = k + 1 ∨ m' = k + 2 ∨ m' = k + 3 := by omega
  rcases hcases with h | h | h
  · exact hne.1 (by rw [← hmod, h]; push_cast; ring)
  · exact hne.2.1 (by rw [← hmod, h]; push_cast; ring)
  · exact hne.2.2 (by rw [← hmod, h]; push_cast; ring)

lemma r7CaseB (q : ℕ) (hq7 : q = 7) (w : ℕ) (hw : 1 ≤ w) (vb vc va : ℕ) (φb φc φa φd : ℝ)
    (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hb : Nat.Coprime vb q) (hD : (vb : ℤ) - ε * vc = q * D)
    (hD0 : D ≠ 0) (μ : ZMod 7) (hμ : (va : ZMod 7) = μ * (vb : ZMod 7)) (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hμ2 : μ ≠ -1) (hres : D.natAbs = w → μ = 3 ∨ μ = -3) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ ∃ j : ℤ,
      GoodR vb φb (((j : ℝ) + x) / q) ∧ GoodR vc φc (((j : ℝ) + x) / q) ∧
        GoodR va φa (((j : ℝ) + x) / q) := by
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hb
  by_cases hcase : ¬ D ∣ (w : ℤ) ∨ 2 * (D.natAbs : ℤ) ≤ (w : ℤ)
  · obtain ⟨x, m, hm, hfar⟩ := lemma4R_tight D hD0 w hw hcase (φb - ε * φc) φd
    obtain ⟨M, hM⟩ := bc_good q hq7 vb vc A B hAB ε D hε hD φb φc x m (1 / 10) (by norm_num) 5
      (by norm_num) hm
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊-((va : ℝ) * x + q * φa) - (q : ℝ) / 5⌋ := ⟨_, rfl⟩
    rcases ap3 μ ((M + 5 : ℤ) : ZMod 7) (k : ZMod 7) hμ0 hμ1 hμ2 with h | h | h
    · obtain ⟨gb, gc⟩ := hM (M + 5) (by omega) (by omega)
      exact ⟨x, hfar, (M + 5) * A, gb, gc, a_good q hq7 va vb A B hAB μ hμ φa x (M + 5) k hk h⟩
    · obtain ⟨gb, gc⟩ := hM (M + 5 + 1) (by omega) (by omega)
      exact ⟨x, hfar, (M + 5 + 1) * A, gb, gc,
        a_good q hq7 va vb A B hAB μ hμ φa x (M + 5 + 1) k hk (by push_cast at h ⊢; exact h)⟩
    · obtain ⟨gb, gc⟩ := hM (M + 5 + 2) (by omega) (by omega)
      exact ⟨x, hfar, (M + 5 + 2) * A, gb, gc,
        a_good q hq7 va vb A B hAB μ hμ φa x (M + 5 + 2) k hk (by push_cast at h ⊢; exact h)⟩
  · obtain ⟨h1, h2⟩ := not_or.mp hcase
    have hdvd : D ∣ (w : ℤ) := not_not.mp h1
    have hnat : D.natAbs = w := by
      by_contra hne
      have h3 : |D| ≠ (w : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hne
      have h4 := two_abs_le D w (by exact_mod_cast hw) hdvd h3
      rw [Int.abs_eq_natAbs] at h4
      exact h2 h4
    have hμ3 := hres hnat
    obtain ⟨x, m, hm, hfar⟩ := lemma4R D hD0 w hw (φb - ε * φc) φd
    obtain ⟨M, hM⟩ := bc_good q hq7 vb vc A B hAB ε D hε hD φb φc x m (1 / 5) (by norm_num) 6
      (by norm_num) hm
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊-((va : ℝ) * x + q * φa) - (q : ℝ) / 5⌋ := ⟨_, rfl⟩
    rcases ap2 μ ((M + 6 : ℤ) : ZMod 7) (k : ZMod 7) hμ3 with h | h
    · obtain ⟨gb, gc⟩ := hM (M + 6) (by omega) (by omega)
      exact ⟨x, hfar, (M + 6) * A, gb, gc, a_good q hq7 va vb A B hAB μ hμ φa x (M + 6) k hk h⟩
    · obtain ⟨gb, gc⟩ := hM (M + 6 + 1) (by omega) (by omega)
      exact ⟨x, hfar, (M + 6 + 1) * A, gb, gc,
        a_good q hq7 va vb A B hAB μ hμ φa x (M + 6 + 1) k hk (by push_cast at h ⊢; exact h)⟩

end LRSpectrumFull
