/-
# R7-partial, module A: three free runners in one class (pattern (A)), general modulus `q`

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem R7-partial" case (A), with the two
repairs of F4_CHECKS: the spread is the LIFTED real spread (the lemma `cluster_div` of `RFiveCluster` is stated for the
reals `r_i = D_i x + σ_i - m_i` with fixed integers `m_i`; its conclusion is `|r_b|, |r_c|, |r_b - r_c| ≤ 2/5`), and
the constant is `2/5` as stated (not `7/20`).  The three window centres are then pairwise within `2q/5 ≤ 3q/5 - 1`
(needs `q ≥ 5`), so all bad integers lie in one window `(N, N + q)` (`window_gap3`).

The case analysis is that of `RFiveCase.case3R` with modulus `5` replaced by `q`: if Lemma 6 fails on none of the
three pairs, an exactly coinciding pair plus counting (`exact_pair`); otherwise all three `D` divide `w` and
`cluster_div` applies.  Hypothesis `hq : 2 (⌊(2q-1)/5⌋ + 1) < q` holds for `q = 7` and all `q ≥ 9`.

* `r7CaseA` : slow runner `(w, φ_d)` and three coprime runners `a, b, c` with `v_a - ε_b v_b = q D_b`,
            `v_a - ε_c v_c = q D_c`, `D_b, D_c ≠ 0`, `D_b ≠ D_c`.
-/
import LRSpectrumFull.RSevenCore
import LRSpectrumFull.RFiveCase

namespace LRSpectrumFull

lemma r7CaseA (q : ℕ) (hq : 2 * ((2 * q - 1) / 5 + 1) < q) (hq5 : 5 ≤ q) (w : ℕ) (hw : 1 ≤ w)
    (va vb vc : ℕ) (φa φb φc φd : ℝ) (εb εc : ℤ)
    (hεb : εb = 1 ∨ εb = -1) (hεc : εc = 1 ∨ εc = -1)
    (ha : Nat.Coprime va q) (hb : Nat.Coprime vb q) (hc : Nat.Coprime vc q)
    (Db Dc : ℤ) (hDb : (va : ℤ) - εb * vb = q * Db) (hDc : (va : ℤ) - εc * vc = q * Dc)
    (hDb0 : Db ≠ 0) (hDc0 : Dc ≠ 0) (hDne : Db ≠ Dc) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) ∧ ∃ j : ℤ,
      GoodR va φa (((j : ℝ) + x) / q) ∧ GoodR vb φb (((j : ℝ) + x) / q) ∧
        GoodR vc φc (((j : ℝ) + x) / q) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq5R : (5 : ℝ) ≤ q := by exact_mod_cast hq5
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq0
  by_cases f1 : L6 Db w (φa - εb * φb) φd
  · by_cases f2 : L6 Dc w (φa - εc * φc) φd
    · by_cases f3 : L6 (Db - Dc) w ((φa - εb * φb) - (φa - εc * φc)) φd
      · -- all three `D` divide `w`: cluster lemma, one window for the three centres
        obtain ⟨t1, ht1, -⟩ := f1
        obtain ⟨t2, ht2, -⟩ := f2
        obtain ⟨t3, ht3, -⟩ := f3
        obtain ⟨x, mb, mc, hfar, r2, r3, r4⟩ := cluster_div w hw Db Dc (φa - εb * φb)
          (φa - εc * φc) φd hDb0 hDc0 hDne ⟨t1, ht1⟩ ⟨t2, ht2⟩ ⟨t3, ht3⟩
        obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr ha
        have cb := centre_diff q va vb φa φb x εb Db hDb mb
        have cc := centre_diff q va vc φa φc x εc Dc hDc mc
        obtain ⟨ua, hua⟩ : ∃ u : ℝ, u = -((va : ℝ) * x + q * φa) := ⟨_, rfl⟩
        obtain ⟨ub, hub⟩ : ∃ u : ℝ, u = -((εb : ℝ) * ((vb : ℝ) * x + q * φb)) - q * (mb : ℝ) :=
          ⟨_, rfl⟩
        obtain ⟨uc, huc⟩ : ∃ u : ℝ, u = -((εc : ℝ) * ((vc : ℝ) * x + q * φc)) - q * (mc : ℝ) :=
          ⟨_, rfl⟩
        have eb : ub - ua = q * ((Db : ℝ) * x + (φa - εb * φb) - mb) := by rw [hub, hua]; exact cb
        have ec : uc - ua = q * ((Dc : ℝ) * x + (φa - εc * φc) - mc) := by rw [huc, hua]; exact cc
        have key : ∀ r : ℝ, |r| ≤ 2 / 5 → |(q : ℝ) * r| ≤ (3 / 5 : ℝ) * q - 1 := by
          intro r hr
          rw [abs_mul, abs_of_pos hqR]
          have := mul_le_mul_of_nonneg_left hr hqR.le
          linarith
        have s12 : |ua - ub| ≤ (3 / 5 : ℝ) * q - 1 := by rw [abs_sub_comm, eb]; exact key _ r2
        have s13 : |ua - uc| ≤ (3 / 5 : ℝ) * q - 1 := by rw [abs_sub_comm, ec]; exact key _ r3
        have s23 : |ub - uc| ≤ (3 / 5 : ℝ) * q - 1 := by
          have e : ub - uc = q * (((Db : ℝ) * x + (φa - εb * φb) - mb)
              - ((Dc : ℝ) * x + (φa - εc * φc) - mc)) := by linear_combination eb - ec
          rw [e]
          exact key _ r4
        obtain ⟨N, hN⟩ := window_gap3 q ua ub uc s12 s13 s23
        have hNa : ∀ m : ℤ, |(m : ℝ) - ua| < (q : ℝ) / 5 → ¬ (q : ℤ) ∣ m - N := fun m hm =>
          win_ne_dvd q N m hqZ (hN m (Or.inl hm)).1 (hN m (Or.inl hm)).2
        have hNb : ∀ m : ℤ, |(m : ℝ) - ub| < (q : ℝ) / 5 → ¬ (q : ℤ) ∣ m - N := fun m hm =>
          win_ne_dvd q N m hqZ (hN m (Or.inr (Or.inl hm))).1 (hN m (Or.inr (Or.inl hm))).2
        have hNc : ∀ m : ℤ, |(m : ℝ) - uc| < (q : ℝ) / 5 → ¬ (q : ℤ) ∣ m - N := fun m hm =>
          win_ne_dvd q N m hqZ (hN m (Or.inr (Or.inr hm))).1 (hN m (Or.inr (Or.inr hm))).2
        refine ⟨x, hfar, N * A, ?_, ?_, ?_⟩
        · exact good_of_win q hq0 va va A B hAB 1 0 (Or.inl rfl) (by ring) φa x 0 N ua
            (by rw [hua]; push_cast; ring) hNa
        · exact good_of_win q hq0 va vb A B hAB εb Db hεb hDb φb x mb N ub hub hNb
        · exact good_of_win q hq0 va vc A B hAB εc Dc hεc hDc φc x mc N uc huc hNc
      · -- the pair `(b, c)` coincides exactly
        obtain ⟨x, m, hx, hfar⟩ := exists_exactR (Db - Dc) (sub_ne_zero.mpr hDne) w
          ((φa - εb * φb) - (φa - εc * φc)) φd f3
        have hε' : εb * εc = 1 ∨ εb * εc = -1 := by
          rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> simp
        have hD' : (vb : ℤ) - (εb * εc) * vc = q * (εb * (Dc - Db)) := by
          rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;>
            first | linear_combination hDc - hDb | linear_combination hDb - hDc
        have hM' : ((εb * (Dc - Db) : ℤ) : ℝ) * x + (φb - ((εb * εc : ℤ) : ℝ) * φc)
            = ((-εb * m : ℤ) : ℝ) := by
          rcases hεb with rfl | rfl <;> rcases hεc with rfl | rfl <;> push_cast at hx ⊢ <;>
            first | linear_combination (-1) * hx | linear_combination hx
        obtain ⟨j, jb, jc, ja⟩ := exact_pair q hq vb vc va hb ha φb φc φa x (εb * εc)
          (εb * (Dc - Db)) (-εb * m) hε' hD' hM'
        exact ⟨x, hfar, j, ja, jb, jc⟩
    · -- the pair `(a, c)` coincides exactly
      obtain ⟨x, m, hx, hfar⟩ := exists_exactR Dc hDc0 w (φa - εc * φc) φd f2
      obtain ⟨j, ja, jc, jb⟩ := exact_pair q hq va vc vb ha hb φa φc φb x εc Dc m hεc hDc hx
      exact ⟨x, hfar, j, ja, jb, jc⟩
  · -- the pair `(a, b)` coincides exactly
    obtain ⟨x, m, hx, hfar⟩ := exists_exactR Db hDb0 w (φa - εb * φb) φd f1
    obtain ⟨j, ja, jb, jc⟩ := exact_pair q hq va vb vc ha hc φa φb φc x εb Db m hεb hDb hx
    exact ⟨x, hfar, j, ja, jb, jc⟩

end LRSpectrumFull
