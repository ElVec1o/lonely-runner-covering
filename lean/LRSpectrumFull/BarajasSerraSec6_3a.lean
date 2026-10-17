import LRSpectrumFull.BarajasSerraSec6_6

/-!
# E6 session 19: Barajas-Serra Section 6.3 (`|A1| = 3`, `|A2| = |A4| = 1`), part 1

`A1 = {d1, d2, d3}` (class `ρ`), `d4` (class `2ρ`), `d5` (class `4ρ`), all level 0. This module:
the finishing lemmas, the window case (all congruent, Lemma 11 (i), (ii.1) with `h < m`: Lemma 9 in
window form then Lemma 5 at `(2,1,1)`), and the two top cases of Lemma 11 (`h = m`).
* (ii.1), `h = m`: offsets `(0,1,2)`, Lemma 7 on `(d4, d5)` with `X = {2,4}` (always applicable,
  no two consecutive elements), Lemma 5 at `(3,1,1)` outside the exception.
* (ii.2), `h = m`: offsets `(0,1,3)`; the eight bad pairs `(e~34, e~45)` of the paper (`Z7.bad63`;
  `z63hm` shows that these are exactly the failures of every `Lambda_0` shift). Lemma 7 on `(d3, d4)`
  with `X = {2,3,4,5}` unless `e34 ∈ {3,4,5} N/7`; then Lemma 7 (i) on `(d4, d5)` with a set depending
  on `z` when `e45` is below the top, and otherwise the paper's argument with `q(7 d3) = 4 e1 + 2 e2`
  (`carry7`, Lemma 2 at level 1, `m ≥ 2`), `(e~34, e~45) = (z - e1, z' - e2)`, and `Z7.sec63_escape`.
Falsified first: `e6s19/z63.rs` (every finite statement below, controls fire) and `e6s19/lean19.rs`
(`sub`: the 6.3 conclusion, m = 2, 50000825 configurations, 0 failures; `Lambda_0` only: 7042133).
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- the 6.3 finish for a labeled triple `(a, b, c)` of `A1`, `d4 ∈ A2`, `d5 ∈ A4`. -/
theorem finish63 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [a, b, c], ¬ 7 ∣ x ∧ x % 7 = a % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R a) (hr5 : R d5 = 4 * R a) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (K : ZMod 7) (hK : ∀ x ∈ [a, b, c], ok7 ((qq m (μ * x) : ZMod 7) + K))
    (hK4 : ok7 ((qq m (μ * d4) : ZMod 7) + 2 * K)) (hK5 : ok7 ((qq m (μ * d5) : ZMod 7) + 4 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [a, b, c, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have ha := (hd a (by simp)).1
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; exact ha (dvd_zero 7)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hρ : R (μ * a) ≠ 0 := R_ne_zero (Nat.mul_ne_zero hμ0 ha0)
  obtain ⟨lam, hc, hall⟩ := finish_list m hm μ hμ _ hρ
    ([(a, 1), (b, 1), (c, 1), (d4, 2), (d5, 4)])
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨ha, by ring⟩
      · obtain ⟨h7, hcl⟩ := hd b (by simp)
        have hx0 : b ≠ 0 := by intro h; rw [h] at h7; exact h7 (dvd_zero 7)
        refine ⟨h7, ?_⟩
        rw [R_mul_unit hμ hx0, R_mul_unit hμ ha0, R_of_not_dvd h7, R_of_not_dvd ha, hcl]; ring
      · obtain ⟨h7, hcl⟩ := hd c (by simp)
        have hx0 : c ≠ 0 := by intro h; rw [h] at h7; exact h7 (dvd_zero 7)
        refine ⟨h7, ?_⟩
        rw [R_mul_unit hμ hx0, R_mul_unit hμ ha0, R_of_not_dvd h7, R_of_not_dvd ha, hcl]; ring
      · exact ⟨h4, by rw [R_mul_unit hμ h40, R_mul_unit hμ ha0, hr4]; ring⟩
      · exact ⟨h5, by rw [R_mul_unit hμ h50, R_mul_unit hμ ha0, hr5]; ring⟩) K
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · simpa using hK a (by simp)
      · simpa using hK b (by simp)
      · simpa using hK c (by simp)
      · exact hK4
      · exact hK5)
  refine ⟨lam, hc, ?_⟩
  intro x hx
  rcases mem_list5 hx with rfl | rfl | rfl | rfl | rfl
  · exact hall (x, 1) (by simp)
  · exact hall (x, 1) (by simp)
  · exact hall (x, 1) (by simp)
  · exact hall (x, 2) (by simp)
  · exact hall (x, 4) (by simp)

/-- finish from explicit offsets `q(B) = q(C) + β`, `q(A) = q(C) + α`. -/
theorem finish63_off (m : ℕ) (hm : 1 ≤ m) (C B A d4 d5 : ℕ) (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (β α : ZMod 7)
    (hB : (qq m (μ * B) : ZMod 7) = qq m (μ * C) + β) (hA : (qq m (μ * A) : ZMod 7) = qq m (μ * C) + α)
    (hZ : ∃ K, ok7 ((qq m (μ * C) : ZMod 7) + K) ∧ ok7 ((qq m (μ * C) : ZMod 7) + β + K) ∧
      ok7 ((qq m (μ * C) : ZMod 7) + α + K) ∧ ok7 ((qq m (μ * d4) : ZMod 7) + 2 * K) ∧
      ok7 ((qq m (μ * d5) : ZMod 7) + 4 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨K, k0, k1, k2, k4, k5⟩ := hZ
  apply finish63 m hm C B A d4 d5 hd h4 h5 hr4 hr5 μ hμ K
  · intro x hx
    rcases (show x = C ∨ x = B ∨ x = A by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [hB])
    · exact ok7_congr k2 (by rw [hA])
  · exact k4
  · exact k5

/-! ## finite facts (checked first in `e6s19/z63.rs`) -/

theorem z63w : ∀ a g1 g2 p4 p5 : ZMod 7, g1.val < 2 → g2.val < 2 →
    ∃ K, ok7 (a + K) ∧ ok7 (a + g1 + K) ∧ ok7 (a + g2 + K) ∧ ok7 (p4 + 2 * K) ∧ ok7 (p5 + 4 * K) := by
  decide +kernel

theorem z63top1 : ∀ a p4 p5 : ZMod 7, 2 * p4 - p5 ∉ ({2, 4} : Finset (ZMod 7)) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + 1 + K) ∧ ok7 (a + 2 + K) ∧ ok7 (p4 + 2 * K) ∧ ok7 (p5 + 4 * K) := by
  decide +kernel

/-- `h = m`, offsets `(0,1,3)`: the paper's eight bad pairs are exactly the failures. -/
theorem z63hm : ∀ a p4 p5 : ZMod 7, (2 * a - p4, 2 * p4 - p5) ∉ Z7.bad63 →
    ∃ K, ok7 (a + K) ∧ ok7 (a + 1 + K) ∧ ok7 (a + 3 + K) ∧ ok7 (p4 + 2 * K) ∧ ok7 (p5 + 4 * K) := by
  decide +kernel

theorem z63_first : ∀ a b : ZMod 7, a ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) → (a, b) ∉ Z7.bad63 := by
  decide +kernel

theorem z63_z3 : ∀ a b : ZMod 7, (a = 3 ∨ a = 3 - 1) → b ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) →
    (a, b) ∉ Z7.bad63 := by decide +kernel
theorem z63_z4 : ∀ a b : ZMod 7, (a = 4 ∨ a = 4 - 1) → b ∉ ({2, 3, 4} : Finset (ZMod 7)) →
    (a, b) ∉ Z7.bad63 := by decide +kernel
theorem z63_z5 : ∀ a b : ZMod 7, (a = 5 ∨ a = 5 - 1) → b ∉ ({1, 2, 3, 4} : Finset (ZMod 7)) →
    (a, b) ∉ Z7.bad63 := by decide +kernel

theorem ell234' : Z7.ell {2, 3, 4} ≤ 4 := by decide
theorem ell1234 : Z7.ell {1, 2, 3, 4} ≤ 4 := by decide
theorem z7_345 : ∀ z : ZMod 7, z ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) → z - 1 ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) →
    z = 3 ∨ z = 4 ∨ z = 5 := by decide

/-! ## window case -/

theorem win63 (m : ℕ) (hm : 1 ≤ m) (a b c d4 d5 : ℕ) (hd : ∀ x ∈ [c, b, a], ¬ 7 ∣ x ∧ x % 7 = c % 7)
    (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (hr4 : R d4 = 2 * R c) (hr5 : R d5 = 4 * R c) (μ0 : ℕ)
    (hμ0 : Nat.Coprime μ0 7) (hw : Wb m (μ0 * a) (μ0 * b) (μ0 * c)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [c, b, a, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨hA, hB⟩ := hw
  obtain ⟨e1, he1, qa⟩ := carry_le (E_modEq m (μ0 * a) (μ0 * c)) hA
  obtain ⟨e2, he2, qb⟩ := carry_le (E_modEq m (μ0 * b) (μ0 * c)) hB
  obtain ⟨K, k0, k1, k2, k4, k5⟩ := z63w (qq m (μ0 * c)) (e2 : ZMod 7) (e1 : ZMod 7) (qq m (μ0 * d4))
    (qq m (μ0 * d5)) (val_lt_of he2 (by norm_num)) (val_lt_of he1 (by norm_num))
  apply finish63 m hm c b a d4 d5 hd h4 h5 hr4 hr5 μ0 hμ0 K
  · intro x hx
    rcases (show x = c ∨ x = b ∨ x = a by simpa using hx) with rfl | rfl | rfl
    · exact k0
    · exact ok7_congr k1 (by rw [qb])
    · exact ok7_congr k2 (by rw [qa])
  · exact k4
  · exact k5

/-! ## `h = m` -/

/-- (ii.1), `h = m`. -/
theorem top1_63 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = m) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = m)
    (h2 : R (E m A C) = 2 * R (E m B C)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨nB, -, hBm0, hRB⟩ := off_of_top m B C hB.1 hB.2
  obtain ⟨nA, -, hAm0, hRA⟩ := off_of_top m A C hA.1 hA.2
  set w := R (E m B C) with hw
  have hw0 : w ≠ 0 := R_ne_zero hB.1
  obtain ⟨u, hu⟩ := z7_solve w 1 hw0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  set μ := u.val
  have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
  have hμ : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
  have hμ0 := nz_of_cop hμ
  have hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
    scale_top hBm0 (by norm_num) (by push_cast; rw [hμu, hRB, hu])
  have hAm : μ * A ≡ μ * C + 7 ^ m * 2 [MOD 7 ^ (m + 1)] :=
    scale_top hAm0 (by norm_num) (by push_cast; rw [hμu, hRA, h2]; linear_combination 2 * hu)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hr45 : rp 7 (μ * d5) = 2 * rp 7 (μ * d4) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h50, R_mul_unit hμ h40, hr5, hr4]; ring
  obtain ⟨lam, hl, hX⟩ := steer m hm (μ * d4) (μ * d5) (not_dvd_mul hμ h4) (not_dvd_mul hμ h5) hr45
    {2, 4} ell24 (fun z _ _ => z7_nc24 _)
  rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 h40) (Nat.mul_ne_zero hμ0 h50) hr45] at hX
  have hlc := (coprime_of_modEq_one (by norm_num) hl).1
  have hB' := qq_top_eq hBm lam hl
  have hA' := qq_top_eq hAm lam hl
  set μ' := lam * μ with hμ'
  have r : ∀ x, lam * (μ * x) = μ' * x := fun x => by rw [hμ']; ring
  rw [r, r] at hB' hA'
  rw [r, r] at hX
  apply finish63_off m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ' (Nat.Coprime.mul_left hlc hμ) 1 2
    (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring)
  exact z63top1 _ _ _ hX

/-- `q(7y) = 4 e1 + 2 e2` pins the doubling carries of `y` and `2y`. -/
theorem carry7 (m y e1 e2 : ℕ) (he1 : e1 < 2) (he2 : e2 < 2) (h7 : qq m (7 * y) = 4 * e1 + 2 * e2) :
    qq m (2 * y) = (2 * qq m y + e1) % 7 ∧ qq m (4 * y) = (2 * qq m (2 * y) + e2) % 7 := by
  have key : ∀ x, qq m x = x / 7 ^ m % 7 := fun x => by
    unfold qq qarc; rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have hM : 0 < 7 ^ m := by positivity
  set M := 7 ^ m with hMdef
  obtain ⟨Q, r, hr, hy⟩ : ∃ Q r, r < M ∧ y = M * Q + r :=
    ⟨y / M, y % M, Nat.mod_lt _ hM, (Nat.div_add_mod y M).symm⟩
  have hn : ∀ n, n * y / M = n * Q + n * r / M := fun n => by
    rw [hy, show n * (M * Q + r) = n * r + M * (n * Q) by ring, Nat.add_mul_div_left _ _ hM]; ring
  have hyq : y / M = Q := by rw [hy, Nat.mul_add_div hM, Nat.div_eq_of_lt hr, add_zero]
  rw [key, key, key, hn 2, hn 4, hyq]
  rw [key, hn 7] at h7
  have b7 : 7 * r / M < 7 := (Nat.div_lt_iff_lt_mul hM).mpr (by linarith)
  have h7' : 7 * r / M = 4 * e1 + 2 * e2 := by
    clear hn hyq key hy
    generalize 7 * r / M = c7 at h7 b7
    omega
  have l7 := Nat.div_mul_le_self (7 * r) M
  have u7 := Nat.lt_div_mul_add (a := 7 * r) hM
  rw [h7'] at l7 u7
  have l2 := Nat.div_mul_le_self (2 * r) M
  have u2 := Nat.lt_div_mul_add (a := 2 * r) hM
  have l4 := Nat.div_mul_le_self (4 * r) M
  have u4 := Nat.lt_div_mul_add (a := 4 * r) hM
  have b2 : 2 * r / M < 2 := (Nat.div_lt_iff_lt_mul hM).mpr (by linarith)
  have b4 : 4 * r / M < 4 := (Nat.div_lt_iff_lt_mul hM).mpr (by linarith)
  clear hn hyq key hy h7
  generalize 2 * r / M = c2 at *
  generalize 4 * r / M = c4 at *
  generalize 7 * r / M = c7 at *
  interval_cases e1 <;> interval_cases e2 <;> interval_cases c2 <;> interval_cases c4 <;> omega

/-- (ii.2), `h = m`. -/
theorem top2_63 (m : ℕ) (hm : 2 ≤ m) (A B C d4 d5 : ℕ)
    (hd : ∀ x ∈ [C, B, A], ¬ 7 ∣ x ∧ x % 7 = C % 7) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5)
    (hr4 : R d4 = 2 * R C) (hr5 : R d5 = 4 * R C)
    (hB : E m B C ≠ 0 ∧ nu 7 (E m B C) = m) (hA : E m A C ≠ 0 ∧ nu 7 (E m A C) = m)
    (h3 : R (E m A C) = 3 * R (E m B C)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨nB, -, hBm0, hRB⟩ := off_of_top m B C hB.1 hB.2
  obtain ⟨nA, -, hAm0, hRA⟩ := off_of_top m A C hA.1 hA.2
  set w := R (E m B C) with hw
  have hw0 : w ≠ 0 := R_ne_zero hB.1
  obtain ⟨u, hu⟩ := z7_solve w 1 hw0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  set μ := u.val
  have hμu : (μ : ZMod 7) = u := ZMod.natCast_zmod_val u
  have hμ : Nat.Coprime μ 7 := coprime_of_zmod_ne_zero hu0
  have hμ0 := nz_of_cop hμ
  have hBm : μ * B ≡ μ * C + 7 ^ m * 1 [MOD 7 ^ (m + 1)] :=
    scale_top hBm0 (by norm_num) (by push_cast; rw [hμu, hRB, hu])
  have hAm : μ * A ≡ μ * C + 7 ^ m * 3 [MOD 7 ^ (m + 1)] :=
    scale_top hAm0 (by norm_num) (by push_cast; rw [hμu, hRA, h3]; linear_combination 3 * hu)
  have hC := (hd C (by simp)).1
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; exact hC (dvd_zero 7)
  have h40 : d4 ≠ 0 := by intro h; rw [h] at h4; exact h4 (dvd_zero 7)
  have h50 : d5 ≠ 0 := by intro h; rw [h] at h5; exact h5 (dvd_zero 7)
  have hr34 : rp 7 (μ * d4) = 2 * rp 7 (μ * C) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h40, R_mul_unit hμ hC0, hr4]; ring
  have hr45 : rp 7 (μ * d5) = 2 * rp 7 (μ * d4) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ h50, R_mul_unit hμ h40, hr5, hr4]; ring
  -- the final step from a multiplier `lam ≡ 1 [MOD 7]` and a good pair `(e~34, e~45)`
  have fin : ∀ lam, lam ≡ 1 [MOD 7] →
      (2 * (qq m (lam * (μ * C)) : ZMod 7) - qq m (lam * (μ * d4)),
        2 * (qq m (lam * (μ * d4)) : ZMod 7) - qq m (lam * (μ * d5))) ∉ Z7.bad63 →
      ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
    intro lam hl hbad
    have hlc := (coprime_of_modEq_one (by norm_num) hl).1
    have hB' := qq_top_eq hBm lam hl
    have hA' := qq_top_eq hAm lam hl
    set μ' := lam * μ with hμ'
    have r : ∀ x, lam * (μ * x) = μ' * x := fun x => by rw [hμ']; ring
    rw [r, r] at hB' hA'
    rw [r, r, r] at hbad
    apply finish63_off m (by omega) C B A d4 d5 hd h4 h5 hr4 hr5 μ' (Nat.Coprime.mul_left hlc hμ) 1 3
      (by rw [hB']; push_cast; ring) (by rw [hA']; push_cast; ring)
    exact z63hm _ _ _ hbad
  by_cases h345 : ∃ z, (z = 3 ∨ z = 4 ∨ z = 5) ∧ ediff m (μ * C) (μ * d4) = 7 ^ m * z
  · obtain ⟨z, hz, hze⟩ := h345
    have hz7 : z < 7 := by omega
    by_cases hlow : ediff m (μ * d4) (μ * d5) ≠ 0 ∧ nu 7 (ediff m (μ * d4) (μ * d5)) < m
    · -- Lemma 7 (i) on `(d4, d5)`, the set depending on `z`
      have go : ∀ X : Finset (ZMod 7), Z7.ell X ≤ 4 →
          (∀ a b : ZMod 7, (a = (z : ZMod 7) ∨ a = (z : ZMod 7) - 1) → b ∉ X → (a, b) ∉ Z7.bad63) →
          ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [C, B, A, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
        intro X hX hab
        obtain ⟨h', hh', lam, hlam, hX'⟩ := lemma7_i m (μ * d4) (μ * d5) X (not_dvd_mul hμ h4)
          (not_dvd_mul hμ h5) hr45 hlow.1 hlow.2 hX
        have hl := Lam_modEq_seven hh' hlam
        rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 h40) (Nat.mul_ne_zero hμ0 h50) hr45] at hX'
        have ha := et_of_top m (μ * C) (μ * d4) z lam hr34 hze hl
        exact fin lam hl (hab _ _ ha hX')
      rcases hz with rfl | rfl | rfl
      · exact go {2, 3, 4, 5} ell2345 (fun a b ha hb => z63_z3 a b (by simpa using ha) hb)
      · exact go {2, 3, 4} ell234' (fun a b ha hb => z63_z4 a b (by simpa using ha) hb)
      · exact go {1, 2, 3, 4} ell1234 (fun a b ha hb => z63_z5 a b (by simpa using ha) hb)
    · -- both at the top (or zero): Lemma 2 on `7 d3`
      have h0 : ediff m (μ * d4) (μ * d5) = 0 ∨ nu 7 (ediff m (μ * d4) (μ * d5)) = m := by
        by_cases h0 : ediff m (μ * d4) (μ * d5) = 0
        · exact Or.inl h0
        · right; have := nu_le_m h0 (ediff_lt m _ _); push Not at hlow; have := hlow h0; omega
      obtain ⟨z', hz'7, hz'e⟩ := top_or_zero (ediff_lt m _ _) h0
      obtain ⟨ε1, ε2, he1, he2, hesc⟩ := Z7.sec63_escape (z : ZMod 7) (z' : ZMod 7)
      have ht1 : ε1.val < 2 := by rcases he1 with h | h <;> subst h <;> decide
      have ht2 : ε2.val < 2 := by rcases he2 with h | h <;> subst h <;> decide
      have hc1 : ((ε1.val : ℕ) : ZMod 7) = ε1 := ZMod.natCast_zmod_val ε1
      have hc2 : ((ε2.val : ℕ) : ZMod 7) = ε2 := ZMod.natCast_zmod_val ε2
      set t1 := ε1.val
      set t2 := ε2.val
      obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := 1) (m := m) (x := 7 * (μ * C))
        (t := 4 * t1 + 2 * t2) (by norm_num) (by omega) (nu_seven_mul _ (not_dvd_mul hμ hC)) (Nat.mul_ne_zero (by norm_num) (Nat.mul_ne_zero hμ0 hC0))
        (by omega)
      set lam := 1 + 7 ^ (m - 1) * k with hlam
      have hlmem : lam ∈ Lam 1 m 7 := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      have hl := Lam_modEq_seven (by omega) hlmem
      have h7y : qq m (7 * (lam * (μ * C))) = 4 * t1 + 2 * t2 := by
        unfold qq; rw [show 7 * (lam * (μ * C)) = lam * (7 * (μ * C)) by ring]; exact hkq
      obtain ⟨cy2, cy4⟩ := carry7 m (lam * (μ * C)) t1 t2 ht1 ht2 h7y
      -- the top relations
      have b34 : 2 * (μ * C) ≡ μ * d4 + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
        have := modEq_add_dsub (7 ^ (m + 1)) (2 * (μ * C)) (μ * d4) (N_pos m)
        rwa [← (ediff_branch1 m _ _ hr34).1, hze] at this
      have b45 : 2 * (μ * d4) ≡ μ * d5 + 7 ^ m * z' [MOD 7 ^ (m + 1)] := by
        have := modEq_add_dsub (7 ^ (m + 1)) (2 * (μ * d4)) (μ * d5) (N_pos m)
        rwa [← (ediff_branch1 m _ _ hr45).1, hz'e] at this
      have l34 : 2 * (lam * (μ * C)) ≡ lam * (μ * d4) + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
        rw [show 2 * (lam * (μ * C)) = lam * (2 * (μ * C)) by ring]; exact top_keep hl b34
      have l45 : 2 * (lam * (μ * d4)) ≡ lam * (μ * d5) + 7 ^ m * z' [MOD 7 ^ (m + 1)] := by
        rw [show 2 * (lam * (μ * d4)) = lam * (2 * (μ * d4)) by ring]; exact top_keep hl b45
      have l44 : 2 * (2 * (lam * (μ * C))) ≡ 2 * (lam * (μ * d4)) + 7 ^ m * (2 * z) [MOD 7 ^ (m + 1)] := by
        have := l34.mul_left 2; rw [mul_add] at this; rwa [show 2 * (7 ^ m * z) = 7 ^ m * (2 * z) by ring] at this
      have A1 := qq_of_top1 l34
      have A2 := qq_of_top1 l45
      have A3 := qq_of_top1 l44
      have D1 : (qq m (2 * (lam * (μ * C))) : ZMod 7) = 2 * (qq m (lam * (μ * C)) : ZMod 7) + t1 := by
        rw [cy2, ZMod.natCast_mod]; push_cast; ring
      have D2 : (qq m (4 * (lam * (μ * C))) : ZMod 7) = 2 * (qq m (2 * (lam * (μ * C))) : ZMod 7) + t2 := by
        rw [cy4, ZMod.natCast_mod]; push_cast; ring
      rw [show 2 * (2 * (lam * (μ * C))) = 4 * (lam * (μ * C)) by ring] at A3
      apply fin lam hl
      have e34 : 2 * (qq m (lam * (μ * C)) : ZMod 7) - qq m (lam * (μ * d4)) = (z : ZMod 7) - ε1 := by
        rw [← hc1]; linear_combination A1 - D1
      have e45 : 2 * (qq m (lam * (μ * d4)) : ZMod 7) - qq m (lam * (μ * d5)) = (z' : ZMod 7) - ε2 := by
        rw [← hc2]; push_cast at A3; linear_combination A2 + A3 - D2 - 2 * A1
      rw [e34, e45]; exact hesc
  · have hz : ∀ z, z < 7 → ediff m (μ * C) (μ * d4) = 7 ^ m * z →
        ¬ ((z : ZMod 7) ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) ∧
          (z : ZMod 7) - 1 ∈ ({2, 3, 4, 5} : Finset (ZMod 7))) := by
      intro z hz7 hze hmem
      apply h345
      rcases z7_345 _ hmem.1 hmem.2 with h | h | h
      · have e : z = 3 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h]; rfl)
        exact ⟨3, Or.inl rfl, by rw [hze, e]⟩
      · have e : z = 4 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h]; rfl)
        exact ⟨4, Or.inr (Or.inl rfl), by rw [hze, e]⟩
      · have e : z = 5 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h]; rfl)
        exact ⟨5, Or.inr (Or.inr rfl), by rw [hze, e]⟩
    obtain ⟨lam, hl, hX⟩ := steer m hm (μ * C) (μ * d4) (not_dvd_mul hμ hC) (not_dvd_mul hμ h4) hr34
      {2, 3, 4, 5} ell2345 hz
    rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 hC0) (Nat.mul_ne_zero hμ0 h40) hr34] at hX
    exact fin lam hl (z63_first _ _ hX)

end LRSpectrumFull.BarajasSerra.Sec6
