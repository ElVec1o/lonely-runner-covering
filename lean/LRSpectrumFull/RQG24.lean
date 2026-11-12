/-
# RQ, module G24: Theorem G24 (modulus 4: two odd speeds, one speed `≡ 2 (mod 4)`, one speed `≡ 0 (mod 4)`)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem G24".
`a, b` odd (one class mod 4: `v a - ε v b = 4 D`), `e ≡ 2 (mod 4)`, `s = 4 u`.  If `s ∉ {a + b, |a - b|}` then
`|D| ≠ u`; a coincidence point `x` (`lemma4R_tight`) makes `s` good and `‖D x + σ‖ ≤ 1/10`.  Then `a, b` forbid at
most two consecutive residues `N+1, N+2` of `z = v a * j` (`window_gap4`), and `e` forbids at most one parity class
of `j` (`parity_ok`); one of `N+3, N+4` has the allowed parity.

* `window_gap4`, `e_val`, `not_both_near`, `parity_ok`, `lemma4R_tight_pos`, `lemma4R_tight`, `g24_core`, `G24`.
-/
import LRSpectrumFull.RQGen

namespace LRSpectrumFull

lemma window_gap4 (u w : ℝ) (huw : |u - w| ≤ 2 / 5) :
    ∃ N : ℤ, ∀ m : ℤ, (|(m : ℝ) - u| < ((4 : ℕ) : ℝ) / 5 ∨ |(m : ℝ) - w| < ((4 : ℕ) : ℝ) / 5) →
      N < m ∧ m < N + 3 := by
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h4]
  obtain ⟨huw1, huw2⟩ := abs_le.mp huw
  rcases le_total u w with h | h
  · refine ⟨⌊u - 4 / 5⌋, fun m hm => ?_⟩
    have h1 := Int.floor_le (u - 4 / 5)
    have h2 := Int.lt_floor_add_one (u - 4 / 5)
    have hm' : u - 4 / 5 < m ∧ (m : ℝ) < w + 4 / 5 := by
      rcases hm with hm | hm
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
    constructor
    · have : ((⌊u - 4 / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
      exact_mod_cast this
    · have : (m : ℝ) < ((⌊u - 4 / 5⌋ : ℤ) : ℝ) + 3 := by linarith [hm'.2]
      exact_mod_cast this
  · refine ⟨⌊w - 4 / 5⌋, fun m hm => ?_⟩
    have h1 := Int.floor_le (w - 4 / 5)
    have h2 := Int.lt_floor_add_one (w - 4 / 5)
    have hm' : w - 4 / 5 < m ∧ (m : ℝ) < u + 4 / 5 := by
      rcases hm with hm | hm
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
    constructor
    · have : ((⌊w - 4 / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
      exact_mod_cast this
    · have : (m : ℝ) < ((⌊w - 4 / 5⌋ : ℤ) : ℝ) + 3 := by linarith [hm'.2]
      exact_mod_cast this

lemma e_val (ve : ℕ) (he : ve % 4 = 2) (φ x : ℝ) (j : ℤ) :
    ∃ z : ℤ, (ve : ℝ) * (((j : ℝ) + x) / ((4 : ℕ) : ℝ)) + φ
      = ((ve : ℝ) * x / 4 + φ) + ((j % 2 : ℤ) : ℝ) / 2 + z := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ve = 4 * k + 2 := ⟨ve / 4, by omega⟩
  have hveR : (ve : ℝ) = 4 * k + 2 := by exact_mod_cast hk
  have hj : (j % 2) + 2 * (j / 2) = j := Int.emod_add_mul_ediv j 2
  have hjR : ((j % 2 : ℤ) : ℝ) + 2 * ((j / 2 : ℤ) : ℝ) = j := by exact_mod_cast hj
  refine ⟨(k : ℤ) * j + j / 2, ?_⟩
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h4, hveR]
  push_cast
  linear_combination (-1 / 2 : ℝ) * hjR

lemma not_both_near (y : ℝ) : 1 / 5 ≤ tpDist y ∨ 1 / 5 ≤ tpDist (y + 1 / 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨n, hn⟩ := exists_near_of_not_good (not_le.mpr h1)
  obtain ⟨n', hn'⟩ := exists_near_of_not_good (not_le.mpr h2)
  obtain ⟨a1, a2⟩ := abs_lt.mp hn
  obtain ⟨b1, b2⟩ := abs_lt.mp hn'
  have hd1 : (0 : ℝ) < ((n' - n : ℤ) : ℝ) := by push_cast; linarith
  have hd2 : ((n' - n : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h3 : (0 : ℤ) < n' - n := by exact_mod_cast hd1
  have h4 : n' - n < 1 := by exact_mod_cast hd2
  omega

/-- the runner `e ≡ 2 (mod 4)` forbids at most one parity class of `j` -/
lemma parity_ok (ve : ℕ) (he : ve % 4 = 2) (φ x : ℝ) :
    ∃ p : ℤ, (p = 0 ∨ p = 1) ∧
      ∀ j : ℤ, j % 2 = p → GoodR ve φ (((j : ℝ) + x) / ((4 : ℕ) : ℝ)) := by
  rcases not_both_near ((ve : ℝ) * x / 4 + φ) with h | h
  · refine ⟨0, Or.inl rfl, fun j hj => ?_⟩
    obtain ⟨z, hz⟩ := e_val ve he φ x j
    unfold GoodR
    rw [hz, hj, Int.cast_zero, zero_div, add_zero, tpDist_add_int]
    exact h
  · refine ⟨1, Or.inr rfl, fun j hj => ?_⟩
    obtain ⟨z, hz⟩ := e_val ve he φ x j
    unfold GoodR
    rw [hz, hj, Int.cast_one, tpDist_add_int]
    exact h

lemma lemma4R_tight_pos (D : ℤ) (hD : 0 < D) (w : ℕ) (hw : 1 ≤ w)
    (h : ¬ D ∣ (w : ℤ) ∨ 2 * D ≤ (w : ℤ)) (σ φd : ℝ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + σ - m| ≤ 1 / 10 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  by_cases hdvd : D ∣ (w : ℤ)
  · have h2 : 2 * D ≤ (w : ℤ) := h.resolve_left (not_not.mpr hdvd)
    have h2R : 2 * (D : ℝ) ≤ w := by exact_mod_cast h2
    have hwne : (w : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < w).ne'
    set x0 : ℝ := -σ / D with hx0
    have hDx0 : (D : ℝ) * x0 + σ = 0 := by
      have := mul_div_cancel₀ (-σ) hDR.ne'
      rw [hx0]; linarith
    obtain ⟨δ, hδ, hfar⟩ := exists_perturb ((w : ℝ) * x0 + φd)
    have hwd : (w : ℝ) * (δ / w) = δ := mul_div_cancel₀ _ hwne
    refine ⟨x0 + δ / w, 0, ?_, ?_⟩
    · have e : (D : ℝ) * (x0 + δ / w) + σ - ((0 : ℤ) : ℝ) = D * δ / w := by
        push_cast; linear_combination hDx0
      rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < w), abs_mul, abs_of_pos hDR,
        div_le_iff₀ (by linarith : (0 : ℝ) < w)]
      have := mul_le_mul_of_nonneg_left hδ hDR.le
      nlinarith
    · have e : (w : ℝ) * (x0 + δ / w) + φd = ((w : ℝ) * x0 + φd) + δ := by
        rw [mul_add, hwd]; ring
      rw [e]
      exact hfar
  · obtain ⟨k, hk⟩ := coset_branchR D hD w hdvd σ φd
    refine ⟨((k : ℝ) - σ) / D, k, ?_, hk⟩
    have := mul_div_cancel₀ ((k : ℝ) - σ) hDR.ne'
    have h0 : (D : ℝ) * (((k : ℝ) - σ) / D) + σ - k = 0 := by linarith
    rw [h0]; norm_num

lemma lemma4R_tight (D : ℤ) (hD : D ≠ 0) (w : ℕ) (hw : 1 ≤ w)
    (h : ¬ D ∣ (w : ℤ) ∨ 2 * (D.natAbs : ℤ) ≤ (w : ℤ)) (σ φd : ℝ) :
    ∃ x : ℝ, ∃ m : ℤ, |(D : ℝ) * x + σ - m| ≤ 1 / 10 ∧ 1 / 5 ≤ tpDist ((w : ℝ) * x + φd) := by
  rcases lt_or_gt_of_ne hD with hlt | hgt
  · obtain ⟨x, m, h1, h2⟩ := lemma4R_tight_pos (-D) (by omega) w hw
      (by
        rcases h with h | h
        · exact Or.inl (fun hd => h (neg_dvd.mp hd))
        · right; omega) (-σ) φd
    refine ⟨x, -m, ?_, h2⟩
    have : (D : ℝ) * x + σ - ((-m : ℤ) : ℝ) = -(((-D : ℤ) : ℝ) * x + (-σ) - m) := by
      push_cast; ring
    rw [this, abs_neg]; exact h1
  · exact lemma4R_tight_pos D hgt w hw (by
      rcases h with h | h
      · exact Or.inl h
      · right; omega) σ φd

theorem g24_core (va vb ve : ℕ) (ha : va % 2 = 1) (he : ve % 4 = 2) (ε D : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vb = 4 * D) (φa φb φe x : ℝ) (n : ℤ)
    (hn : |(D : ℝ) * x + (φa - ε * φb) - n| ≤ 1 / 10) :
    ∃ j : ℤ, GoodR va φa (((j : ℝ) + x) / ((4 : ℕ) : ℝ)) ∧ GoodR vb φb (((j : ℝ) + x) / ((4 : ℕ) : ℝ)) ∧
      GoodR ve φe (((j : ℝ) + x) / ((4 : ℕ) : ℝ)) := by
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  have hDR : (va : ℝ) - ε * vb = 4 * D := by exact_mod_cast hD
  have huw : |(-((va : ℝ) * x + ((4 : ℕ) : ℝ) * φa)) -
      (-((ε : ℝ) * ((vb : ℝ) * x + ((4 : ℕ) : ℝ) * φb)) - ((4 : ℕ) : ℝ) * n)| ≤ 2 / 5 := by
    have e : (-((va : ℝ) * x + ((4 : ℕ) : ℝ) * φa)) -
        (-((ε : ℝ) * ((vb : ℝ) * x + ((4 : ℕ) : ℝ) * φb)) - ((4 : ℕ) : ℝ) * n)
        = -(4 * ((D : ℝ) * x + (φa - ε * φb) - n)) := by
      rw [h4]; linear_combination (-x) * hDR
    rw [e, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  obtain ⟨N, hN⟩ := window_gap4 _ _ huw
  obtain ⟨p, hp, hpar⟩ := parity_ok ve he φe x
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (z = N + 3 ∨ z = N + 4) ∧ z % 2 = p := by
    by_cases h : (N + 3) % 2 = p
    · exact ⟨N + 3, Or.inl rfl, h⟩
    · exact ⟨N + 4, Or.inr rfl, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (va : ℤ) = 2 * k + 1 := ⟨(va : ℤ) / 2, by omega⟩
  have hjz : (va : ℤ) * (z * va) = z + 4 * (z * k * (k + 1)) := by rw [hk]; ring
  have hjp : (z * (va : ℤ)) % 2 = p := by
    have : z * (va : ℤ) = 2 * (z * k) + z := by rw [hk]; ring
    rw [this]
    generalize z * k = w
    omega
  have hε1 : |(ε : ℝ)| = 1 := by rcases hε with rfl | rfl <;> simp
  refine ⟨z * (va : ℤ), ?_, ?_, hpar _ hjp⟩
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n1, hn1⟩ := exists_near_of_not_good hbad
    have h1 := near_to_int 4 (by norm_num) va φa x (z * (va : ℤ)) n1 hn1
    obtain ⟨hm1, hm2⟩ := hN _ (Or.inl h1)
    have e : ((va : ℤ) * (z * (va : ℤ)) - ((4 : ℕ) : ℤ) * n1) = z + 4 * (z * k * (k + 1) - n1) := by
      push_cast; linear_combination hjz
    rw [e] at hm1 hm2
    generalize z * k * (k + 1) = w at hm1 hm2
    omega
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n2, hn2⟩ := exists_near_of_not_good hbad
    have h2 := near_to_int 4 (by norm_num) vb φb x (z * (va : ℤ)) n2 hn2
    have h3 : |(((ε * ((vb : ℤ) * (z * (va : ℤ)) - ((4 : ℕ) : ℤ) * n2) - ((4 : ℕ) : ℤ) * n : ℤ)) : ℝ)
        - (-((ε : ℝ) * ((vb : ℝ) * x + ((4 : ℕ) : ℝ) * φb)) - ((4 : ℕ) : ℝ) * n)| < ((4 : ℕ) : ℝ) / 5 := by
      have e : (((ε * ((vb : ℤ) * (z * (va : ℤ)) - ((4 : ℕ) : ℤ) * n2) - ((4 : ℕ) : ℤ) * n : ℤ)) : ℝ)
          - (-((ε : ℝ) * ((vb : ℝ) * x + ((4 : ℕ) : ℝ) * φb)) - ((4 : ℕ) : ℝ) * n)
          = ε * ((((vb : ℤ) * (z * (va : ℤ)) - ((4 : ℕ) : ℤ) * n2 : ℤ) : ℝ)
            - (-((vb : ℝ) * x + ((4 : ℕ) : ℝ) * φb))) := by
        push_cast
        ring
      rw [e, abs_mul, hε1, one_mul]
      exact h2
    obtain ⟨hm1, hm2⟩ := hN _ (Or.inr h3)
    have e2 : ε * ((vb : ℤ) * (z * (va : ℤ)) - ((4 : ℕ) : ℤ) * n2) - ((4 : ℕ) : ℤ) * n
        = z + 4 * (z * k * (k + 1) - D * (z * (va : ℤ)) - ε * n2 - n) := by
      push_cast
      linear_combination (-(z * (va : ℤ))) * hD + hjz
    rw [e2] at hm1 hm2
    generalize z * k * (k + 1) - D * (z * (va : ℤ)) - ε * n2 - n = w at hm1 hm2
    omega

/-- Theorem G24: speeds `v a, v b` odd, `v e ≡ 2 (mod 4)`, `v s ≡ 0 (mod 4)`, `v s ∉ {v a + v b, |v a - v b|}`
(written without absolute values); four distinct positive speeds, arbitrary real phases. -/
theorem G24 (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (a b e s : Fin 4)
    (hse : s ≠ e) (hsa : s ≠ a) (hsb : s ≠ b) (hea : e ≠ a) (heb : e ≠ b) (hab : a ≠ b)
    (ha : v a % 2 = 1) (hb : v b % 2 = 1) (he : v e % 4 = 2) (hs : v s % 4 = 0)
    (hr : v s ≠ v a + v b ∧ v a ≠ v b + v s ∧ v b ≠ v a + v s) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  obtain ⟨ε, D, hε, hD⟩ := eps_D4 (v a) (v b) ha hb
  have hvab : v a ≠ v b := fun h => hab (hinj h)
  have hD0 : D ≠ 0 := D_ne4 _ _ (hpos a) (hpos b) hvab ε D hε hD
  obtain ⟨u, hu⟩ : ∃ u, v s = 4 * u := ⟨v s / 4, by omega⟩
  have pu : 0 < u := pos_of_mul_eq 4 u (v s) (hpos s) hu
  have hnr : D.natAbs ≠ u := by
    have := nonres4 (v a) (v b) (v s) ε D hε hD ⟨u, hu⟩ hr.1 hr.2.1 hr.2.2
    omega
  have hcase : ¬ D ∣ (u : ℤ) ∨ 2 * (D.natAbs : ℤ) ≤ (u : ℤ) := by
    by_cases hdvd : D ∣ (u : ℤ)
    · right
      obtain ⟨t, ht⟩ := hdvd
      have hnat : u = D.natAbs * t.natAbs := by
        have := congrArg Int.natAbs ht
        rw [Int.natAbs_mul] at this
        simpa using this
      have hd : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
      rcases Nat.lt_or_ge t.natAbs 2 with h | h
      · exfalso
        interval_cases hτ : t.natAbs
        · simp at hnat; omega
        · apply hnr; omega
      · have := Nat.mul_le_mul_left D.natAbs h
        omega
    · exact Or.inl hdvd
  obtain ⟨x, m, hm, g⟩ := lemma4R_tight D hD0 u pu hcase (φ a - ε * φ b) (φ s)
  obtain ⟨j, ja, jb, je⟩ := g24_core (v a) (v b) (v e) ha he ε D hε hD (φ a) (φ b) (φ e) x m hm
  refine ⟨((j : ℝ) + x) / ((4 : ℕ) : ℝ), fun i => ?_⟩
  rcases cover4 s e a b i hse hsa hsb hea heb hab with h | h | h | h
  · rw [h, hu]
    exact (goodR_mulq 4 u (by norm_num) _ x j).2 g
  · rw [h]; exact je
  · rw [h]; exact ja
  · rw [h]; exact jb

end LRSpectrumFull
