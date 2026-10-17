import LRSpectrumFull.BarajasSerraSec5

/-!
# E6 session 20: LRC6 hard cases (b), (c), (d) (paper Sections 4-5), minimal level normalised to 0

* (b) four level-0 speeds, the rest at the top level `m ≥ 1`: `sec5` directly.
* (c) four level-0 speeds, one speed `e` at level `0 < i0 < m`, one top speed: multipliers
  `(1 + 7^m k) j w` with `w = u'(1 + 7^(m - i0))`, `u u' ≡ 1 (mod 7^(m+1-i0))`, `e = 7^i0 u`; then
  `q(λ e) = j ∈ [1,5]` (`mid_digit`, the paper's eq. (8)) and `sec5` on `w x_i`.
* (d) one level-0 speed `z`, four at level `0 < i0 < m`, one top: `sec5` at level `m - i0` for the
  four (divided by `7^i0`), then `primeFilteringBelow` (G1) with `v = i0` for `z`; the correcting
  multiplier is `≡ 1 (mod 7^(m+1-i0))` and does not move the upper speeds.
-/

namespace LRSpectrumFull.BarajasSerra.Sec5

open LRSpectrumFull LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.Sec6
  LRSpectrumFull.BarajasSerra.G

theorem coprime7_of_not_dvd {x : ℕ} (hx : ¬ 7 ∣ x) : Nat.Coprime x 7 :=
  (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hx))

/-- **Case (b)**: four level-0 speeds, any number of top speeds. -/
theorem case_b0 (m : ℕ) (hm : 1 ≤ m) (x : Fin 4 → ℕ) (hx : ∀ i, ¬ 7 ∣ x i) (T : List ℕ)
    (hT : ∀ d ∈ T, d ≠ 0 ∧ nu 7 d = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * x i)) ∧
      ∀ d ∈ T, (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  obtain ⟨j, k, hj1, hj5, -, h⟩ := sec5 m hm (x 0) (x 1) (x 2) (x 3) (hx 0) (hx 1) (hx 2) (hx 3)
  obtain ⟨t, ht, hall⟩ := witness_of_lam m ((1 + 7 ^ m * k) * j) (lam_coprime m j k hm hj1 hj5)
    [x 0, x 1, x 2, x 3] T (fun d hd => by rw [mul_assoc]; exact h d hd) hT
  refine ⟨t, ht, fun i => hall _ (List.mem_append_left _ ?_), fun d hd => hall _ (List.mem_append_right _ hd)⟩
  fin_cases i <;> simp

/-- eq. (8): the fifth speed `e = 7^i0 u` has `q = j` under `(1 + 7^m k) j u' (1 + 7^(m-i0))`. -/
theorem mid_digit (a e j k u u' s : ℕ) (hj : j < 7) (hs : u * u' = 7 ^ (e + 2) * s + 1) :
    qq (a + e + 2) ((1 + 7 ^ (a + e + 2) * k) * j * (u' * (1 + 7 ^ (e + 1))) * (7 ^ (a + 1) * u)) = j := by
  set R := s * (1 + 7 ^ (e + 1))
  have hX : (1 + 7 ^ (a + e + 2) * k) * j * (u' * (1 + 7 ^ (e + 1))) * (7 ^ (a + 1) * u) =
      j * 7 ^ (a + 1) + 7 ^ (a + e + 2) * (j + 7 * (j * (R + k * (7 ^ a + 7 ^ (a + e + 1)) +
        7 ^ (a + e + 2) * k * R))) := by
    have : (1 + 7 ^ (a + e + 2) * k) * j * (u' * (1 + 7 ^ (e + 1))) * (7 ^ (a + 1) * u) =
        (1 + 7 ^ (a + e + 2) * k) * j * (1 + 7 ^ (e + 1)) * 7 ^ (a + 1) * (u * u') := by ring
    rw [this, hs]; simp only [R]; ring
  rw [hX, qq_eq_div, Nat.add_mul_div_left _ _ (by positivity)]
  have hlt : j * 7 ^ (a + 1) < 7 ^ (a + e + 2) := by
    calc j * 7 ^ (a + 1) < 7 * 7 ^ (a + 1) := Nat.mul_lt_mul_of_pos_right hj (by positivity)
      _ = 7 ^ (a + 2) := by ring
      _ ≤ 7 ^ (a + e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.div_eq_of_lt hlt, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-- **Case (c)**: four level-0 speeds, one at level `0 < i0 < m`, one at the top. -/
theorem case_c0 (m i0 : ℕ) (h1 : 1 ≤ i0) (h2 : i0 < m) (x : Fin 4 → ℕ) (hx : ∀ i, ¬ 7 ∣ x i)
    (e : ℕ) (he0 : e ≠ 0) (hev : nu 7 e = i0) (d : ℕ) (hd0 : d ≠ 0) (hdv : nu 7 d = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * x i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * e) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, rfl⟩ : ∃ a, i0 = a + 1 := ⟨i0 - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = a + b + 2 := ⟨m - a - 2, by omega⟩
  -- e = 7^(a+1) u
  have hdiv : 7 ^ (a + 1) ∣ e := by rw [← hev]; exact pow_padicValNat_dvd
  obtain ⟨u, rfl⟩ := hdiv
  have hu : ¬ 7 ∣ u := by
    intro h
    have : 7 ^ (a + 1 + 1) ∣ 7 ^ (a + 1) * u := by rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h
    have h' := pow_succ_padicValNat_not_dvd (p := 7) he0
    unfold nu at hev; rw [hev] at h'
    exact h' this
  obtain ⟨u', -, hu'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.pow_right (b + 2) (coprime7_of_not_dvd hu)) (Nat.one_lt_pow (by omega) (by norm_num))
  have hs : u * u' = 7 ^ (b + 2) * (u * u' / 7 ^ (b + 2)) + 1 := by
    have := Nat.div_add_mod (u * u') (7 ^ (b + 2)); rw [hu'] at this; omega
  have hu'7 : ¬ 7 ∣ u' := by
    intro h
    have h7 : 7 ∣ u * u' % 7 ^ (b + 2) :=
      (Nat.dvd_mod_iff (dvd_pow_self 7 (by omega))).mpr (Dvd.dvd.mul_left h u)
    rw [hu'] at h7; omega
  set w := u' * (1 + 7 ^ (b + 1)) with hw
  have hw7 : ¬ 7 ∣ w := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
    · exact hu'7 h
    · have : 7 ∣ 7 ^ (b + 1) := dvd_pow_self 7 (by omega)
      omega
  have hwx : ∀ i, ¬ 7 ∣ w * x i := fun i h => by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
    exacts [hw7 h, hx i h]
  have hm1 : 1 ≤ a + b + 2 := by omega
  obtain ⟨j, k, hj1, hj5, -, h⟩ := sec5 (a + b + 2) hm1 (w * x 0) (w * x 1) (w * x 2) (w * x 3)
    (hwx 0) (hwx 1) (hwx 2) (hwx 3)
  set lam := (1 + 7 ^ (a + b + 2) * k) * j * w with hlam
  have hlc : Nat.Coprime lam 7 :=
    Nat.Coprime.mul_left (lam_coprime _ j k hm1 hj1 hj5) (coprime7_of_not_dvd hw7)
  have hS : ∀ y ∈ [x 0, x 1, x 2, x 3, 7 ^ (a + 1) * u], qq (a + b + 2) (lam * y) ≠ 0 ∧
      qq (a + b + 2) (lam * y) ≠ 6 := by
    have hx4 : ∀ i, qq (a + b + 2) (lam * x i) ≠ 0 ∧ qq (a + b + 2) (lam * x i) ≠ 6 := by
      intro i
      rw [show lam * x i = (1 + 7 ^ (a + b + 2) * k) * (j * (w * x i)) by rw [hlam]; ring]
      exact h _ (by fin_cases i <;> simp)
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hx4 0
    · exact hx4 1
    · exact hx4 2
    · exact hx4 3
    · rw [hlam, hw, mid_digit a b j k u u' _ (by omega) hs]; omega
  obtain ⟨t, ht, hall⟩ := witness_of_lam (a + b + 2) lam hlc _ [d] hS
    (by intro y hy; simp at hy; subst hy; exact ⟨hd0, hdv⟩)
  refine ⟨t, ht, fun i => hall _ (List.mem_append_left _ ?_), hall _ (by simp), hall _ (by simp)⟩
  fin_cases i <;> simp

/-- **Case (d)**: one level-0 speed, four at level `0 < i0 < m`, one at the top. -/
theorem case_d0 (m i0 : ℕ) (h1 : 1 ≤ i0) (h2 : i0 < m) (z : ℕ) (hz : ¬ 7 ∣ z) (x : Fin 4 → ℕ)
    (hx0 : ∀ i, x i ≠ 0) (hxv : ∀ i, nu 7 (x i) = i0) (d : ℕ) (hd0 : d ≠ 0) (hdv : nu 7 d = m) :
    ∃ t : ℝ, 0 < t ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * z) ∧
      (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * x i)) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + i0 := ⟨m - i0, by omega⟩
  have hdvx : ∀ i, 7 ^ i0 ∣ x i := fun i => by rw [← hxv i]; exact pow_padicValNat_dvd
  set x' : Fin 4 → ℕ := fun i => x i / 7 ^ i0 with hx'
  have hxeq : ∀ i, x i = 7 ^ i0 * x' i := fun i => (Nat.mul_div_cancel' (hdvx i)).symm
  have hx'7 : ∀ i, ¬ 7 ∣ x' i := by
    intro i h
    have h1 : 7 ^ i0 * 7 ∣ x i := by rw [hxeq i]; exact Nat.mul_dvd_mul_left _ h
    rw [← pow_succ, ← hxv i] at h1
    exact pow_succ_padicValNat_not_dvd (hx0 i) h1
  have hm' : 1 ≤ m' := by omega
  obtain ⟨j, k, hj1, hj5, -, h⟩ := sec5 m' hm' (x' 0) (x' 1) (x' 2) (x' 3) (hx'7 0) (hx'7 1)
    (hx'7 2) (hx'7 3)
  set lam' := (1 + 7 ^ m' * k) * j with hlam'
  have hl'c : Nat.Coprime lam' 7 := lam_coprime m' j k hm' hj1 hj5
  have hl'z : ¬ 7 ∣ lam' * z := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
    · exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mp hl'c.symm h
    · exact hz h
  -- G1: fix the level-0 speed with a multiplier `≡ 1 (mod 7^(m'+1))`
  obtain ⟨μ, hμ, hμz⟩ := primeFilteringBelow 7 (by norm_num) {lam' * z} (fun _ => {0, 6})
    (m' + i0) (7 ^ (m' + i0 + 1)) rfl i0 (by omega)
    (by
      intro y hy _
      rw [Finset.mem_singleton] at hy; subst hy
      rw [nu_zero_of_not_dvd hl'z]; omega)
    (by
      intro j' _
      calc (∑ y ∈ Dlevel 7 (({lam' * z} : Finset ℕ).filter (fun d => d % 7 ^ (m' + i0 + 1) ≠ 0)) j',
            (({0, 6} : Finset ℕ)).card)
          ≤ ∑ y ∈ ({lam' * z} : Finset ℕ), (({0, 6} : Finset ℕ)).card := by
            apply Finset.sum_le_sum_of_subset
            intro y hy
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
        _ ≤ 7 - 1 := by simp)
    (by
      intro y hy hy0
      rw [Finset.mem_singleton] at hy; subst hy
      exfalso; apply hl'z
      exact (dvd_pow_self 7 (by omega)).trans (Nat.dvd_of_mod_eq_zero hy0))
  have hμ' : μ ≡ 1 [MOD 7 ^ (m' + i0 + 1 - i0)] := hμ
  have hμ7 : μ ≡ 1 [MOD 7] := by
    have := modEq_one_mono (p := 7) hμ' (show 1 ≤ m' + i0 + 1 - i0 by omega)
    simpa using this
  set lam := μ * lam' with hlam
  have hlc : Nat.Coprime lam 7 := Nat.Coprime.mul_left (coprime_of_modEq_one (by norm_num) hμ7).1 hl'c
  have hS : ∀ y ∈ z :: List.ofFn x, qq (m' + i0) (lam * y) ≠ 0 ∧ qq (m' + i0) (lam * y) ≠ 6 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have := hμz (lam' * y) (Finset.mem_singleton_self _)
      unfold qq; rw [hlam, mul_assoc]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
      exact this
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      have hfix : qq (m' + i0) (lam * x i) = qq (m' + i0) (lam' * x i) := by
        unfold qq; rw [hlam, mul_assoc]
        exact qarc_mul_fix (v := i0) (by omega) hμ (Dvd.dvd.mul_left (hdvx i) _)
      have hlev : qq (m' + i0) (lam' * x i) = qq m' (lam' * x' i) := by
        rw [qq_eq_div, qq_eq_div, hxeq i, show lam' * (7 ^ i0 * x' i) = lam' * x' i * 7 ^ i0 by ring,
          pow_add, Nat.mul_div_mul_right _ _ (by positivity)]
      rw [hfix, hlev, hlam', mul_assoc]
      exact h _ (by fin_cases i <;> simp)
  obtain ⟨t, ht, hall⟩ := witness_of_lam (m' + i0) lam hlc _ [d] hS
    (by intro y hy; simp at hy; subst hy; exact ⟨hd0, hdv⟩)
  refine ⟨t, ht, hall _ (by simp), fun i => hall _ (List.mem_append_left _ ?_), hall _ (by simp)⟩
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end LRSpectrumFull.BarajasSerra.Sec5
