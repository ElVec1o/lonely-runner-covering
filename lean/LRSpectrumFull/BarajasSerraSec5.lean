import LRSpectrumFull.BarajasSerraSec6G4
import LRSpectrumFull.BarajasSerraSec5Fin

/-!
# E6 session 20: Barajas-Serra Section 5 (`|A| = 4`), the multiplier statement

For four level-0 speeds `x1..x4` (`7 ∤ xi`) and `m ≥ 1` there are `1 ≤ j ≤ 5` and `k < 7` with
`q((1 + 7^m k) j xi) ∉ {0, 6}` for all `i` (`sec5`). This is the finite core of cases (b), (c), (d)
of LRC6 (paper Section 5: the fifth speed `d5` is handled by the prefactor `u'(1 + 7^(m - i0))`,
which is not part of this statement).

Route: sign flips (`fl`, as in G4) put every residue in `{1,2,4}`; a `Λ_0` pre-shift makes
`q(x1) = 0`; each `xi` is modelled by `(q(xi), Farey row of (xi mod 7^m)/7^m)` (`model`), exact for
`j ≤ 5`; the finite facts `F1`-`F3`, `Z1`-`Z3` of `BarajasSerraSec5Fin` close the three class
profiles `4`, `3+1`, `2+(1+1 or 2)` (the paper's Cases 1-3; profile `2+0+2` is rebased).
Rust first: (development file, not part of this archive) (exact claim, m = 1 and m = 2 exhaustive over all
4-multisets of units: 0 failures), `sec5f.rs`, `sec5d.rs` (model statements, 0 failures).
-/

namespace LRSpectrumFull.BarajasSerra.Sec5

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.Sec6 LRSpectrumFull.BarajasSerra.Sec5Fin

/-! ## Bool extraction -/

theorem all_range {n : ℕ} {f : ℕ → Bool} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) :
    f i = true := List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem all_mem {α : Type} {l : List α} {f : α → Bool} (h : l.all f = true) {i : α} (hi : i ∈ l) : f i = true :=
  List.all_eq_true.mp h i hi

theorem any_range {n : ℕ} {f : ℕ → Bool} (h : (List.range n).any f = true) : ∃ i < n, f i = true := by
  obtain ⟨i, hi, h⟩ := List.any_eq_true.mp h; exact ⟨i, List.mem_range.mp hi, h⟩

theorem hasArc_spec {len : ℕ} {vs : List ℕ} (h : hasArc len vs = true) :
    ∃ t < 7, ∀ v ∈ vs, (v + 7 - t) % 7 < len := by
  obtain ⟨t, ht, h⟩ := any_range h
  refine ⟨t, ht, fun v hv => ?_⟩
  have := List.all_eq_true.mp h v hv
  simpa using this

theorem gd_spec {v : ℕ} (h : gd v = true) : v % 7 ≠ 0 ∧ v % 7 ≠ 6 := by
  simpa [gd] using h

/-! ## `q` arithmetic -/

theorem qq_eq_div (m y : ℕ) : qq m y = y / 7 ^ m % 7 := by
  unfold qq qarc; rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem qq_lt (m y : ℕ) : qq m y < 7 := by rw [qq_eq_div]; exact Nat.mod_lt _ (by norm_num)

/-- `Λ_0` shift. -/
theorem qq_lam0 (m k y : ℕ) : qq m ((1 + 7 ^ m * k) * y) = (qq m y + k * (y % 7)) % 7 := by
  rw [qq_eq_div, qq_eq_div]
  have hM : 0 < 7 ^ m := by positivity
  rw [show (1 + 7 ^ m * k) * y = y + 7 ^ m * (k * y) by ring, Nat.add_mul_div_left _ _ hM]
  exact Nat.ModEq.add (Nat.mod_modEq _ 7).symm (Nat.ModEq.mul_left k (Nat.mod_modEq y 7).symm)

/-- carries of `j x`. -/
theorem qq_mul (m x j : ℕ) : qq m (j * x) = (j * qq m x + j * (x % 7 ^ m) / 7 ^ m) % 7 := by
  rw [qq_eq_div, qq_eq_div]
  have hM : 0 < 7 ^ m := by positivity
  have hx : j * x = j * (x % 7 ^ m) + 7 ^ m * (j * (x / 7 ^ m)) := by
    conv_lhs => rw [← Nat.mod_add_div x (7 ^ m)]
    ring
  rw [hx, Nat.add_mul_div_left _ _ hM, add_comm]
  exact Nat.ModEq.add_right _ (Nat.ModEq.mul_left j (Nat.mod_modEq _ 7).symm)

theorem farey (M b : ℕ) (hM : 0 < M) (hb : b < M) :
    ∃ p < 10, ∀ j, 1 ≤ j → j ≤ 5 → j * b / M = cf p j := by
  have hc : ∀ j, 1 ≤ j → j * b / M < j := fun j hj =>
    (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mul_lt_mul_of_pos_left hb (by omega))
  have l2 := hc 2 (by norm_num); have l3 := hc 3 (by norm_num)
  have l4 := hc 4 (by norm_num); have l5 := hc 5 (by norm_num)
  have hcont : CT.contains [0, 2 * b / M, 3 * b / M, 4 * b / M, 5 * b / M] = true := by
    have e2 := Nat.div_add_mod (2 * b) M; have r2 := Nat.mod_lt (2 * b) hM
    have e3 := Nat.div_add_mod (3 * b) M; have r3 := Nat.mod_lt (3 * b) hM
    have e4 := Nat.div_add_mod (4 * b) M; have r4 := Nat.mod_lt (4 * b) hM
    have e5 := Nat.div_add_mod (5 * b) M; have r5 := Nat.mod_lt (5 * b) hM
    generalize 2 * b / M = c2 at *; generalize 3 * b / M = c3 at *
    generalize 4 * b / M = c4 at *; generalize 5 * b / M = c5 at *
    generalize 2 * b % M = s2 at *; generalize 3 * b % M = s3 at *
    generalize 4 * b % M = s4 at *; generalize 5 * b % M = s5 at *
    interval_cases c2 <;> interval_cases c3 <;> interval_cases c4 <;> interval_cases c5 <;>
      first | decide | (exfalso; omega)
  have hp := all_range (all_range (all_range (all_range farey_pick l2) l3) l4) l5
  simp only [hcont, Bool.not_true, Bool.false_or] at hp
  obtain ⟨p, hp10, hpe⟩ := any_range hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hpe
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := hpe
  have h1 : cf p 1 = 0 := by simpa using all_range cf_one hp10
  refine ⟨p, hp10, fun j hj1 hj5 => ?_⟩
  interval_cases j
  · rw [h1]; simp [Nat.div_eq_of_lt hb]
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm
  · exact h5.symm

/-- the Farey model of a speed. -/
theorem model (m x : ℕ) : ∃ p < 10, ∀ j, 1 ≤ j → j ≤ 5 → qq m (j * x) = qm (qq m x) p j := by
  obtain ⟨p, hp, hpe⟩ := farey (7 ^ m) (x % 7 ^ m) (by positivity) (Nat.mod_lt _ (by positivity))
  exact ⟨p, hp, fun j h1 h5 => by rw [qq_mul, hpe j h1 h5]; rfl⟩

theorem qm_rep (a p j : ℕ) (hp : p < 10) (hj : j < 5) : qm a (rep4 p) j = qm a p j := by
  have h := all_range rep4_spec hp
  simp only [Bool.and_eq_true] at h
  have := all_range h.2 hj
  simp only [beq_iff_eq] at this
  unfold qm; rw [this]

theorem rep_mem (p : ℕ) (hp : p < 10) : rep4 p ∈ [0, 2, 3, 5, 7, 8] := by
  have h := all_range rep4_spec hp
  simp only [Bool.and_eq_true] at h
  simpa using h.1

theorem qm_one (a p : ℕ) (ha : a < 7) (hp : p < 10) : qm a p 1 = a := by
  have h1 : cf p 1 = 0 := by simpa using all_range cf_one hp
  unfold qm; rw [h1]; omega

/-! ## the statement and its bookkeeping -/

/-- the Section 5 multipliers `(1 + 7^m k) j`, `1 ≤ j ≤ 5`, keep all of `L` off `q ∈ {0,6}`. -/
def T4 (m : ℕ) (L : List ℕ) : Prop :=
  ∃ j k, 1 ≤ j ∧ j ≤ 5 ∧ k < 7 ∧ ∀ x ∈ L, qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 0 ∧
    qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 6

theorem t4_sub {m : ℕ} {L L' : List ℕ} (h : T4 m L) (hs : ∀ x ∈ L', x ∈ L) : T4 m L' := by
  obtain ⟨j, k, h1, h5, hk, hx⟩ := h
  exact ⟨j, k, h1, h5, hk, fun x hx' => hx x (hs x hx')⟩

set_option hygiene false in
macro "sub4" : tactic => `(tactic| (intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp))

theorem mod7_shift (m c y : ℕ) (hm : 1 ≤ m) : (1 + 7 ^ m * c) * y % 7 = y % 7 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show (1 + 7 ^ (m' + 1) * c) * y = y + 7 * (7 ^ m' * c * y) by ring, Nat.add_mul_mod_self_left]

/-- a `Λ_0` pre-shift of all speeds is absorbed into `k`. -/
theorem t4_shift (m c : ℕ) (hm : 1 ≤ m) (L : List ℕ)
    (h : T4 m (L.map (fun x => (1 + 7 ^ m * c) * x))) : T4 m L := by
  obtain ⟨j, k, h1, h5, hk, hx⟩ := h
  refine ⟨j, (k + c) % 7, h1, h5, Nat.mod_lt _ (by norm_num), fun x hxL => ?_⟩
  have hy := hx _ (List.mem_map.mpr ⟨x, hxL, rfl⟩)
  have e : qq m ((1 + 7 ^ m * ((k + c) % 7)) * (j * x)) =
      qq m ((1 + 7 ^ m * k) * (j * ((1 + 7 ^ m * c) * x))) := by
    rw [show j * ((1 + 7 ^ m * c) * x) = (1 + 7 ^ m * c) * (j * x) by ring, qq_lam0, qq_lam0 m k,
      qq_lam0 m c, mod7_shift m c _ hm]
    apply (ZMod.natCast_eq_natCast_iff' _ _ 7).mp
    push_cast [ZMod.natCast_mod]
    ring
  rw [e]; exact hy

/-- finishing one speed of ratio `r` to `x1`. -/
theorem el_good {m x x1 j k r : ℕ} (hr : x % 7 = r * x1 % 7)
    (hg : gd (qq m (j * x) + k * (r * (j * x1 % 7) % 7)) = true) :
    qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 6 := by
  rw [qq_lam0]
  have e : (qq m (j * x) + k * (j * x % 7)) % 7 = (qq m (j * x) + k * (r * (j * x1 % 7) % 7)) % 7 := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 7).mp
    have hr' : ((x : ℕ) : ZMod 7) = r * x1 := by
      have := (ZMod.natCast_eq_natCast_iff' x (r * x1) 7).mpr hr
      simpa using this
    push_cast [ZMod.natCast_mod]
    rw [hr']; ring
  rw [e]; exact gd_spec hg

theorem J_ne (x1 j : ℕ) (n1 : ¬ 7 ∣ x1) (h1 : 1 ≤ j) (h5 : j ≤ 5) : j * x1 % 7 ≠ 0 := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp (Nat.dvd_of_mod_eq_zero h) with h | h
  · omega
  · exact n1 h

/-! ## core adapters (`q(x1) = 0`) -/

theorem core4 (m : ℕ) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1)
    (r2 : x2 % 7 = 1 * x1 % 7) (r3 : x3 % 7 = 1 * x1 % 7) (r4 : x4 % 7 = 1 * x1 % 7)
    (h0 : qq m x1 = 0) : T4 m [x1, x2, x3, x4] := by
  obtain ⟨p1, hp1, e1⟩ := model m x1
  obtain ⟨p2, hp2, e2⟩ := model m x2
  obtain ⟨p3, hp3, e3⟩ := model m x3
  obtain ⟨p4, hp4, e4⟩ := model m x4
  have a2 := qq_lt m x2; have a3 := qq_lt m x3; have a4 := qq_lt m x4
  -- an arc of length 5 for some `j ≤ 4`
  have harc : ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ ∃ t < 7, ∀ v ∈ [qq m (j * x1), qq m (j * x2), qq m (j * x3),
      qq m (j * x4)], (v + 7 - t) % 7 < 5 := by
    have hA := all_range F1a (i := qq m x2 + 7 * qq m x3 + 49 * qq m x4) (by omega)
    have c1 : (qq m x2 + 7 * qq m x3 + 49 * qq m x4) % 7 = qq m x2 := by omega
    have c2 : (qq m x2 + 7 * qq m x3 + 49 * qq m x4) / 7 % 7 = qq m x3 := by omega
    have c3 : (qq m x2 + 7 * qq m x3 + 49 * qq m x4) / 49 = qq m x4 := by omega
    rw [c1, c2, c3] at hA
    rcases Bool.or_eq_true_iff.mp hA with hA | hA
    · refine ⟨1, le_rfl, by norm_num, ?_⟩
      simp only [one_mul]
      rw [← h0] at hA; exact hasArc_spec hA
    · have hI := all_mem F1b (List.elem_iff.mp hA)
      unfold inner1 at hI
      rw [c1, c2, c3] at hI
      have hI := all_mem (all_mem (all_mem (all_mem hI (rep_mem p1 hp1)) (rep_mem p2 hp2))
        (rep_mem p3 hp3)) (rep_mem p4 hp4)
      obtain ⟨j, hj, hJ⟩ := any_range hI
      refine ⟨j + 1, by omega, by omega, ?_⟩
      rw [e1 _ (by omega) (by omega), e2 _ (by omega) (by omega), e3 _ (by omega) (by omega),
        e4 _ (by omega) (by omega), h0]
      rw [qm_rep _ _ _ hp1 (by omega), qm_rep _ _ _ hp2 (by omega), qm_rep _ _ _ hp3 (by omega),
        qm_rep _ _ _ hp4 (by omega)] at hJ
      exact hasArc_spec hJ
  obtain ⟨j, hj1, hj5, t, ht, hv⟩ := harc
  have hJ := J_ne x1 j n1 hj1 hj5
  have hz := all_range (all_range Z1 ht) (Nat.mod_lt (j * x1) (by norm_num : 0 < 7))
  rw [show (j * x1 % 7 == 0) = false from by simpa using hJ, Bool.false_or] at hz
  obtain ⟨k, hk, hkk⟩ := any_range hz
  refine ⟨j, k, hj1, hj5, hk, fun x hx => ?_⟩
  have hfin : ∀ y, y % 7 = 1 * x1 % 7 → qq m (j * y) ∈ [qq m (j * x1), qq m (j * x2), qq m (j * x3),
      qq m (j * x4)] → qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 6 := by
    intro y hy hmem
    apply el_good hy
    have := all_range hkk (qq_lt m (j * y))
    have ha := hv _ hmem
    simp only [ha, decide_true, Bool.not_true, Bool.false_or] at this
    rw [one_mul, Nat.mod_mod]; exact this
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hfin _ (by rw [one_mul]) (by simp)
  · exact hfin _ r2 (by simp)
  · exact hfin _ r3 (by simp)
  · exact hfin _ r4 (by simp)

theorem core31 (m : ℕ) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1) (r : ℕ) (hr : r = 2 ∨ r = 4)
    (r2 : x2 % 7 = 1 * x1 % 7) (r3 : x3 % 7 = 1 * x1 % 7) (r4 : x4 % 7 = r * x1 % 7)
    (h0 : qq m x1 = 0) : T4 m [x1, x2, x3, x4] := by
  obtain ⟨p1, hp1, e1⟩ := model m x1
  obtain ⟨p2, hp2, e2⟩ := model m x2
  obtain ⟨p3, hp3, e3⟩ := model m x3
  have a2 := qq_lt m x2; have a3 := qq_lt m x3
  have harc : ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ ∃ t < 7, ∀ v ∈ [qq m (j * x1), qq m (j * x2), qq m (j * x3)],
      (v + 7 - t) % 7 < 4 := by
    have hA := all_range F2 (i := qq m x2 + 7 * qq m x3) (by omega)
    have c1 : (qq m x2 + 7 * qq m x3) % 7 = qq m x2 := by omega
    have c2 : (qq m x2 + 7 * qq m x3) / 7 = qq m x3 := by omega
    rw [c1, c2] at hA
    have hI := all_mem (all_mem (all_mem hA (rep_mem p1 hp1)) (rep_mem p2 hp2)) (rep_mem p3 hp3)
    obtain ⟨j, hj, hJ⟩ := any_range hI
    refine ⟨j + 1, by omega, by omega, ?_⟩
    rw [e1 _ (by omega) (by omega), e2 _ (by omega) (by omega), e3 _ (by omega) (by omega), h0]
    rw [qm_rep _ _ _ hp1 (by omega), qm_rep _ _ _ hp2 (by omega), qm_rep _ _ _ hp3 (by omega)] at hJ
    exact hasArc_spec hJ
  obtain ⟨j, hj1, hj5, t, ht, hv⟩ := harc
  have hJ := J_ne x1 j n1 hj1 hj5
  have hz := all_range (all_range (all_range Z2 ht) (qq_lt m (j * x4)))
    (Nat.mod_lt (j * x1) (by norm_num : 0 < 7))
  rw [show (j * x1 % 7 == 0) = false from by simpa using hJ, Bool.false_or] at hz
  have hz := all_mem hz (show r ∈ [2, 4] by rcases hr with rfl | rfl <;> simp)
  obtain ⟨k, hk, hkk⟩ := any_range hz
  simp only [Bool.and_eq_true] at hkk
  obtain ⟨hkc, hk4⟩ := hkk
  refine ⟨j, k, hj1, hj5, hk, fun x hx => ?_⟩
  have hfin : ∀ y, y % 7 = 1 * x1 % 7 → qq m (j * y) ∈ [qq m (j * x1), qq m (j * x2), qq m (j * x3)] →
      qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 6 := by
    intro y hy hmem
    apply el_good hy
    have := all_range hkc (qq_lt m (j * y))
    have ha := hv _ hmem
    simp only [ha, decide_true, Bool.not_true, Bool.false_or] at this
    rw [one_mul, Nat.mod_mod]; exact this
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hfin _ (by rw [one_mul]) (by simp)
  · exact hfin _ r2 (by simp)
  · exact hfin _ r3 (by simp)
  · exact el_good r4 hk4

theorem core2 (m : ℕ) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1) (r3 r4 : ℕ)
    (hrr : (r3, r4) ∈ [(2, 2), (2, 4), (4, 2)])
    (e2r : x2 % 7 = 1 * x1 % 7) (e3r : x3 % 7 = r3 * x1 % 7) (e4r : x4 % 7 = r4 * x1 % 7)
    (h0 : qq m x1 = 0) : T4 m [x1, x2, x3, x4] := by
  obtain ⟨p1, hp1, e1⟩ := model m x1
  obtain ⟨p2, hp2, e2⟩ := model m x2
  have a2 := qq_lt m x2
  have harc : ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ ∃ t < 7, ∀ v ∈ [qq m (j * x1), qq m (j * x2)],
      (v + 7 - t) % 7 < 2 := by
    have hA := all_range (all_range F3 a2) (i := p1 + 10 * p2) (by omega)
    have c1 : (p1 + 10 * p2) % 10 = p1 := by omega
    have c2 : (p1 + 10 * p2) / 10 = p2 := by omega
    rw [c1, c2] at hA
    obtain ⟨j, hj, hJ⟩ := any_range hA
    refine ⟨j + 1, by omega, by omega, ?_⟩
    rw [e1 _ (by omega) (by omega), e2 _ (by omega) (by omega), h0]
    exact hasArc_spec hJ
  obtain ⟨j, hj1, hj5, t, ht, hv⟩ := harc
  have hJ := J_ne x1 j n1 hj1 hj5
  have hz := all_range (all_range (all_range (all_range Z3 ht) (qq_lt m (j * x3))) (qq_lt m (j * x4)))
    (Nat.mod_lt (j * x1) (by norm_num : 0 < 7))
  rw [show (j * x1 % 7 == 0) = false from by simpa using hJ, Bool.false_or] at hz
  have hz := all_mem hz hrr
  obtain ⟨k, hk, hkk⟩ := any_range hz
  simp only [Bool.and_eq_true] at hkk
  obtain ⟨⟨hkc, hk3⟩, hk4⟩ := hkk
  refine ⟨j, k, hj1, hj5, hk, fun x hx => ?_⟩
  have hfin : ∀ y, y % 7 = 1 * x1 % 7 → qq m (j * y) ∈ [qq m (j * x1), qq m (j * x2)] →
      qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 6 := by
    intro y hy hmem
    apply el_good hy
    have := all_range hkc (qq_lt m (j * y))
    have ha := hv _ hmem
    simp only [ha, decide_true, Bool.not_true, Bool.false_or] at this
    rw [one_mul, Nat.mod_mod]; exact this
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hfin _ (by rw [one_mul]) (by simp)
  · exact hfin _ e2r (by simp)
  · exact el_good e3r hk3
  · exact el_good e4r hk4

/-! ## normalisation `q(x1) = 0` by a `Λ_0` pre-shift -/

theorem shift_prep (m : ℕ) (x1 : ℕ) (n1 : ¬ 7 ∣ x1) : ∃ c, qq m ((1 + 7 ^ m * c) * x1) = 0 := by
  have hr : x1 % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hz := all_range (all_range shift0 (qq_lt m x1)) hr
  rw [show (x1 % 7 == 0) = false from by simpa [Nat.dvd_iff_mod_eq_zero] using n1, Bool.false_or] at hz
  obtain ⟨c, -, hc⟩ := any_range hz
  refine ⟨c, ?_⟩
  rw [qq_lam0]; simpa using hc

theorem hmul (m c r a b : ℕ) (hm : 1 ≤ m) (h : a % 7 = r * b % 7) :
    (1 + 7 ^ m * c) * a % 7 = r * ((1 + 7 ^ m * c) * b) % 7 := by
  rw [mod7_shift m c a hm, Nat.mul_mod, mod7_shift m c b hm, ← Nat.mul_mod]; exact h

theorem shift_nd (m c x : ℕ) (hm : 1 ≤ m) (hx : ¬ 7 ∣ x) : ¬ 7 ∣ (1 + 7 ^ m * c) * x := by
  rw [Nat.dvd_iff_mod_eq_zero, mod7_shift m c x hm]; rwa [Nat.dvd_iff_mod_eq_zero] at hx

theorem A4 (m : ℕ) (hm : 1 ≤ m) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1) (n2 : ¬ 7 ∣ x2) (n3 : ¬ 7 ∣ x3)
    (n4 : ¬ 7 ∣ x4) (r2 : x2 % 7 = 1 * x1 % 7) (r3 : x3 % 7 = 1 * x1 % 7) (r4 : x4 % 7 = 1 * x1 % 7) :
    T4 m [x1, x2, x3, x4] := by
  obtain ⟨c, hc⟩ := shift_prep m x1 n1
  apply t4_shift m c hm
  simp only [List.map_cons, List.map_nil]
  exact core4 m ((1 + 7 ^ m * c) * x1) ((1 + 7 ^ m * c) * x2) ((1 + 7 ^ m * c) * x3)
    ((1 + 7 ^ m * c) * x4) (shift_nd m c x1 hm n1) (hmul m c 1 _ _ hm r2) (hmul m c 1 _ _ hm r3)
    (hmul m c 1 _ _ hm r4) hc

theorem A31 (m : ℕ) (hm : 1 ≤ m) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1) (n2 : ¬ 7 ∣ x2) (n3 : ¬ 7 ∣ x3)
    (n4 : ¬ 7 ∣ x4) (r : ℕ) (hr : r = 2 ∨ r = 4) (r2 : x2 % 7 = 1 * x1 % 7)
    (r3 : x3 % 7 = 1 * x1 % 7) (r4 : x4 % 7 = r * x1 % 7) : T4 m [x1, x2, x3, x4] := by
  obtain ⟨c, hc⟩ := shift_prep m x1 n1
  apply t4_shift m c hm
  simp only [List.map_cons, List.map_nil]
  exact core31 m ((1 + 7 ^ m * c) * x1) ((1 + 7 ^ m * c) * x2) ((1 + 7 ^ m * c) * x3)
    ((1 + 7 ^ m * c) * x4) (shift_nd m c x1 hm n1) r hr (hmul m c 1 _ _ hm r2) (hmul m c 1 _ _ hm r3)
    (hmul m c r _ _ hm r4) hc

theorem A2 (m : ℕ) (hm : 1 ≤ m) (x1 x2 x3 x4 : ℕ) (n1 : ¬ 7 ∣ x1) (n2 : ¬ 7 ∣ x2) (n3 : ¬ 7 ∣ x3)
    (n4 : ¬ 7 ∣ x4) (r3 r4 : ℕ) (hrr : (r3, r4) ∈ [(2, 2), (2, 4), (4, 2)])
    (e2 : x2 % 7 = 1 * x1 % 7) (e3 : x3 % 7 = r3 * x1 % 7) (e4 : x4 % 7 = r4 * x1 % 7) :
    T4 m [x1, x2, x3, x4] := by
  obtain ⟨c, hc⟩ := shift_prep m x1 n1
  apply t4_shift m c hm
  simp only [List.map_cons, List.map_nil]
  exact core2 m ((1 + 7 ^ m * c) * x1) ((1 + 7 ^ m * c) * x2) ((1 + 7 ^ m * c) * x3)
    ((1 + 7 ^ m * c) * x4) (shift_nd m c x1 hm n1) r3 r4 hrr (hmul m c 1 _ _ hm e2)
    (hmul m c r3 _ _ hm e3) (hmul m c r4 _ _ hm e4) hc

/-! ## dispatcher: residues in `{1, 2, 4}` -/

set_option maxHeartbeats 4000000 in
theorem t4_124 (m : ℕ) (hm : 1 ≤ m) (y0 y1 y2 y3 : ℕ) (n0 : ¬ 7 ∣ y0) (n1 : ¬ 7 ∣ y1)
    (n2 : ¬ 7 ∣ y2) (n3 : ¬ 7 ∣ y3)
    (h0 : y0 % 7 = 1 ∨ y0 % 7 = 2 ∨ y0 % 7 = 4) (h1 : y1 % 7 = 1 ∨ y1 % 7 = 2 ∨ y1 % 7 = 4)
    (h2 : y2 % 7 = 1 ∨ y2 % 7 = 2 ∨ y2 % 7 = 4) (h3 : y3 % 7 = 1 ∨ y3 % 7 = 2 ∨ y3 % 7 = 4) :
    T4 m [y0, y1, y2, y3] := by
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3
  · exact t4_sub (A4 m hm y0 y1 y2 y3 n0 n1 n2 n3 (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y2 y0 n1 n3 n2 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y2 y1 n0 n3 n2 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y1 y0 n2 n3 n1 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y2 y1 n0 n3 n2 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y1 y0 n2 n3 n1 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A4 m hm y0 y1 y2 y3 n0 n1 n2 n3 (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y2 y0 n1 n3 n2 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y2 y0 n1 n3 n2 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y1 y2 n0 n3 n1 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y1 y3 n0 n2 n1 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y1 y0 n2 n3 n1 n0 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y3 y2 y1 n0 n3 n2 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y1 y2 y3 y0 n1 n2 n3 n0 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y2 y0 y3 n1 n2 n0 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y2 y3 y1 n0 n2 n3 n1 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y1 y3 y0 y2 n1 n3 n0 n2 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y2 y3 y1 n0 n2 n3 n1 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y0 y1 y3 y2 n0 n1 n3 n2 2 4 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A2 m hm y2 y3 y0 y1 n2 n3 n0 n1 2 2 (by decide) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y3 y2 n0 n1 n3 n2 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 2 (Or.inl rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A31 m hm y0 y1 y2 y3 n0 n1 n2 n3 4 (Or.inr rfl) (by omega) (by omega) (by omega)) (by sub4)
  · exact t4_sub (A4 m hm y0 y1 y2 y3 n0 n1 n2 n3 (by omega) (by omega) (by omega)) (by sub4)

/-! ## sign flips and the main statement -/

theorem pick7 (m : ℕ) {x : ℕ} (hx : ¬ 7 ∣ x) :
    ∃ y, (y = x ∨ y = fl m x) ∧ ¬ 7 ∣ y ∧ (y % 7 = 1 ∨ y % 7 = 2 ∨ y % 7 = 4) := by
  obtain ⟨y, hy, hny, hR⟩ := pick m hx
  refine ⟨y, hy, hny, ?_⟩
  rw [R_of_not_dvd hny] at hR
  have key : ∀ c : ℕ, c < 7 → ((y % 7 : ℕ) : ZMod 7) = (c : ℕ) → y % 7 = c := by
    intro c hc h
    have := (ZMod.natCast_eq_natCast_iff' _ _ 7).mp h
    rw [Nat.mod_mod, Nat.mod_eq_of_lt hc] at this; exact this
  rcases hR with h | h | h
  · exact Or.inl (key 1 (by norm_num) (by rw [h]; rfl))
  · exact Or.inr (Or.inl (key 2 (by norm_num) (by rw [h]; rfl)))
  · exact Or.inr (Or.inr (key 4 (by norm_num) (by rw [h]; rfl)))

theorem lam_coprime (m j k : ℕ) (hm : 1 ≤ m) (h1 : 1 ≤ j) (h5 : j ≤ 5) :
    Nat.Coprime ((1 + 7 ^ m * k) * j) 7 := by
  have p7 : Nat.Prime 7 := by norm_num
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd p7]
  intro h
  rcases (Nat.Prime.dvd_mul p7).mp h with h | h
  · rw [Nat.dvd_iff_mod_eq_zero, show 1 + 7 ^ m * k = (1 + 7 ^ m * k) * 1 by ring, mod7_shift m k 1 hm] at h
    omega
  · omega

theorem t4_el {m j k x y : ℕ} (hm : 1 ≤ m) (h1 : 1 ≤ j) (h5 : j ≤ 5) (hx : ¬ 7 ∣ x)
    (hy : y = x ∨ y = fl m x)
    (hq : qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * y)) ≠ 6) :
    qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 0 ∧ qq m ((1 + 7 ^ m * k) * (j * x)) ≠ 6 := by
  rw [← mul_assoc] at hq ⊢
  exact transfer hm (lam_coprime m j k hm h1 h5) hx hy hq

/-- **Section 5 multiplier statement.** Four level-0 speeds, `m ≥ 1`: some `(1 + 7^m k) j`,
`1 ≤ j ≤ 5`, keeps all four off `q ∈ {0, 6}`. -/
theorem sec5 (m : ℕ) (hm : 1 ≤ m) (x0 x1 x2 x3 : ℕ) (n0 : ¬ 7 ∣ x0) (n1 : ¬ 7 ∣ x1)
    (n2 : ¬ 7 ∣ x2) (n3 : ¬ 7 ∣ x3) : T4 m [x0, x1, x2, x3] := by
  obtain ⟨y0, e0, m0, h0⟩ := pick7 m n0
  obtain ⟨y1, e1, m1, h1⟩ := pick7 m n1
  obtain ⟨y2, e2, m2, h2⟩ := pick7 m n2
  obtain ⟨y3, e3, m3, h3⟩ := pick7 m n3
  obtain ⟨j, k, hj1, hj5, hk, h⟩ := t4_124 m hm y0 y1 y2 y3 m0 m1 m2 m3 h0 h1 h2 h3
  refine ⟨j, k, hj1, hj5, hk, fun x hx => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact t4_el hm hj1 hj5 n0 e0 (h y0 (by simp))
  · exact t4_el hm hj1 hj5 n1 e1 (h y1 (by simp))
  · exact t4_el hm hj1 hj5 n2 e2 (h y2 (by simp))
  · exact t4_el hm hj1 hj5 n3 e3 (h y3 (by simp))

end LRSpectrumFull.BarajasSerra.Sec5
