/-
# Symmetry reduction for the eight-runner Lemma 7 check (atom S1)

For `k = 7` velocities (Rosenfeld's convention, `k + 1 = 8`) and a prime `p > 7`, the Lemma 7 check
`lemma7Check 7 p` (no admissible 7-tuple satisfies the side condition and covers the window) is
equivalent to the same check restricted to the tuples containing `1`.

Argument.  Let `q = 8p` and `‖x‖ = min (x mod q) (q - x mod q)`.  A bad tuple `V` has at most five
even members, hence an odd member `u`, which is a unit mod `q` since `p ∤ u`.  Let `u c ≡ 1 (mod q)`
and `φ v = ‖c v‖`.  Then `φ` maps the admissible set into itself injectively (`v ≡ -w (mod q)` with
`v, w ≤ 4p` forces `v = w = 4p`, a multiple of `p`), preserves parity (`q` even, `c` odd), sends `u`
to `1`, and `‖j φ(v)‖ = ‖(‖c j‖) v‖` with `‖c j‖` again in the window.  So `φ(V)` is a bad tuple
containing `1`.

This is the reduction used by (development file, not part of this archive) in mode `sym1`.
-/

import LRSpectrumFull.LRCFourRunnersCore

namespace LRSpectrumFull

/-- The Lemma 7 check restricted to tuples containing the speed `1`. -/
def lemma7Check1 (k p : ℕ) : Bool :=
  (tuples k p).all (fun V => !(decide (1 ∈ V)) || !(sideOK k V && coversWindow k p V))

namespace EightWLOG

/-- distance from `x` to the nearest multiple of `q` -/
def nrm (q x : ℕ) : ℕ := min (x % q) (q - x % q)

theorem coversAt_eq (k p j v : ℕ) :
    coversAt k p j v = decide ((k + 1) * nrm ((k + 1) * p) (j * v) < (k + 1) * p) := rfl

theorem nrm_cases {q : ℕ} (hq : 0 < q) (b : ℕ) :
    nrm q b ≡ b [MOD q] ∨ nrm q b + b ≡ 0 [MOD q] := by
  unfold nrm
  have hr := Nat.mod_lt b hq
  by_cases h : b % q ≤ q - b % q
  · left; rw [min_eq_left h]; exact Nat.mod_modEq b q
  · right
    rw [min_eq_right (by omega)]
    have hd := Nat.div_add_mod b q
    have : q - b % q + b = q * (b / q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      generalize q * (b / q) = t at hd ⊢
      omega
    unfold Nat.ModEq
    rw [this, Nat.mul_mod_right, Nat.zero_mod]

theorem nrm_congr {q x y : ℕ} (h : x ≡ y [MOD q]) : nrm q x = nrm q y := by
  unfold nrm; rw [h]

theorem nrm_neg {q x y : ℕ} (hq : 0 < q) (h : x + y ≡ 0 [MOD q]) : nrm q x = nrm q y := by
  have hx := Nat.mod_lt x hq
  have hy := Nat.mod_lt y hq
  have h' : (x % q + y % q) % q = 0 := by
    have h0 := h
    unfold Nat.ModEq at h0
    rw [← Nat.add_mod, h0, Nat.zero_mod]
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h'
  have ht2 : t < 2 := by
    by_contra hc
    push Not at hc
    have : q * 2 ≤ q * t := Nat.mul_le_mul_left q hc
    omega
  unfold nrm
  interval_cases t <;> simp at ht <;> omega

theorem nrm_mul_nrm {q : ℕ} (hq : 0 < q) (a b : ℕ) : nrm q (a * nrm q b) = nrm q (a * b) := by
  rcases nrm_cases hq b with h | h
  · exact nrm_congr (h.mul_left a)
  · apply nrm_neg hq
    have := h.mul_left a
    rw [Nat.mul_add, Nat.mul_zero] at this
    exact this

theorem nrm_le (q x : ℕ) : nrm q x ≤ q / 2 := by
  unfold nrm; omega

theorem nrm_pos {q x : ℕ} (hq : 0 < q) (h : x % q ≠ 0) : 0 < nrm q x := by
  have := Nat.mod_lt x hq
  unfold nrm; omega

theorem nrm_inj {q x y : ℕ} (hq : 0 < q) (h : nrm q x = nrm q y) :
    x ≡ y [MOD q] ∨ x + y ≡ 0 [MOD q] := by
  have hx := Nat.mod_lt x hq
  have hy := Nat.mod_lt y hq
  unfold nrm at h
  have : x % q = y % q ∨ x % q + y % q = q := by omega
  rcases this with h1 | h1
  · exact Or.inl h1
  · right
    unfold Nat.ModEq
    rw [Nat.add_mod, h1, Nat.mod_self, Nat.zero_mod]

theorem nrm_mod_two {q : ℕ} (hq : 0 < q) (h2 : 2 ∣ q) (x : ℕ) : nrm q x % 2 = x % 2 := by
  rcases nrm_cases hq x with h | h
  · exact Nat.ModEq.of_dvd h2 h
  · have := Nat.ModEq.of_dvd h2 h
    unfold Nat.ModEq at this
    omega

theorem mem_admissible (k p v : ℕ) :
    v ∈ admissible k p ↔ v < (k + 1) * p / 2 + 1 ∧ 1 ≤ v ∧ v % p ≠ 0 := by
  simp [admissible]

theorem nodup_admissible (k p : ℕ) : (admissible k p).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem coversWindow_iff (k p : ℕ) (V : List ℕ) :
    coversWindow k p V = true ↔
      ∀ j, j ≤ (k + 1) * p / 2 → 1 ≤ j → ∃ v ∈ V, coversAt k p j v = true := by
  simp [coversWindow]
  constructor
  · intro h j hj h1
    rcases h j hj with h0 | h0
    · omega
    · exact h0
  · intro h j hj
    by_cases h0 : j = 0
    · exact Or.inl h0
    · exact Or.inr (h j hj (by omega))

theorem primes_of_eight :
    (List.range (7 + 2)).filter (fun l => 2 ≤ l && (7 + 1) % l == 0 && Nat.Prime l) = [2] := by
  decide

theorem sideOK_seven (V : List ℕ) :
    sideOK 7 V = decide ((V.filter (fun v => v % 2 == 0)).length ≤ 5) := by
  unfold sideOK
  rw [primes_of_eight]
  simp

/-- The map `v ↦ ‖c v‖` sends a bad tuple with an odd member `u` (`u c ≡ 1`) to a bad tuple
containing `1`. -/
theorem exists_bad_with_one (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (V : List ℕ)
    (hV : V ∈ tuples 7 p) (hs : sideOK 7 V = true) (hc : coversWindow 7 p V = true) :
    ∃ V' ∈ tuples 7 p, 1 ∈ V' ∧ sideOK 7 V' = true ∧ coversWindow 7 p V' = true := by
  unfold tuples at hV ⊢
  rw [List.mem_sublistsLen] at hV
  obtain ⟨hsub, hlen⟩ := hV
  have hadm : ∀ v ∈ V, v ∈ admissible 7 p := fun v hv => hsub.subset hv
  set q := (7 + 1) * p with hqdef
  have hq : 0 < q := by omega
  have hW : q / 2 = 4 * p := by omega
  have h2q : 2 ∣ q := ⟨4 * p, by omega⟩
  have hpq : p ∣ q := ⟨8, by omega⟩
  -- an odd member
  rw [sideOK_seven] at hs
  have hodd : ∃ u ∈ V, u % 2 = 1 := by
    by_contra hno
    push Not at hno
    have hall : V.filter (fun v => v % 2 == 0) = V := by
      rw [List.filter_eq_self]
      intro v hv
      have := hno v hv
      simp only [beq_iff_eq]
      omega
    rw [hall, hlen] at hs
    simp at hs
  obtain ⟨u, huV, hu2⟩ := hodd
  have hu := (mem_admissible 7 p u).1 (hadm u huV)
  -- `u` is a unit mod `q`
  have hcop2 : Nat.Coprime u 2 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hu2]; rfl
  have hcop8 : Nat.Coprime u 8 := by simpa using hcop2.pow_right 3
  have hcopp : Nat.Coprime u p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd; exact hu.2.2 (Nat.mod_eq_zero_of_dvd hd)
  have hcopq : Nat.Coprime u q := Nat.Coprime.mul_right hcop8 hcopp
  obtain ⟨c, -, hc1⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopq (by omega)
  have huc : u * c ≡ 1 [MOD q] := by
    unfold Nat.ModEq; rw [hc1, Nat.mod_eq_of_lt (by omega)]
  have hcq : Nat.Coprime c q := Nat.coprime_of_mul_modEq_one u (by rw [Nat.mul_comm]; exact huc)
  have hc2 : c % 2 = 1 := by
    have h1 : u * c % 2 = 1 := by rw [← Nat.mod_mod_of_dvd _ h2q, hc1]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · rw [Nat.mul_mod, h] at h1; simp at h1
    · exact h
  -- `u * (c * x) ≡ x`
  have hback : ∀ x, u * (c * x) ≡ x [MOD q] := by
    intro x
    have := huc.mul_right x
    rwa [Nat.one_mul, Nat.mul_assoc] at this
  -- `c * x` is not `0` mod `q` on the window
  have hnz : ∀ x, 1 ≤ x → x ≤ 4 * p → (c * x) % q ≠ 0 := by
    intro x hx1 hx2 h0
    have hd : q ∣ c * x := Nat.dvd_of_mod_eq_zero h0
    have : q ∣ x := (Nat.Coprime.symm hcq).dvd_of_dvd_mul_left hd
    have := Nat.le_of_dvd (by omega) this
    omega
  let φ : ℕ → ℕ := fun v => nrm q (c * v)
  -- (F1) admissibility
  have hF1 : ∀ v ∈ admissible 7 p, φ v ∈ admissible 7 p := by
    intro v hv
    rw [mem_admissible] at hv ⊢
    refine ⟨?_, ?_, ?_⟩
    · show nrm q (c * v) < _
      have := nrm_le q (c * v); omega
    · exact nrm_pos hq (hnz v hv.2.1 (by omega))
    · intro h0
      have hcv : c * v % p = 0 := by
        rcases nrm_cases hq (c * v) with h | h
        · have := Nat.ModEq.of_dvd hpq h
          unfold Nat.ModEq at this
          change nrm q (c * v) % p = 0 at h0
          omega
        · have := Nat.ModEq.of_dvd hpq h
          unfold Nat.ModEq at this
          change nrm q (c * v) % p = 0 at h0
          rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.zero_mod] at this
          exact this
      rcases (Nat.Prime.dvd_mul hp).1 (Nat.dvd_of_mod_eq_zero hcv) with hdc | hdv
      · have := Nat.Coprime.coprime_dvd_left hdc hcq
        have := Nat.Coprime.eq_one_of_dvd this hpq
        exact hp.one_lt.ne' this
      · exact hv.2.2 (Nat.mod_eq_zero_of_dvd hdv)
  -- (F2) injectivity on the admissible set
  have hF2 : ∀ v ∈ admissible 7 p, ∀ w ∈ admissible 7 p, φ v = φ w → v = w := by
    intro v hv w hw h
    rw [mem_admissible] at hv hw
    rcases nrm_inj hq h with h1 | h1
    · have : v ≡ w [MOD q] := ((hback v).symm.trans (h1.mul_left u)).trans (hback w)
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · have h2 := h1.mul_left u
      rw [Nat.mul_add, Nat.mul_zero] at h2
      have h3 : v + w ≡ 0 [MOD q] := ((hback v).add (hback w)).symm.trans h2
      unfold Nat.ModEq at h3
      rw [Nat.zero_mod] at h3
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h3
      have ht1 : t = 1 := by
        rcases Nat.lt_or_ge t 2 with h | h
        · interval_cases t <;> omega
        · have : q * 2 ≤ q * t := Nat.mul_le_mul_left q h
          omega
      subst ht1
      have hv4 : v = 4 * p := by omega
      exact absurd (by rw [hv4, Nat.mul_mod_left]) hv.2.2
  -- (F3) parity
  have hF3 : ∀ v, φ v % 2 = v % 2 := by
    intro v
    change nrm q (c * v) % 2 = v % 2
    rw [nrm_mod_two hq h2q, Nat.mul_mod, hc2, Nat.one_mul, Nat.mod_mod]
  -- (F4) `φ u = 1`
  have hF4 : φ u = 1 := by
    change nrm q (c * u) = 1
    unfold nrm
    rw [Nat.mul_comm, hc1]
    omega
  -- (F5) the covering identity
  have hF5 : ∀ j v, nrm q (j * φ v) = nrm q (nrm q (c * j) * v) := by
    intro j v
    change nrm q (j * nrm q (c * v)) = nrm q (nrm q (c * j) * v)
    rw [nrm_mul_nrm hq, Nat.mul_comm (nrm q (c * j)) v, nrm_mul_nrm hq]
    congr 1; ring
  -- the image tuple
  have hVnd : V.Nodup := hsub.nodup (nodup_admissible 7 p)
  have hmapnd : (V.map φ).Nodup :=
    List.Nodup.map_on (fun v hv w hw h => hF2 v (hadm v hv) w (hadm w hw) h) hVnd
  refine ⟨(admissible 7 p).filter (fun w => decide (w ∈ V.map φ)), ?_, ?_, ?_, ?_⟩
  · -- membership in `tuples`
    have hperm : List.Perm ((admissible 7 p).filter (fun w => decide (w ∈ V.map φ))) (V.map φ) := by
      rw [List.perm_ext_iff_of_nodup ((nodup_admissible 7 p).filter _) hmapnd]
      intro a
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
        exact hF1 v (hadm v hv)
    rw [List.mem_sublistsLen]
    exact ⟨List.filter_sublist, by rw [hperm.length_eq, List.length_map, hlen]⟩
  · -- `1` belongs to the image
    simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, List.mem_map.2 ⟨u, huV, hF4⟩⟩
    rw [← hF4]; exact hF1 u (hadm u huV)
  · -- the side condition
    have hperm : List.Perm ((admissible 7 p).filter (fun w => decide (w ∈ V.map φ))) (V.map φ) := by
      rw [List.perm_ext_iff_of_nodup ((nodup_admissible 7 p).filter _) hmapnd]
      intro a
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
        exact hF1 v (hadm v hv)
    rw [sideOK_seven, (hperm.filter _).length_eq, List.filter_map, List.length_map]
    have : ((fun v => v % 2 == 0) ∘ φ) = (fun v => v % 2 == 0) := by
      funext v; simp only [Function.comp, hF3]
    rw [this]; exact hs
  · -- the covering
    rw [coversWindow_iff] at hc ⊢
    intro j hj1 hj0
    have hjW : j ≤ 4 * p := by omega
    have hj'1 : 1 ≤ nrm q (c * j) := nrm_pos hq (hnz j hj0 hjW)
    have hj'2 : nrm q (c * j) ≤ (7 + 1) * p / 2 := by have := nrm_le q (c * j); omega
    obtain ⟨v, hv, hcov⟩ := hc (nrm q (c * j)) hj'2 hj'1
    refine ⟨φ v, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hF1 v (hadm v hv), List.mem_map.2 ⟨v, hv, rfl⟩⟩
    · rw [coversAt_eq] at hcov ⊢
      rw [hF5]; exact hcov

end EightWLOG

open EightWLOG in
/-- **Symmetry reduction (S1).**  For a prime `p > 7`, the eight-runner Lemma 7 check holds iff it
holds on the tuples containing `1`. -/
theorem lemma7Check_seven_iff_one (p : ℕ) (hp : p.Prime) (h7 : 7 < p) :
    lemma7Check 7 p = true ↔ lemma7Check1 7 p = true := by
  unfold lemma7Check lemma7Check1
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h V hV
    have := h V hV
    cases h1 : decide (1 ∈ V) <;> simp_all
  · intro h V hV
    by_contra hbad
    have hb : sideOK 7 V = true ∧ coversWindow 7 p V = true := by
      cases h1 : sideOK 7 V <;> cases h2 : coversWindow 7 p V <;> simp_all
    obtain ⟨V', hV', h1, hs', hc'⟩ := exists_bad_with_one p hp h7 V hV hb.1 hb.2
    have := h V' hV'
    simp [h1, hs', hc'] at this

end LRSpectrumFull
