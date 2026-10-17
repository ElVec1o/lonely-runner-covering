/-
# The coprime pigeonhole: an unconditional uniform slice of open territory

At the modulus `q = 2(k+2)` the band condition `q ≤ (k+2)·min(r, q−r)` is exactly `r ∉ {0, 1, q−1}`.
A velocity coprime to `q` forbids exactly the two multipliers `p ≡ ±v⁻¹`, and `v·p ≡ 0` is
impossible for `p ≠ 0`; so `k+1` velocities forbid at most `2(k+1)` of the `2(k+2)−1` nonzero
multipliers — one always survives.  Hence **every family with all velocities coprime to `2(k+2)`
satisfies the Lonely-Runner floor**, uniformly in `k` and with no height restriction.  This is
elementary (possibly folklore; novelty unchecked) but it is, to our knowledge, the first
machine-checked uniform statement here that covers open territory `k ≥ 12`.

Also: two concrete certified verdicts for 18-runner families (`m = 17` velocities, beyond the
literature's `n ≤ 13`), including a forced-multiplier family whose only witnesses have `p ≥ 2`.
-/
import LRSpectrumFull.Delta2CubeWitness

namespace LRSpectrumFull

set_option maxHeartbeats 1600000 in
/-- **The coprime pigeonhole.**  If every velocity is coprime to `2(k+2)`, the floor holds:
some multiplier `p` avoids the `≤ 2(k+1)` forbidden residues `±v_i⁻¹` and the zero multiplier,
and then every runner sits at distance `≥ 2/(2(k+2)) = 1/(k+2)` at time `p/(2(k+2))`. -/
theorem floor_of_coprime_double {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hcop : ∀ i, Nat.Coprime ((v i).toNat) (2 * (k + 2))) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero (2 * (k + 2)) := ⟨by omega⟩
  set F : Fin (k + 1) → Finset (ZMod (2 * (k + 2))) := fun i =>
    Finset.univ.filter (fun p => (((v i).toNat : ZMod (2 * (k + 2))) * p = 1 ∨
      ((v i).toNat : ZMod (2 * (k + 2))) * p = -1)) with hFdef
  have hunit : ∀ i, IsUnit (((v i).toNat : ZMod (2 * (k + 2)))) := fun i =>
    (ZMod.isUnit_iff_coprime _ _).mpr (hcop i)
  have hFcard : ∀ i, (F i).card ≤ 2 := by
    intro i
    obtain ⟨u, hu⟩ := hunit i
    have hsub : F i ⊆ {(↑u⁻¹ : ZMod (2 * (k + 2))) * 1, (↑u⁻¹ : ZMod (2 * (k + 2))) * (-1)} := by
      intro p hp
      rw [hFdef] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rcases hp with h | h
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_self _ _
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (by simp))
  set S : Finset (ZMod (2 * (k + 2))) := insert 0 (Finset.univ.biUnion F) with hSdef
  have hScard : S.card < 2 * (k + 2) := by
    have h1 : S.card ≤ (Finset.univ.biUnion F).card + 1 := Finset.card_insert_le _ _
    have h2 : (Finset.univ.biUnion F).card ≤ ∑ i, (F i).card := Finset.card_biUnion_le
    have h3 : ∑ i : Fin (k + 1), (F i).card ≤ ∑ _i : Fin (k + 1), 2 :=
      Finset.sum_le_sum (fun i _ => hFcard i)
    have h4 : ∑ _i : Fin (k + 1), (2 : ℕ) = 2 * (k + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    omega
  obtain ⟨p, hpS⟩ : ∃ p : ZMod (2 * (k + 2)), p ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod (2 * (k + 2)))) ⊆ S := fun p _ => hcon p
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  rw [hSdef, Finset.mem_insert] at hpS
  push_neg at hpS
  obtain ⟨hp0, hpB⟩ := hpS
  have hpF : ∀ i, ((v i).toNat : ZMod (2 * (k + 2))) * p ≠ 1 ∧
      ((v i).toNat : ZMod (2 * (k + 2))) * p ≠ -1 := by
    intro i
    have hnot : p ∉ F i := fun hmem =>
      hpB (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
    rw [hFdef] at hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    push_neg at hnot
    exact hnot
  refine cube_floor_of_witness v hv p.val (2 * (k + 2)) (by omega) (fun i => ?_)
  obtain ⟨u, hu⟩ := hunit i
  set x : ZMod (2 * (k + 2)) := ((v i).toNat : ZMod (2 * (k + 2))) * p with hxdef
  have hres : (v i).toNat * p.val % (2 * (k + 2)) = x.val := by
    rw [hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hp0
    have hkey := (Units.inv_mul_cancel_left u p).symm
    rw [hu] at hkey
    rw [← hxdef] at hkey
    rw [h0, mul_zero] at hkey
    exact hkey
  have hx1 : x ≠ 1 := by
    have h := (hpF i).1
    rw [← hxdef] at h
    exact h
  have hxm : x ≠ -1 := by
    have h := (hpF i).2
    rw [← hxdef] at h
    exact h
  have hcast : ((x.val : ℕ) : ZMod (2 * (k + 2))) = x := ZMod.natCast_rightInverse x
  have hval0 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
  have hval1 : x.val ≠ 1 := by
    intro h
    apply hx1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : x.val ≠ 2 * (k + 2) - 1 := by
    intro h
    apply hxm
    rw [← hcast, h]
    have h1 : ((2 * (k + 2) - 1 : ℕ) : ZMod (2 * (k + 2)))
        = ((2 * (k + 2) : ℕ) : ZMod (2 * (k + 2))) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : x.val < 2 * (k + 2) := ZMod.val_lt x
  rw [hres]
  have hmin : 2 ≤ min x.val (2 * (k + 2) - x.val) := le_min (by omega) (by omega)
  calc 2 * (k + 2) = (k + 2) * 2 := by ring
    _ ≤ (k + 2) * min x.val (2 * (k + 2) - x.val) := Nat.mul_le_mul_left _ hmin

/-- **Certified verdict, forced family.**  A concrete 18-runner family in open territory
(`m = 17` velocities), everywhere-prime-blocked and with **no** multiplier-1 witness at any
modulus; the floor is certified at the composite modulus `26` with multiplier `11`. -/
theorem lrc_floor_verdict_forced18 :
    1 / (18 : ℝ) ≤ ML ![1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 29, 31] := by
  have h := cube_floor_of_witness (k := 16)
    ![1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 29, 31]
    (by decide) 11 26 (by norm_num) (by decide)
  norm_num at h
  exact h

/-- **Certified verdict, extremal family.**  The extremal 18-runner family `(1, …, 17)`,
certified at `q = 18`, `p = 1`. -/
theorem lrc_floor_verdict_extremal18 :
    1 / (18 : ℝ) ≤ ML ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] := by
  have h := cube_floor_of_witness (k := 16)
    ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
    (by decide) 1 18 (by norm_num) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
/-- **The pair-sum kill-lemma.**  If `Q = 2k+3` is prime, divides no velocity, and **some pair
sums to `Q`**, the floor holds with witness modulus `Q`.  Mechanism: the pair `v a + v b = Q`
means `v b ≡ −v a (mod Q)`, so the two runners' forbidden multiplier sets `{±v⁻¹}` **coincide** —
the `k+1` runners forbid at most `2k` nonzero multipliers of the `2k+2` available, and a survivor
`p` puts every runner's residue outside `{0, ±1}`.  A collision (= a pair sum divisible by the
modulus) is exactly what creates witness room: the mechanism behind the unfilled-pair-sum law. -/
theorem floor_of_pairsum_prime {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hP : Nat.Prime (2 * k + 3))
    (hnd : ∀ l, ¬ ((2 * k + 3 : ℤ) ∣ v l))
    (a b : Fin (k + 1)) (hab : a ≠ b) (hsum : v a + v b = 2 * k + 3) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero (2 * k + 3) := ⟨by omega⟩
  haveI : Fact (Nat.Prime (2 * k + 3)) := ⟨hP⟩
  have hne : ∀ l, ((v l : ℤ) : ZMod (2 * k + 3)) ≠ 0 := by
    intro l h0
    exact hnd l ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  set F : Fin (k + 1) → Finset (ZMod (2 * k + 3)) := fun i =>
    Finset.univ.filter (fun p => (((v i : ℤ) : ZMod (2 * k + 3)) * p = 1 ∨
      ((v i : ℤ) : ZMod (2 * k + 3)) * p = -1)) with hFdef
  have hcb : ((v b : ℤ) : ZMod (2 * k + 3)) = -((v a : ℤ) : ZMod (2 * k + 3)) := by
    have h0 : ((v a : ℤ) : ZMod (2 * k + 3)) + ((v b : ℤ) : ZMod (2 * k + 3)) = 0 := by
      have hcast : (((v a + v b : ℤ)) : ZMod (2 * k + 3)) = 0 := by
        rw [hsum]
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
        push_cast
        exact dvd_refl _
      push_cast at hcast
      exact hcast
    exact eq_neg_of_add_eq_zero_left (by linear_combination h0)
  have hiff : ∀ p : ZMod (2 * k + 3),
      (((v b : ℤ) : ZMod (2 * k + 3)) * p = 1 ∨ ((v b : ℤ) : ZMod (2 * k + 3)) * p = -1) ↔
      (((v a : ℤ) : ZMod (2 * k + 3)) * p = 1 ∨ ((v a : ℤ) : ZMod (2 * k + 3)) * p = -1) := by
    intro p
    rw [hcb, neg_mul]
    constructor
    · rintro (h | h)
      · exact Or.inr (neg_eq_iff_eq_neg.mp h)
      · exact Or.inl (neg_inj.mp h)
    · rintro (h | h)
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, neg_neg])
  have hFab : F b = F a := by
    rw [hFdef]
    exact Finset.filter_congr (fun p _ => hiff p)
  have hFcard : ∀ i, (F i).card ≤ 2 := by
    intro i
    have hu : IsUnit (((v i : ℤ) : ZMod (2 * k + 3))) := Ne.isUnit (hne i)
    obtain ⟨u, hu⟩ := hu
    have hsub : F i ⊆ {(↑u⁻¹ : ZMod (2 * k + 3)) * 1, (↑u⁻¹ : ZMod (2 * k + 3)) * (-1)} := by
      intro p hp
      rw [hFdef] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rcases hp with h | h
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_self _ _
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    rw [Finset.card_singleton]
  set S : Finset (ZMod (2 * k + 3)) := insert 0 ((Finset.univ.erase b).biUnion F) with hSdef
  have hScard : S.card < 2 * k + 3 := by
    have h1 : S.card ≤ ((Finset.univ.erase b).biUnion F).card + 1 := Finset.card_insert_le _ _
    have h2 : ((Finset.univ.erase b).biUnion F).card ≤ ∑ i ∈ Finset.univ.erase b, (F i).card :=
      Finset.card_biUnion_le
    have h3 : ∑ i ∈ Finset.univ.erase b, (F i).card ≤ ∑ _i ∈ Finset.univ.erase b, 2 :=
      Finset.sum_le_sum (fun i _ => hFcard i)
    have h4 : ∑ _i ∈ Finset.univ.erase b, (2 : ℕ) = 2 * k := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    omega
  obtain ⟨p, hpS⟩ : ∃ p : ZMod (2 * k + 3), p ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod (2 * k + 3))) ⊆ S := fun p _ => hcon p
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  rw [hSdef, Finset.mem_insert] at hpS
  push_neg at hpS
  obtain ⟨hp0, hpB⟩ := hpS
  have hpF : ∀ i, ((v i : ℤ) : ZMod (2 * k + 3)) * p ≠ 1 ∧
      ((v i : ℤ) : ZMod (2 * k + 3)) * p ≠ -1 := by
    intro i
    by_cases hib : i = b
    · subst hib
      have hnot : p ∉ F i := by
        rw [hFab]
        intro hmem
        exact hpB (Finset.mem_biUnion.mpr
          ⟨a, Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩, hmem⟩)
      rw [hFdef] at hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push_neg at hnot
      exact hnot
    · have hnot : p ∉ F i := fun hmem =>
        hpB (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_erase.mpr ⟨hib, Finset.mem_univ i⟩, hmem⟩)
      rw [hFdef] at hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push_neg at hnot
      exact hnot
  refine cube_floor_of_witness v hv p.val (2 * k + 3) (by omega) (fun i => ?_)
  set x : ZMod (2 * k + 3) := ((v i : ℤ) : ZMod (2 * k + 3)) * p with hxdef
  have htn : (((v i).toNat : ℕ) : ZMod (2 * k + 3)) = ((v i : ℤ) : ZMod (2 * k + 3)) := by
    exact_mod_cast congrArg (fun z : ℤ => ((z : ℤ) : ZMod (2 * k + 3)))
      (Int.toNat_of_nonneg (hv i).le)
  have hres : (v i).toNat * p.val % (2 * k + 3) = x.val := by
    rw [hxdef, ← htn, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (hne i) (fun h => hp0 h)
  have hx1 : x ≠ 1 := by
    have h := (hpF i).1
    rw [← hxdef] at h
    exact h
  have hxm : x ≠ -1 := by
    have h := (hpF i).2
    rw [← hxdef] at h
    exact h
  have hcast : ((x.val : ℕ) : ZMod (2 * k + 3)) = x := ZMod.natCast_rightInverse x
  have hval0 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
  have hval1 : x.val ≠ 1 := by
    intro h
    apply hx1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : x.val ≠ 2 * k + 3 - 1 := by
    intro h
    apply hxm
    rw [← hcast, h]
    have h1 : ((2 * k + 3 - 1 : ℕ) : ZMod (2 * k + 3))
        = ((2 * k + 3 : ℕ) : ZMod (2 * k + 3)) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : x.val < 2 * k + 3 := ZMod.val_lt x
  rw [hres]
  have hmin : 2 ≤ min x.val (2 * k + 3 - x.val) := le_min (by omega) (by omega)
  calc 2 * k + 3 ≤ (k + 2) * 2 := by omega
    _ ≤ (k + 2) * min x.val (2 * k + 3 - x.val) := Nat.mul_le_mul_left _ hmin

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- **The weighted gcd-cost pigeonhole** (the counting half of the composite coverage ledger).
At `q = 2(k+2)` each velocity forbids at most `c(d)` multipliers, `d = gcd(v, q)`: a unit
(`d = 1`) forbids the two inverses `±v⁻¹`; a resonant velocity (`d > 1`) forbids the `d − 1`
nonzero elements of its annihilator subgroup and can never produce `±1`.  If
`1 + ∑ c(d_l) < 2(k+2)`, a multiplier survives and the floor holds.  Subsumes the coprime
pigeonhole (`all d = 1`) and makes resonance *cheap* (`d = 2` costs `1`). -/
theorem floor_of_gcd_cost {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hcost : 1 + ∑ l, (if Nat.gcd ((v l).toNat) (2 * (k + 2)) = 1 then 2
      else Nat.gcd ((v l).toNat) (2 * (k + 2)) - 1) < 2 * (k + 2)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero (2 * (k + 2)) := ⟨by omega⟩
  set F : Fin (k + 1) → Finset (ZMod (2 * (k + 2))) := fun i =>
    Finset.univ.filter (fun p => ((v i).toNat : ZMod (2 * (k + 2))) * p = 1 ∨
      ((v i).toNat : ZMod (2 * (k + 2))) * p = -1 ∨
      (((v i).toNat : ZMod (2 * (k + 2))) * p = 0 ∧ p ≠ 0)) with hFdef
  have hFcard : ∀ i, (F i).card ≤ (if Nat.gcd ((v i).toNat) (2 * (k + 2)) = 1 then 2
      else Nat.gcd ((v i).toNat) (2 * (k + 2)) - 1) := by
    intro i
    by_cases hd : Nat.gcd ((v i).toNat) (2 * (k + 2)) = 1
    · rw [if_pos hd]
      obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime _ _).mpr hd
      have hsub : F i ⊆ {(↑u⁻¹ : ZMod (2 * (k + 2))) * 1, (↑u⁻¹ : ZMod (2 * (k + 2))) * (-1)} := by
        intro p hp
        rw [hFdef] at hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hkey := (Units.inv_mul_cancel_left u p).symm
        rw [hu] at hkey
        rcases hp with h | h | h
        · rw [h] at hkey
          rw [hkey]
          exact Finset.mem_insert_self _ _
        · rw [h] at hkey
          rw [hkey]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exfalso
          apply h.2
          rw [h.1, mul_zero] at hkey
          exact hkey
      refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
      rw [Finset.card_singleton]
    · rw [if_neg hd]
      have hq0 : 0 < 2 * (k + 2) := by omega
      have hdpos : 0 < Nat.gcd ((v i).toNat) (2 * (k + 2)) :=
        Nat.gcd_pos_of_pos_right _ hq0
      have hd1 : 1 < Nat.gcd ((v i).toNat) (2 * (k + 2)) := by omega
      have hdq : Nat.gcd ((v i).toNat) (2 * (k + 2)) ∣ 2 * (k + 2) := Nat.gcd_dvd_right _ _
      have htd : (2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2))
          * Nat.gcd ((v i).toNat) (2 * (k + 2)) = 2 * (k + 2) := Nat.div_mul_cancel hdq
      have ht0 : 0 < (2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)) :=
        Nat.div_pos (Nat.le_of_dvd hq0 hdq) hdpos
      have hnu : ¬ IsUnit (((v i).toNat : ZMod (2 * (k + 2)))) := by
        rw [ZMod.isUnit_iff_coprime]
        exact hd
      have hmem : ∀ p ∈ F i,
          (2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)) ∣ p.val ∧ p ≠ 0 := by
        intro p hp
        rw [hFdef] at hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rcases hp with h | h | h
        · exact absurd (isUnit_iff_exists_inv.mpr ⟨p, h⟩) hnu
        · exact absurd (isUnit_iff_exists_inv.mpr ⟨-p, by rw [mul_neg, h, neg_neg]⟩) hnu
        · refine ⟨?_, h.2⟩
          have h0 : ((v i).toNat * p.val) % (2 * (k + 2)) = 0 := by
            have hval := congrArg ZMod.val h.1
            rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] at hval
            exact hval
          have hq_dvd : (2 * (k + 2)) ∣ (v i).toNat * p.val := Nat.dvd_of_mod_eq_zero h0
          have hx' : Nat.gcd ((v i).toNat) (2 * (k + 2))
              * ((v i).toNat / Nat.gcd ((v i).toNat) (2 * (k + 2))) = (v i).toNat :=
            Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
          have hcop : Nat.Coprime ((v i).toNat / Nat.gcd ((v i).toNat) (2 * (k + 2)))
              ((2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2))) :=
            Nat.coprime_div_gcd_div_gcd hdpos
          have h2 : Nat.gcd ((v i).toNat) (2 * (k + 2))
              * (((v i).toNat / Nat.gcd ((v i).toNat) (2 * (k + 2))) * p.val)
              = (v i).toNat * p.val := by
            rw [← mul_assoc, hx']
          have h4 : ((2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)))
              * Nat.gcd ((v i).toNat) (2 * (k + 2))
              ∣ Nat.gcd ((v i).toNat) (2 * (k + 2))
              * (((v i).toNat / Nat.gcd ((v i).toNat) (2 * (k + 2))) * p.val) := by
            rw [htd, h2]
            exact hq_dvd
          rw [Nat.mul_comm ((2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)))
            (Nat.gcd ((v i).toNat) (2 * (k + 2)))] at h4
          have h3 : ((2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)))
              ∣ ((v i).toNat / Nat.gcd ((v i).toNat) (2 * (k + 2))) * p.val :=
            (Nat.mul_dvd_mul_iff_left hdpos).mp h4
          exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h3
      have hcard : (F i).card
          ≤ ((Finset.range (Nat.gcd ((v i).toNat) (2 * (k + 2)))).erase 0).card :=
        Finset.card_le_card_of_injOn
        (fun p : ZMod (2 * (k + 2)) =>
          p.val / ((2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2))))
        (fun p hp => by
          obtain ⟨hdvd, hne⟩ := hmem p hp
          have hlt : p.val < 2 * (k + 2) := ZMod.val_lt p
          have hvne : p.val ≠ 0 := fun h => hne ((ZMod.val_eq_zero p).mp h)
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr ?_⟩)
          · show p.val / (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2))) ≠ 0
            have hge : (2 * (k + 2)) / Nat.gcd ((v i).toNat) (2 * (k + 2)) ≤ p.val :=
              Nat.le_of_dvd (by omega) hdvd
            have hpos := Nat.div_pos hge ht0
            omega
          · show p.val / (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2)))
              < Nat.gcd ((v i).toNat) (2 * (k + 2))
            rw [Nat.div_lt_iff_lt_mul ht0]
            calc p.val < 2 * (k + 2) := hlt
              _ = Nat.gcd ((v i).toNat) (2 * (k + 2))
                  * (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2))) := by
                    rw [Nat.mul_comm (Nat.gcd ((v i).toNat) (2 * (k + 2)))
                      (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2)))]
                    exact htd.symm)
        (fun p₁ h₁ p₂ h₂ heq => by
          obtain ⟨hd1', -⟩ := hmem p₁ h₁
          obtain ⟨hd2', -⟩ := hmem p₂ h₂
          have e1 := Nat.div_mul_cancel hd1'
          have e2 := Nat.div_mul_cancel hd2'
          have heq2 : p₁.val / (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2)))
              = p₂.val / (2 * (k + 2) / Nat.gcd ((v i).toNat) (2 * (k + 2))) := heq
          have hveq : p₁.val = p₂.val := by
            rw [← e1, ← e2, heq2]
          rw [← ZMod.natCast_rightInverse p₁, ← ZMod.natCast_rightInverse p₂, hveq])
      calc (F i).card ≤ ((Finset.range (Nat.gcd ((v i).toNat) (2 * (k + 2)))).erase 0).card :=
            hcard
        _ = Nat.gcd ((v i).toNat) (2 * (k + 2)) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  set S : Finset (ZMod (2 * (k + 2))) := insert 0 (Finset.univ.biUnion F) with hSdef
  have hScard : S.card < 2 * (k + 2) := by
    have h1 : S.card ≤ (Finset.univ.biUnion F).card + 1 := Finset.card_insert_le _ _
    have h2 : (Finset.univ.biUnion F).card ≤ ∑ i, (F i).card := Finset.card_biUnion_le
    have h3 : ∑ i, (F i).card
        ≤ ∑ l, (if Nat.gcd ((v l).toNat) (2 * (k + 2)) = 1 then 2
          else Nat.gcd ((v l).toNat) (2 * (k + 2)) - 1) :=
      Finset.sum_le_sum (fun i _ => hFcard i)
    omega
  obtain ⟨p, hpS⟩ : ∃ p : ZMod (2 * (k + 2)), p ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod (2 * (k + 2)))) ⊆ S := fun p _ => hcon p
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  rw [hSdef, Finset.mem_insert] at hpS
  push_neg at hpS
  obtain ⟨hp0, hpB⟩ := hpS
  have hpF : ∀ i, ((v i).toNat : ZMod (2 * (k + 2))) * p ≠ 1 ∧
      ((v i).toNat : ZMod (2 * (k + 2))) * p ≠ -1 ∧
      ((v i).toNat : ZMod (2 * (k + 2))) * p ≠ 0 := by
    intro i
    have hnot : p ∉ F i := fun hmem =>
      hpB (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
    rw [hFdef] at hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    push_neg at hnot
    exact ⟨hnot.1, hnot.2.1, fun h0 => hp0 (hnot.2.2 h0)⟩
  refine cube_floor_of_witness v hv p.val (2 * (k + 2)) (by omega) (fun i => ?_)
  set x : ZMod (2 * (k + 2)) := ((v i).toNat : ZMod (2 * (k + 2))) * p with hxdef
  have hres : (v i).toNat * p.val % (2 * (k + 2)) = x.val := by
    rw [hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    have h := (hpF i).2.2
    rw [← hxdef] at h
    exact h
  have hx1 : x ≠ 1 := by
    have h := (hpF i).1
    rw [← hxdef] at h
    exact h
  have hxm : x ≠ -1 := by
    have h := (hpF i).2.1
    rw [← hxdef] at h
    exact h
  have hcast : ((x.val : ℕ) : ZMod (2 * (k + 2))) = x := ZMod.natCast_rightInverse x
  have hval0 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
  have hval1 : x.val ≠ 1 := by
    intro h
    apply hx1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : x.val ≠ 2 * (k + 2) - 1 := by
    intro h
    apply hxm
    rw [← hcast, h]
    have h1 : ((2 * (k + 2) - 1 : ℕ) : ZMod (2 * (k + 2)))
        = ((2 * (k + 2) : ℕ) : ZMod (2 * (k + 2))) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : x.val < 2 * (k + 2) := ZMod.val_lt x
  rw [hres]
  have hmin : 2 ≤ min x.val (2 * (k + 2) - x.val) := le_min (by omega) (by omega)
  calc 2 * (k + 2) = (k + 2) * 2 := by ring
    _ ≤ (k + 2) * min x.val (2 * (k + 2) - x.val) := Nat.mul_le_mul_left _ hmin

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- **The deduplicated gcd-cost pigeonhole, at any window modulus.**  For `2 ≤ q ≤ 2(k+2)`:
velocities sharing a gcd class `d` with `q` share one annihilator subgroup, so the class costs
`d − 1` **once**; units cost `2` each.  If `1 + 2·#units + ∑_{d ∈ gcd-image, d ≠ 1} (d−1) < q`,
a multiplier survives and the floor holds.  Retires `78%` of the enumerated blocked class. -/
theorem floor_of_gcd_cost_dedup {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q : ℕ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * (k + 2))
    (hcost : 1 + 2 * (Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).card
      + ∑ d ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1,
          (d - 1) < q) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  set Finv : Fin (k + 1) → Finset (ZMod q) := fun i =>
    Finset.univ.filter (fun p => ((v i).toNat : ZMod q) * p = 1 ∨
      ((v i).toNat : ZMod q) * p = -1) with hFdef
  set K : ℕ → Finset (ZMod q) := fun d =>
    Finset.univ.filter (fun p => (q / d) ∣ p.val ∧ p ≠ 0) with hKdef
  have hFcard : ∀ i, Nat.gcd ((v i).toNat) q = 1 → (Finv i).card ≤ 2 := by
    intro i hd
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime _ _).mpr hd
    have hsub : Finv i ⊆ {(↑u⁻¹ : ZMod q) * 1, (↑u⁻¹ : ZMod q) * (-1)} := by
      intro p hp
      rw [hFdef] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rcases hp with h | h
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_self _ _
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    rw [Finset.card_singleton]
  have hKcard : ∀ d, 2 ≤ d → d ∣ q → (K d).card ≤ d - 1 := by
    intro d hd2 hdq
    have ht0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) (by omega)
    have htd : q / d * d = q := Nat.div_mul_cancel hdq
    have hcard : (K d).card ≤ ((Finset.range d).erase 0).card :=
      Finset.card_le_card_of_injOn (fun p => p.val / (q / d))
        (fun p hp => by
          have hp2 : p ∈ K d := Finset.mem_coe.mp hp
          rw [hKdef] at hp2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp2
          obtain ⟨hdvd, hne⟩ := hp2
          have hlt : p.val < q := ZMod.val_lt p
          have hvne : p.val ≠ 0 := fun h => hne ((ZMod.val_eq_zero p).mp h)
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr ?_⟩)
          · show p.val / (q / d) ≠ 0
            have hge : q / d ≤ p.val := Nat.le_of_dvd (by omega) hdvd
            have hpos := Nat.div_pos hge ht0
            omega
          · show p.val / (q / d) < d
            rw [Nat.div_lt_iff_lt_mul ht0]
            calc p.val < q := hlt
              _ = d * (q / d) := by rw [Nat.mul_comm d (q / d)]; exact htd.symm)
        (fun p₁ h₁ p₂ h₂ heq => by
          have h₁2 : p₁ ∈ K d := Finset.mem_coe.mp h₁
          have h₂2 : p₂ ∈ K d := Finset.mem_coe.mp h₂
          rw [hKdef] at h₁2 h₂2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁2 h₂2
          have e1 := Nat.div_mul_cancel h₁2.1
          have e2 := Nat.div_mul_cancel h₂2.1
          have heq2 : p₁.val / (q / d) = p₂.val / (q / d) := heq
          have hveq : p₁.val = p₂.val := by
            rw [← e1, ← e2, heq2]
          rw [← ZMod.natCast_rightInverse p₁, ← ZMod.natCast_rightInverse p₂, hveq])
    calc (K d).card ≤ ((Finset.range d).erase 0).card := hcard
      _ = d - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  set S : Finset (ZMod q) := insert 0
    (((Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).biUnion Finv)
      ∪ ((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K)
    with hSdef
  have hScard : S.card < q := by
    have h1 : S.card ≤
        (((Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).biUnion Finv)
          ∪ ((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K).card
        + 1 := Finset.card_insert_le _ _
    have h2 := Finset.card_union_le
      ((Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).biUnion Finv)
      (((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K)
    have h3 : ((Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).biUnion Finv).card
        ≤ 2 * (Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1)).card := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ l ∈ Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1), (Finv l).card
          ≤ ∑ l ∈ Finset.univ.filter (fun l => Nat.gcd ((v l).toNat) q = 1), 2 :=
            Finset.sum_le_sum (fun l hl => hFcard l (Finset.mem_filter.mp hl).2)
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have h4 : (((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K).card
        ≤ ∑ d ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1,
            (d - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hd1, hdim⟩ := Finset.mem_erase.mp hd
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hdim
      have hdpos : 0 < d := by
        rw [← hl]
        exact Nat.gcd_pos_of_pos_right _ (by omega)
      have hdq : d ∣ q := by
        rw [← hl]
        exact Nat.gcd_dvd_right _ _
      exact hKcard d (by omega) hdq
    omega
  obtain ⟨p, hpS⟩ : ∃ p : ZMod q, p ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod q)) ⊆ S := fun p _ => hcon p
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  rw [hSdef, Finset.mem_insert] at hpS
  push_neg at hpS
  obtain ⟨hp0, hpB⟩ := hpS
  rw [Finset.mem_union] at hpB
  push_neg at hpB
  obtain ⟨hpA, hpK⟩ := hpB
  have hker : ∀ l, ((v l).toNat : ZMod q) * p = 0 →
      (q / Nat.gcd ((v l).toNat) q) ∣ p.val := by
    intro l h1
    have h0 : ((v l).toNat * p.val) % q = 0 := by
      have hval := congrArg ZMod.val h1
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] at hval
      exact hval
    have hq_dvd : q ∣ (v l).toNat * p.val := Nat.dvd_of_mod_eq_zero h0
    have hdpos : 0 < Nat.gcd ((v l).toNat) q := Nat.gcd_pos_of_pos_right _ (by omega)
    have hdq : Nat.gcd ((v l).toNat) q ∣ q := Nat.gcd_dvd_right _ _
    have htd : q / Nat.gcd ((v l).toNat) q * Nat.gcd ((v l).toNat) q = q :=
      Nat.div_mul_cancel hdq
    have hx' : Nat.gcd ((v l).toNat) q * ((v l).toNat / Nat.gcd ((v l).toNat) q)
        = (v l).toNat := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hcop : Nat.Coprime ((v l).toNat / Nat.gcd ((v l).toNat) q)
        (q / Nat.gcd ((v l).toNat) q) := Nat.coprime_div_gcd_div_gcd hdpos
    have h2 : Nat.gcd ((v l).toNat) q
        * (((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val) = (v l).toNat * p.val := by
      rw [← mul_assoc, hx']
    have h4 : (q / Nat.gcd ((v l).toNat) q) * Nat.gcd ((v l).toNat) q
        ∣ Nat.gcd ((v l).toNat) q * (((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val) := by
      rw [htd, h2]
      exact hq_dvd
    rw [Nat.mul_comm (q / Nat.gcd ((v l).toNat) q) (Nat.gcd ((v l).toNat) q)] at h4
    have h3 : (q / Nat.gcd ((v l).toNat) q)
        ∣ ((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val :=
      (Nat.mul_dvd_mul_iff_left hdpos).mp h4
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h3
  have hpF : ∀ i, ((v i).toNat : ZMod q) * p ≠ 1 ∧
      ((v i).toNat : ZMod q) * p ≠ -1 ∧ ((v i).toNat : ZMod q) * p ≠ 0 := by
    intro i
    by_cases hd : Nat.gcd ((v i).toNat) q = 1
    · have hnot : p ∉ Finv i := fun hmem => hpA (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd⟩, hmem⟩)
      rw [hFdef] at hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push_neg at hnot
      refine ⟨hnot.1, hnot.2, ?_⟩
      intro h0
      apply hp0
      obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime _ _).mpr hd
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rw [h0, mul_zero] at hkey
      exact hkey
    · have hnu : ¬ IsUnit (((v i).toNat : ZMod q)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact hd
      refine ⟨?_, ?_, ?_⟩
      · intro h
        exact hnu (isUnit_iff_exists_inv.mpr ⟨p, h⟩)
      · intro h
        exact hnu (isUnit_iff_exists_inv.mpr ⟨-p, by rw [mul_neg, h, neg_neg]⟩)
      · intro h0
        have hdvd := hker i h0
        have hdim : Nat.gcd ((v i).toNat) q
            ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1 :=
          Finset.mem_erase.mpr ⟨hd, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
        have hmemK : p ∈ K (Nat.gcd ((v i).toNat) q) := by
          rw [hKdef]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hdvd, hp0⟩
        exact hpK (Finset.mem_biUnion.mpr ⟨_, hdim, hmemK⟩)
  refine cube_floor_of_witness v hv p.val q (by omega) (fun i => ?_)
  set x : ZMod q := ((v i).toNat : ZMod q) * p with hxdef
  have hres : (v i).toNat * p.val % q = x.val := by
    rw [hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    have h := (hpF i).2.2
    rw [← hxdef] at h
    exact h
  have hx1 : x ≠ 1 := by
    have h := (hpF i).1
    rw [← hxdef] at h
    exact h
  have hxm : x ≠ -1 := by
    have h := (hpF i).2.1
    rw [← hxdef] at h
    exact h
  have hcast : ((x.val : ℕ) : ZMod q) = x := ZMod.natCast_rightInverse x
  have hval0 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
  have hval1 : x.val ≠ 1 := by
    intro h
    apply hx1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : x.val ≠ q - 1 := by
    intro h
    apply hxm
    rw [← hcast, h]
    have h1 : ((q - 1 : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : x.val < q := ZMod.val_lt x
  rw [hres]
  have hmin : 2 ≤ min x.val (q - x.val) := le_min (by omega) (by omega)
  calc q ≤ 2 * (k + 2) := hqle
    _ = (k + 2) * 2 := by ring
    _ ≤ (k + 2) * min x.val (q - x.val) := Nat.mul_le_mul_left _ hmin

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- **The ledger theorem** (merge-complete driver).  At any modulus `2 ≤ q ≤ 2(k+2)`, let `R` be
a set of unit representatives: every unit velocity is congruent to `±v_r` for some `r ∈ R`.
Mirror-congruent units share their forbidden pair `{±v⁻¹}`, so the unit side costs `2·|R|`; each
resonant gcd class `d` costs `d − 1` once.  If `1 + 2|R| + ∑ (d−1) < q`, the floor holds.
With `R` = the distinct `±`-classes this retires `115 500/115 508` of the `m = 17` blocked class;
the eight stragglers are the extremal-type families covered by `floor_of_not_dvd_le`/hybrid. -/
theorem floor_of_ledger {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q : ℕ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * (k + 2))
    (R : Finset (Fin (k + 1)))
    (hRu : ∀ r ∈ R, Nat.gcd ((v r).toNat) q = 1)
    (hrep : ∀ l, Nat.gcd ((v l).toNat) q = 1 → ∃ r ∈ R,
      (((v l).toNat : ZMod q) = ((v r).toNat : ZMod q) ∨
       ((v l).toNat : ZMod q) = -((v r).toNat : ZMod q)))
    (hcost : 1 + 2 * R.card
      + ∑ d ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1,
          (d - 1) < q) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  set Finv : Fin (k + 1) → Finset (ZMod q) := fun i =>
    Finset.univ.filter (fun p => ((v i).toNat : ZMod q) * p = 1 ∨
      ((v i).toNat : ZMod q) * p = -1) with hFdef
  set K : ℕ → Finset (ZMod q) := fun d =>
    Finset.univ.filter (fun p => (q / d) ∣ p.val ∧ p ≠ 0) with hKdef
  have hFcard : ∀ i, Nat.gcd ((v i).toNat) q = 1 → (Finv i).card ≤ 2 := by
    intro i hd
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime _ _).mpr hd
    have hsub : Finv i ⊆ {(↑u⁻¹ : ZMod q) * 1, (↑u⁻¹ : ZMod q) * (-1)} := by
      intro p hp
      rw [hFdef] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rcases hp with h | h
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_self _ _
      · rw [h] at hkey
        rw [hkey]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    rw [Finset.card_singleton]
  have hFeq : ∀ l r, (((v l).toNat : ZMod q) = ((v r).toNat : ZMod q) ∨
      ((v l).toNat : ZMod q) = -((v r).toNat : ZMod q)) → Finv l = Finv r := by
    intro l r hlr
    rw [hFdef]
    rcases hlr with h | h
    · exact Finset.filter_congr (fun p _ => by rw [h])
    · refine Finset.filter_congr (fun p _ => ?_)
      rw [h, neg_mul]
      constructor
      · rintro (h1 | h1)
        · exact Or.inr (neg_eq_iff_eq_neg.mp h1)
        · exact Or.inl (neg_inj.mp h1)
      · rintro (h1 | h1)
        · exact Or.inr (by rw [h1])
        · exact Or.inl (by rw [h1, neg_neg])
  have hKcard : ∀ d, 2 ≤ d → d ∣ q → (K d).card ≤ d - 1 := by
    intro d hd2 hdq
    have ht0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) (by omega)
    have htd : q / d * d = q := Nat.div_mul_cancel hdq
    have hcard : (K d).card ≤ ((Finset.range d).erase 0).card :=
      Finset.card_le_card_of_injOn (fun p => p.val / (q / d))
        (fun p hp => by
          have hp2 : p ∈ K d := Finset.mem_coe.mp hp
          rw [hKdef] at hp2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp2
          obtain ⟨hdvd, hne⟩ := hp2
          have hlt : p.val < q := ZMod.val_lt p
          have hvne : p.val ≠ 0 := fun h => hne ((ZMod.val_eq_zero p).mp h)
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr ?_⟩)
          · show p.val / (q / d) ≠ 0
            have hge : q / d ≤ p.val := Nat.le_of_dvd (by omega) hdvd
            have hpos := Nat.div_pos hge ht0
            omega
          · show p.val / (q / d) < d
            rw [Nat.div_lt_iff_lt_mul ht0]
            calc p.val < q := hlt
              _ = d * (q / d) := by rw [Nat.mul_comm d (q / d)]; exact htd.symm)
        (fun p₁ h₁ p₂ h₂ heq => by
          have h₁2 : p₁ ∈ K d := Finset.mem_coe.mp h₁
          have h₂2 : p₂ ∈ K d := Finset.mem_coe.mp h₂
          rw [hKdef] at h₁2 h₂2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁2 h₂2
          have e1 := Nat.div_mul_cancel h₁2.1
          have e2 := Nat.div_mul_cancel h₂2.1
          have heq2 : p₁.val / (q / d) = p₂.val / (q / d) := heq
          have hveq : p₁.val = p₂.val := by
            rw [← e1, ← e2, heq2]
          rw [← ZMod.natCast_rightInverse p₁, ← ZMod.natCast_rightInverse p₂, hveq])
    calc (K d).card ≤ ((Finset.range d).erase 0).card := hcard
      _ = d - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  set S : Finset (ZMod q) := insert 0 ((R.biUnion Finv)
      ∪ ((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K)
    with hSdef
  have hScard : S.card < q := by
    have h1 : S.card ≤ ((R.biUnion Finv)
        ∪ ((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K).card
        + 1 := Finset.card_insert_le _ _
    have h2 := Finset.card_union_le (R.biUnion Finv)
      (((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K)
    have h3 : (R.biUnion Finv).card ≤ 2 * R.card := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ r ∈ R, (Finv r).card ≤ ∑ _r ∈ R, 2 :=
            Finset.sum_le_sum (fun r hr => hFcard r (hRu r hr))
        _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have h4 : (((Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1).biUnion K).card
        ≤ ∑ d ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1,
            (d - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hd1, hdim⟩ := Finset.mem_erase.mp hd
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hdim
      have hdpos : 0 < d := by
        rw [← hl]
        exact Nat.gcd_pos_of_pos_right _ (by omega)
      have hdq : d ∣ q := by
        rw [← hl]
        exact Nat.gcd_dvd_right _ _
      exact hKcard d (by omega) hdq
    omega
  obtain ⟨p, hpS⟩ : ∃ p : ZMod q, p ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod q)) ⊆ S := fun p _ => hcon p
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  rw [hSdef, Finset.mem_insert] at hpS
  push_neg at hpS
  obtain ⟨hp0, hpB⟩ := hpS
  rw [Finset.mem_union] at hpB
  push_neg at hpB
  obtain ⟨hpA, hpK⟩ := hpB
  have hker : ∀ l, ((v l).toNat : ZMod q) * p = 0 →
      (q / Nat.gcd ((v l).toNat) q) ∣ p.val := by
    intro l h1
    have h0 : ((v l).toNat * p.val) % q = 0 := by
      have hval := congrArg ZMod.val h1
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] at hval
      exact hval
    have hq_dvd : q ∣ (v l).toNat * p.val := Nat.dvd_of_mod_eq_zero h0
    have hdpos : 0 < Nat.gcd ((v l).toNat) q := Nat.gcd_pos_of_pos_right _ (by omega)
    have hdq : Nat.gcd ((v l).toNat) q ∣ q := Nat.gcd_dvd_right _ _
    have htd : q / Nat.gcd ((v l).toNat) q * Nat.gcd ((v l).toNat) q = q :=
      Nat.div_mul_cancel hdq
    have hx' : Nat.gcd ((v l).toNat) q * ((v l).toNat / Nat.gcd ((v l).toNat) q)
        = (v l).toNat := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hcop : Nat.Coprime ((v l).toNat / Nat.gcd ((v l).toNat) q)
        (q / Nat.gcd ((v l).toNat) q) := Nat.coprime_div_gcd_div_gcd hdpos
    have h2 : Nat.gcd ((v l).toNat) q
        * (((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val) = (v l).toNat * p.val := by
      rw [← mul_assoc, hx']
    have h4 : (q / Nat.gcd ((v l).toNat) q) * Nat.gcd ((v l).toNat) q
        ∣ Nat.gcd ((v l).toNat) q * (((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val) := by
      rw [htd, h2]
      exact hq_dvd
    rw [Nat.mul_comm (q / Nat.gcd ((v l).toNat) q) (Nat.gcd ((v l).toNat) q)] at h4
    have h3 : (q / Nat.gcd ((v l).toNat) q)
        ∣ ((v l).toNat / Nat.gcd ((v l).toNat) q) * p.val :=
      (Nat.mul_dvd_mul_iff_left hdpos).mp h4
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h3
  have hpF : ∀ i, ((v i).toNat : ZMod q) * p ≠ 1 ∧
      ((v i).toNat : ZMod q) * p ≠ -1 ∧ ((v i).toNat : ZMod q) * p ≠ 0 := by
    intro i
    by_cases hd : Nat.gcd ((v i).toNat) q = 1
    · obtain ⟨r, hrR, hlr⟩ := hrep i hd
      have heqF := hFeq i r hlr
      have hnot : p ∉ Finv i := by
        rw [heqF]
        exact fun hmem => hpA (Finset.mem_biUnion.mpr ⟨r, hrR, hmem⟩)
      rw [hFdef] at hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push_neg at hnot
      refine ⟨hnot.1, hnot.2, ?_⟩
      intro h0
      apply hp0
      obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime _ _).mpr hd
      have hkey := (Units.inv_mul_cancel_left u p).symm
      rw [hu] at hkey
      rw [h0, mul_zero] at hkey
      exact hkey
    · have hnu : ¬ IsUnit (((v i).toNat : ZMod q)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact hd
      refine ⟨?_, ?_, ?_⟩
      · intro h
        exact hnu (isUnit_iff_exists_inv.mpr ⟨p, h⟩)
      · intro h
        exact hnu (isUnit_iff_exists_inv.mpr ⟨-p, by rw [mul_neg, h, neg_neg]⟩)
      · intro h0
        have hdvd := hker i h0
        have hdim : Nat.gcd ((v i).toNat) q
            ∈ (Finset.univ.image (fun l : Fin (k + 1) => Nat.gcd ((v l).toNat) q)).erase 1 :=
          Finset.mem_erase.mpr ⟨hd, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
        have hmemK : p ∈ K (Nat.gcd ((v i).toNat) q) := by
          rw [hKdef]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hdvd, hp0⟩
        exact hpK (Finset.mem_biUnion.mpr ⟨_, hdim, hmemK⟩)
  refine cube_floor_of_witness v hv p.val q (by omega) (fun i => ?_)
  set x : ZMod q := ((v i).toNat : ZMod q) * p with hxdef
  have hres : (v i).toNat * p.val % q = x.val := by
    rw [hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    have h := (hpF i).2.2
    rw [← hxdef] at h
    exact h
  have hx1 : x ≠ 1 := by
    have h := (hpF i).1
    rw [← hxdef] at h
    exact h
  have hxm : x ≠ -1 := by
    have h := (hpF i).2.1
    rw [← hxdef] at h
    exact h
  have hcast : ((x.val : ℕ) : ZMod q) = x := ZMod.natCast_rightInverse x
  have hval0 : x.val ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
  have hval1 : x.val ≠ 1 := by
    intro h
    apply hx1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : x.val ≠ q - 1 := by
    intro h
    apply hxm
    rw [← hcast, h]
    have h1 : ((q - 1 : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : x.val < q := ZMod.val_lt x
  rw [hres]
  have hmin : 2 ≤ min x.val (q - x.val) := le_min (by omega) (by omega)
  calc q ≤ 2 * (k + 2) := hqle
    _ = (k + 2) * 2 := by ring
    _ ≤ (k + 2) * min x.val (q - x.val) := Nat.mul_le_mul_left _ hmin

end LRSpectrumFull
