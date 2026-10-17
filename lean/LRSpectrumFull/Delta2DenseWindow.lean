/-
# The dense window is settled whenever `2m+1` is prime

Tao (arXiv:1701.02048, Prop. 1.5) proves the Lonely-Runner floor for velocities in `[1, 1.2m]`
and names `[1, 2m]` as "a natural target"; it is Problem 6 of the Perarnau-Serra survey.  The
survey records that the case `v_1 = 1` is the obstruction: everything with `min v >= 2` is easy.

This file proves the target **outright, uniformly in `m`, for every `m` with `2m+1` prime**
(equivalently `m = (p-1)/2` for an odd prime `p` -- infinitely many `m`).  Three cases:

* `1 ∉ V`  : `t = 1/(2m+2)` works, since every `v ∈ [2, 2m]` has `min(v, 2m+2-v) >= 2`.
* some `q <= m+1` divides no velocity : `t = 1/q` works (`floor_of_not_dvd_le`).
* otherwise `1 ∈ V` and every `q <= m+1` divides some velocity.  Then `q = m+1` forces
  `m+1 ∈ V` (its only multiple in `[1,2m]`), and `q = m` forces `m ∈ V` or `2m ∈ V`.  Either
  `(m) + (m+1) = 2m+1` or `(1) + (2m) = 2m+1`, so the pair-sum kill-lemma applies.

No distinctness hypothesis is needed, matching the form of Tao's Proposition 1.5.
-/
import LRSpectrumFull.Delta2Pigeonhole
import LRSpectrumFull.Delta2DigitGreedy
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient

namespace LRSpectrumFull

set_option maxHeartbeats 1600000 in
/-- **The dense window, settled for prime `2m+1`.**  With `m = k+1` velocities, all positive and
at most `2m`, and `2m+1 = 2k+3` prime, the Lonely-Runner floor `1/(m+1)` holds. -/
theorem dense_floor_of_prime {k : ℕ} (hk : 1 ≤ k) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, 0 < v i) (hd : ∀ i, v i ≤ 2 * ((k : ℤ) + 1))
    (hP : Nat.Prime (2 * k + 3)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub : ∀ i, (v i).toNat ≤ 2 * k + 2 := by
    intro i
    have h := hd i
    have hc := hnat i
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h := hv i
    have hc := hnat i
    omega
  by_cases h1 : ∃ i, v i = 1
  · obtain ⟨i1, hi1⟩ := h1
    by_cases hres : ∀ q : ℕ, 2 ≤ q → q ≤ k + 2 → ∃ i, q ∣ (v i).toNat
    · -- fully resonant: the two forced divisibilities produce a pair summing to `2k+3`
      have hnd : ∀ l, ¬ ((2 * (k : ℤ) + 3) ∣ v l) := by
        intro l hdvd
        have h1' : (2 * (k : ℤ) + 3) ≤ v l := Int.le_of_dvd (hv l) hdvd
        have h2 := hd l
        linarith
      obtain ⟨ib, cb, hcb⟩ := hres (k + 2) (by omega) (le_refl _)
      have hb : (v ib).toNat = k + 2 := by
        have h1' := hub ib
        have h2 := hlb ib
        rcases Nat.lt_or_ge cb 2 with h | h
        · interval_cases cb <;> omega
        · exfalso
          have hmul : (k + 2) * 2 ≤ (k + 2) * cb := Nat.mul_le_mul_left _ h
          omega
      have hbZ : v ib = (k : ℤ) + 2 := by
        have := hnat ib
        omega
      obtain ⟨ia, ca, hca⟩ := hres (k + 1) (by omega) (by omega)
      have ha : (v ia).toNat = k + 1 ∨ (v ia).toNat = 2 * k + 2 := by
        have h1' := hub ia
        have h2 := hlb ia
        rcases Nat.lt_or_ge ca 3 with h | h
        · interval_cases ca <;> omega
        · exfalso
          have hmul : (k + 1) * 3 ≤ (k + 1) * ca := Nat.mul_le_mul_left _ h
          omega
      rcases ha with ha | ha
      · -- `v ia = m`, `v ib = m+1`, and `m + (m+1) = 2m+1`
        have haZ : v ia = (k : ℤ) + 1 := by
          have := hnat ia
          omega
        refine floor_of_pairsum_prime v hv hP hnd ia ib ?_ ?_
        · intro hab
          rw [hab, hbZ] at haZ
          omega
        · rw [haZ, hbZ]
          ring
      · -- `v ia = 2m` and `1 ∈ V`, and `1 + 2m = 2m+1`
        have haZ : v ia = 2 * (k : ℤ) + 2 := by
          have := hnat ia
          omega
        refine floor_of_pairsum_prime v hv hP hnd i1 ia ?_ ?_
        · intro hab
          rw [hab, haZ] at hi1
          omega
        · rw [hi1, haZ]
          ring
    · -- some `q <= m+1` divides no velocity
      push_neg at hres
      obtain ⟨q, hq2, hqk, hq⟩ := hres
      exact floor_of_not_dvd_le q hq2 hqk v hv hq
  · -- `1 ∉ V`: the witness `t = 1/(2m+2)`
    push_neg at h1
    refine cube_floor_of_witness v hv 1 (2 * k + 4) (by omega) (fun i => ?_)
    rw [mul_one]
    have hne : (v i).toNat ≠ 1 := by
      intro h
      exact h1 i (by have := hnat i; omega)
    have hlow : 2 ≤ (v i).toNat := by
      have := hlb i
      omega
    have hmod : (v i).toNat % (2 * k + 4) = (v i).toNat :=
      Nat.mod_eq_of_lt (by have := hub i; omega)
    rw [hmod]
    have hmin : 2 ≤ min ((v i).toNat) (2 * k + 4 - (v i).toNat) := by
      have := hub i
      omega
    calc 2 * k + 4 = (k + 2) * 2 := by ring
      _ ≤ (k + 2) * min ((v i).toNat) (2 * k + 4 - (v i).toNat) :=
          Nat.mul_le_mul_left _ hmin

/-! ## The missed-class criterion: the engine, with no primality hypothesis -/

set_option maxHeartbeats 1600000 in
/-- **Theorem E (missed sign-class).**  Work at the modulus `q = 2m+1` (`m = k+1` velocities), all
of which lie in `[1, 2m]`, so none is `0` mod `q`.  If some *unit* residue class `c` is missed —
no velocity is `≡ ±c` — then the multiplier `c⁻¹` puts every velocity outside `{0, ±1}` mod `q`,
hence at distance `>= 2/(2m+1) > 1/(m+1)`.  No primality of `2m+1` is required; for `2m+1` prime
this is equivalent to a collision, which is what the pair-sum kill-lemma produces. -/
theorem floor_of_missed_class {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, 0 < v i) (hd : ∀ i, v i ≤ 2 * ((k : ℤ) + 1))
    (c : ZMod (2 * k + 3)) (hc : IsUnit c)
    (hmiss : ∀ i, ((v i).toNat : ZMod (2 * k + 3)) ≠ c ∧
      ((v i).toNat : ZMod (2 * k + 3)) ≠ -c) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero (2 * k + 3) := ⟨by omega⟩
  obtain ⟨u, hu⟩ := hc
  set a : ZMod (2 * k + 3) := (↑u⁻¹ : ZMod (2 * k + 3)) with hadef
  have hca : c * a = 1 := by
    rw [hadef, ← hu]
    exact u.mul_inv
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub : ∀ i, (v i).toNat ≤ 2 * k + 2 := by
    intro i
    have h := hd i
    have hc' := hnat i
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h := hv i
    have hc' := hnat i
    omega
  refine cube_floor_of_witness v hv a.val (2 * k + 3) (by omega) (fun i => ?_)
  set x : ZMod (2 * k + 3) := ((v i).toNat : ZMod (2 * k + 3)) with hxdef
  set r : ZMod (2 * k + 3) := x * a with hrdef
  have hres : (v i).toNat * a.val % (2 * k + 3) = r.val := by
    rw [hrdef, hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  -- `x` is a nonzero residue since `1 <= v i <= 2k+2 < 2k+3`
  have hxval : x.val = (v i).toNat := by
    rw [hxdef, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by have := hub i; omega)
  have hx0 : x ≠ 0 := by
    intro h0
    have := hlb i
    rw [h0, ZMod.val_zero] at hxval
    omega
  -- multiplication by the unit `a` is injective, so `r ≠ 0`
  have hr0 : r ≠ 0 := by
    intro h0
    apply hx0
    have h2 : r * c = 0 := by rw [h0, zero_mul]
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hr1 : r ≠ 1 := by
    intro h1
    refine (hmiss i).1 ?_
    have h2 : r * c = c := by rw [h1, one_mul]
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hrm : r ≠ -1 := by
    intro h1
    refine (hmiss i).2 ?_
    have h2 : r * c = -c := by rw [h1]; ring
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hcast : ((r.val : ℕ) : ZMod (2 * k + 3)) = r := ZMod.natCast_rightInverse r
  have hval0 : r.val ≠ 0 := fun h => hr0 ((ZMod.val_eq_zero r).mp h)
  have hval1 : r.val ≠ 1 := by
    intro h
    apply hr1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : r.val ≠ 2 * k + 3 - 1 := by
    intro h
    apply hrm
    rw [← hcast, h]
    have h1 : ((2 * k + 3 - 1 : ℕ) : ZMod (2 * k + 3))
        = ((2 * k + 3 : ℕ) : ZMod (2 * k + 3)) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : r.val < 2 * k + 3 := ZMod.val_lt r
  rw [hres]
  have hmin : 2 ≤ min r.val (2 * k + 3 - r.val) := le_min (by omega) (by omega)
  calc 2 * k + 3 ≤ (k + 2) * 2 := by omega
    _ ≤ (k + 2) * min r.val (2 * k + 3 - r.val) := Nat.mul_le_mul_left _ hmin

/-! ## The perturbation theorem: families concentrated near the extremal segment -/

set_option maxHeartbeats 1600000 in
/-- **Theorem E' (missed class at an arbitrary modulus).**  For any `2 <= q <= 2(k+2)` dividing no
velocity, a missed unit class gives the floor.  Generalises `floor_of_missed_class`. -/
theorem floor_of_missed_class_gen {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q : ℕ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * (k + 2))
    (hnd : ∀ i, ¬ ((q : ℤ) ∣ v i))
    (c : ZMod q) (hc : IsUnit c)
    (hmiss : ∀ i, ((v i).toNat : ZMod q) ≠ c ∧ ((v i).toNat : ZMod q) ≠ -c) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨u, hu⟩ := hc
  set a : ZMod q := (↑u⁻¹ : ZMod q) with hadef
  have hca : c * a = 1 := by
    rw [hadef, ← hu]
    exact u.mul_inv
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  refine cube_floor_of_witness v hv a.val q (by omega) (fun i => ?_)
  set x : ZMod q := ((v i).toNat : ZMod q) with hxdef
  set r : ZMod q := x * a with hrdef
  have hres : (v i).toNat * a.val % q = r.val := by
    rw [hrdef, hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    intro h0
    refine hnd i ?_
    have h0' : (((v i).toNat : ℕ) : ZMod q) = 0 := by rw [← hxdef]; exact h0
    obtain ⟨e, he⟩ := (CharP.cast_eq_zero_iff (ZMod q) q _).mp h0'
    refine ⟨(e : ℤ), ?_⟩
    have hn := hnat i
    rw [← hn, he]
    push_cast
    ring
  have hr0 : r ≠ 0 := by
    intro h0
    apply hx0
    have h2 : r * c = 0 := by rw [h0, zero_mul]
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hr1 : r ≠ 1 := by
    intro h1
    refine (hmiss i).1 ?_
    have h2 : r * c = c := by rw [h1, one_mul]
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hrm : r ≠ -1 := by
    intro h1
    refine (hmiss i).2 ?_
    have h2 : r * c = -c := by rw [h1]; ring
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  have hcast : ((r.val : ℕ) : ZMod q) = r := ZMod.natCast_rightInverse r
  have hval0 : r.val ≠ 0 := fun h => hr0 ((ZMod.val_eq_zero r).mp h)
  have hval1 : r.val ≠ 1 := by
    intro h
    apply hr1
    rw [← hcast, h, Nat.cast_one]
  have hvalm : r.val ≠ q - 1 := by
    intro h
    apply hrm
    rw [← hcast, h]
    have h1 : ((q - 1 : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [h1, ZMod.natCast_self, zero_sub]
  have hlt : r.val < q := ZMod.val_lt r
  rw [hres]
  have hmin : 2 ≤ min r.val (q - r.val) := le_min (by omega) (by omega)
  calc q ≤ 2 * (k + 2) := hqle
    _ = (k + 2) * 2 := by ring
    _ ≤ (k + 2) * min r.val (q - r.val) := Nat.mul_le_mul_left _ hmin

set_option maxHeartbeats 1600000 in
/-- **Theorem F (perturbations of the extremal segment).**  If every velocity is at most `m+1`
(`m = k+1`) and some `j` with `2j <= m+1` is *not* a velocity, the floor holds.  The witness is
`q = 1 + j(⌊m/j⌋ + 2)`, which satisfies `m+1+j < q <= 2m+2` and `q ≡ 1 (mod j)`: the class of `j`
meets `[1, m+1]` only in `j` itself, so it is missed, and Theorem E' applies.

The `m` velocities in `[1, m+1]` omit exactly one value; when the omitted value exceeds
`(m+1)/2` the family is instead covered by `floor_of_not_dvd_le`.  Together these settle every
family concentrated on the extremal segment. -/
theorem floor_of_small_gap {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, v i ≤ (k : ℤ) + 2)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : 2 * j ≤ k + 2)
    (hgap : ∀ i, v i ≠ (j : ℤ)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set t : ℕ := (k + 1) / j with ht
  set q : ℕ := 1 + j * (t + 2) with hqdef
  have hA : j * t + (k + 1) % j = k + 1 := Nat.div_add_mod (k + 1) j
  have hmod : (k + 1) % j < j := Nat.mod_lt _ (by omega)
  have hqexp : q = j * t + 2 * j + 1 := by rw [hqdef]; ring
  have hqlb : k + 2 + j < q := by omega
  have hqub : q ≤ 2 * (k + 2) := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime j q := by
    have h1 : Nat.gcd j q ∣ j := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd j q ∣ q := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd j q ∣ j * (t + 2) := Dvd.dvd.mul_right h1 _
    have h5 : q = j * (t + 2) + 1 := by rw [hqdef]; ring
    have h2' : Nat.gcd j q ∣ j * (t + 2) + 1 := by rw [← h5]; exact h2
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h2')
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub : ∀ i, (v i).toNat ≤ k + 2 := by
    intro i
    have h := hd i
    have hc := hnat i
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h := hv i
    have hc := hnat i
    omega
  refine floor_of_missed_class_gen v hv q (by omega) hqub (fun i => ?_)
    ((j : ℕ) : ZMod q) ((ZMod.isUnit_iff_coprime j q).mpr hcop) (fun i => ⟨?_, ?_⟩)
  · intro hdvd
    have h1 : (q : ℤ) ≤ v i := Int.le_of_dvd (hv i) hdvd
    have h2 := hd i
    have h3 : ((q : ℕ) : ℤ) = (q : ℤ) := by push_cast; ring
    omega
  · -- `v i ≠ j` as residues: both are `< q`
    intro heq
    have hjq : j < q := by omega
    have hviq : (v i).toNat < q := by have := hub i; omega
    have h1 : ((v i).toNat : ZMod q).val = ((j : ℕ) : ZMod q).val := by rw [heq]
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hviq, Nat.mod_eq_of_lt hjq] at h1
    refine hgap i ?_
    have := hnat i
    omega
  · -- `v i ≠ -j`: that would force `v i = q - j > k + 2`
    intro heq
    have hjq : j < q := by omega
    have hviq : (v i).toNat < q := by have := hub i; omega
    have hneg : ((j : ℕ) : ZMod q) + ((v i).toNat : ZMod q) = 0 := by
      rw [heq]
      ring
    have hdvd : q ∣ j + (v i).toNat := by
      have hc2 : ((j + (v i).toNat : ℕ) : ZMod q) = 0 := by
        rw [Nat.cast_add]
        exact hneg
      exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp hc2
    have h1 := hlb i
    have h2 := hub i
    obtain ⟨e, he⟩ := hdvd
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · interval_cases e <;> omega
    · have : q * 2 ≤ q * e := Nat.mul_le_mul_left _ hge
      omega

/-! ## The full driver ladder: missed classes at band `b` -/

set_option maxHeartbeats 1600000 in
/-- **Theorem E^(b) (the ladder).**  At a modulus `q <= b·(k+2)` dividing no velocity, suppose
some unit `c` has *all* of the classes `c, 2c, …, (b-1)c` missed — no velocity is `≡ ±jc` for
`1 <= j < b`.  Then the floor holds: the multiplier `c⁻¹` pushes every residue outside
`{0, ±1, …, ±(b-1)}`, so each distance is at least `b/q >= 1/(k+2)`.

`b = 2` is `floor_of_missed_class_gen`; `b = 3` (below) covers the families that admit no witness
at any window modulus `q <= 2(k+2)`. -/
theorem floor_of_missed_classes {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q b : ℕ) (hb : 1 ≤ b) (hq2 : 2 ≤ q) (hqle : q ≤ b * (k + 2))
    (hnd : ∀ i, ¬ ((q : ℤ) ∣ v i))
    (c : ZMod q) (hc : IsUnit c)
    (hmiss : ∀ i, ∀ j : ℕ, 1 ≤ j → j < b →
      ((v i).toNat : ZMod q) ≠ (j : ZMod q) * c ∧
      ((v i).toNat : ZMod q) ≠ -((j : ZMod q) * c)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨u, hu⟩ := hc
  set a : ZMod q := (↑u⁻¹ : ZMod q) with hadef
  have hca : c * a = 1 := by
    rw [hadef, ← hu]
    exact u.mul_inv
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  refine cube_floor_of_witness v hv a.val q (by omega) (fun i => ?_)
  set x : ZMod q := ((v i).toNat : ZMod q) with hxdef
  set r : ZMod q := x * a with hrdef
  have hres : (v i).toNat * a.val % q = r.val := by
    rw [hrdef, hxdef, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hx0 : x ≠ 0 := by
    intro h0
    refine hnd i ?_
    have h0' : (((v i).toNat : ℕ) : ZMod q) = 0 := by rw [← hxdef]; exact h0
    obtain ⟨e, he⟩ := (CharP.cast_eq_zero_iff (ZMod q) q _).mp h0'
    refine ⟨(e : ℤ), ?_⟩
    have hn := hnat i
    rw [← hn, he]
    push_cast
    ring
  have hr0 : r ≠ 0 := by
    intro h0
    apply hx0
    have h2 : r * c = 0 := by rw [h0, zero_mul]
    rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
    exact h2
  -- transfer the missed classes from `x` to the residue `r`
  have hrj : ∀ j : ℕ, 1 ≤ j → j < b → r ≠ (j : ZMod q) ∧ r ≠ -((j : ZMod q)) := by
    intro j hj1 hj2
    constructor
    · intro hEq
      refine (hmiss i j hj1 hj2).1 ?_
      have h2 : r * c = (j : ZMod q) * c := by rw [hEq]
      rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
      exact h2
    · intro hEq
      refine (hmiss i j hj1 hj2).2 ?_
      have h2 : r * c = -((j : ZMod q)) * c := by rw [hEq]
      rw [hrdef, mul_assoc, mul_comm a c, hca, mul_one] at h2
      exact h2.trans (neg_mul _ _)
  have hrv : ((r.val : ℕ) : ZMod q) = r := ZMod.natCast_rightInverse r
  have hval0 : r.val ≠ 0 := fun h => hr0 ((ZMod.val_eq_zero r).mp h)
  have hlt : r.val < q := ZMod.val_lt r
  have hge : b ≤ r.val := by
    by_contra hcon
    push_neg at hcon
    have hpos : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr hval0
    exact (hrj r.val hpos hcon).1 hrv.symm
  have hle : r.val + b ≤ q := by
    by_contra hcon
    push_neg at hcon
    have hj1 : 1 ≤ q - r.val := by omega
    have hj2 : q - r.val < b := by omega
    refine (hrj (q - r.val) hj1 hj2).2 ?_
    have hsum : (q - r.val) + r.val = q := by omega
    have hz : (((q - r.val : ℕ)) : ZMod q) + r = 0 := by
      have hc2 := congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) hsum
      simp only [Nat.cast_add] at hc2
      rw [hrv, ZMod.natCast_self] at hc2
      exact hc2
    linear_combination hz
  rw [hres]
  have hmin : b ≤ min r.val (q - r.val) := le_min hge (by omega)
  calc q ≤ b * (k + 2) := hqle
    _ = (k + 2) * b := by ring
    _ ≤ (k + 2) * min r.val (q - r.val) := Nat.mul_le_mul_left _ hmin

/-- **The `b = 3` rung.**  At `q <= 3(k+2)` dividing no velocity, if some unit `c` has *both* the
class of `c` and the class of `2c` missed, the floor holds.  This is the criterion that certifies
the families admitting no witness at any window modulus `q <= 2(k+2)`. -/
theorem floor_of_missed_class_pair {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q : ℕ) (hq2 : 2 ≤ q) (hqle : q ≤ 3 * (k + 2))
    (hnd : ∀ i, ¬ ((q : ℤ) ∣ v i))
    (c : ZMod q) (hc : IsUnit c)
    (h1 : ∀ i, ((v i).toNat : ZMod q) ≠ c ∧ ((v i).toNat : ZMod q) ≠ -c)
    (h2 : ∀ i, ((v i).toNat : ZMod q) ≠ 2 * c ∧ ((v i).toNat : ZMod q) ≠ -(2 * c)) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  refine floor_of_missed_classes v hv q 3 (by omega) hq2 hqle hnd c hc (fun i j hj1 hj2 => ?_)
  interval_cases j
  · simpa using h1 i
  · have := h2 i
    norm_num
    exact this

/-! ## The counting rung: a witness from cardinalities alone -/

set_option maxHeartbeats 1600000 in
/-- **Theorem H (counting rung).**  At a modulus `q <= 2(k+2)` dividing no velocity, let `S` index
the velocities that are units mod `q` (any superset will do) and let `Un` be any set of units of
`ZMod q`.  If `2·|S| < |Un|`, the floor holds.

Each unit velocity forbids only the two classes `±v`, so the `|S|` unit velocities rule out at
most `2|S|` of the `|Un|` candidates; a survivor `c` is a missed class and Theorem E' applies.
Non-unit velocities are automatically compatible, since `c` and `-c` are units.  Taking `Un` to be
all of the units gives the recognisable form `2·#{units among the velocities} < φ(q)`. -/
theorem floor_of_unit_count {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (q : ℕ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * (k + 2))
    (hnd : ∀ i, ¬ ((q : ℤ) ∣ v i))
    (S : Finset (Fin (k + 1)))
    (hS : ∀ i, IsUnit (((v i).toNat : ZMod q)) → i ∈ S)
    (Un : Finset (ZMod q)) (hUn : ∀ c ∈ Un, IsUnit c)
    (hcard : 2 * S.card < Un.card) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  set B : Finset (ZMod q) :=
    (S.image (fun i => (((v i).toNat : ℕ) : ZMod q))) ∪
    (S.image (fun i => -(((v i).toNat : ℕ) : ZMod q))) with hBdef
  have hBcard : B.card ≤ 2 * S.card := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := S) (f := fun i => (((v i).toNat : ℕ) : ZMod q))
    have h2 := Finset.card_image_le (s := S) (f := fun i => -(((v i).toNat : ℕ) : ZMod q))
    omega
  obtain ⟨c, hcUn, hcB⟩ : ∃ c ∈ Un, c ∉ B := by
    by_contra hcon
    push_neg at hcon
    have hsub : Un ⊆ B := fun c hc => hcon c hc
    have := Finset.card_le_card hsub
    omega
  have hcu : IsUnit c := hUn c hcUn
  refine floor_of_missed_class_gen v hv q hq2 hqle hnd c hcu (fun i => ?_)
  by_cases hu : IsUnit (((v i).toNat : ZMod q))
  · have hiS : i ∈ S := hS i hu
    constructor
    · intro hEq
      exact hcB (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiS, hEq⟩))
    · intro hEq
      refine hcB (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiS, ?_⟩))
      rw [hEq, neg_neg]
  · constructor
    · intro hEq
      exact hu (hEq ▸ hcu)
    · intro hEq
      exact hu (hEq ▸ hcu.neg)

/-! ## Lemma P: the complement always contains a window pair -/

set_option maxHeartbeats 1600000 in
/-- **Lemma P.**  Let `m >= 3` and let `W ⊆ [1, 2m]` have exactly `m` elements, with at least one
element `<= m` (equivalently `W ≠ [m+1, 2m]`).  Then `W` contains two distinct elements whose sum
lies in `[m+2, 2m+2]`.

Applied to the complement `W = [1,2m] \ V` of a dense family, this says the pair needed by
Theorem P' always exists; the excluded case `W = [m+1,2m]` is `V = [1,m]`, which is not fully
resonant. -/
theorem complement_window_pair (m : ℕ) (hm : 3 ≤ m) (W : Finset ℕ)
    (hsub : ∀ x ∈ W, 1 ≤ x ∧ x ≤ 2 * m) (hcard : W.card = m)
    (hlow : ∃ x ∈ W, x ≤ m) :
    ∃ a ∈ W, ∃ b ∈ W, a ≠ b ∧ m + 2 ≤ a + b ∧ a + b ≤ 2 * m + 2 := by
  classical
  by_cases hfull : ∃ c ∈ W, c ≤ m ∧ (2 * m + 1 - c) ∈ W
  · -- a full pair `{c, 2m+1-c}` gives the sum `2m+1`
    obtain ⟨c, hcW, hcm, hc2⟩ := hfull
    have hc1 := (hsub c hcW).1
    exact ⟨c, hcW, 2 * m + 1 - c, hc2, by omega, by omega, by omega⟩
  · push_neg at hfull
    set A : Finset ℕ := W.filter (fun x => x ≤ m) with hA
    set B : Finset ℕ := W.filter (fun x => m < x) with hB
    set H : Finset ℕ := B.image (fun b => 2 * m + 1 - b) with hH
    have hunion : A ∪ B = W := by
      ext x
      simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : x ≤ m
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxa hxb
      simp only [hA, hB, Finset.mem_filter] at hxa hxb
      omega
    have hAB : A.card + B.card = m := by
      rw [← hcard, ← hunion, Finset.card_union_of_disjoint hdisj]
    have hHcard : H.card = B.card := by
      rw [hH]
      refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
      have hx2 : x ∈ B := Finset.mem_coe.mp hx
      have hy2 : y ∈ B := Finset.mem_coe.mp hy
      simp only [hB, Finset.mem_filter] at hx2 hy2
      have h1 := (hsub x hx2.1).2
      have h2 := (hsub y hy2.1).2
      omega
    have hsubI : A ∪ H ⊆ Finset.Icc 1 m := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · simp only [hA, Finset.mem_filter] at h
        have := (hsub x h.1).1
        rw [Finset.mem_Icc]
        omega
      · rw [hH, Finset.mem_image] at h
        obtain ⟨b, hb, rfl⟩ := h
        simp only [hB, Finset.mem_filter] at hb
        have := (hsub b hb.1).2
        rw [Finset.mem_Icc]
        omega
    have hdisjAH : Disjoint A H := by
      rw [Finset.disjoint_left]
      intro x hxa hxh
      simp only [hA, Finset.mem_filter] at hxa
      rw [hH, Finset.mem_image] at hxh
      obtain ⟨b, hb, hbx⟩ := hxh
      simp only [hB, Finset.mem_filter] at hb
      have hbb := (hsub b hb.1).2
      have hrec : 2 * m + 1 - x = b := by omega
      exact hfull x hxa.1 hxa.2 (hrec ▸ hb.1)
    have hcardU : (A ∪ H).card = m := by
      rw [Finset.card_union_of_disjoint hdisjAH, hHcard]
      omega
    have hIcc : (Finset.Icc 1 m).card = m := by
      rw [Nat.card_Icc]
      omega
    have heq : A ∪ H = Finset.Icc 1 m :=
      Finset.eq_of_subset_of_card_le hsubI (by omega)
    have hAne : A.Nonempty := by
      obtain ⟨x, hxW, hxm⟩ := hlow
      exact ⟨x, by rw [hA, Finset.mem_filter]; exact ⟨hxW, hxm⟩⟩
    rcases Finset.eq_empty_or_nonempty H with hHe | hHne
    · -- no high elements: `W = [1,m]`, take `m` and `m-1`
      have hAeq : A = Finset.Icc 1 m := by rw [← heq, hHe, Finset.union_empty]
      have hmW : m ∈ W := by
        have h : m ∈ A := by rw [hAeq, Finset.mem_Icc]; omega
        exact Finset.mem_of_mem_filter _ h
      have hm1W : m - 1 ∈ W := by
        have h : m - 1 ∈ A := by rw [hAeq, Finset.mem_Icc]; omega
        exact Finset.mem_of_mem_filter _ h
      exact ⟨m, hmW, m - 1, hm1W, by omega, by omega, by omega⟩
    · -- both sides present: cross at the top of `H`
      have hjmem : H.max' hHne ∈ H := H.max'_mem hHne
      have ha0mem : A.min' hAne ∈ A := A.min'_mem hAne
      have hjIcc := hsubI (Finset.mem_union_right _ hjmem)
      have ha0Icc := hsubI (Finset.mem_union_left _ ha0mem)
      rw [Finset.mem_Icc] at hjIcc ha0Icc
      have hle : A.min' hAne ≤ H.max' hHne + 1 := by
        by_contra hcon
        push_neg at hcon
        have hin : H.max' hHne + 1 ∈ Finset.Icc 1 m := by
          rw [Finset.mem_Icc]
          omega
        rw [← heq, Finset.mem_union] at hin
        rcases hin with h | h
        · have := A.min'_le _ h
          omega
        · have := H.le_max' _ h
          omega
      have ha0W : A.min' hAne ∈ W := Finset.mem_of_mem_filter _ ha0mem
      obtain ⟨b, hbB, hbj⟩ := Finset.mem_image.mp hjmem
      have hbW : b ∈ W := by
        simp only [hB, Finset.mem_filter] at hbB
        exact hbB.1
      have hbm : m < b := by
        simp only [hB, Finset.mem_filter] at hbB
        exact hbB.2
      have hb2 := (hsub b hbW).2
      exact ⟨A.min' hAne, ha0W, b, hbW, by omega, by omega, by omega⟩

set_option maxHeartbeats 1600000 in
/-- **Lemma P (sharp form).**  If in addition `W` has an element `> m`, the sum can be confined to
`{2m, 2m+1, 2m+2}`.  Instead of `min A` and `max H`, use the *first adjacent split* of the
partition `A ⊔ H = [1,m]`: a step `A → H` at `(c, c+1)` gives the pair `c`, `2m-c` summing to
`2m`, and a step `H → A` gives `c+1`, `2m+1-c` summing to `2m+2`; a full pair gives `2m+1`.
The excluded configurations are exactly `W = [1,m]` and `W = [m+1,2m]`. -/
theorem complement_window_pair_sharp (m : ℕ) (hm : 3 ≤ m) (W : Finset ℕ)
    (hsub : ∀ x ∈ W, 1 ≤ x ∧ x ≤ 2 * m) (hcard : W.card = m)
    (hlow : ∃ x ∈ W, x ≤ m) (hhigh : ∃ x ∈ W, m < x) :
    ∃ a ∈ W, ∃ b ∈ W, a ≠ b ∧ (a + b = 2 * m ∨ a + b = 2 * m + 1 ∨ a + b = 2 * m + 2) := by
  classical
  by_cases hfull : ∃ c ∈ W, c ≤ m ∧ (2 * m + 1 - c) ∈ W
  · obtain ⟨c, hcW, hcm, hc2⟩ := hfull
    have hc1 := (hsub c hcW).1
    exact ⟨c, hcW, 2 * m + 1 - c, hc2, by omega, Or.inr (Or.inl (by omega))⟩
  · push_neg at hfull
    set A : Finset ℕ := W.filter (fun x => x ≤ m) with hA
    set B : Finset ℕ := W.filter (fun x => m < x) with hB
    set H : Finset ℕ := B.image (fun b => 2 * m + 1 - b) with hH
    have hunion : A ∪ B = W := by
      ext x
      simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : x ≤ m
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxa hxb
      simp only [hA, hB, Finset.mem_filter] at hxa hxb
      omega
    have hAB : A.card + B.card = m := by
      rw [← hcard, ← hunion, Finset.card_union_of_disjoint hdisj]
    have hHcard : H.card = B.card := by
      rw [hH]
      refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
      have hx2 : x ∈ B := Finset.mem_coe.mp hx
      have hy2 : y ∈ B := Finset.mem_coe.mp hy
      simp only [hB, Finset.mem_filter] at hx2 hy2
      have h1 := (hsub x hx2.1).2
      have h2 := (hsub y hy2.1).2
      omega
    have hsubI : A ∪ H ⊆ Finset.Icc 1 m := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · simp only [hA, Finset.mem_filter] at h
        have := (hsub x h.1).1
        rw [Finset.mem_Icc]
        omega
      · rw [hH, Finset.mem_image] at h
        obtain ⟨b, hb, rfl⟩ := h
        simp only [hB, Finset.mem_filter] at hb
        have := (hsub b hb.1).2
        rw [Finset.mem_Icc]
        omega
    have hdisjAH : Disjoint A H := by
      rw [Finset.disjoint_left]
      intro x hxa hxh
      simp only [hA, Finset.mem_filter] at hxa
      rw [hH, Finset.mem_image] at hxh
      obtain ⟨b, hb, hbx⟩ := hxh
      simp only [hB, Finset.mem_filter] at hb
      have hbb := (hsub b hb.1).2
      have hrec : 2 * m + 1 - x = b := by omega
      exact hfull x hxa.1 hxa.2 (hrec ▸ hb.1)
    have hIcc : (Finset.Icc 1 m).card = m := by
      rw [Nat.card_Icc]
      omega
    have heq : A ∪ H = Finset.Icc 1 m := by
      refine Finset.eq_of_subset_of_card_le hsubI ?_
      rw [Finset.card_union_of_disjoint hdisjAH, hHcard, hIcc]
      omega
    have hAne : A.Nonempty := by
      obtain ⟨x, hxW, hxm⟩ := hlow
      exact ⟨x, by rw [hA, Finset.mem_filter]; exact ⟨hxW, hxm⟩⟩
    have hHne : H.Nonempty := by
      obtain ⟨x, hxW, hxm⟩ := hhigh
      have hxB : x ∈ B := by rw [hB, Finset.mem_filter]; exact ⟨hxW, hxm⟩
      exact ⟨2 * m + 1 - x, by rw [hH]; exact Finset.mem_image_of_mem _ hxB⟩
    -- pull an element of `W` out of a membership in `H`
    have hHW : ∀ c ∈ H, 2 * m + 1 - c ∈ W ∧ 1 ≤ c ∧ c ≤ m := by
      intro c hc
      obtain ⟨b, hbB, hbc⟩ := Finset.mem_image.mp (by rw [hH] at hc; exact hc)
      simp only [hB, Finset.mem_filter] at hbB
      have hb2 := (hsub b hbB.1).2
      refine ⟨?_, by omega, by omega⟩
      have : 2 * m + 1 - c = b := by omega
      rw [this]
      exact hbB.1
    have hAW : ∀ c ∈ A, c ∈ W ∧ 1 ≤ c ∧ c ≤ m := by
      intro c hc
      simp only [hA, Finset.mem_filter] at hc
      exact ⟨hc.1, (hsub c hc.1).1, hc.2⟩
    have hjmem : H.min' hHne ∈ H := H.min'_mem hHne
    have hjb := hHW _ hjmem
    by_cases hj1 : H.min' hHne = 1
    · -- `1 ∈ H`, so the first split is `H → A`: sum `2m+2`
      have ha0mem : A.min' hAne ∈ A := A.min'_mem hAne
      have ha0b := hAW _ ha0mem
      have ha0ne : A.min' hAne ≠ 1 := by
        intro h1
        have : (1 : ℕ) ∈ A := h1 ▸ ha0mem
        have h2 : (1 : ℕ) ∈ H := hj1 ▸ hjmem
        exact (Finset.disjoint_left.mp hdisjAH this) h2
      have hprev : A.min' hAne - 1 ∈ H := by
        have hin : A.min' hAne - 1 ∈ Finset.Icc 1 m := by
          rw [Finset.mem_Icc]
          omega
        rw [← heq, Finset.mem_union] at hin
        rcases hin with h | h
        · have := A.min'_le _ h
          omega
        · exact h
      have hpb := hHW _ hprev
      refine ⟨A.min' hAne, ha0b.1, 2 * m + 1 - (A.min' hAne - 1), hpb.1, by omega,
        Or.inr (Or.inr (by omega))⟩
    · -- `min H > 1`, so `min H - 1 ∈ A`: the split is `A → H`, sum `2m`
      have hprev : H.min' hHne - 1 ∈ A := by
        have hin : H.min' hHne - 1 ∈ Finset.Icc 1 m := by
          rw [Finset.mem_Icc]
          omega
        rw [← heq, Finset.mem_union] at hin
        rcases hin with h | h
        · exact h
        · have := H.min'_le _ h
          omega
      have hpb := hAW _ hprev
      refine ⟨H.min' hHne - 1, hpb.1, 2 * m + 1 - H.min' hHne, hjb.1, by omega,
        Or.inl (by omega)⟩

/-! ## The complement form: an absent pair certifies the floor -/

set_option maxHeartbeats 1600000 in
/-- **Theorem P' (absent pair).**  Let every velocity lie in `[1, 2m]` (`m = k+1`) and let
`q = 2m+1` or `q = 2m+2`.  If some `a` with `1 <= a < q` and `gcd(a,q) = 1` has **neither `a` nor
`q-a` among the velocities**, the floor holds.

This is the complement form of the criterion: the sign class of `a` mod `q` meets `[1,2m]` in
exactly `{a, q-a}` (the next member `q+a` exceeds `2m`), so the class is missed precisely when
both lie in the complement `W = [1,2m] \ V`.  Because `q > 2m`, the conditions "`q` divides no
velocity" and "the class is only the pair" are automatic — only coprimality remains. -/
theorem floor_of_absent_pair {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, v i ≤ 2 * ((k : ℤ) + 1))
    (q : ℕ) (hq : q = 2 * k + 3 ∨ q = 2 * k + 4)
    (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a < q) (hcop : Nat.Coprime a q)
    (habs : ∀ i, (v i).toNat ≠ a ∧ (v i).toNat ≠ q - a) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub : ∀ i, (v i).toNat ≤ 2 * k + 2 := by
    intro i
    have h := hd i
    have hc := hnat i
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h := hv i
    have hc := hnat i
    omega
  refine floor_of_missed_class_gen v hv q (by omega) (by omega) (fun i => ?_)
    ((a : ℕ) : ZMod q) ((ZMod.isUnit_iff_coprime a q).mpr hcop) (fun i => ⟨?_, ?_⟩)
  · intro hdvd
    have h1 : (q : ℤ) ≤ v i := Int.le_of_dvd (hv i) hdvd
    have h2 := hd i
    have h3 : ((q : ℕ) : ℤ) = (q : ℤ) := by push_cast; ring
    omega
  · intro heq
    have hviq : (v i).toNat < q := by have := hub i; omega
    have h1 : ((v i).toNat : ZMod q).val = ((a : ℕ) : ZMod q).val := by rw [heq]
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hviq,
      Nat.mod_eq_of_lt (by omega)] at h1
    exact (habs i).1 h1
  · intro heq
    have hviq : (v i).toNat < q := by have := hub i; omega
    have hsum : (((v i).toNat + a : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_add, heq]
      ring
    obtain ⟨e, he⟩ := (CharP.cast_eq_zero_iff (ZMod q) q _).mp hsum
    have h1 := hlb i
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · interval_cases e
      · omega
      · refine (habs i).2 ?_
        omega
    · have : q * 2 ≤ q * e := Nat.mul_le_mul_left _ hge
      omega

set_option maxHeartbeats 1600000 in
/-- **Theorem P'' (the three free moduli).**  Extends `floor_of_absent_pair` down to `q = 2m`.
For any `q` with `2m <= q <= 2m+2` (`m = k+1`), if some `a` coprime to `q` has none of `a`, `q-a`,
`q` among the velocities, the floor holds.  For `q = 2m+1, 2m+2` the condition `q` is not a
velocity is automatic; for `q = 2m` it is exactly `2m ∈ W`, which holds on the hard core because
`1` being a velocity puts `2m` in the complement.  Combined with the sharp form of Lemma P — whose
pairs sum to `2m`, `2m+1` or `2m+2` — this is the band-`2` criterion in its final form. -/
theorem floor_of_absent_pair_three {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, v i ≤ 2 * ((k : ℤ) + 1))
    (q : ℕ) (hq1 : 2 * k + 2 ≤ q) (hq2 : q ≤ 2 * k + 4)
    (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a < q) (hcop : Nat.Coprime a q)
    (habs : ∀ i, (v i).toNat ≠ a ∧ (v i).toNat ≠ q - a ∧ (v i).toNat ≠ q) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub : ∀ i, (v i).toNat ≤ 2 * k + 2 := by
    intro i
    have h := hd i
    have hc := hnat i
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h := hv i
    have hc := hnat i
    omega
  refine floor_of_missed_class_gen v hv q (by omega) (by omega) (fun i => ?_)
    ((a : ℕ) : ZMod q) ((ZMod.isUnit_iff_coprime a q).mpr hcop) (fun i => ⟨?_, ?_⟩)
  · -- `q` divides no velocity: the only possible multiple in range is `q` itself
    intro hdvd
    have h1 : (q : ℤ) ≤ v i := Int.le_of_dvd (hv i) hdvd
    have hc := hnat i
    have h1' : ((q : ℕ) : ℤ) ≤ (((v i).toNat : ℕ) : ℤ) := by rw [hc]; exact h1
    have h1'' : q ≤ (v i).toNat := by exact_mod_cast h1'
    have h2 := hub i
    exact (habs i).2.2 (by omega)
  · intro heq
    have hviq : (v i).toNat < q := by
      have h2 := hub i
      have h3 := (habs i).2.2
      omega
    have h1 : ((v i).toNat : ZMod q).val = ((a : ℕ) : ZMod q).val := by rw [heq]
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hviq,
      Nat.mod_eq_of_lt (by omega)] at h1
    exact (habs i).1 h1
  · intro heq
    have hviq : (v i).toNat < q := by
      have h2 := hub i
      have h3 := (habs i).2.2
      omega
    have hsum : (((v i).toNat + a : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_add, heq]
      ring
    obtain ⟨e, he⟩ := (CharP.cast_eq_zero_iff (ZMod q) q _).mp hsum
    have h1 := hlb i
    have he1 : e = 1 := by
      rcases Nat.lt_or_ge e 2 with hlt | hge
      · rcases Nat.lt_or_ge e 1 with hlt0 | hge0
        · exfalso
          have he0 : e = 0 := by omega
          rw [he0, Nat.mul_zero] at he
          omega
        · omega
      · exfalso
        have hmul : q * 2 ≤ q * e := Nat.mul_le_mul_left _ hge
        omega
    rw [he1, Nat.mul_one] at he
    exact (habs i).2.1 (by omega)

/-! ## Why no rung fires for free: criticality of the union bound -/

/-- **Criticality.**  For every modulus `q` in the window `2 <= q <= 2m+2` one has
`φ(q) <= 2m`.  Since a good multiplier is guaranteed by counting only when `φ(q) > 2m` (each of
the `m` velocities forbids two units), **the union bound never has slack** — for any family, at
any window modulus.  Equality `φ(q) = 2m` forces `q = 2m+1` prime (see the note): there the bound
is short by exactly one, which is precisely the single collision that full resonance supplies,
giving `dense_floor_of_prime`.  For composite `2m+1` the shortfall is strictly larger and no
counting argument can close it. -/
theorem totient_le_window (m q : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) (hqle : q ≤ 2 * m + 2) :
    Nat.totient q ≤ 2 * m := by
  rcases Nat.lt_or_ge q 3 with hlt | hge
  · interval_cases q
    · rw [Nat.totient_two]
      omega
  · have he : Even (Nat.totient q) := Nat.totient_even hge
    have hl : Nat.totient q < q := Nat.totient_lt q (by omega)
    obtain ⟨t, ht⟩ := he
    omega

/-! ## Tao's Lemma 5.1 -/

/-- **Tao's Lemma 5.1(i)** (arXiv:1701.02048, §5), in contrapositive form: if the floor fails then
every `j` in `[2, m+1]` divides some velocity (`m = k+1`).  This is exactly the contrapositive of
`floor_of_not_dvd_le`, so it is available here already verified; `j = 1` is trivial.  Clause (i) is
the full-resonance condition used throughout this development. -/
theorem tao_5_1_i {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hlt : ML v < 1 / ((k : ℝ) + 2)) (j : ℕ) (hj2 : 2 ≤ j) (hjk : j ≤ k + 2) :
    ∃ i, j ∣ (v i).toNat := by
  by_contra hcon
  push_neg at hcon
  exact absurd (floor_of_not_dvd_le j hj2 hjk v hv hcon) (not_le.mpr hlt)

set_option maxHeartbeats 1600000 in
/-- **Tao's Lemma 5.1(ii)** (arXiv:1701.02048, §5), core form, VERIFIED.  With `m = k+1`
velocities of height at most `K·m` and the floor failing, for every `j <= m` and every `d` there
is a velocity `v` such that, writing `r = (v·d) mod j`, either `r = 0` and `v < Kj`, or
`r = j-1` and `v > K(m+1-j)`.

Taking `d` with `a·d ≡ -1 (mod j)` turns the second branch into `v ≡ a (mod j)`, which is Tao's
stated form; the first branch says `j ∣ v` and `v = cj` with `c <= K-1`.

The proof is Tao's, but recast so that no real analysis is needed: at `t = p/q` with
`q = K·j·(k+2)` and `p = dK(k+2)+1`, the residue of `v·p` mod `q` is exactly `rK(k+2) + v`, and the
three cases of Tao's argument become integer inequalities.  The floor statement itself is supplied
by `cube_floor_of_witness` in contrapositive form. -/
theorem tao_5_1_ii {k K : ℕ} (hK : 1 ≤ K) (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hub : ∀ i, v i ≤ (K : ℤ) * ((k : ℤ) + 1))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (d : ℕ)
    (hlt : ML v < 1 / ((k : ℝ) + 2)) :
    ∃ i, (((v i).toNat * d) % j = 0 ∧ (v i).toNat < K * j) ∨
         (((v i).toNat * d) % j = j - 1 ∧ K * (k + 2 - j) < (v i).toNat) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hnat : ∀ i, ((v i).toNat : ℤ) = v i := fun i => Int.toNat_of_nonneg (hv i).le
  have hub' : ∀ i, (v i).toNat ≤ K * (k + 1) := by
    intro i
    have h1 := hub i
    have h2 := hnat i
    have h3 : ((K * (k + 1) : ℕ) : ℤ) = (K : ℤ) * ((k : ℤ) + 1) := by push_cast; ring
    omega
  have hlb : ∀ i, 1 ≤ (v i).toNat := by
    intro i
    have h1 := hv i
    have h2 := hnat i
    omega
  set q : ℕ := K * j * (k + 2) with hq
  have hqpos : 0 < q := by
    rw [hq]
    have : 0 < K * j := Nat.mul_pos (by omega) (by omega)
    exact Nat.mul_pos this (by omega)
  refine absurd (cube_floor_of_witness v hv (d * K * (k + 2) + 1) q hqpos (fun i => ?_))
    (not_le.mpr hlt)
  -- residue identity: `v·p ≡ r·K(k+2) + v  (mod q)`
  set n : ℕ := (v i).toNat with hn
  set r : ℕ := (n * d) % j with hr
  have hrj : r < j := Nat.mod_lt _ (by omega)
  have hdm : n * d = (n * d / j) * j + r := by
    have h := Nat.div_add_mod (n * d) j
    rw [Nat.mul_comm] at h
    rw [hr]
    omega
  have hexp : n * (d * K * (k + 2) + 1) = (n * d / j) * q + (r * (K * (k + 2)) + n) := by
    rw [hq]
    calc n * (d * K * (k + 2) + 1) = (n * d) * (K * (k + 2)) + n := by ring
      _ = ((n * d / j) * j + r) * (K * (k + 2)) + n := by rw [← hdm]
      _ = (n * d / j) * (K * j * (k + 2)) + (r * (K * (k + 2)) + n) := by ring
  have hKk : K * (k + 2) ≤ q / j * 1 + K * (k + 2) := by omega
  have hsmall : r * (K * (k + 2)) + n < q := by
    have h1 : r * (K * (k + 2)) + K * (k + 2) ≤ j * (K * (k + 2)) := by
      have : (r + 1) * (K * (k + 2)) ≤ j * (K * (k + 2)) :=
        Nat.mul_le_mul_right _ (by omega)
      calc r * (K * (k + 2)) + K * (k + 2) = (r + 1) * (K * (k + 2)) := by ring
        _ ≤ j * (K * (k + 2)) := this
    have h2 : n < K * (k + 2) := by
      have h3 := hub' i
      have h4 : K * (k + 1) < K * (k + 2) := by
        have : K * (k + 1) + K = K * (k + 2) := by ring
        omega
      omega
    have h5 : j * (K * (k + 2)) = q := by rw [hq]; ring
    omega
  have hres : n * (d * K * (k + 2) + 1) % q = r * (K * (k + 2)) + n := by
    rw [hexp, Nat.mul_comm (n * d / j) q, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  rw [hres]
  -- the two cases of the hypothesis give the band bound
  have hband : K * j ≤ min (r * (K * (k + 2)) + n) (q - (r * (K * (k + 2)) + n)) := by
    have hKj : K * j ≤ K * (k + 2) := Nat.mul_le_mul_left _ (by omega)
    refine le_min ?_ ?_
    · rcases Nat.eq_zero_or_pos r with h0 | hpos
      · have := (hcon i).1
        rw [← hr, h0] at this
        simp only [h0, Nat.zero_mul, Nat.zero_add]
        omega
      · have : K * (k + 2) ≤ r * (K * (k + 2)) := by
          calc K * (k + 2) = 1 * (K * (k + 2)) := by ring
            _ ≤ r * (K * (k + 2)) := Nat.mul_le_mul_right _ hpos
        omega
    · by_cases hrj1 : r = j - 1
      · have h2 := (hcon i).2
        rw [← hr] at h2
        have h3 : n ≤ K * (k + 2 - j) := by
          have := h2 hrj1
          omega
        have h4 : (j - r) = 1 := by omega
        have h5 : q - r * (K * (k + 2)) = K * (k + 2) := by
          have : q = j * (K * (k + 2)) := by rw [hq]; ring
          have h6 : r + 1 = j := by omega
          calc q - r * (K * (k + 2)) = j * (K * (k + 2)) - r * (K * (k + 2)) := by rw [this]
            _ = (j - r) * (K * (k + 2)) := by rw [Nat.sub_mul]
            _ = K * (k + 2) := by rw [h4, Nat.one_mul]
        have h7 : K * (k + 2 - j) + K * j = K * (k + 2) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        omega
      · have hge2 : r + 2 ≤ j := by omega
        have h1 : (r + 2) * (K * (k + 2)) ≤ j * (K * (k + 2)) := Nat.mul_le_mul_right _ hge2
        have h2 : q = j * (K * (k + 2)) := by rw [hq]; ring
        have h3 : n ≤ K * (k + 1) := hub' i
        have h4 : K * j + K * (k + 1) < 2 * (K * (k + 2)) := by
          have e1 : K * j + K * (k + 1) = K * (j + (k + 1)) := by ring
          have e2 : 2 * (K * (k + 2)) = K * (2 * k + 4) := by ring
          have hjj : j + (k + 1) < 2 * k + 4 := by omega
          have hmm : K * (j + (k + 1)) < K * (2 * k + 4) :=
            Nat.mul_lt_mul_of_pos_left hjj (by omega)
          omega
        have e3 : (r + 2) * (K * (k + 2)) = r * (K * (k + 2)) + 2 * (K * (k + 2)) := by ring
        omega
  calc q = (k + 2) * (K * j) := by rw [hq]; ring
    _ ≤ (k + 2) * min (r * (K * (k + 2)) + n) (q - (r * (K * (k + 2)) + n)) :=
        Nat.mul_le_mul_left _ hband

/-- **Tao's Lemma 5.1(ii)**, original `a`-form, stated for reference.  With height bound `K·m` and the floor
failing, for every `j <= m` and every `a` coprime to `j` some velocity is either `cj` with
`1 <= c <= K-1`, or is `≡ a (mod j)` and exceeds `K(m+1-j)`.  Tao's proof evaluates the hypothesis
at `t = d/j + 1/(Kj(m+1))` where `ad ≡ -1 (mod j)` and splits on `v_i d mod j`: the residue `0`
forces `v_i < Kj` and `j ∣ v_i`; the residue `-1` forces `v_i > K(m+1-j)` and `v_i ≡ a`; any other
residue forces `v_i > K(2m+2-j) >= Km`, contradicting the height bound.

This is the clause that drives the filter used in this paper.  It is stated here as a `Prop` to pin
its semantics (Rule 5); its Lean proof requires the `Int.fract` case analysis above and is not yet
written, so every result depending on it carries the label of the cited lemma, not `VERIFIED`. -/
def Tao51ii : Prop :=
  ∀ (k K : ℕ) (v : Fin (k + 1) → ℤ), 1 ≤ K → (∀ i, 0 < v i) →
    (∀ i, v i ≤ (K : ℤ) * ((k : ℤ) + 1)) → ML v < 1 / ((k : ℝ) + 2) →
    ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ a : ℕ, Nat.Coprime a j →
      ∃ i, (∃ c : ℕ, 1 ≤ c ∧ c ≤ K - 1 ∧ (v i).toNat = c * j) ∨
        ((v i).toNat % j = a % j ∧ (K : ℤ) * ((k : ℤ) + 2 - j) < v i)

/-! ## The open statements, pinned, and the verified reduction between them -/

/-- **The dense-window statement** (Tao's `2n` target, Problem 6 of the Perarnau--Serra survey):
every family of `k+1` positive velocities bounded by `2(k+1)` meets the Lonely-Runner floor.
Theorem `dense_floor_of_prime` establishes this whenever `2k+3` is prime. -/
def DenseWindow : Prop :=
  ∀ (k : ℕ) (v : Fin (k + 1) → ℤ), (∀ i, 0 < v i) → (∀ i, v i ≤ 2 * ((k : ℤ) + 1)) →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **The ladder conjecture**: every *fully resonant* dense family admits a rung of the criterion
family `E^(b)` — a band `b`, a modulus `q <= b(k+2)` dividing no velocity, and a unit `c` all of
whose multiples `c, 2c, …, (b-1)c` are missed.  This is the sole remaining gap: it holds on every
family ever enumerated (`> 55·10⁶` at `m = 10..17`), with the case `2k+3` prime already a theorem,
but no proof is known and Theorem `totient_le_window` shows no counting argument can supply one. -/
def LadderConjecture : Prop :=
  ∀ (k : ℕ) (v : Fin (k + 1) → ℤ), (∀ i, 0 < v i) → (∀ i, v i ≤ 2 * ((k : ℤ) + 1)) →
    (∀ q : ℕ, 2 ≤ q → q ≤ k + 2 → ∃ i, q ∣ (v i).toNat) →
    ∃ q b : ℕ, 1 ≤ b ∧ 2 ≤ q ∧ q ≤ b * (k + 2) ∧ (∀ i, ¬ ((q : ℤ) ∣ v i)) ∧
      ∃ c : ZMod q, IsUnit c ∧ ∀ i, ∀ j : ℕ, 1 ≤ j → j < b →
        ((v i).toNat : ZMod q) ≠ (j : ZMod q) * c ∧
        ((v i).toNat : ZMod q) ≠ -((j : ZMod q) * c)

/-- **The reduction (VERIFIED).**  The ladder conjecture implies the dense-window statement.
A dense family either fails full resonance — and then `floor_of_not_dvd_le` gives the floor
outright — or is fully resonant, and the conjectured rung fires through `floor_of_missed_classes`.
So the whole of Tao's `2n` target reduces to `LadderConjecture`. -/
theorem denseWindow_of_ladder : LadderConjecture → DenseWindow := by
  intro hL k v hv hd
  by_cases hres : ∀ q : ℕ, 2 ≤ q → q ≤ k + 2 → ∃ i, q ∣ (v i).toNat
  · obtain ⟨q, b, hb, hq2, hqle, hnd, c, hc, hmiss⟩ := hL k v hv hd hres
    exact floor_of_missed_classes v hv q b hb hq2 hqle hnd c hc hmiss
  · push_neg at hres
    obtain ⟨q, hq2, hqk, hq⟩ := hres
    exact floor_of_not_dvd_le q hq2 hqk v hv hq

end LRSpectrumFull
