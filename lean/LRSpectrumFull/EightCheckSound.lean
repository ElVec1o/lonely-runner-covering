/-
# Soundness of the v4 certificate checker (atom E7d): statements first (Rule 5)

`EightCheckV4.lean` defines `checkRoot` / `checkState`.  This file pins, as Lean statements, what a
successful replay is supposed to mean, and proves the combinatorial core of the bound leaves.

STATUS (2026-09-24).
* `weighted_bound_no_cover` (the weighted-bound leaf lemma, `Y ≤ ∑ loads` argument, with exception
  set `T` and threshold `t`) and its uniform special case `uniform_bound_no_cover`: proved.
* `exists_rep` (the ratio-min representative lemma): proved.
* `lemma7Check_of_noBadRep` (no bad representative ⇒ `lemma7Check 7 p`): proved.
* `checkState_sound`, `checkRoot_sound`, `checkRootH_sound` (the tree semantics of the replay):
  proved, via the bit-level lemmas below (base-`2^16` digits of the spread counters, `allLe`,
  lowest-bit isolation and the `lgk` binary search, popcount bound), the leaf lemmas, the
  child-state update, and an induction over the fuel of `go` / `kids` / `rootKids`.
  `checkState` checks that `avail` is a sub-mask of `adm` (the parity leaf counts `avail` by `spc`).
* `lemma7Check_of_checkRoot`, `lemma7Check_of_checkRootH`, `lemma7Check1_of_checkRoot`: proved from
  the above.  What remains for a prime `p` is `TableOK X` for its context and the kernel replay.

Conventions (as in `LRCFourRunnersCore` / `LRCEightWLOG`): `k = 7`, `q = 8p`, window `[1, 4p]`,
admissible speeds `[1, 4p]` minus the multiples of `p`, side condition "at most 5 even".
For admissible `v` (so `p ∤ v`, `p > 7` prime), `v` is a unit mod `q` iff `v` is odd.
-/

import LRSpectrumFull.EightCheckV4
import LRSpectrumFull.LRCEightWLOG

namespace LRSpectrumFull.EightV4

open Finset

/-! ## The weighted-bound leaf lemma (proved) -/

section Leaf

variable {ι κ : Type*} [DecidableEq ι]

/-- load of the speed `v`: total weight of the positions of `U` it covers -/
def load (cov : κ → ι → Prop) [∀ j v, Decidable (cov j v)] (U : Finset κ) (y : κ → ℕ) (v : ι) : ℕ :=
  ∑ j ∈ U, if cov j v then y j else 0

/-- **Weighted-bound leaf.**  Weights `y` on the uncovered set `U`, total `Y = ∑_U y`, loads
`L v = ∑_{j ∈ U, v covers j} y j`.  Suppose an exception set `T` with `|T| ≤ r` and a threshold `t`
satisfy: every available speed outside `T` has load `≤ t`, every speed of `T` has load `≥ t`, and
`∑_T L + (r - |T|) t < Y`.  Then no set of at most `r` available speeds covers `U`. -/
theorem weighted_bound_no_cover (cov : κ → ι → Prop) [∀ j v, Decidable (cov j v)]
    (U : Finset κ) (y : κ → ℕ) (A T : Finset ι) (r t : ℕ)
    (hT : T.card ≤ r)
    (hout : ∀ v ∈ A, v ∉ T → load cov U y v ≤ t)
    (hin : ∀ v ∈ T, t ≤ load cov U y v)
    (hlt : ∑ v ∈ T, load cov U y v + (r - T.card) * t < ∑ j ∈ U, y j)
    (Z : Finset ι) (hZA : Z ⊆ A) (hZr : Z.card ≤ r)
    (hcov : ∀ j ∈ U, ∃ v ∈ Z, cov j v) : False := by
  -- Step 1: `Y ≤ ∑_{v ∈ Z} L v` (every `j` is covered at least once; swap the sums)
  have h1 : ∑ j ∈ U, y j ≤ ∑ v ∈ Z, load cov U y v := by
    unfold load
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨v, hvZ, hv⟩ := hcov j hj
    calc y j = (if cov j v then y j else 0) := by simp [hv]
      _ ≤ ∑ w ∈ Z, (if cov j w then y j else 0) :=
          Finset.single_le_sum (f := fun w => if cov j w then y j else 0)
            (fun _ _ => Nat.zero_le _) hvZ
  -- Step 2: split `Z` along `T`
  have hsplit : ∑ v ∈ Z, load cov U y v =
      ∑ v ∈ Z.filter (· ∈ T), load cov U y v + ∑ v ∈ Z.filter (· ∉ T), load cov U y v :=
    (Finset.sum_filter_add_sum_filter_not Z (· ∈ T) _).symm
  -- outside `T`: each load `≤ t`
  have h2 : ∑ v ∈ Z.filter (· ∉ T), load cov U y v ≤ (Z.filter (· ∉ T)).card * t := by
    have := Finset.sum_le_card_nsmul (Z.filter (· ∉ T)) (load cov U y) t (by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact hout v (hZA hv.1) hv.2)
    simpa using this
  -- inside `T`: `∑_{Z ∩ T} L + (|T| - |Z ∩ T|) t ≤ ∑_T L`
  have hZT : Z.filter (· ∈ T) ⊆ T := by
    intro v hv; rw [Finset.mem_filter] at hv; exact hv.2
  have h3 : ∑ v ∈ Z.filter (· ∈ T), load cov U y v + (T.card - (Z.filter (· ∈ T)).card) * t ≤
      ∑ v ∈ T, load cov U y v := by
    rw [← Finset.sum_sdiff hZT]
    have hc : (T \ Z.filter (· ∈ T)).card = T.card - (Z.filter (· ∈ T)).card :=
      Finset.card_sdiff_of_subset hZT
    have : (T.card - (Z.filter (· ∈ T)).card) * t ≤ ∑ v ∈ T \ Z.filter (· ∈ T), load cov U y v := by
      rw [← hc]
      have := Finset.card_nsmul_le_sum (T \ Z.filter (· ∈ T)) (load cov U y) t (by
        intro v hv
        exact hin v (Finset.mem_sdiff.mp hv).1)
      simpa using this
    omega
  -- cardinalities
  have hcard : (Z.filter (· ∈ T)).card + (Z.filter (· ∉ T)).card = Z.card :=
    Finset.card_filter_add_card_filter_not (· ∈ T)
  have hZTc : (Z.filter (· ∈ T)).card ≤ T.card := Finset.card_le_card hZT
  -- combine: (|Z| - |Z∩T|) t ≤ (r - |Z∩T|) t = (|T| - |Z∩T|) t + (r - |T|) t
  have h4 : (Z.filter (· ∉ T)).card * t ≤
      (T.card - (Z.filter (· ∈ T)).card) * t + (r - T.card) * t := by
    rw [← Nat.add_mul]
    apply Nat.mul_le_mul_right
    omega
  omega

/-- Uniform special case (`y ≡ 1`): loads are the counts `|{j ∈ U : v covers j}|`. -/
theorem uniform_bound_no_cover (cov : κ → ι → Prop) [∀ j v, Decidable (cov j v)]
    (U : Finset κ) (A T : Finset ι) (r t : ℕ)
    (hT : T.card ≤ r)
    (hout : ∀ v ∈ A, v ∉ T → (U.filter (fun j => cov j v)).card ≤ t)
    (hin : ∀ v ∈ T, t ≤ (U.filter (fun j => cov j v)).card)
    (hlt : ∑ v ∈ T, (U.filter (fun j => cov j v)).card + (r - T.card) * t < U.card)
    (Z : Finset ι) (hZA : Z ⊆ A) (hZr : Z.card ≤ r)
    (hcov : ∀ j ∈ U, ∃ v ∈ Z, cov j v) : False := by
  have hl : ∀ v, load cov U (fun _ => 1) v = (U.filter (fun j => cov j v)).card := by
    intro v
    unfold load
    rw [Finset.card_filter]
  refine weighted_bound_no_cover cov U (fun _ => 1) A T r t hT ?_ ?_ ?_ Z hZA hZr hcov
  · intro v hv hvT; rw [hl]; exact hout v hv hvT
  · intro v hv; rw [hl]; exact hin v hv
  · simp only [hl]; simpa using hlt

end Leaf

/-! ## Semantics of the tables and of the search (statements) -/

/-- spread encoding of a finite set of speeds: bit `16 v` -/
def spreadOf (s : Finset ℕ) : ℕ := ∑ v ∈ s, 2 ^ (16 * v)
/-- compact encoding of a finite set of positions: bit `j` -/
def compactOf (s : Finset ℕ) : ℕ := ∑ j ∈ s, 2 ^ j

/-- the admissible speeds for `k = 7` at `p` -/
def admSet (p : ℕ) : Finset ℕ := (Finset.Icc 1 (4 * p)).filter (fun v => v % p ≠ 0)
/-- the window -/
def winSet (p : ℕ) : Finset ℕ := Finset.Icc 1 (4 * p)

/-- the context `X` encodes the covering data of `p` -/
def TableOK (X : Ctx) : Prop :=
  0 < X.p ∧ X.W = 4 * X.p ∧ X.W < 1024 ∧
  X.adm = spreadOf (admSet X.p) ∧
  X.even = spreadOf ((admSet X.p).filter (fun v => v % 2 = 0)) ∧
  X.m8 = spreadOf ((admSet X.p).filter (fun v => v % 8 = 0)) ∧
  X.ones = spreadOf (Finset.range (X.W + 1)) ∧
  (∀ v ∈ admSet X.p, X.cov v = compactOf ((winSet X.p).filter (fun j => coversAt 7 X.p j v))) ∧
  (∀ j ∈ winSet X.p, X.covby j = spreadOf ((admSet X.p).filter (fun v => coversAt 7 X.p j v))) ∧
  (∀ u acc, (∀ j, u.testBit j = true → j ∈ winSet X.p) →
    X.cntF u acc = acc + ∑ j ∈ (winSet X.p).filter (fun j => u.testBit j = true), X.covby j)

/-- the finitely checkable part of `TableOK` (decidable; `decide +kernel` per prime) -/
abbrev TableFin (X : Ctx) : Prop :=
  0 < X.p ∧ X.W = 4 * X.p ∧ X.W < 1024 ∧
  X.adm = spreadOf (admSet X.p) ∧
  X.even = spreadOf ((admSet X.p).filter (fun v => v % 2 = 0)) ∧
  X.m8 = spreadOf ((admSet X.p).filter (fun v => v % 8 = 0)) ∧
  X.ones = spreadOf (Finset.range (X.W + 1)) ∧
  (∀ v ∈ admSet X.p, X.cov v = compactOf ((winSet X.p).filter (fun j => coversAt 7 X.p j v))) ∧
  (∀ j ∈ winSet X.p, X.covby j = spreadOf ((admSet X.p).filter (fun v => coversAt 7 X.p j v)))

/-- `|y / u| < d` modulo `q = 8p`, witnessed without inverses -/
def RatioLt (p d y u : ℕ) : Prop := ∃ x, 1 ≤ x ∧ x < d ∧ nrm (8 * p) (x * u) = y

/-- a bad 7-set: admissible, at most five even members, covers the window -/
def Bad (p : ℕ) (V : Finset ℕ) : Prop :=
  V ⊆ admSet p ∧ V.card = 7 ∧ (V.filter (fun v => v % 2 = 0)).card ≤ 5 ∧
  ∀ j ∈ winSet p, ∃ v ∈ V, coversAt 7 p j v = true

/-- `V` is a ratio-min representative with parameter `d`: `1, d ∈ V`, `8 ∣ d`, and no pair
(unit `u`, multiple of 8 `y`) of `V` has `|y / u| < d` -/
def Rep (p d : ℕ) (V : Finset ℕ) : Prop :=
  1 ∈ V ∧ d ∈ V ∧ d % 8 = 0 ∧
  ∀ u ∈ V, u % 2 = 1 → ∀ y ∈ V, y % 8 = 0 → ¬ RatioLt p d y u

/-- the checker's `nrm` is the `min` form of `EightWLOG.nrm` -/
theorem nrm_eq_wlog (q y : ℕ) : nrm q y = EightWLOG.nrm q y := by
  unfold nrm EightWLOG.nrm
  show (bif Nat.ble (y % q) (q - y % q) then y % q else q - y % q) = min (y % q) (q - y % q)
  cases hb : Nat.ble (y % q) (q - y % q) with
  | true =>
    have := Nat.le_of_ble_eq_true hb
    simp [min_eq_left this]
  | false =>
    have : ¬ (y % q ≤ q - y % q) := Nat.not_le_of_not_ble_eq_true (by rw [hb]; decide)
    simp only [cond_false]
    omega

theorem mem_admSet {p v : ℕ} : v ∈ admSet p ↔ 1 ≤ v ∧ v ≤ 4 * p ∧ v % p ≠ 0 := by
  simp [admSet, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem mem_winSet {p j : ℕ} : j ∈ winSet p ↔ 1 ≤ j ∧ j ≤ 4 * p := by
  simp [winSet, Finset.mem_Icc]

open EightWLOG in
/-- a speed covering the position `p` is a multiple of 8 -/
theorem mod8_of_covers_p {p v : ℕ} (hp : 0 < p) (h : coversAt 7 p p v = true) : v % 8 = 0 := by
  rw [coversAt_eq] at h
  have h' : (7 + 1) * EightWLOG.nrm ((7 + 1) * p) (p * v) < (7 + 1) * p := of_decide_eq_true h
  have hm : p * v % ((7 + 1) * p) = p * (v % 8) := by
    rw [show (7 + 1) * p = p * 8 by ring]; exact Nat.mul_mod_mul_left p v 8
  unfold EightWLOG.nrm at h'
  rw [hm] at h'
  have : v % 8 = 0 ∨ v % 8 = 1 ∨ v % 8 = 2 ∨ v % 8 = 3 ∨ v % 8 = 4 ∨ v % 8 = 5 ∨ v % 8 = 6 ∨
      v % 8 = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> rw [h] at h' <;> omega

open EightWLOG in
/-- `nrm` preserves divisibility by 8 when `8 ∣ q` -/
theorem nrm_mod_eight {q : ℕ} (hq : 0 < q) (h8 : 8 ∣ q) (x : ℕ) :
    (EightWLOG.nrm q x % 8 = 0 ↔ x % 8 = 0) := by
  rcases nrm_cases hq x with h | h
  · have := Nat.ModEq.of_dvd h8 h
    unfold Nat.ModEq at this
    omega
  · have := Nat.ModEq.of_dvd h8 h
    unfold Nat.ModEq at this
    omega

open EightWLOG in
/-- **Ratio-min representative lemma.**  Every bad set has a bad image, under multiplication by a
unit mod `8p` followed by `nrm`, which is a ratio-min representative. -/
theorem exists_rep (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (V : Finset ℕ) (hV : Bad p V) :
    ∃ d V', Rep p d V' ∧ Bad p V' := by
  obtain ⟨hsub, hcard, hev, hcovV⟩ := hV
  set q := (7 + 1) * p with hqdef
  have hq : 0 < q := by omega
  have h2q : 2 ∣ q := ⟨4 * p, by omega⟩
  have h8q : 8 ∣ q := ⟨p, by omega⟩
  have hpq : p ∣ q := ⟨8, by omega⟩
  have hadm : ∀ v ∈ V, 1 ≤ v ∧ v ≤ 4 * p ∧ v % p ≠ 0 := fun v hv => mem_admSet.1 (hsub hv)
  -- inverses of odd admissible speeds
  have hinv : ∀ a, 1 ≤ a ∧ a ≤ 4 * p ∧ a % p ≠ 0 → a % 2 = 1 →
      ∃ c, a * c ≡ 1 [MOD q] ∧ c % 2 = 1 ∧ Nat.Coprime c q := by
    intro a ha ha2
    have hcop2 : Nat.Coprime a 2 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, ha2]; rfl
    have hcop8 : Nat.Coprime a 8 := by simpa using hcop2.pow_right 3
    have hcopp : Nat.Coprime a p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd; exact ha.2.2 (Nat.mod_eq_zero_of_dvd hd)
    have hcopq : Nat.Coprime a q := Nat.Coprime.mul_right hcop8 hcopp
    obtain ⟨c, -, hc1⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopq (by omega)
    have hac : a * c ≡ 1 [MOD q] := by
      unfold Nat.ModEq; rw [hc1, Nat.mod_eq_of_lt (by omega)]
    have hcq : Nat.Coprime c q := Nat.coprime_of_mul_modEq_one a (by rw [Nat.mul_comm]; exact hac)
    have hc2 : c % 2 = 1 := by
      have h1 : a * c % 2 = 1 := by rw [← Nat.mod_mod_of_dvd _ h2q, hc1]
      rcases Nat.mod_two_eq_zero_or_one c with h | h
      · rw [Nat.mul_mod, h] at h1; simp at h1
      · exact h
    exact ⟨c, hac, hc2, hcq⟩
  -- an odd member and a multiple of 8
  have hodd : ∃ u ∈ V, u % 2 = 1 := by
    by_contra hno
    push Not at hno
    have hall : V.filter (fun v => v % 2 = 0) = V := by
      rw [Finset.filter_eq_self]
      intro v hv; have := hno v hv; omega
    rw [hall, hcard] at hev
    omega
  have hm8 : ∃ y ∈ V, y % 8 = 0 := by
    obtain ⟨v, hv, hc⟩ := hcovV p (mem_winSet.2 ⟨by omega, by omega⟩)
    exact ⟨v, hv, mod8_of_covers_p (by omega) hc⟩
  -- the ratio set is nonempty: `n` with `‖n a‖ = b` for a unit `a` and a multiple of 8 `b` of `V`
  have hex : ∃ n, ∃ a ∈ V, a % 2 = 1 ∧ ∃ b ∈ V, b % 8 = 0 ∧ 1 ≤ n ∧ EightWLOG.nrm q (n * a) = b := by
    obtain ⟨u, hu, hu2⟩ := hodd
    obtain ⟨y, hy, hy8⟩ := hm8
    obtain ⟨c, huc, -, hcq⟩ := hinv u (hadm u hu) hu2
    have hya := hadm y hy
    refine ⟨EightWLOG.nrm q (c * y), u, hu, hu2, y, hy, hy8, ?_, ?_⟩
    · apply nrm_pos hq
      intro h0
      have hd : q ∣ c * y := Nat.dvd_of_mod_eq_zero h0
      have : q ∣ y := (Nat.Coprime.symm hcq).dvd_of_dvd_mul_left hd
      have := Nat.le_of_dvd (by omega) this
      omega
    · rw [Nat.mul_comm (EightWLOG.nrm q (c * y)) u, nrm_mul_nrm hq]
      have : u * (c * y) ≡ y [MOD q] := by
        have := huc.mul_right y; rwa [Nat.one_mul, Nat.mul_assoc] at this
      rw [nrm_congr this]
      unfold EightWLOG.nrm
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  classical
  set d := Nat.find hex with hd
  obtain ⟨a0, ha0, ha02, b0, hb0, hb08, hd1, hdab⟩ := Nat.find_spec hex
  have hmin : ∀ n < d, ¬ ∃ a ∈ V, a % 2 = 1 ∧ ∃ b ∈ V, b % 8 = 0 ∧ 1 ≤ n ∧
      EightWLOG.nrm q (n * a) = b := fun n hn => Nat.find_min hex hn
  obtain ⟨c, hac, hc2, hcq⟩ := hinv a0 (hadm a0 ha0) ha02
  -- `c * x` is not `0` mod `q` on the window
  have hnz : ∀ x, 1 ≤ x → x ≤ 4 * p → (c * x) % q ≠ 0 := by
    intro x hx1 hx2 h0
    have hd' : q ∣ c * x := Nat.dvd_of_mod_eq_zero h0
    have : q ∣ x := (Nat.Coprime.symm hcq).dvd_of_dvd_mul_left hd'
    have := Nat.le_of_dvd (by omega) this
    omega
  have hback : ∀ x, a0 * (c * x) ≡ x [MOD q] := by
    intro x
    have := hac.mul_right x
    rwa [Nat.one_mul, Nat.mul_assoc] at this
  have hsmall : ∀ x, x ≤ 4 * p → EightWLOG.nrm q x = x := by
    intro x hx
    unfold EightWLOG.nrm
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  let φ : ℕ → ℕ := fun v => EightWLOG.nrm q (c * v)
  -- (F1) admissibility
  have hF1 : ∀ v, 1 ≤ v ∧ v ≤ 4 * p ∧ v % p ≠ 0 → 1 ≤ φ v ∧ φ v ≤ 4 * p ∧ φ v % p ≠ 0 := by
    intro v hv
    refine ⟨?_, ?_, ?_⟩
    · exact nrm_pos hq (hnz v hv.1 hv.2.1)
    · show EightWLOG.nrm q (c * v) ≤ 4 * p
      have := nrm_le q (c * v); omega
    · intro h0
      have hcv : c * v % p = 0 := by
        rcases nrm_cases hq (c * v) with h | h
        · have := Nat.ModEq.of_dvd hpq h
          unfold Nat.ModEq at this
          change EightWLOG.nrm q (c * v) % p = 0 at h0
          omega
        · have := Nat.ModEq.of_dvd hpq h
          unfold Nat.ModEq at this
          change EightWLOG.nrm q (c * v) % p = 0 at h0
          rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.zero_mod] at this
          exact this
      rcases (Nat.Prime.dvd_mul hp).1 (Nat.dvd_of_mod_eq_zero hcv) with hdc | hdv
      · have := Nat.Coprime.coprime_dvd_left hdc hcq
        have := Nat.Coprime.eq_one_of_dvd this hpq
        exact hp.one_lt.ne' this
      · exact hv.2.2 (Nat.mod_eq_zero_of_dvd hdv)
  -- (F2) injectivity on the admissible set
  have hF2 : ∀ v, 1 ≤ v ∧ v ≤ 4 * p ∧ v % p ≠ 0 → ∀ w, 1 ≤ w ∧ w ≤ 4 * p ∧ w % p ≠ 0 →
      φ v = φ w → v = w := by
    intro v hv w hw h
    rcases nrm_inj hq h with h1 | h1
    · have : v ≡ w [MOD q] := ((hback v).symm.trans (h1.mul_left a0)).trans (hback w)
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · have h2 := h1.mul_left a0
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
  -- (F3) parity and divisibility by 8
  have hF3 : ∀ v, φ v % 2 = v % 2 := by
    intro v
    change EightWLOG.nrm q (c * v) % 2 = v % 2
    rw [nrm_mod_two hq h2q, Nat.mul_mod, hc2, Nat.one_mul, Nat.mod_mod]
  have hc8 : Nat.Coprime c 8 := Nat.Coprime.coprime_dvd_right h8q hcq
  have hF8 : ∀ v, φ v % 8 = 0 ↔ v % 8 = 0 := by
    intro v
    change EightWLOG.nrm q (c * v) % 8 = 0 ↔ v % 8 = 0
    rw [nrm_mod_eight hq h8q]
    constructor
    · intro h
      have : 8 ∣ c * v := Nat.dvd_of_mod_eq_zero h
      exact Nat.mod_eq_zero_of_dvd ((Nat.Coprime.symm hc8).dvd_of_dvd_mul_left this)
    · intro h
      exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) c)
  -- (F4) `φ a0 = 1`
  have hF4 : φ a0 = 1 := by
    change EightWLOG.nrm q (c * a0) = 1
    have : c * a0 ≡ 1 [MOD q] := by rw [Nat.mul_comm]; exact hac
    rw [nrm_congr this, hsmall 1 (by omega)]
  -- (F5) the covering identity
  have hF5 : ∀ j v, EightWLOG.nrm q (j * φ v) = EightWLOG.nrm q (EightWLOG.nrm q (c * j) * v) := by
    intro j v
    change EightWLOG.nrm q (j * EightWLOG.nrm q (c * v)) = EightWLOG.nrm q (EightWLOG.nrm q (c * j) * v)
    rw [nrm_mul_nrm hq, Nat.mul_comm (EightWLOG.nrm q (c * j)) v, nrm_mul_nrm hq]
    congr 1; ring
  -- `‖x a‖ = b` and `‖x' a‖ = b` scale to `‖x (φ a)‖ = φ b`, and back
  have hratio : ∀ x a b, EightWLOG.nrm q (x * φ a) = φ b ↔ EightWLOG.nrm q (x * a) = EightWLOG.nrm q b := by
    intro x a b
    have e1 : EightWLOG.nrm q (x * φ a) = EightWLOG.nrm q (c * (x * a)) := by
      change EightWLOG.nrm q (x * EightWLOG.nrm q (c * a)) = _
      rw [nrm_mul_nrm hq]; congr 1; ring
    rw [e1]
    constructor
    · intro h
      rcases nrm_inj hq h with h1 | h1
      · exact nrm_congr ((hback (x * a)).symm.trans ((h1.mul_left a0).trans (hback b)))
      · have := h1.mul_left a0
        rw [Nat.mul_add, Nat.mul_zero] at this
        exact nrm_neg hq (((hback (x * a)).add (hback b)).symm.trans this)
    · intro h
      rcases nrm_inj hq h with h1 | h1
      · exact nrm_congr ((h1.mul_left c))
      · apply nrm_neg hq
        have := h1.mul_left c
        rw [Nat.mul_add, Nat.mul_zero] at this
        exact this
  -- `d ≤ 4p` and `φ b0 = d`
  have hb0a := hadm b0 hb0
  have hx0 : 1 ≤ φ b0 ∧ φ b0 ≤ 4 * p ∧ φ b0 % p ≠ 0 := hF1 b0 hb0a
  have hdle : d ≤ φ b0 := by
    apply Nat.find_min' hex
    refine ⟨a0, ha0, ha02, b0, hb0, hb08, hx0.1, ?_⟩
    have := (hratio (φ b0) a0 b0).1
    rw [hF4, Nat.mul_one, hsmall _ hx0.2.1] at this
    exact (this rfl).trans (hsmall b0 hb0a.2.1)
  have hphib0 : φ b0 = d := by
    have h1 : EightWLOG.nrm q (d * φ a0) = φ b0 := by
      rw [hratio, hsmall b0 hb0a.2.1]; exact hdab
    rw [hF4, Nat.mul_one, hsmall d (by omega)] at h1
    exact h1.symm
  -- the image
  refine ⟨d, V.image φ, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨a0, ha0, hF4⟩
  · exact Finset.mem_image.2 ⟨b0, hb0, hphib0⟩
  · rw [← hphib0]; exact (hF8 b0).2 hb08
  · intro u' hu' hu'2 y' hy' hy'8 ⟨x, hx1, hxd, hx⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy'
    rw [nrm_eq_wlog, show 8 * p = q by omega, hratio, hsmall b (hadm b hb).2.1] at hx
    exact hmin x hxd ⟨a, ha, by rw [← hF3]; exact hu'2, b, hb, (hF8 b).1 hy'8, hx1, hx⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact mem_admSet.2 (hF1 v (hadm v hv))
  · rw [Finset.card_image_of_injOn (fun v hv w hw h => hF2 v (hadm v hv) w (hadm w hw) h), hcard]
  · have : (V.image φ).filter (fun v => v % 2 = 0) = (V.filter (fun v => v % 2 = 0)).image φ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, h2⟩
        exact ⟨v, ⟨hv, by rw [← hF3]; exact h2⟩, rfl⟩
      · rintro ⟨v, ⟨hv, h2⟩, rfl⟩
        exact ⟨⟨v, hv, rfl⟩, by rw [hF3]; exact h2⟩
    rw [this]
    exact le_trans Finset.card_image_le hev
  · intro j hj
    have hjw := mem_winSet.1 hj
    have hj'1 : 1 ≤ EightWLOG.nrm q (c * j) := nrm_pos hq (hnz j hjw.1 hjw.2)
    have hj'2 : EightWLOG.nrm q (c * j) ≤ 4 * p := by have := nrm_le q (c * j); omega
    obtain ⟨v, hv, hcov⟩ := hcovV _ (mem_winSet.2 ⟨hj'1, hj'2⟩)
    refine ⟨φ v, Finset.mem_image.2 ⟨v, hv, rfl⟩, ?_⟩
    rw [coversAt_eq] at hcov ⊢
    rw [← hqdef] at hcov ⊢
    rw [hF5]; exact hcov


/-- a search state is closed: with the chosen set `S` (ghost), no completion `Z ⊆ avail`
disjoint from `S` making `S ∪ Z` a bad representative covers the positions of `unc` -/
def StateClosed (X : Ctx) (d : ℕ) (S : Finset ℕ) (avail unc : ℕ) : Prop :=
  ∀ Z : Finset ℕ, Disjoint S Z → (∀ v ∈ Z, bitS avail v = true) →
    Bad X.p (S ∪ Z) → Rep X.p d (S ∪ Z) →
    (∀ j, bitC unc j = true → ∃ v ∈ Z, coversAt 7 X.p j v = true) → False

/-! # Proof of the replay semantics -/

/-! ## Bridges from the raw checker primitives to `Nat.testBit` / division -/

theorem ltN_eq (a b : ℕ) : ltN a b = decide (a < b) := by
  show Nat.ble (a + 1) b = decide (a < b)
  cases h : Nat.ble (a + 1) b
  · have : ¬ (a + 1 ≤ b) := by intro h'; rw [← Nat.ble_eq] at h'; rw [h] at h'; exact absurd h' (by decide)
    simp; omega
  · have : a + 1 ≤ b := by rw [← Nat.ble_eq]; exact h
    simp; omega

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have : ¬ a = b := by intro h'; rw [← Nat.beq_eq] at h'; rw [h] at h'; exact absurd h' (by decide)
    simp [this]
  · have : a = b := by rw [← Nat.beq_eq]; exact h
    simp [this]

theorem ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := by intro h'; rw [← Nat.ble_eq] at h'; rw [h] at h'; exact absurd h' (by decide)
    simp [this]
  · have : a ≤ b := by rw [← Nat.ble_eq]; exact h
    simp [this]

theorem testBit_eq_land (x i : ℕ) : x.testBit i = !Nat.beq (Nat.land (Nat.shiftRight x i) 1) 0 := by
  rw [beq_eq_decide, Nat.testBit_eq_decide_div_mod_eq]
  show decide (x / 2 ^ i % 2 = 1) = !decide ((x >>> i) &&& 1 = 0)
  rw [Nat.shiftRight_eq_div_pow, show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_two_eq_zero_or_one (x / 2 ^ i)
  rcases this with h | h <;> simp [h]

theorem bitS_eq (x v : ℕ) : bitS x v = x.testBit (16 * v) := by
  rw [testBit_eq_land]; rfl

theorem bitC_eq (x j : ℕ) : bitC x j = x.testBit j := by
  rw [testBit_eq_land]; rfl

theorem fld_eq (x v : ℕ) : fld x v = x / 2 ^ (16 * v) % 2 ^ 16 := by
  show (x >>> (16 * v)) &&& (2 ^ 16 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_clr (x m i : ℕ) : (clr x m).testBit i = (x.testBit i && !m.testBit i) := by
  show (x ^^^ (x &&& m)).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases x.testBit i <;> cases m.testBit i <;> rfl

theorem sbit_eq (v : ℕ) : sbit v = 2 ^ (16 * v) := by
  show 1 <<< (16 * v) = _
  rw [Nat.one_shiftLeft]

/-! ## Base-`b` digits of a finite sum -/

theorem geom_lt (b : ℕ) (hb : 0 < b) (f : ℕ → ℕ) :
    ∀ N, (∀ v < N, f v < b) → ∑ v ∈ range N, f v * b ^ v < b ^ N
  | 0 => by intro; simp
  | N + 1 => by
    intro h
    rw [sum_range_succ, pow_succ]
    have h1 := geom_lt b hb f N (fun v hv => h v (by omega))
    have h2 : f N * b ^ N ≤ (b - 1) * b ^ N := Nat.mul_le_mul_right _ (by have := h N (by omega); omega)
    have h3 : (b - 1) * b ^ N + b ^ N = b ^ N * b := by
      rw [Nat.mul_comm (b ^ N) b, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    omega

theorem digit (b : ℕ) (hb : 0 < b) (f : ℕ → ℕ) :
    ∀ N, (∀ v < N, f v < b) → ∀ v0, (∑ v ∈ range N, f v * b ^ v) / b ^ v0 % b = if v0 < N then f v0 else 0
  | 0 => by intro _ v0; simp
  | N + 1 => by
    intro h v0
    have hpos : ∀ n, 0 < b ^ n := fun n => Nat.pow_pos hb
    rw [sum_range_succ]
    rcases lt_trichotomy v0 N with hlt | heq | hgt
    · have ih := digit b hb f N (fun v hv => h v (by omega)) v0
      have e : f N * b ^ N = b ^ v0 * (b * (f N * b ^ (N - v0 - 1))) := by
        rw [show b ^ N = b ^ (v0 + 1 + (N - v0 - 1)) by congr 1; omega]; ring
      rw [e, Nat.add_mul_div_left _ _ (hpos v0), Nat.add_mul_mod_self_left, ih]
      simp [hlt, show v0 < N + 1 by omega]
    · subst heq
      have hS := geom_lt b hb f v0 (fun v hv => h v (by omega))
      rw [Nat.mul_comm (f v0), Nat.add_mul_div_left _ _ (hpos v0), Nat.div_eq_of_lt hS, Nat.zero_add,
        Nat.mod_eq_of_lt (h v0 (by omega))]
      simp
    · have hS := geom_lt b hb f (N + 1) h
      rw [sum_range_succ] at hS
      have : b ^ (N + 1) ≤ b ^ v0 := Nat.pow_le_pow_right hb (by omega)
      rw [Nat.div_eq_of_lt (by omega)]
      simp [show ¬ v0 < N + 1 by omega]

theorem sum_to_range (b : ℕ) (E : Finset ℕ) (g : ℕ → ℕ) (N : ℕ) (hE : ∀ v ∈ E, v < N) :
    ∑ v ∈ E, g v * b ^ v = ∑ v ∈ range N, (if v ∈ E then g v else 0) * b ^ v := by
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  congr 1
  ext v; simp only [mem_inter, mem_range]
  constructor
  · intro h; exact ⟨hE v h, h⟩
  · intro h; exact h.2

theorem testBit_compactOf (s : Finset ℕ) (i : ℕ) : (compactOf s).testBit i = decide (i ∈ s) := by
  set N := s.sup id + 1
  have hN : ∀ v ∈ s, v < N := fun v hv => Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)
  have e : compactOf s = ∑ v ∈ range N, (if v ∈ s then 1 else 0) * 2 ^ v := by
    unfold compactOf
    rw [← sum_to_range 2 s (fun _ => 1) N hN]
    simp
  rw [Nat.testBit_eq_decide_div_mod_eq, e, digit 2 (by norm_num) _ N (by intro v _; split <;> omega) i]
  by_cases hi : i ∈ s
  · simp [hi, hN i hi]
  · by_cases h2 : i < N <;> simp [hi, h2]

theorem spreadOf_eq_compactOf (A : Finset ℕ) : spreadOf A = compactOf (A.image (16 * ·)) := by
  unfold spreadOf compactOf
  rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]

theorem testBit_spreadOf (A : Finset ℕ) (i : ℕ) :
    (spreadOf A).testBit i = decide (∃ v ∈ A, 16 * v = i) := by
  rw [spreadOf_eq_compactOf, testBit_compactOf]
  simp

theorem bitS_spreadOf (A : Finset ℕ) (v : ℕ) : bitS (spreadOf A) v = decide (v ∈ A) := by
  rw [bitS_eq, testBit_spreadOf]
  congr 1
  apply propext
  constructor
  · rintro ⟨w, hw, h⟩; have : w = v := by omega
    subst this; exact hw
  · intro h; exact ⟨v, h, rfl⟩

theorem fld_sum (N : ℕ) (f : ℕ → ℕ) (hf : ∀ v < N, f v < 2 ^ 16) (v : ℕ) :
    fld (∑ w ∈ range N, f w * 2 ^ (16 * w)) v = if v < N then f v else 0 := by
  rw [fld_eq]
  simp_rw [pow_mul]
  exact digit (2 ^ 16) (by norm_num) f N hf v

theorem sum_spread (U : Finset ℕ) (y : ℕ → ℕ) (A : ℕ → Finset ℕ) (N : ℕ)
    (hA : ∀ j ∈ U, ∀ v ∈ A j, v < N) :
    ∑ j ∈ U, y j * spreadOf (A j) =
      ∑ v ∈ range N, (∑ j ∈ U, if v ∈ A j then y j else 0) * 2 ^ (16 * v) := by
  have e : ∀ j ∈ U, y j * spreadOf (A j) =
      ∑ v ∈ range N, (if v ∈ A j then y j else 0) * 2 ^ (16 * v) := by
    intro j hj
    unfold spreadOf
    rw [Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem]
    congr 1
    ext v; simp only [mem_inter, mem_range]
    exact ⟨fun h => ⟨hA j hj v h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-! ## Lowest set bit -/

theorem testBit_two_pow_mul_add (n h c i : ℕ) (hc : c < 2 ^ n) :
    (2 ^ n * h + c).testBit i = if i < n then c.testBit i else h.testBit (i - n) := by
  split
  · rename_i hi
    have : (2 ^ n * h + c) % 2 ^ n = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    have h2 := Nat.testBit_mod_two_pow (2 ^ n * h + c) n i
    rw [this] at h2
    simp [hi] at h2
    exact h2.symm
  · rename_i hi
    have h1 : (2 ^ n * h + c) >>> n = h := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num)),
        Nat.div_eq_of_lt hc, Nat.zero_add]
    have h2 := Nat.testBit_shiftRight (i := n) (j := i - n) (2 ^ n * h + c)
    rw [h1, show n + (i - n) = i by omega] at h2
    exact h2.symm

theorem low_iso (u : ℕ) (hu : u ≠ 0) :
    ∃ k, u ^^^ (u &&& (u - 1)) = 2 ^ k ∧ u.testBit k = true ∧ ∀ i < k, u.testBit i = false := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hu
  obtain ⟨h, rfl⟩ := hm
  have hk1 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ k * (2 * h + 1) = 2 ^ (k + 1) * h + 2 ^ k := by ring
  have e2 : 2 ^ k * (2 * h + 1) - 1 = 2 ^ (k + 1) * h + (2 ^ k - 1) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [e1]; omega
  have b1 : ∀ i, (2 ^ k * (2 * h + 1)).testBit i = if i < k + 1 then decide (k = i) else h.testBit (i - (k + 1)) := by
    intro i; rw [e1, testBit_two_pow_mul_add _ _ _ _ hk1, Nat.testBit_two_pow]
  have b2 : ∀ i, (2 ^ k * (2 * h + 1) - 1).testBit i = if i < k + 1 then decide (i < k) else h.testBit (i - (k + 1)) := by
    intro i; rw [e2, testBit_two_pow_mul_add _ _ _ _ (by omega), Nat.testBit_two_pow_sub_one]
  refine ⟨k, ?_, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_and, b1, b2, Nat.testBit_two_pow]
    split
    · by_cases hi : k = i
      · subst hi; simp
      · simp [hi]
    · rename_i hi
      have : ¬ k = i := by omega
      simp [this]
  · rw [b1]; simp
  · intro i hi; rw [b1]; simp [show i < k + 1 by omega]; omega

theorem lgk_pow : ∀ k e i, e < 2 ^ k → lgk k (2 ^ e) i = i + e
  | 0, e, i, h => by
    have : e = 0 := by simp at h; omega
    subst this; rfl
  | k + 1, e, i, h => by
    rw [lgk]
    show (bif Nat.beq ((2 ^ e) >>> (1 <<< k)) 0 then lgk k (2 ^ e) i
      else lgk k ((2 ^ e) >>> (1 <<< k)) (i + (1 <<< k))) = i + e
    rw [Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow, beq_eq_decide]
    by_cases he : e < 2 ^ k
    · have : 2 ^ e / 2 ^ 2 ^ k = 0 := Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) he)
      rw [this]; simp
      exact lgk_pow k e i he
    · have hle : 2 ^ k ≤ e := by omega
      rw [Nat.pow_div hle (by norm_num)]
      simp
      rw [lgk_pow k (e - 2 ^ k) _ (by rw [pow_succ] at h; omega)]
      omega

theorem lowS_eq (x k : ℕ) (hx : x ^^^ (x &&& (x - 1)) = 2 ^ k) (hk : k < 2 ^ 14) : lowS x = k := by
  show lgk 14 (x ^^^ (x &&& (x - 1))) 0 = k
  rw [hx, lgk_pow 14 k 0 hk, Nat.zero_add]

/-! ## Popcount loops -/

theorem bits_and_pred_lt (K u : ℕ) (hu : u ≠ 0) (hK : u < 2 ^ K) :
    ((range K).filter (fun i => (u &&& (u - 1)).testBit i = true)).card <
      ((range K).filter (fun i => u.testBit i = true)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro i; simp only [mem_filter, mem_range, Nat.testBit_and, Bool.and_eq_true]; tauto
  · intro heq
    have hlt : u &&& (u - 1) < u := lt_of_le_of_lt Nat.and_le_right (by omega)
    apply (ne_of_lt hlt)
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < K
    · have := congrArg (fun s => i ∈ s) heq
      simp only [mem_filter, mem_range, hi, true_and, eq_iff_iff] at this
      cases h1 : (u &&& (u - 1)).testBit i <;> cases h2 : u.testBit i <;> simp_all
    · have h2 : u < 2 ^ i := lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow h2, Nat.testBit_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (by omega))]

theorem pcl_le (K : ℕ) : ∀ f u acc, u < 2 ^ K →
    pcl f u acc ≤ acc + ((range K).filter (fun i => u.testBit i = true)).card
  | 0, u, acc, _ => by simp [pcl]
  | f + 1, u, acc, hK => by
    rw [pcl]
    show (bif Nat.beq u 0 then acc else pcl f (u &&& (u - 1)) (acc + 1)) ≤ _
    rw [beq_eq_decide]
    by_cases hu : u = 0
    · simp [hu]
    · simp only [hu, decide_false, cond_false]
      have := pcl_le K f (u &&& (u - 1)) (acc + 1) (lt_of_le_of_lt Nat.and_le_left hK)
      have := bits_and_pred_lt K u hu hK
      omega

theorem cntB_eq (K : ℕ) (cb' : ℕ → ℕ) : ∀ f u acc, u < 2 ^ K →
    ((range K).filter (fun i => u.testBit i = true)).card ≤ f →
    cntB cb' f u acc = acc + ∑ j ∈ (range K).filter (fun i => u.testBit i = true), cb' (2 ^ j)
  | 0, u, acc, hK, hc => by
    have : (range K).filter (fun i => u.testBit i = true) = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    rw [this]; simp [cntB]
  | f + 1, u, acc, hK, hc => by
    rw [cntB]
    show (bif Nat.beq u 0 then acc else cntB cb' f (u ^^^ (u ^^^ (u &&& (u - 1))))
      (acc + cb' (u ^^^ (u &&& (u - 1))))) = _
    rw [beq_eq_decide]
    by_cases hu : u = 0
    · subst hu; simp
    · obtain ⟨k, hk, hkb, -⟩ := low_iso u hu
      simp only [hu, decide_false, cond_false, hk]
      have hkK : k < K := by
        by_contra hh
        have : u < 2 ^ k := lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [Nat.testBit_lt_two_pow this] at hkb; exact absurd hkb (by decide)
      have hset : (range K).filter (fun i => (u ^^^ 2 ^ k).testBit i = true) =
          ((range K).filter (fun i => u.testBit i = true)).erase k := by
        ext i
        simp only [mem_filter, mem_range, mem_erase, Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hi : k = i
        · subst hi; simp [hkb]
        · simp [hi, Ne.symm hi]
      have hmem : k ∈ (range K).filter (fun i => u.testBit i = true) := by simp [hkK, hkb]
      have hlt' : u ^^^ 2 ^ k < 2 ^ K := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_lt_two_pow (lt_of_lt_of_le hK
          (Nat.pow_le_pow_right (by norm_num) hi))]
        simp; omega
      rw [cntB_eq K cb' f _ _ hlt' (by rw [hset, Finset.card_erase_of_mem hmem]; omega), hset,
        ← Finset.add_sum_erase _ _ hmem]
      ring


/-! ## Spread / compact semantics of the context -/

/-- the positions of the compact mask `u` inside the window -/
def Uf (p u : ℕ) : Finset ℕ := (winSet p).filter (fun j => u.testBit j = true)

/-- a spread mask whose set bits are admissible speeds -/
def Clean (p x : ℕ) : Prop := ∀ i, x.testBit i = true → ∃ v ∈ admSet p, 16 * v = i

/-- the covering relation restricted to admissible speeds -/
def cv (p : ℕ) (j v : ℕ) : Prop := v ∈ admSet p ∧ coversAt 7 p j v = true

instance (p j v : ℕ) : Decidable (cv p j v) := by unfold cv; infer_instance

theorem adm_lt {p v : ℕ} (h : v ∈ admSet p) : v < 4 * p + 1 := by
  have := (mem_admSet.1 h).2.1; omega

theorem testBit_fld (x v s : ℕ) (hs : s < 16) : x.testBit (16 * v + s) = (fld x v).testBit s := by
  rw [fld_eq, Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  simp [hs]

theorem spreadOf_range (A : Finset ℕ) (N : ℕ) (hA : ∀ v ∈ A, v < N) :
    spreadOf A = ∑ v ∈ range N, (if v ∈ A then 1 else 0) * 2 ^ (16 * v) := by
  unfold spreadOf
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  congr 1
  ext v; simp only [mem_inter, mem_range]
  exact ⟨fun h => ⟨hA v h, h⟩, fun h => h.2⟩

/-- product digit identity used by `spc` -/
theorem mul_ones (N : ℕ) (f : ℕ → ℕ) :
    (∑ a ∈ range N, f a * 2 ^ (16 * a)) * (∑ b ∈ range N, 1 * 2 ^ (16 * b)) =
      ∑ c ∈ range (2 * N), (∑ a ∈ range N, if a ≤ c ∧ c < a + N then f a else 0) * 2 ^ (16 * c) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm (s := range (2 * N))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : (range (2 * N)).filter (fun c => a ≤ c ∧ c < a + N) = (range N).map (addLeftEmbedding a) := by
    ext c
    simp only [mem_filter, mem_range, mem_map, addLeftEmbedding_apply]
    constructor
    · intro h; exact ⟨c - a, by omega, by omega⟩
    · rintro ⟨b, hb, rfl⟩; omega
  rw [this, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro b _
  simp only [addLeftEmbedding_apply]
  rw [Nat.mul_add, pow_add]; ring

section Tab
variable {X : Ctx} (hX : TableOK X)
include hX

theorem tab_W : X.W = 4 * X.p := hX.2.1
theorem tab_p : 0 < X.p := hX.1
theorem tab_W1024 : X.W < 1024 := hX.2.2.1

theorem covby_eq {j : ℕ} (hj : j ∈ winSet X.p) :
    X.covby j = spreadOf ((admSet X.p).filter (fun v => coversAt 7 X.p j v = true)) :=
  hX.2.2.2.2.2.2.2.2.1 j hj

theorem bitS_covby {j v : ℕ} (hj : j ∈ winSet X.p) : bitS (X.covby j) v = decide (cv X.p j v) := by
  rw [covby_eq hX hj, bitS_spreadOf]
  simp [cv]

theorem testBit_cov {v j : ℕ} (hv : v ∈ admSet X.p) :
    (X.cov v).testBit j = decide (j ∈ winSet X.p ∧ coversAt 7 X.p j v = true) := by
  rw [hX.2.2.2.2.2.2.2.1 v hv, testBit_compactOf]
  simp

theorem cntF_eq (u acc : ℕ) (hu : ∀ j, u.testBit j = true → j ∈ winSet X.p) :
    X.cntF u acc = acc + ∑ j ∈ Uf X.p u, X.covby j :=
  hX.2.2.2.2.2.2.2.2.2 u acc hu

/-- the counter vector of weights `y` on `U` in digit form -/
theorem weighted_repr (U : Finset ℕ) (hU : U ⊆ winSet X.p) (y : ℕ → ℕ) :
    ∑ j ∈ U, y j * X.covby j = ∑ v ∈ range (X.W + 1), load (cv X.p) U y v * 2 ^ (16 * v) := by
  rw [Finset.sum_congr rfl (fun j hj => by rw [covby_eq hX (hU hj)])]
  rw [sum_spread U y _ (X.W + 1) (by
    intro j _ v hv; rw [tab_W hX]; exact adm_lt (mem_filter.1 hv).1)]
  congr 1; ext v; congr 1
  unfold load
  apply Finset.sum_congr rfl
  intro j _
  simp [cv]

omit hX in
theorem load_le (U : Finset ℕ) (y : ℕ → ℕ) (v : ℕ) : load (cv X.p) U y v ≤ ∑ j ∈ U, y j := by
  unfold load
  apply Finset.sum_le_sum
  intro j _; split <;> omega

theorem load_out (U : Finset ℕ) (y : ℕ → ℕ) (v : ℕ) (hv : ¬ v < X.W + 1) : load (cv X.p) U y v = 0 := by
  unfold load
  apply Finset.sum_eq_zero
  intro j _
  have : ¬ cv X.p j v := by
    intro h; have := adm_lt h.1; rw [tab_W hX] at hv; omega
  simp [this]

theorem fld_weighted (U : Finset ℕ) (hU : U ⊆ winSet X.p) (y : ℕ → ℕ) (hY : ∑ j ∈ U, y j < 2 ^ 16)
    (v : ℕ) : fld (∑ j ∈ U, y j * X.covby j) v = load (cv X.p) U y v := by
  rw [weighted_repr hX U hU, fld_sum _ _ (fun w _ => lt_of_le_of_lt (load_le (X := X) U y w) hY)]
  split
  · rfl
  · rw [load_out hX U y v (by assumption)]

theorem ones_repr : X.ones = ∑ v ∈ range (X.W + 1), 1 * 2 ^ (16 * v) := by
  rw [hX.2.2.2.2.2.2.1]; unfold spreadOf; simp

/-- **`allLe` semantics.** -/
theorem allLe_sound (L : ℕ) (ℓ : ℕ → ℕ) (hL : L = ∑ v ∈ range (X.W + 1), ℓ v * 2 ^ (16 * v))
    (hℓ : ∀ v, ℓ v < 2 ^ 15) (M t : ℕ) (h : allLe X L M t = true) :
    ∀ v < X.W + 1, bitS M v = true → ℓ v ≤ t := by
  intro v hv hM
  unfold allLe at h
  rw [Bool.and_eq_true, ltN_eq, beq_eq_decide] at h
  obtain ⟨h1, h2⟩ := h
  have ht : t < 32768 := of_decide_eq_true h1
  have h0 : (L + (32767 - t) * X.ones) &&& (M <<< 15) = 0 := of_decide_eq_true h2
  have hsum : L + (32767 - t) * X.ones = ∑ w ∈ range (X.W + 1), (ℓ w + (32767 - t)) * 2 ^ (16 * w) := by
    rw [hL, ones_repr hX, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _; ring
  have hb := congrArg (fun x => x.testBit (16 * v + 15)) h0
  simp only [Nat.testBit_and, Nat.zero_testBit] at hb
  rw [Nat.testBit_shiftLeft, show 16 * v + 15 - 15 = 16 * v by omega, ← bitS_eq, hM] at hb
  simp only [ge_iff_le, show 15 ≤ 16 * v + 15 by omega, decide_true, Bool.and_true] at hb
  rw [hsum, testBit_fld _ _ _ (by norm_num),
    fld_sum _ _ (fun w _ => by have := hℓ w; omega), if_pos hv, Nat.testBit_eq_decide_div_mod_eq] at hb
  have := hℓ v
  simp at hb
  omega

theorem spc_spreadOf (A : Finset ℕ) (hA : A ⊆ admSet X.p) : spc X (spreadOf A) = A.card := by
  have hW := tab_W1024 hX
  have hN : ∀ v ∈ A, v < X.W + 1 := fun v hv => by rw [tab_W hX]; exact adm_lt (hA hv)
  show fld (spreadOf A * X.ones) X.W = A.card
  rw [spreadOf_range A (X.W + 1) hN, ones_repr hX, mul_ones]
  have hcard : ∑ a ∈ range (X.W + 1), (if a ∈ A then 1 else 0) = A.card := by
    simp only [Finset.sum_boole, Nat.cast_id]; congr 1; ext v; simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hN v h, h⟩⟩
  have hle : ∀ c, (∑ a ∈ range (X.W + 1), if a ≤ c ∧ c < a + (X.W + 1) then (if a ∈ A then 1 else 0) else 0)
      ≤ X.W + 1 := by
    intro c
    calc _ ≤ ∑ a ∈ range (X.W + 1), 1 := Finset.sum_le_sum (fun a _ => by split <;> (try split) <;> omega)
      _ = X.W + 1 := by simp
  rw [fld_sum _ _ (fun c _ => lt_of_le_of_lt (hle c) (by omega)), if_pos (by omega)]
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro a ha; rw [mem_range] at ha
  rw [if_pos ⟨by omega, by omega⟩]

omit hX in
theorem clean_eq (x : ℕ) (hx : Clean X.p x) :
    x = spreadOf ((admSet X.p).filter (fun v => bitS x v = true)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_spreadOf]
  cases h : x.testBit i
  · symm; rw [decide_eq_false_iff_not]
    rintro ⟨v, hv, rfl⟩
    rw [mem_filter, bitS_eq, h] at hv; exact absurd hv.2 (by decide)
  · obtain ⟨v, hv, rfl⟩ := hx i h
    symm; rw [decide_eq_true_iff]
    exact ⟨v, mem_filter.2 ⟨hv, by rw [bitS_eq]; exact h⟩, rfl⟩

end Tab

theorem clean_clr {p x : ℕ} (m : ℕ) (hx : Clean p x) : Clean p (clr x m) := by
  intro i hi
  rw [testBit_clr, Bool.and_eq_true] at hi
  exact hx i hi.1

theorem clean_spreadOf {p : ℕ} (A : Finset ℕ) (hA : A ⊆ admSet p) : Clean p (spreadOf A) := by
  intro i hi
  rw [testBit_spreadOf] at hi
  obtain ⟨v, hv, h⟩ := of_decide_eq_true hi
  exact ⟨v, hA hv, h⟩

theorem clean_land {p x : ℕ} (m : ℕ) (hx : Clean p x) : Clean p (x &&& m) := by
  intro i hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  exact hx i hi.1

theorem bitS_clr (x m v : ℕ) : bitS (clr x m) v = (bitS x v && !bitS m v) := by
  rw [bitS_eq, bitS_eq, bitS_eq, testBit_clr]

theorem bitS_clr_sbit (x c v : ℕ) : bitS (clr x (sbit c)) v = (bitS x v && !decide (v = c)) := by
  rw [bitS_clr, sbit_eq, bitS_eq (2 ^ _), Nat.testBit_two_pow]
  congr 2
  rw [decide_eq_decide]; omega

theorem bitS_land (x m v : ℕ) : bitS (x &&& m) v = (bitS x v && bitS m v) := by
  rw [bitS_eq, bitS_eq, bitS_eq, Nat.testBit_and]


/-! ## Bound leaves -/

theorem readT_sound (C : ℕ → ℕ) (L t : ℕ) : ∀ n pv s M pos s' M' pos',
    readT C L t n pv s M pos = some (s', M', pos') →
    ∃ T : Finset ℕ, T.card = n ∧ (∀ v ∈ T, pv < v) ∧ (∀ v ∈ T, t ≤ fld L v) ∧
      s' = s + ∑ v ∈ T, fld L v ∧ ∀ v, bitS M' v = (bitS M v && decide (v ∉ T))
  | 0, pv, s, M, pos, s', M', pos', h => by
    simp only [readT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
  | n + 1, pv, s, M, pos, s', M', pos', h => by
    rw [readT] at h
    cases hc : (ltN pv (rd C pos) && Nat.ble t (fld L (rd C pos)))
    · rw [hc] at h; exact absurd h (by simp)
    · rw [hc] at h
      rw [Bool.and_eq_true, ltN_eq, ble_eq_decide] at hc
      have h1 : pv < rd C pos := of_decide_eq_true hc.1
      have h2 : t ≤ fld L (rd C pos) := of_decide_eq_true hc.2
      obtain ⟨T, hTc, hTp, hTt, hs, hM⟩ := readT_sound C L t n _ _ _ _ s' M' pos' h
      set v := rd C pos
      have hvT : v ∉ T := fun hv => by have := hTp v hv; omega
      refine ⟨insert v T, by rw [Finset.card_insert_of_notMem hvT, hTc], ?_, ?_, ?_, ?_⟩
      · intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h1
        · have := hTp w hw; omega
      · intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h2
        · exact hTt w hw
      · rw [hs, Finset.sum_insert hvT]; show s + fld L v + _ = _; ring
      · intro w
        rw [hM w, bitS_clr_sbit]
        by_cases hw : w = v
        · subst hw; simp
        · simp [hw]

theorem tailOK_sound (X : Ctx) (C : ℕ → ℕ) (L B av r pos pos' : ℕ)
    (h : tailOK X C L B av r pos = some pos') :
    ∃ T : Finset ℕ, ∃ t M, T.card ≤ r ∧ (∀ v ∈ T, t ≤ fld L v) ∧
      ∑ v ∈ T, fld L v + (r - T.card) * t < B ∧ allLe X L M t = true ∧
      ∀ v, bitS M v = (bitS av v && decide (v ∉ T)) := by
  unfold tailOK at h
  dsimp only at h
  cases hn : Nat.ble (rd C (Nat.succ pos)) r
  · rw [hn] at h; exact absurd h (by simp)
  · rw [hn] at h
    simp only [cond_true] at h
    split at h
    · exact absurd h (by simp)
    · rename_i s M p2 hr
      cases hc : (allLe X L M (rd C pos) && ltN (Nat.add s (Nat.mul (Nat.sub r (rd C (Nat.succ pos))) (rd C pos))) B)
      · rw [hc] at h; exact absurd h (by simp)
      · rw [Bool.and_eq_true, ltN_eq] at hc
        obtain ⟨T, hTc, -, hTt, hs, hM⟩ := readT_sound C L _ _ _ _ _ _ _ _ _ hr
        have hnr : rd C (Nat.succ pos) ≤ r := by rw [ble_eq_decide] at hn; exact of_decide_eq_true hn
        refine ⟨T, rd C pos, M, by omega, hTt, ?_, hc.1, hM⟩
        have h' : s + (r - rd C (Nat.succ pos)) * rd C pos < B := of_decide_eq_true hc.2
        rw [hs, ← hTc, Nat.zero_add] at h'; exact h'

theorem leaf_false {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ) (U' : Finset ℕ) (hU' : U' ⊆ winSet X.p)
    (y : ℕ → ℕ) (hY : ∑ j ∈ U', y j < 2 ^ 15) (B : ℕ) (hB : B ≤ ∑ j ∈ U', y j) (av r pos pos' : ℕ)
    (h : tailOK X C (∑ j ∈ U', y j * X.covby j) B av r pos = some pos')
    (Z : Finset ℕ) (hZa : Z ⊆ admSet X.p) (hZb : ∀ v ∈ Z, bitS av v = true) (hZr : Z.card ≤ r)
    (hcov : ∀ j ∈ U', ∃ v ∈ Z, coversAt 7 X.p j v = true) : False := by
  obtain ⟨T, t, M, hTr, hTt, hlt, hall, hM⟩ := tailOK_sound X C _ B av r pos pos' h
  have hfl : ∀ v, fld (∑ j ∈ U', y j * X.covby j) v = load (cv X.p) U' y v :=
    fld_weighted hX U' hU' y (by omega)
  have hle := allLe_sound hX _ (load (cv X.p) U' y) (weighted_repr hX U' hU' y)
    (fun v => lt_of_le_of_lt (load_le (X := X) U' y v) hY) M t hall
  refine weighted_bound_no_cover (cv X.p) U' y Z T r t hTr ?_ ?_ ?_ Z (subset_refl _) hZr ?_
  · intro v hv hvT
    apply hle v (by rw [tab_W hX]; exact adm_lt (hZa hv))
    rw [hM v, hZb v hv]; simp [hvT]
  · intro v hv; rw [← hfl]; exact hTt v hv
  · simp only [hfl] at hlt; omega
  · intro j hj
    obtain ⟨v, hv, hc⟩ := hcov j hj
    exact ⟨v, hv, hZa hv, hc⟩

theorem readW_sound (X : Ctx) (C : ℕ → ℕ) (unc : ℕ) : ∀ n pj L Y pos L' Y' pos',
    readW X C unc n pj L Y pos = some (L', Y', pos') →
    ∃ U' : Finset ℕ, ∃ y : ℕ → ℕ, (∀ j ∈ U', pj < j ∧ unc.testBit j = true) ∧
      L' = L + ∑ j ∈ U', y j * X.covby j ∧ Y' = Y + ∑ j ∈ U', y j
  | 0, pj, L, Y, pos, L', Y', pos', h => by
    simp only [readW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  | n + 1, pj, L, Y, pos, L', Y', pos', h => by
    rw [readW] at h
    cases hc : (ltN pj (Nat.land (rd C pos) 1023) && bitC unc (Nat.land (rd C pos) 1023) &&
        Nat.ble 1 (Nat.shiftRight (rd C pos) 10))
    · rw [hc] at h; exact absurd h (by simp)
    · rw [hc] at h
      rw [Bool.and_eq_true, Bool.and_eq_true, ltN_eq, bitC_eq] at hc
      set j := Nat.land (rd C pos) 1023
      set yv := Nat.shiftRight (rd C pos) 10
      have h1 : pj < j := of_decide_eq_true hc.1.1
      obtain ⟨U'', y'', hU, hL, hY⟩ := readW_sound X C unc n _ _ _ _ L' Y' pos' h
      have hjU : j ∉ U'' := fun hj => by have := (hU j hj).1; omega
      refine ⟨insert j U'', Function.update y'' j yv, ?_, ?_, ?_⟩
      · intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
        · exact ⟨h1, hc.1.2⟩
        · have := hU w hw; exact ⟨by omega, this.2⟩
      · rw [hL, Finset.sum_insert hjU]
        simp only [Function.update_self]
        rw [Finset.sum_congr (f := fun w => Function.update y'' j yv w * X.covby w) rfl (fun w hw => by
          show Function.update y'' j yv w * X.covby w = y'' w * X.covby w
          rw [Function.update_of_ne (by rintro rfl; exact hjU hw)])]
        show L + yv * X.covby j + _ = _; ring
      · rw [hY, Finset.sum_insert hjU]
        simp only [Function.update_self]
        rw [Finset.sum_congr (f := fun w => Function.update y'' j yv w) rfl (fun w hw => by
          show Function.update y'' j yv w = y'' w
          rw [Function.update_of_ne (by rintro rfl; exact hjU hw)])]
        show Y + yv + _ = _; ring

theorem card_Uf_lt (p u : ℕ) (hp : 4 * p < 1024) : (Uf p u).card < 2 ^ 15 := by
  have : (Uf p u).card ≤ (winSet p).card := Finset.card_le_card (Finset.filter_subset _ _)
  have h2 : (winSet p).card = 4 * p := by simp [winSet]
  omega

theorem boundLeaf_false {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ) (unc cu nu av r pos pos' : ℕ)
    (h : boundLeaf X C unc cu nu av r pos = some pos')
    (hunc : ∀ j, unc.testBit j = true → j ∈ winSet X.p)
    (hcu : cu = ∑ j ∈ Uf X.p unc, X.covby j) (hnu : nu ≤ (Uf X.p unc).card)
    (Z : Finset ℕ) (hZa : Z ⊆ admSet X.p) (hZb : ∀ v ∈ Z, bitS av v = true) (hZr : Z.card ≤ r)
    (hcov : ∀ j, unc.testBit j = true → ∃ v ∈ Z, coversAt 7 X.p j v = true) : False := by
  have hW := tab_W1024 hX; rw [tab_W hX] at hW
  unfold boundLeaf at h
  dsimp only at h
  cases h3 : Nat.beq (rd C pos) 3
  · rw [h3] at h
    simp only [cond_false] at h
    cases h5 : Nat.beq (rd C pos) 5
    · rw [h5] at h; exact absurd h (by simp)
    · rw [h5] at h
      simp only [cond_true] at h
      split at h
      · exact absurd h (by simp)
      · rename_i L Y p2 hr
        obtain ⟨U', y, hU, hL, hY⟩ := readW_sound X C unc _ _ _ _ _ _ _ _ hr
        cases hy : ltN Y 32768
        · rw [hy] at h; exact absurd h (by simp)
        · rw [hy] at h
          simp only [cond_true] at h
          rw [ltN_eq] at hy
          have hy' := of_decide_eq_true hy
          simp only [Nat.zero_add] at hL hY
          subst hL hY
          have hU' : U' ⊆ winSet X.p := fun j hj => hunc j (hU j hj).2
          exact leaf_false hX C U' hU' y (by simpa using hy') _ le_rfl av r _ _ h Z hZa hZb hZr
            (fun j hj => hcov j (hU j hj).2)
  · rw [h3] at h
    simp only [cond_true] at h
    have e : cu = ∑ j ∈ Uf X.p unc, (fun _ => 1) j * X.covby j := by simp [hcu]
    rw [e] at h
    exact leaf_false hX C (Uf X.p unc) (Finset.filter_subset _ _) (fun _ => 1)
      (by simpa using card_Uf_lt X.p unc (by omega)) nu (by simpa using hnu) av r _ _ h Z hZa hZb hZr
      (fun j hj => hcov j (mem_filter.1 hj).2)


/-! ## Ratio-min filter, parity leaf, child state -/

theorem filt_sound (X : Ctx) (C : ℕ → ℕ) (c d : ℕ) (V : Finset ℕ)
    (hRep : ∀ u ∈ V, u % 2 = 1 → ∀ y ∈ V, y % 8 = 0 → ¬ RatioLt X.p d y u) (hc : c ∈ V) :
    ∀ n av pos av2 pos2, filt X C c d n av pos = some (av2, pos2) →
      (∀ i, av2.testBit i = true → av.testBit i = true) ∧ ∀ v ∈ V, bitS av v = true → bitS av2 v = true
  | 0, av, pos, av2, pos2, h => by
    simp only [filt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => h, fun _ _ h => h⟩
  | n + 1, av, pos, av2, pos2, h => by
    rw [filt] at h
    dsimp only at h
    set w := rd C pos
    set x := rd C (Nat.succ pos)
    cases hcond : (Nat.ble 1 x && ltN x d &&
        ((Nat.beq (Nat.mod c 2) 1 && Nat.beq (Nat.mod w 8) 0 && Nat.beq (nrm (Nat.mul 8 X.p) (Nat.mul x c)) w) ||
         (Nat.beq (Nat.mod c 8) 0 && Nat.beq (Nat.mod w 2) 1 && Nat.beq (nrm (Nat.mul 8 X.p) (Nat.mul x w)) c)))
    · rw [hcond] at h; exact absurd h (by simp)
    · rw [hcond] at h
      simp only [cond_true] at h
      obtain ⟨ih1, ih2⟩ := filt_sound X C c d V hRep hc n _ _ _ _ h
      simp only [Bool.and_eq_true, Bool.or_eq_true, ble_eq_decide, ltN_eq, beq_eq_decide,
        decide_eq_true_eq] at hcond
      obtain ⟨⟨hx1, hxd⟩, hor⟩ := hcond
      have hwV : w ∉ V := by
        intro hw
        rcases hor with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
        · exact hRep c hc h1 w hw h2 ⟨x, hx1, hxd, h3⟩
        · exact hRep w hw h2 c hc h1 ⟨x, hx1, hxd, h3⟩
      refine ⟨fun i hi => ?_, fun v hv hb => ?_⟩
      · have := ih1 i hi; rw [testBit_clr, Bool.and_eq_true] at this; exact this.1
      · apply ih2 v hv
        rw [bitS_clr_sbit, hb]
        have : v ≠ w := fun e => hwV (e ▸ hv)
        simp [this]

theorem noCompl_sound (ev lim ae ao r : ℕ) : ∀ e, noCompl ev lim ae ao r e = true →
    ∀ e' ≤ e, lim < ev + e' ∨ ae < e' ∨ ao < r - e'
  | 0, h, e', he' => by
    have : e' = 0 := by omega
    subst this
    simp only [noCompl, Bool.or_eq_true, Bool.not_eq_true', ble_eq_decide, ltN_eq,
      decide_eq_true_eq, decide_eq_false_iff_not] at h
    omega
  | e + 1, h, e', he' => by
    rw [noCompl, Bool.and_eq_true] at h
    by_cases hlt : e' ≤ e
    · exact noCompl_sound ev lim ae ao r e h.2 e' hlt
    · have : e' = e + 1 := by omega
      subst this
      have h1 := h.1
      simp only [Bool.or_eq_true, Bool.not_eq_true', ble_eq_decide, ltN_eq,
        decide_eq_true_eq, decide_eq_false_iff_not] at h1
      omega

section Child
variable {X : Ctx} (hX : TableOK X)
include hX

theorem Uf_land_cov (unc c : ℕ) (hc : c ∈ admSet X.p) :
    Uf X.p (unc &&& X.cov c) = (Uf X.p unc).filter (fun j => coversAt 7 X.p j c = true) := by
  ext j
  simp only [Uf, mem_filter, Nat.testBit_and, Bool.and_eq_true, testBit_cov hX hc, decide_eq_true_eq]
  tauto

theorem Uf_clr_cov (unc c : ℕ) (hc : c ∈ admSet X.p) :
    Uf X.p (clr unc (X.cov c)) = (Uf X.p unc).filter (fun j => ¬ coversAt 7 X.p j c = true) := by
  ext j
  simp only [Uf, mem_filter, testBit_clr, Bool.and_eq_true, testBit_cov hX hc, Bool.not_eq_true',
    decide_eq_false_iff_not]
  tauto

theorem child_state (unc cu nu c : ℕ) (hunc : ∀ j, unc.testBit j = true → j ∈ winSet X.p)
    (hcu : cu = ∑ j ∈ Uf X.p unc, X.covby j) (hnu : nu ≤ (Uf X.p unc).card) (hc : c ∈ admSet X.p) :
    (∀ j, (clr unc (X.cov c)).testBit j = true → j ∈ winSet X.p) ∧
    cu - X.cntF (unc &&& X.cov c) 0 = ∑ j ∈ Uf X.p (clr unc (X.cov c)), X.covby j ∧
    nu - fld cu c ≤ (Uf X.p (clr unc (X.cov c))).card := by
  have hW := tab_W1024 hX; rw [tab_W hX] at hW
  refine ⟨?_, ?_, ?_⟩
  · intro j hj; rw [testBit_clr, Bool.and_eq_true] at hj; exact hunc j hj.1
  · rw [cntF_eq hX _ _ (by intro j hj; rw [Nat.testBit_and, Bool.and_eq_true] at hj; exact hunc j hj.1),
      Uf_land_cov hX unc c hc, Uf_clr_cov hX unc c hc, hcu, Nat.zero_add,
      ← Finset.sum_filter_add_sum_filter_not (Uf X.p unc) (fun j => coversAt 7 X.p j c = true)]
    omega
  · have e1 : cu = ∑ j ∈ Uf X.p unc, (fun _ => 1) j * X.covby j := by simp [hcu]
    rw [e1, fld_weighted hX (Uf X.p unc) (Finset.filter_subset _ _) (fun _ => 1) (by
      have := card_Uf_lt X.p unc (by omega); simp; omega)]
    have e2 : load (cv X.p) (Uf X.p unc) (fun _ => 1) c =
        ((Uf X.p unc).filter (fun j => coversAt 7 X.p j c = true)).card := by
      unfold load; rw [Finset.card_filter]
      apply Finset.sum_congr rfl; intro j _
      simp [cv, hc]
    rw [e2, Uf_clr_cov hX unc c hc]
    have := Finset.card_filter_add_card_filter_not (s := Uf X.p unc)
      (fun j => coversAt 7 X.p j c = true)
    omega

end Child

/-! ## The replay -/

/-- the invariant of a replay state (the chosen set `S` is ghost) -/
def GoInv (X : Ctx) (S : Finset ℕ) (sz ev avail unc cu nu : ℕ) : Prop :=
  sz = S.card ∧ ev = (S.filter (fun v => v % 2 = 0)).card ∧ Clean X.p avail ∧
  (∀ j, unc.testBit j = true → j ∈ winSet X.p) ∧ cu = ∑ j ∈ Uf X.p unc, X.covby j ∧
  nu ≤ (Uf X.p unc).card

theorem bad_card {p : ℕ} {S Z : Finset ℕ} (hd : Disjoint S Z) (hb : Bad p (S ∪ Z)) :
    S.card + Z.card = 7 := by
  rw [← Finset.card_union_of_disjoint hd]; exact hb.2.1

theorem bad_evens {p : ℕ} {S Z : Finset ℕ} (hd : Disjoint S Z) (hb : Bad p (S ∪ Z)) :
    (S.filter (fun v => v % 2 = 0)).card + (Z.filter (fun v => v % 2 = 0)).card ≤ 5 := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd), ← Finset.filter_union]
  exact hb.2.2.1

theorem kids_false {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ)
    (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ)
    (hg : ∀ sz' ev' av' unc' cu' nu' pos1 pos2 S', g sz' ev' av' unc' cu' nu' pos1 = some pos2 →
      GoInv X S' sz' ev' av' unc' cu' nu' → StateClosed X d S' av' unc')
    (S : Finset ℕ) (sz ev unc cu nu r j : ℕ)
    (hsz : sz = S.card) (hev : ev = (S.filter (fun v => v % 2 = 0)).card)
    (hunc : ∀ j, unc.testBit j = true → j ∈ winSet X.p)
    (hcu : cu = ∑ j ∈ Uf X.p unc, X.covby j) (hnu : nu ≤ (Uf X.p unc).card)
    (hr : r = 7 - sz)
    (Z : Finset ℕ) (hdisj : Disjoint S Z) (hbad : Bad X.p (S ∪ Z)) (hrep : Rep X.p d (S ∪ Z))
    (hcov : ∀ j, unc.testBit j = true → ∃ v ∈ Z, coversAt 7 X.p j v = true)
    (hjZ : ∃ v ∈ Z, coversAt 7 X.p j v = true) :
    ∀ f m avr aer pos pos', kids X C g sz ev unc cu nu d r f m avr aer pos = some pos' →
      Clean X.p avr → (∀ v ∈ Z, bitS avr v = true ∧ bitS aer v = true) →
      (∀ v ∈ Z, coversAt 7 X.p j v = true → bitS m v = true) →
      (∀ c, bitS m c = true → c ∈ admSet X.p) → False
  | 0, m, avr, aer, pos, pos', h, _, _, _, _ => by simp [kids] at h
  | f + 1, m, avr, aer, pos, pos', h, hcl, hZb, hZm, hmadm => by
    have hZa : Z ⊆ admSet X.p := fun v hv => hbad.1 (Finset.mem_union_right _ hv)
    have hZc : Z.card = r := by have := bad_card hdisj hbad; omega
    rw [kids] at h
    dsimp only at h
    cases h0 : Nat.beq (rd C pos) 0
    · rw [h0] at h; simp only [cond_false] at h
      cases h2 : Nat.beq (rd C pos) 2
      · rw [h2] at h; simp only [cond_false] at h
        cases h1 : Nat.beq (rd C pos) 1
        · rw [h1] at h; exact absurd h (by simp)
        · rw [h1] at h; simp only [cond_true] at h
          set c := rd C (Nat.succ pos)
          cases hm : bitS m c
          · rw [hm] at h; exact absurd h (by simp)
          · rw [hm] at h; simp only [cond_true] at h
            split at h
            · exact absurd h (by simp)
            · rename_i avc pos3 hf
              split at h
              · exact absurd h (by simp)
              · rename_i pos4 hgo
                have hcadm := hmadm c hm
                by_cases hcZ : c ∈ Z
                · -- the child that takes `c`
                  have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hcZ
                  obtain ⟨hf1, hf2⟩ := filt_sound X C c d (S ∪ Z) hrep.2.2.2
                    (Finset.mem_union_right _ hcZ) _ _ _ _ _ hf
                  obtain ⟨hu1, hu2, hu3⟩ := child_state hX unc cu nu c hunc hcu hnu hcadm
                  have hinv : GoInv X (insert c S) (Nat.succ sz)
                      (bif Nat.beq (Nat.mod c 2) 0 then Nat.succ ev else ev) avc
                      (clr unc (X.cov c)) (Nat.sub cu (X.cntF (Nat.land unc (X.cov c)) 0))
                      (Nat.sub nu (fld cu c)) := by
                    refine ⟨by rw [Finset.card_insert_of_notMem hcS, hsz], ?_, ?_, hu1, hu2, hu3⟩
                    · rw [Finset.filter_insert, beq_eq_decide]
                      by_cases hc2 : c % 2 = 0
                      · have : Nat.mod c 2 = 0 := hc2
                        simp only [this, decide_true, cond_true, hc2, if_true]
                        rw [Finset.card_insert_of_notMem (fun h => hcS (Finset.mem_filter.1 h).1), hev]
                      · have : ¬ Nat.mod c 2 = 0 := hc2
                        simp only [this, decide_false, cond_false, hc2, if_false, hev]
                    · intro i hi
                      have := hf1 i hi
                      rw [testBit_clr, Bool.and_eq_true] at this
                      exact hcl i this.1
                  have hSZ : insert c S ∪ Z.erase c = S ∪ Z := by
                    ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
                    constructor
                    · rintro ((rfl | h) | ⟨-, h⟩) <;> tauto
                    · rintro (h | h)
                      · tauto
                      · by_cases hv : v = c
                        · left; left; exact hv
                        · right; exact ⟨hv, h⟩
                  apply hg _ _ _ _ _ _ _ _ (insert c S) hgo hinv (Z.erase c)
                  · rw [Finset.disjoint_left]
                    intro v hv hv'
                    rcases Finset.mem_insert.1 hv with rfl | hv
                    · simp at hv'
                    · exact Finset.disjoint_left.1 hdisj hv (Finset.mem_of_mem_erase hv')
                  · intro v hv
                    have hvZ := Finset.mem_of_mem_erase hv
                    have hvc := Finset.ne_of_mem_erase hv
                    apply hf2 v (Finset.mem_union_right _ hvZ)
                    rw [bitS_clr_sbit, (hZb v hvZ).1]; simp [hvc]
                  · rw [hSZ]; exact hbad
                  · rw [hSZ]; exact hrep
                  · intro j' hj'
                    rw [bitC_eq, testBit_clr, Bool.and_eq_true, testBit_cov hX hcadm] at hj'
                    obtain ⟨v, hv, hcv⟩ := hcov j' hj'.1
                    refine ⟨v, Finset.mem_erase.2 ⟨?_, hv⟩, hcv⟩
                    rintro rfl
                    have := hj'.2
                    simp [hunc j' hj'.1, hcv] at this
                · -- `c` is not in `Z`: continue with the later coverers
                  apply kids_false hX C g d hg S sz ev unc cu nu r j hsz hev hunc hcu hnu hr Z hdisj hbad
                    hrep hcov hjZ f _ _ _ _ _ h (clean_clr _ hcl)
                  · intro v hv
                    have hvc : v ≠ c := fun e => hcZ (e ▸ hv)
                    rw [bitS_clr_sbit, bitS_clr_sbit, (hZb v hv).1, (hZb v hv).2]; simp [hvc]
                  · intro v hv hcv
                    have hvc : v ≠ c := fun e => hcZ (e ▸ hv)
                    rw [bitS_clr_sbit, hZm v hv hcv]; simp [hvc]
                  · intro c' hc'
                    rw [bitS_clr_sbit, Bool.and_eq_true] at hc'
                    exact hmadm c' hc'.1
      · rw [h2] at h; simp only [cond_true] at h
        exact boundLeaf_false hX C unc cu nu aer r _ _ h hunc hcu hnu Z hZa
          (fun v hv => (hZb v hv).2) (by omega) hcov
    · rw [h0] at h; simp only [cond_true] at h
      cases hm0 : Nat.beq m 0
      · rw [hm0] at h; exact absurd h (by simp)
      · rw [beq_eq_decide] at hm0
        have hm0' : m = 0 := of_decide_eq_true hm0
        obtain ⟨v, hv, hcv⟩ := hjZ
        have := hZm v hv hcv
        rw [hm0', bitS_eq, Nat.zero_testBit] at this
        exact absurd this (by decide)


theorem bitS_nland (x m v : ℕ) : bitS (Nat.land x m) v = (bitS x v && bitS m v) := bitS_land x m v

theorem go_sound {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ) (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (d : ℕ)
    (hH : ∀ i (S : Finset ℕ) avail unc, H i = (d, S.card, (S.filter (fun v => v % 2 = 0)).card, avail, unc) →
      Clean X.p avail → StateClosed X d S avail unc) :
    ∀ f sz ev avail unc cu nu pos pos' (S : Finset ℕ), go X C H d f sz ev avail unc cu nu pos = some pos' →
      GoInv X S sz ev avail unc cu nu → StateClosed X d S avail unc
  | 0, _, _, _, _, _, _, _, _, _, h, _ => by simp [go] at h
  | f + 1, sz, ev, avail, unc, cu, nu, pos, pos', S, h, hinv => by
    obtain ⟨hsz, hev, hcl, hunc, hcu, hnu⟩ := hinv
    intro Z hdisj hZb hbad hrep hcov
    simp only [bitC_eq] at hcov
    have hZa : Z ⊆ admSet X.p := fun v hv => hbad.1 (Finset.mem_union_right _ hv)
    have hcard := bad_card hdisj hbad
    have hevs := bad_evens hdisj hbad
    have hW := tab_W1024 hX; rw [tab_W hX] at hW
    -- the effective avail
    set av' := (bif Nat.ble 5 ev then clr avail X.even else avail) with hav'
    have hZb' : ∀ v ∈ Z, bitS av' v = true := by
      intro v hv
      rw [hav', ble_eq_decide]
      by_cases h5 : 5 ≤ ev
      · simp only [h5, decide_true, cond_true]
        have hodd : v % 2 ≠ 0 := by
          intro he
          have : 0 < (Z.filter (fun v => v % 2 = 0)).card :=
            Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨hv, he⟩⟩
          omega
        rw [bitS_clr, hZb v hv, hX.2.2.2.2.1, bitS_spreadOf]
        simp [hodd]
      · simp only [h5, decide_false, cond_false]; exact hZb v hv
    have hcl' : Clean X.p av' := by
      rw [hav']; cases Nat.ble 5 ev
      · exact hcl
      · exact clean_clr _ hcl
    rw [go] at h
    dsimp only at h
    rw [← hav'] at h
    cases ht0 : Nat.beq (rd C pos) 0
    · rw [ht0] at h; simp only [cond_false] at h
      cases ht1 : Nat.beq (rd C pos) 1
      · rw [ht1] at h; simp only [cond_false] at h
        cases ht2 : Nat.beq (rd C pos) 2
        · rw [ht2] at h; simp only [cond_false] at h
          cases ht4 : Nat.beq (rd C pos) 4
          · rw [ht4] at h; simp only [cond_false] at h
            cases ht7 : Nat.beq (rd C pos) 7
            · -- bound leaf
              rw [ht7] at h; simp only [cond_false] at h
              cases hs7 : Nat.ble sz 7
              · rw [hs7] at h; exact absurd h (by simp)
              · rw [hs7] at h; simp only [cond_true] at h
                exact boundLeaf_false hX C unc cu nu av' _ _ _ h hunc hcu hnu Z hZa hZb'
                  (by show Z.card ≤ 7 - sz; omega) hcov
            · -- delegated leaf
              rw [ht7] at h; simp only [cond_true] at h
              rcases hHi : H (rd C (Nat.succ pos)) with ⟨d', sz', ev', av'', unc'⟩
              rw [hHi] at h
              simp only at h
              cases hc : (Nat.beq d' d && Nat.beq sz' sz && Nat.beq ev' ev && Nat.beq av'' avail &&
                  Nat.beq unc' unc)
              · rw [hc] at h; exact absurd h (by simp)
              · simp only [Bool.and_eq_true, beq_eq_decide, decide_eq_true_eq] at hc
                obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hc
                exact hH _ S av'' unc' (by rw [hHi, hsz, hev]) hcl Z hdisj hZb hbad hrep
                  (by simpa [bitC_eq] using hcov)
          · -- parity leaf
            rw [ht4] at h; simp only [cond_true] at h
            cases hc : (Nat.beq unc 0 && Nat.ble sz 7 &&
                noCompl ev 5 (spc X (Nat.land av' X.even)) (Nat.sub (spc X av') (spc X (Nat.land av' X.even)))
                  (Nat.sub 7 sz) (Nat.sub 7 sz))
            · rw [hc] at h; exact absurd h (by simp)
            · rw [Bool.and_eq_true, Bool.and_eq_true] at hc
              obtain ⟨-, hnc⟩ := hc
              set A' := (admSet X.p).filter (fun v => bitS av' v = true)
              have hae : spc X (Nat.land av' X.even) = (A'.filter (fun v => v % 2 = 0)).card := by
                have e := clean_eq (X := X) (Nat.land av' X.even) (clean_land _ hcl')
                rw [e, spc_spreadOf hX _ (Finset.filter_subset _ _)]
                congr 1; ext v
                simp only [A', Finset.mem_filter, bitS_nland, Bool.and_eq_true, hX.2.2.2.2.1, bitS_spreadOf,
                  decide_eq_true_eq]
                tauto
              have hao : spc X av' = A'.card := by
                conv_lhs => rw [clean_eq (X := X) _ hcl']
                rw [spc_spreadOf hX _ (Finset.filter_subset _ _)]
              have hsplit := Finset.card_filter_add_card_filter_not (s := A') (fun v => v % 2 = 0)
              have hnc' := noCompl_sound ev 5 _ _ _ _ hnc (Z.filter (fun v => v % 2 = 0)).card (by
                have := Finset.card_filter_le Z (fun v => v % 2 = 0)
                show _ ≤ 7 - sz; omega)
              rw [hae, show Nat.sub (spc X av') (A'.filter (fun v => v % 2 = 0)).card
                = spc X av' - (A'.filter (fun v => v % 2 = 0)).card from rfl, hao] at hnc'
              have hZe : (Z.filter (fun v => v % 2 = 0)).card ≤ (A'.filter (fun v => v % 2 = 0)).card := by
                apply Finset.card_le_card
                intro v hv; rw [Finset.mem_filter] at hv ⊢
                exact ⟨Finset.mem_filter.2 ⟨hZa hv.1, hZb' v hv.1⟩, hv.2⟩
              have hZo : (Z.filter (fun v => ¬ v % 2 = 0)).card ≤ (A'.filter (fun v => ¬ v % 2 = 0)).card := by
                apply Finset.card_le_card
                intro v hv; rw [Finset.mem_filter] at hv ⊢
                exact ⟨Finset.mem_filter.2 ⟨hZa hv.1, hZb' v hv.1⟩, hv.2⟩
              have hZs := Finset.card_filter_add_card_filter_not (s := Z) (fun v => v % 2 = 0)
              show False
              have : Nat.sub 7 sz = 7 - sz := rfl
              rw [this] at hnc'
              omega
        · -- no coverer of an uncovered position
          rw [ht2] at h; simp only [cond_true] at h
          cases hc : (bitC unc (rd C (Nat.succ pos)) && Nat.beq (Nat.land (X.covby (rd C (Nat.succ pos))) av') 0)
          · rw [hc] at h; exact absurd h (by simp)
          · rw [Bool.and_eq_true, bitC_eq, beq_eq_decide] at hc
            set j := rd C (Nat.succ pos)
            have hz : X.covby j &&& av' = 0 := of_decide_eq_true hc.2
            obtain ⟨v, hv, hcv⟩ := hcov j hc.1
            have hb : bitS (X.covby j &&& av') v = true := by
              rw [bitS_land, bitS_covby hX (hunc j hc.1), hZb' v hv]
              simp [cv, hZa hv, hcv]
            rw [hz, bitS_eq, Nat.zero_testBit] at hb
            exact absurd hb (by decide)
      · -- no slot left
        rw [ht1] at h; simp only [cond_true] at h
        cases hc : (Nat.beq (Nat.sub 7 sz) 0 && !Nat.beq unc 0)
        · rw [hc] at h; exact absurd h (by simp)
        · simp only [Bool.and_eq_true, beq_eq_decide, Bool.not_eq_true', decide_eq_true_eq,
            decide_eq_false_iff_not] at hc
          obtain ⟨hr0, hu0⟩ := hc
          have hr0' : 7 - sz = 0 := hr0
          obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hu0
          obtain ⟨v, hv, -⟩ := hcov j hj
          have : Z.card = 0 := by omega
          rw [Finset.card_eq_zero] at this
          subst this; simp at hv
    · -- branch node
      rw [ht0] at h; simp only [cond_true] at h
      cases hc : (ltN sz 7 && bitC unc (rd C (Nat.succ pos)))
      · rw [hc] at h; exact absurd h (by simp)
      · rw [hc] at h; simp only [cond_true] at h
        rw [Bool.and_eq_true, bitC_eq] at hc
        set j := rd C (Nat.succ pos)
        have hjw := hunc j hc.2
        refine kids_false hX C (go X C H d f) d (fun sz' ev' av2 unc' cu' nu' pos1 pos2 S' hg hi =>
            go_sound hX C H d hH f sz' ev' av2 unc' cu' nu' pos1 pos2 S' hg hi)
          S sz ev unc cu nu (Nat.sub 7 sz) j hsz hev hunc hcu hnu rfl Z hdisj hbad hrep hcov (hcov j hc.2)
          _ _ _ _ _ _ h hcl (fun v hv => ⟨hZb v hv, hZb' v hv⟩) ?_ ?_
        · intro v hv hcv
          rw [bitS_nland, bitS_covby hX hjw, hZb' v hv]
          simp [cv, hZa hv, hcv]
        · intro c hc'
          rw [bitS_nland, bitS_covby hX hjw, Bool.and_eq_true] at hc'
          exact (of_decide_eq_true hc'.1).1


/-! ## Entry points -/

theorem closed_of_big (X : Ctx) (d : ℕ) (S : Finset ℕ) (avail unc : ℕ) (h : 7 < S.card) :
    StateClosed X d S avail unc := by
  intro Z hd _ hb _ _
  have := bad_card hd hb; omega

theorem noH_ok (X : Ctx) (d : ℕ) : ∀ i (S : Finset ℕ) avail unc,
    noH i = (d, S.card, (S.filter (fun v => v % 2 = 0)).card, avail, unc) →
      Clean X.p avail → StateClosed X d S avail unc := by
  intro i S avail unc h _
  have : S.card = 99 := by
    have := congrArg (fun t => t.2.1) h; simp only [noH] at this; omega
  exact closed_of_big X d S avail unc (by omega)

theorem window_of_lt {X : Ctx} (hX : TableOK X) (u : ℕ) (hu : u < 2 ^ (X.W + 1))
    (h0 : u.testBit 0 = false) : ∀ j, u.testBit j = true → j ∈ winSet X.p := by
  intro j hj
  rw [mem_winSet, ← tab_W hX]
  refine ⟨?_, ?_⟩
  · by_contra h; have : j = 0 := by omega
    subst this; rw [h0] at hj; exact absurd hj (by decide)
  · by_contra h
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hj
    exact absurd hj (by decide)

theorem pcl_Uf {X : Ctx} (hX : TableOK X) (u : ℕ) (hu : u < 2 ^ (X.W + 1))
    (hw : ∀ j, u.testBit j = true → j ∈ winSet X.p) : pcl 1024 u 0 ≤ (Uf X.p u).card := by
  have h1 := pcl_le (X.W + 1) 1024 u 0 hu
  have : (range (X.W + 1)).filter (fun i => u.testBit i = true) = Uf X.p u := by
    ext j
    simp only [mem_filter, mem_range, Uf]
    constructor
    · intro h; exact ⟨hw j h.2, h.2⟩
    · intro h; have := mem_winSet.1 h.1; rw [tab_W hX]; exact ⟨by omega, h.2⟩
  rw [this] at h1; omega

/-- **Subtree soundness.** -/
theorem checkState_sound' (X : Ctx) (hX : TableOK X) (d : ℕ) (S : Finset ℕ) (avail unc : ℕ)
    (C : ℕ → ℕ)
    (h : checkState X d S.card (S.filter (fun v => v % 2 = 0)).card avail unc C = true) :
    StateClosed X d S avail unc := by
  unfold checkState at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hlt⟩, hb0⟩, hcl⟩, hgo⟩ := h
  have hlt' : unc < 2 ^ (X.W + 1) := by
    rw [ltN_eq] at hlt
    have := of_decide_eq_true hlt
    rwa [show Nat.shiftLeft 1 (Nat.succ X.W) = 2 ^ (X.W + 1) from Nat.one_shiftLeft _] at this
  have hb0' : unc.testBit 0 = false := by
    rw [Bool.not_eq_true', bitC_eq] at hb0; exact hb0
  have hw := window_of_lt hX unc hlt' hb0'
  have hcl' : Clean X.p avail := by
    rw [beq_eq_decide] at hcl
    have h0 : clr avail X.adm = 0 := of_decide_eq_true hcl
    intro i hi
    have := congrArg (fun x => x.testBit i) h0
    simp only [testBit_clr, hi, Bool.true_and, Nat.zero_testBit, Bool.not_eq_false'] at this
    rw [hX.2.2.2.1, testBit_spreadOf] at this
    exact of_decide_eq_true this
  split at hgo
  · rename_i pos' hg
    exact go_sound hX C noH d (noH_ok X d) 9 _ _ _ _ _ _ _ _ S hg
      ⟨rfl, rfl, hcl', hw, by rw [cntF_eq hX _ _ hw, Nat.zero_add], pcl_Uf hX unc hlt' hw⟩
  · exact absurd hgo (by decide)

/-- no multiple of 8 below the ratio-min parameter -/
theorem rep_no_small {p d : ℕ} {V : Finset ℕ} (hR : Rep p d V) (y : ℕ) (hy : y ∈ V) (h8 : y % 8 = 0)
    (h1 : 1 ≤ y) (hyd : y < d) (hyp : y ≤ 4 * p) : False := by
  apply hR.2.2.2 1 hR.1 (by norm_num) y hy h8
  refine ⟨y, h1, hyd, ?_⟩
  rw [nrm_eq_wlog, Nat.mul_one]
  unfold EightWLOG.nrm
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem testBit_twoW (W j : ℕ) : (2 ^ (W + 1) - 2).testBit j = decide (1 ≤ j ∧ j ≤ W) := by
  have e : 2 ^ (W + 1) - 2 = 2 ^ 1 * (2 ^ W - 1) + 0 := by
    have : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    rw [pow_succ]; omega
  rw [e, testBit_two_pow_mul_add _ _ _ _ (by norm_num)]
  split_ifs with hj
  · rw [Nat.zero_testBit]; symm; rw [decide_eq_false_iff_not]; omega
  · rw [Nat.testBit_two_pow_sub_one, decide_eq_decide]; omega

theorem rootKids_false {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ) (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ)
    (hH : ∀ d' i (S : Finset ℕ) avail unc, H i = (d', S.card, (S.filter (fun v => v % 2 = 0)).card, avail, unc) →
      Clean X.p avail → StateClosed X d' S avail unc)
    (d : ℕ) (V : Finset ℕ) (hR : Rep X.p d V) (hB : Bad X.p V)
    (unc1 cu1 nu1 : ℕ) (hunc1 : ∀ j, unc1.testBit j = true ↔ j ∈ winSet X.p ∧ coversAt 7 X.p j 1 = false)
    (hcu1 : cu1 = ∑ j ∈ Uf X.p unc1, X.covby j) (hnu1 : nu1 ≤ (Uf X.p unc1).card) :
    ∀ f m run pos pos' (M : Finset ℕ), rootKids X C H unc1 cu1 nu1 f m run pos = some pos' →
      m = spreadOf M → M ⊆ (admSet X.p).filter (fun v => v % 8 = 0) → d ∈ M → Clean X.p run →
      (∀ v ∈ V, v ≠ 1 → v ≠ d → bitS run v = true) → False
  | 0, _, _, _, _, _, h, _, _, _, _, _ => by simp [rootKids] at h
  | f + 1, m, run, pos, pos', M, h, hm, hM, hdM, hcl, hrun => by
    have hW := tab_W1024 hX; rw [tab_W hX] at hW
    have hVa := hB.1
    have h1V := hR.1
    have hdV := hR.2.1
    have hd8 := hR.2.2.1
    have hd1 : d ≠ 1 := by intro e; rw [e] at hd8; norm_num at hd8
    rw [rootKids] at h
    dsimp only at h
    have hm0 : m ≠ 0 := by
      intro e
      have := bitS_spreadOf M d
      rw [← hm, e, bitS_eq, Nat.zero_testBit] at this
      exact absurd this.symm (by simp [hdM])
    rw [beq_eq_decide, decide_eq_false hm0] at h
    simp only [cond_false] at h
    obtain ⟨k, hk, hkb, hklow⟩ := low_iso m hm0
    -- the lowest bit is `16 e0` with `e0 = min M`
    obtain ⟨e0, he0M, he0k⟩ : ∃ e0 ∈ M, 16 * e0 = k := by
      rw [hm, testBit_spreadOf] at hkb; exact of_decide_eq_true hkb
    have hmin : ∀ v ∈ M, e0 ≤ v := by
      intro v hv
      by_contra hlt
      have h1 := hklow (16 * v) (by omega)
      rw [hm, testBit_spreadOf, decide_eq_false_iff_not] at h1
      exact h1 ⟨v, hv, rfl⟩
    have he0a := (Finset.mem_filter.1 (hM he0M)).1
    have he08 := (Finset.mem_filter.1 (hM he0M)).2
    have hkl : k < 2 ^ 14 := by
      have := adm_lt he0a; rw [← he0k]
      calc 16 * e0 < 16384 := by omega
        _ = 2 ^ 14 := by norm_num
    have hlow : lowS m = k := lowS_eq m k hk hkl
    rw [hlow] at h
    have hek : k >>> 4 = e0 := by
      rw [← he0k, Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 4 = 16 by norm_num]; omega
    rw [show Nat.shiftRight k 4 = e0 from hek] at h
    have hsb : Nat.shiftLeft 1 k = sbit e0 := by rw [sbit_eq, ← he0k]; exact Nat.one_shiftLeft _
    rw [hsb] at h
    split at h
    · exact absurd h (by simp)
    · rename_i av pos1 hf
      split at h
      · exact absurd h (by simp)
      · rename_i pos2 hgo
        by_cases hed : e0 = d
        · -- the child `e0 = d`
          subst hed
          obtain ⟨hf1, hf2⟩ := filt_sound X C e0 e0 V hR.2.2.2 hdV _ _ _ _ _ hf
          have h1a : (1 : ℕ) ∈ admSet X.p := hVa h1V
          have hunc1w : ∀ j, unc1.testBit j = true → j ∈ winSet X.p := fun j hj => ((hunc1 j).1 hj).1
          obtain ⟨hu1, hu2, hu3⟩ := child_state hX unc1 cu1 nu1 e0 hunc1w hcu1 hnu1 he0a
          have hS : ({1, e0} : Finset ℕ).card = 2 := by rw [Finset.card_pair (Ne.symm hd1)]
          have hSe : (({1, e0} : Finset ℕ).filter (fun v => v % 2 = 0)).card = 1 := by
            rw [Finset.filter_insert, Finset.filter_singleton]
            have : e0 % 2 = 0 := by omega
            simp [this]
          have hinv : GoInv X {1, e0} 2 1 av (clr unc1 (X.cov e0))
              (Nat.sub cu1 (X.cntF (Nat.land unc1 (X.cov e0)) 0)) (Nat.sub nu1 (fld cu1 e0)) := by
            refine ⟨hS.symm, hSe.symm, ?_, hu1, hu2, hu3⟩
            intro i hi
            have := hf1 i hi
            rw [testBit_clr, Bool.and_eq_true] at this
            exact hcl i this.1
          have hcl := go_sound hX C H e0 (hH e0) 9 _ _ _ _ _ _ _ _ {1, e0} hgo hinv
          have hsub : ({1, e0} : Finset ℕ) ⊆ V := by
            intro v hv; rcases Finset.mem_insert.1 hv with rfl | hv
            · exact h1V
            · rw [Finset.mem_singleton.1 hv]; exact hdV
          have hU : ({1, e0} : Finset ℕ) ∪ (V \ {1, e0}) = V := Finset.union_sdiff_of_subset hsub
          apply hcl (V \ {1, e0}) Finset.disjoint_sdiff
          · intro v hv
            rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hv
            push Not at hv
            apply hf2 v hv.1
            rw [bitS_clr_sbit, hrun v hv.1 hv.2.1 hv.2.2]
            simp [hv.2.2]
          · rw [hU]; exact hB
          · rw [hU]; exact hR
          · intro j hj
            rw [bitC_eq, testBit_clr, Bool.and_eq_true, testBit_cov hX he0a, hunc1] at hj
            obtain ⟨⟨hjw, hj1⟩, hje⟩ := hj
            obtain ⟨v, hv, hcv⟩ := hB.2.2.2 j hjw
            refine ⟨v, ?_, hcv⟩
            rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            refine ⟨hv, ?_⟩
            rintro (rfl | rfl)
            · rw [hj1] at hcv; exact absurd hcv (by decide)
            · simp [hjw, hcv] at hje
        · -- a smaller multiple of 8, not in `V`
          have hlt : e0 < d := lt_of_le_of_ne (hmin d hdM) hed
          have he0V : e0 ∉ V := fun hv =>
            rep_no_small hR e0 hv he08 (mem_admSet.1 he0a).1 hlt (mem_admSet.1 he0a).2.1
          apply rootKids_false hX C H hH d V hR hB unc1 cu1 nu1 hunc1 hcu1 hnu1 f _ _ _ _ (M.erase e0) h
          · apply Nat.eq_of_testBit_eq; intro i
            rw [testBit_clr, hm, testBit_spreadOf, testBit_spreadOf, sbit_eq, Nat.testBit_two_pow,
              Bool.eq_iff_iff]
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
              Finset.mem_erase]
            constructor
            · rintro ⟨⟨v, hv, rfl⟩, hne⟩; exact ⟨v, ⟨fun e => hne (by rw [e]), hv⟩, rfl⟩
            · rintro ⟨v, ⟨hne, hv⟩, rfl⟩; exact ⟨⟨v, hv, rfl⟩, fun e => hne (by omega)⟩
          · exact fun v hv => hM (Finset.mem_of_mem_erase hv)
          · exact Finset.mem_erase.2 ⟨Ne.symm hed, hdM⟩
          · exact clean_clr _ hcl
          · intro v hv hv1 hvd
            rw [bitS_clr_sbit, hrun v hv hv1 hvd]
            have : v ≠ e0 := fun e => he0V (e ▸ hv)
            simp [this]


theorem root_common {X : Ctx} (hX : TableOK X) (C : ℕ → ℕ) (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ)
    (hH : ∀ d' i (S : Finset ℕ) avail unc, H i = (d', S.card, (S.filter (fun v => v % 2 = 0)).card, avail, unc) →
      Clean X.p avail → StateClosed X d' S avail unc) (pos' : ℕ)
    (hr : rootKids X C H (clr (Nat.sub (Nat.shiftLeft 1 (Nat.succ X.W)) 2) (X.cov 1))
      (X.cntF (clr (Nat.sub (Nat.shiftLeft 1 (Nat.succ X.W)) 2) (X.cov 1)) 0)
      (pcl 1024 (clr (Nat.sub (Nat.shiftLeft 1 (Nat.succ X.W)) 2) (X.cov 1)) 0) 1024
      (Nat.land (clr X.adm (sbit 1)) X.m8) (clr X.adm (sbit 1)) 0 = some pos') :
    ∀ d V, Rep X.p d V → ¬ Bad X.p V := by
  intro d V hR hB
  have hW := tab_W1024 hX
  have h1a : (1 : ℕ) ∈ admSet X.p := hB.1 hR.1
  set unc1 := clr (Nat.sub (Nat.shiftLeft 1 (Nat.succ X.W)) 2) (X.cov 1) with hu1
  have hunc1 : ∀ j, unc1.testBit j = true ↔ j ∈ winSet X.p ∧ coversAt 7 X.p j 1 = false := by
    intro j
    rw [hu1, testBit_clr, show Nat.sub (Nat.shiftLeft 1 (Nat.succ X.W)) 2 = 2 ^ (X.W + 1) - 2 by
      rw [show Nat.shiftLeft 1 (Nat.succ X.W) = 1 <<< (X.W + 1) from rfl, Nat.one_shiftLeft]; rfl,
      testBit_twoW, testBit_cov hX h1a, tab_W hX]
    have hm : j ∈ winSet X.p ↔ 1 ≤ j ∧ j ≤ 4 * X.p := mem_winSet
    by_cases hj : 1 ≤ j ∧ j ≤ 4 * X.p
    · have hj' : j ∈ winSet X.p := hm.2 hj
      cases hc : coversAt 7 X.p j 1 <;> simp [hj, hj']
    · have hj' : j ∉ winSet X.p := fun h => hj (hm.1 h)
      simp [hj, hj']
  have hw : ∀ j, unc1.testBit j = true → j ∈ winSet X.p := fun j hj => ((hunc1 j).1 hj).1
  have hlt : unc1 < 2 ^ (X.W + 1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases h : unc1.testBit i
    · rfl
    · have := mem_winSet.1 (hw i h); rw [tab_W hX] at hi; omega
  have hE8 : Nat.land (clr X.adm (sbit 1)) X.m8 = spreadOf ((admSet X.p).filter (fun v => v % 8 = 0)) := by
    apply Nat.eq_of_testBit_eq; intro i
    show ((clr X.adm (sbit 1)) &&& X.m8).testBit i = _
    rw [Nat.testBit_and, testBit_clr, hX.2.2.2.1, hX.2.2.2.2.2.1, sbit_eq, testBit_spreadOf,
      testBit_spreadOf, Nat.testBit_two_pow, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨v, ⟨hv, h8⟩, rfl⟩
      refine ⟨⟨⟨v, hv, rfl⟩, ?_⟩, ⟨v, ⟨hv, h8⟩, rfl⟩⟩
      intro e; have : v = 1 := by omega
      subst this; norm_num at h8
  exact rootKids_false hX C H hH d V hR hB unc1 _ _ hunc1 (by rw [cntF_eq hX _ _ hw, Nat.zero_add])
    (pcl_Uf hX unc1 hlt hw) 1024 _ _ 0 pos' _ hr hE8 (fun v hv => hv)
    (Finset.mem_filter.2 ⟨hB.1 hR.2.1, hR.2.2.1⟩) (clean_clr _ (by rw [hX.2.2.2.1]; exact clean_spreadOf _ subset_rfl))
    (by
      intro v hv hv1 _
      rw [bitS_clr_sbit, hX.2.2.2.1, bitS_spreadOf]
      simp [hB.1 hv, hv1])

theorem checkRoot_sound' (X : Ctx) (hX : TableOK X) (C : ℕ → ℕ) (h : checkRoot X C = true) :
    ∀ d V, Rep X.p d V → ¬ Bad X.p V := by
  unfold checkRoot at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i pos' hr
    exact root_common hX C noH (fun d' => noH_ok X d') pos' hr
  · exact absurd h2 (by decide)

theorem checkRootH_sound' (X : Ctx) (hX : TableOK X) (C : ℕ → ℕ)
    (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (Cs : ℕ → ℕ → ℕ)
    (hH : ∀ i, (H i).2.1 ≤ 7 →
      checkState X (H i).1 (H i).2.1 (H i).2.2.1 (H i).2.2.2.1 (H i).2.2.2.2 (Cs i) = true)
    (h : checkRootH X C H = true) : ∀ d V, Rep X.p d V → ¬ Bad X.p V := by
  unfold checkRootH at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i pos' hr
    refine root_common hX C H ?_ pos' hr
    intro d' i S avail unc hi _
    by_cases hs : S.card ≤ 7
    · have := hH i (by rw [hi]; exact hs)
      rw [hi] at this
      exact checkState_sound' X hX d' S avail unc (Cs i) this
    · exact closed_of_big X d' S avail unc (by omega)
  · exact absurd h2 (by decide)

/-- **Subtree soundness.** -/
theorem checkState_sound (X : Ctx) (hX : TableOK X) (d : ℕ) (S : Finset ℕ) (avail unc : ℕ)
    (C : ℕ → ℕ)
    (h : checkState X d S.card (S.filter (fun v => v % 2 = 0)).card avail unc C = true) :
    StateClosed X d S avail unc :=
  checkState_sound' X hX d S avail unc C h

/-- **Root soundness**: a successful root replay excludes every bad representative. -/
theorem checkRoot_sound (X : Ctx) (hX : TableOK X) (C : ℕ → ℕ) (h : checkRoot X C = true) :
    ∀ d V, Rep X.p d V → ¬ Bad X.p V :=
  checkRoot_sound' X hX C h

/-- `lemma7Check 7 p` once no bad set is a ratio-min representative (proved; via `exists_rep`). -/
theorem lemma7Check_of_noBadRep (p : ℕ) (hp : p.Prime) (h7 : 7 < p)
    (hno : ∀ d V, Rep p d V → ¬ Bad p V) : lemma7Check 7 p = true := by
  unfold lemma7Check
  rw [List.all_eq_true]
  intro V hV
  by_contra hbad
  have hb : sideOK 7 V = true ∧ coversWindow 7 p V = true := by
    cases h1 : sideOK 7 V <;> cases h2 : coversWindow 7 p V <;> simp_all
  obtain ⟨hs, hc⟩ := hb
  unfold tuples at hV
  rw [List.mem_sublistsLen] at hV
  obtain ⟨hsub, hlen⟩ := hV
  have hnd : V.Nodup := hsub.nodup (EightWLOG.nodup_admissible 7 p)
  have hW : (7 + 1) * p / 2 = 4 * p := by omega
  -- the list tuple as a bad finite set
  have hBad : Bad p V.toFinset := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [List.mem_toFinset] at hv
      have := (EightWLOG.mem_admissible 7 p v).1 (hsub.subset hv)
      exact mem_admSet.2 ⟨this.2.1, by omega, this.2.2⟩
    · rw [List.toFinset_card_of_nodup hnd, hlen]
    · rw [EightWLOG.sideOK_seven] at hs
      have hs' := of_decide_eq_true hs
      have : V.toFinset.filter (fun v => v % 2 = 0) = (V.filter (fun v => v % 2 == 0)).toFinset := by
        ext v; simp
      rw [this, List.toFinset_card_of_nodup (hnd.filter _)]
      exact hs'
    · intro j hj
      have hj' := mem_winSet.1 hj
      obtain ⟨v, hv, hcv⟩ := (EightWLOG.coversWindow_iff 7 p V).1 hc j (by omega) hj'.1
      exact ⟨v, List.mem_toFinset.2 hv, hcv⟩
  obtain ⟨d, V', hRep, hBad'⟩ := exists_rep p hp h7 _ hBad
  exact hno d V' hRep hBad'

/-- `lemma7Check 7 p` from a successful root replay (proved from `checkRoot_sound`). -/
theorem lemma7Check_of_checkRoot (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (X : Ctx) (hX : TableOK X)
    (hXp : X.p = p) (C : ℕ → ℕ) (h : checkRoot X C = true) : lemma7Check 7 p = true := by
  subst hXp
  exact lemma7Check_of_noBadRep X.p hp h7 (checkRoot_sound X hX C h)

/-- **Split-run soundness**: the top replay with delegated states, plus one successful
`checkState` per delegated state, excludes every bad representative.  (`H i` with `sz > 7` is the
junk value of the accessor beyond the last delegated index; it never matches a replay state.) -/
theorem checkRootH_sound (X : Ctx) (hX : TableOK X) (C : ℕ → ℕ)
    (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (Cs : ℕ → ℕ → ℕ)
    (hH : ∀ i, (H i).2.1 ≤ 7 →
      checkState X (H i).1 (H i).2.1 (H i).2.2.1 (H i).2.2.2.1 (H i).2.2.2.2 (Cs i) = true)
    (h : checkRootH X C H = true) : ∀ d V, Rep X.p d V → ¬ Bad X.p V :=
  checkRootH_sound' X hX C H Cs hH h

/-- `lemma7Check 7 p` from a split run (proved from `checkRootH_sound`). -/
theorem lemma7Check_of_checkRootH (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (X : Ctx) (hX : TableOK X)
    (hXp : X.p = p) (C : ℕ → ℕ) (H : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (Cs : ℕ → ℕ → ℕ)
    (hH : ∀ i, (H i).2.1 ≤ 7 →
      checkState X (H i).1 (H i).2.1 (H i).2.2.1 (H i).2.2.2.1 (H i).2.2.2.2 (Cs i) = true)
    (h : checkRootH X C H = true) : lemma7Check 7 p = true := by
  subst hXp
  exact lemma7Check_of_noBadRep X.p hp h7 (checkRootH_sound X hX C H Cs hH h)



/-- the form requested for the eight-runner chain (statement) -/
theorem lemma7Check1_of_checkRoot (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (X : Ctx) (hX : TableOK X)
    (hXp : X.p = p) (C : ℕ → ℕ) (h : checkRoot X C = true) : lemma7Check1 7 p = true :=
  (lemma7Check_seven_iff_one p hp h7).mp (lemma7Check_of_checkRoot p hp h7 X hX hXp C h)

/-- `TableOK` for a context whose counter routine is the bit-keyed loop `cntB`: the finite part
plus the row check `cb' (2^j) = covby j` on the window. -/
theorem tableOK_of_cntB (X : Ctx) (cb' : ℕ → ℕ) (hF : X.cntF = cntB cb' 1024) (h : TableFin X)
    (hcb : ∀ j ∈ winSet X.p, cb' (2 ^ j) = X.covby j) : TableOK X := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  intro u acc hu
  have hlt : u < 2 ^ (X.W + 1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : u.testBit i
    · rfl
    · have := mem_winSet.1 (hu i hb); omega
  have hset : (range (X.W + 1)).filter (fun i => u.testBit i = true) =
      (winSet X.p).filter (fun j => u.testBit j = true) := by
    ext j; simp only [mem_filter, mem_range]
    constructor
    · intro h; exact ⟨hu j h.2, h.2⟩
    · intro h; have := mem_winSet.1 h.1; exact ⟨by omega, h.2⟩
  have hc : ((range (X.W + 1)).filter (fun i => u.testBit i = true)).card ≤ 1024 := by
    have := Finset.card_le_card (Finset.filter_subset (fun i => u.testBit i = true) (range (X.W + 1)))
    simp at this; omega
  rw [hF, cntB_eq (X.W + 1) cb' 1024 u acc hlt hc, hset]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hcb j (mem_filter.1 hj).1

/-! ## Chunked form of the finite table check

One `decide +kernel` over the whole of `TableFin` keeps every intermediate term of every row in the
kernel cache (measured: 9.7 GB at `p = 61`, 14.6 GB at `p = 97`).  Rows are therefore checked in
chunks `[B k, B (k + 1))`, one theorem each, and assembled here. -/

/-- the global (non-row) part of `TableFin` -/
abbrev TableGlob (X : Ctx) : Prop :=
  0 < X.p ∧ X.W = 4 * X.p ∧ X.W < 1024 ∧
  X.adm = spreadOf (admSet X.p) ∧
  X.even = spreadOf ((admSet X.p).filter (fun v => v % 2 = 0)) ∧
  X.m8 = spreadOf ((admSet X.p).filter (fun v => v % 8 = 0)) ∧
  X.ones = spreadOf (Finset.range (X.W + 1))

/-- `cov` rows `v ∈ [B k, B (k + 1))` -/
abbrev TableCovChunk (X : Ctx) (B k : ℕ) : Prop := ∀ v ∈ admSet X.p, B * k ≤ v → v < B * (k + 1) →
  X.cov v = compactOf ((winSet X.p).filter (fun j => coversAt 7 X.p j v))

/-- `covby` rows `j ∈ [B k, B (k + 1))` -/
abbrev TableCovbyChunk (X : Ctx) (B k : ℕ) : Prop := ∀ j ∈ winSet X.p, B * k ≤ j → j < B * (k + 1) →
  X.covby j = spreadOf ((admSet X.p).filter (fun v => coversAt 7 X.p j v))

theorem tableFin_of_chunks (X : Ctx) (B n : ℕ) (hB : 0 < B) (hn : 4 * X.p < B * n)
    (hg : TableGlob X) (hc : ∀ k < n, TableCovChunk X B k) (hcb : ∀ k < n, TableCovbyChunk X B k) :
    TableFin X := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  have hk : ∀ v, v ≤ 4 * X.p → v / B < n ∧ B * (v / B) ≤ v ∧ v < B * (v / B + 1) := by
    intro v hv
    refine ⟨(Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; omega), Nat.mul_div_le v B, ?_⟩
    exact Nat.lt_mul_div_succ v hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, b, c⟩ := hk v (mem_admSet.1 hv).2.1
    exact hc _ a v hv b c
  · intro j hj
    obtain ⟨a, b, c⟩ := hk j (mem_winSet.1 hj).2
    exact hcb _ a j hj b c

end LRSpectrumFull.EightV4
