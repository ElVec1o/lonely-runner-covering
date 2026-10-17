/-
# Eight runners: the contracts file (E2, E3, E4, E5, E6 and the assembly)

Rosenfeld (arXiv:2509.14111), Theorem 1, for `k = 7` speeds (eight runners), in project conventions:
a speed vector is `v : Fin 7 → ℤ` (so `Fin (k+1)` with `k = 6` in the `ML` API), and the claim is
`1/8 ≤ ML v`.

Proof architecture (Rosenfeld, Section 5, `k = 7`):

* E0  gcd reduction: WLOG `gcd v = 1` (`ML_smul`, VERIFIED in `ScaleInvariance.lean`).
* E4  Lemma 5 at `k = 7`: with LRC for 6 speeds (E6), a primitive counterexample has every
      leave-one-out gcd equal to 1; in particular at most 5 of the 7 speeds are even.
      Core: `floor_of_leaveOneOut_imprimitive` (VERIFIED).
* E2  Lemma 6/7 per prime: `lemma7Check 7 p = true` implies `p` divides some speed of every
      counterexample satisfying the parity side condition.  Core: `nid_congr_mod` (VERIFIED),
      `gcd_side_condition_iff` (VERIFIED); `lemma7Check 7 p = true` produced per prime by the
      campaign through `lemma7Check_of_checkRootH` (VERIFIED soundness).
* E3  Lemma 4 plus assembly: `840 * ∏ S ∣ ∏ v`.  Core: `witness_of_missing_divisor`,
      `ML_ge_LRC_of_covering` (VERIFIED).
* E5  MSS Theorem A at `n = 7` (Corollary 3 of Rosenfeld): with E6, a primitive `v` with
      `7^7 ∏ v > 28^42` satisfies LRC.  MISSING; LITERATURE (Malikiosis-Santos-Schymura).
* E6  LRC for 6 speeds: LITERATURE (Barajas-Serra 2008), carried as the hypothesis `LRC6`.
* NUM `28^42 < 7^7 * 840 * ∏ S`: closed here by `decide`/`norm_num`.

SUPERSEDED 2026-09-27: the assembly `eight_runners_STUB_SUPERSEDED` below still has E5 as a
`sorry` (`e5_sum_STUB_SUPERSEDED`) and is not the project's theorem. The actual, sorry-free,
unconditional theorem is `LRSpectrumFull.EightRunners.eight_runners_unconditional` (module
`EightRunners.lean`), which replaces E5 with the VERIFIED staircase + planar-rounding route in
`EightE5.lean` and needs no MSS axiom. STATUS of each declaration in this file is in its docstring.
-/

import LRSpectrumFull.RoomA4_rosenfeld
import LRSpectrumFull.LRCFourRunnersCore

namespace LRSpectrumFull.EightPlan

open LRSpectrumFull

/-- **E6 (hypothesis, LITERATURE).** LRC for six speeds (seven runners), in the exact shape of the
`ih` argument of `floor_of_leaveOneOut_imprimitive` at `k₀ = 5`.  No injectivity: repeated speeds
reduce to at most five distinct ones, where LRC is also known. -/
def LRC6 : Prop :=
  ∀ u : Fin (5 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((5 : ℝ) + 2) ≤ ML u

/-- Rosenfeld's prime set for `k = 7` (27 primes, 31 to 163). -/
def rosenfeldS : Finset ℕ :=
  {31, 37, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163}

/-- A primitive counterexample for eight runners. -/
def IsCE (v : Fin 7 → ℤ) : Prop :=
  (∀ i, 0 < v i) ∧ Finset.univ.gcd v = 1 ∧ ML v < 1 / 8

/-- the number of even speeds -/
def evenCount (v : Fin 7 → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (2 : ℤ) ∣ v i)).card

/-! ## Local helpers (re-proved here so that this module imports only built dependencies) -/

/-- Rescaling reparametrizes the gap (copy of `ScaleInvariance.gap_smul`). -/
theorem gap_smul8 {k : ℕ} (c : ℤ) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => c * v i) t = gap v ((c : ℝ) * t) := by
  unfold gap
  congr 1; funext i; congr 1; push_cast; ring

/-- `ML` is scale-invariant (copy of `ScaleInvariance.ML_smul`). -/
theorem ML_smul8 {k : ℕ} (c : ℤ) (hc : c ≠ 0) (v : Fin (k + 1) → ℤ) :
    ML (fun i => c * v i) = ML v := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hrange : Set.range (gap (fun i => c * v i)) = Set.range (gap v) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨(c : ℝ) * t, (gap_smul8 c v t).symm⟩
    · rintro ⟨s, rfl⟩
      refine ⟨s / (c : ℝ), ?_⟩
      rw [gap_smul8]; congr 1; field_simp
  unfold ML; rw [hrange]

/-- Folding a residue mod `8p` into `[1, 4p]`. -/
theorem fold_facts (p : ℕ) (hp0 : 0 < p) (a : ℤ) (ha : 0 < a) (hna : ¬ (p : ℤ) ∣ a) :
    ∃ f : ℕ, 1 ≤ f ∧ f ≤ 4 * p ∧ f % p ≠ 0 ∧ (f % 2 = 0 → (2 : ℤ) ∣ a) ∧
      (((8 * p : ℕ) : ℤ) ∣ a - (f : ℤ) ∨ ((8 * p : ℕ) : ℤ) ∣ a + (f : ℤ)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg ha.le).symm⟩
  have hnp : ¬ p ∣ n := fun h => hna (by exact_mod_cast h)
  have hdm : 8 * p * (n / (8 * p)) + n % (8 * p) = n := Nat.div_add_mod n (8 * p)
  have hrlt : n % (8 * p) < 8 * p := Nat.mod_lt n (by omega)
  generalize n % (8 * p) = r at hdm hrlt
  generalize n / (8 * p) = d at hdm
  have hpr : ¬ p ∣ r := fun h => hnp (by
    rw [← hdm]; exact dvd_add (Dvd.dvd.mul_right (Dvd.intro_left 8 rfl) d) h)
  have hr0 : r ≠ 0 := fun h => hpr (by rw [h]; exact dvd_zero p)
  obtain ⟨m, hm⟩ : ∃ m, n = 8 * m + r := ⟨p * d, by rw [← hdm]; ring⟩
  by_cases hle : r ≤ 4 * p
  · refine ⟨r, by omega, hle, fun h => hpr (Nat.dvd_of_mod_eq_zero h), fun h2 => ?_, Or.inl ?_⟩
    · have : n % 2 = 0 := by omega
      exact_mod_cast Nat.dvd_of_mod_eq_zero this
    · exact ⟨(d : ℤ), by rw [← hdm]; push_cast; ring⟩
  · refine ⟨8 * p - r, by omega, by omega, ?_, fun h2 => ?_, Or.inr ?_⟩
    · intro h
      apply hpr
      have h1 : p ∣ 8 * p - r := Nat.dvd_of_mod_eq_zero h
      exact (Nat.dvd_add_right h1).mp (by rw [Nat.sub_add_cancel hrlt.le]; exact Dvd.intro_left 8 rfl)
    · have : n % 2 = 0 := by omega
      exact_mod_cast Nat.dvd_of_mod_eq_zero this
    · refine ⟨(d : ℤ) + 1, ?_⟩
      rw [← hdm, Nat.cast_sub hrlt.le]
      push_cast; ring

/-- An uncovered `j` gives distance at least `1/8`. -/
theorem nid_ge_of_uncovered (p j f : ℕ) (hp : 0 < p)
    (h : 8 * p ≤ 8 * min (j * f % (8 * p)) (8 * p - j * f % (8 * p))) :
    (1 : ℝ) / 8 ≤ nearestIntDist (((j : ℤ) : ℝ) * ((f : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ)) := by
  have hq : 0 < 8 * p := by omega
  by_contra hlt
  push Not at hlt
  rw [show ((j : ℤ) : ℝ) * ((f : ℤ) : ℝ) = (((j * f : ℕ) : ℤ) : ℝ) by push_cast; ring] at hlt
  rw [nearestIntDist_div_lt_iff _ _ hq] at hlt
  rw [← Int.natCast_mod] at hlt
  have hrlt : j * f % (8 * p) < 8 * p := Nat.mod_lt _ hq
  generalize j * f % (8 * p) = r at hlt hrlt h
  have h1 : 8 * p ≤ 8 * r := by omega
  have h2 : 8 * p + 8 * r ≤ 8 * (8 * p) := by omega
  have h1R : (8 : ℝ) * p ≤ 8 * (r : ℝ) := by exact_mod_cast h1
  have h2R : (8 : ℝ) * p + 8 * (r : ℝ) ≤ 8 * (8 * p) := by exact_mod_cast h2
  simp only [Int.cast_natCast] at hlt
  push_cast at hlt
  rcases min_lt_iff.mp hlt with h3 | h3 <;> linarith

theorem admissible_mem (p x : ℕ) :
    x ∈ admissible 7 p ↔ (1 ≤ x ∧ x ≤ 4 * p ∧ x % p ≠ 0) := by
  simp only [admissible, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨b, by omega, c⟩
  · rintro ⟨a, b, c⟩; exact ⟨by omega, a, c⟩

theorem sideOK_seven (V : List ℕ) :
    sideOK 7 V = decide ((V.filter (fun v => v % 2 == 0)).length ≤ 5) := by
  have hfilt : ((List.range (7 + 2)).filter
      (fun l => 2 ≤ l && (7 + 1) % l == 0 && Nat.Prime l)) = [2] := by decide
  unfold sideOK
  rw [hfilt]
  simp

theorem padding_odd (p : ℕ) (hp : p.Prime) (h7 : 7 < p) :
    ∀ x ∈ ({1, 3, 5, 7, 9, 15, 21} : Finset ℕ), 1 ≤ x ∧ x ≤ 4 * p ∧ x % p ≠ 0 ∧ x % 2 = 1 := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by norm_num, by omega, ?_, by norm_num⟩ <;>
    intro h <;>
    have hd := Nat.dvd_of_mod_eq_zero h <;>
    have hle := Nat.le_of_dvd (by norm_num) hd <;>
    interval_cases p <;> first | omega | norm_num at hp

/-! ## Arithmetic -/

theorem rosenfeldS_primes : ∀ p ∈ rosenfeldS, p.Prime ∧ 7 < p := by
  intro p hp
  simp only [rosenfeldS, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem numeric : (28 : ℕ) ^ 42 < 7 ^ 7 * (840 * ∏ p ∈ rosenfeldS, p) := by
  simp only [rosenfeldS]
  norm_num

/-! ## E4: Lemma 5 at k = 7 -/

/-- **E4 (target: VERIFIED, from `floor_of_leaveOneOut_imprimitive`).** -/
theorem e4_leaveOneOut (h6 : LRC6) (v : Fin 7 → ℤ) (hce : IsCE v) (l : Fin 7) :
    Finset.univ.gcd (fun j : Fin 6 => v (l.succAbove j)) = 1 := by
  by_contra hl
  have h := RoomA4Rosenfeld.floor_of_leaveOneOut_imprimitive 5 (by norm_num) h6 v hce.1 hce.2.1 l hl
  have h2 := hce.2.2
  norm_num at h
  linarith

/-- **E4' (VERIFIED from E4).** Six even speeds would give an imprimitive leave-one-out family:
the leave-one-out family at the (at most one) odd index is all even. -/
theorem e4_parity (h6 : LRC6) (v : Fin 7 → ℤ) (hce : IsCE v) : evenCount v ≤ 5 := by
  by_contra hgt
  push Not at hgt
  have hex : ∃ l : Fin 7, ∀ i, i ≠ l → (2 : ℤ) ∣ v i := by
    by_contra hno
    push Not at hno
    obtain ⟨i0, -, h0⟩ := hno 0
    obtain ⟨i1, h01, h1⟩ := hno i0
    have hsub : Finset.univ.filter (fun i => (2 : ℤ) ∣ v i) ⊆ (Finset.univ.erase i0).erase i1 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => by subst h; exact h1 hi, fun h => by subst h; exact h0 hi⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [h01]), Finset.card_erase_of_mem (Finset.mem_univ _)]
      at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    unfold evenCount at hgt
    omega
  obtain ⟨l, hl⟩ := hex
  have hg := e4_leaveOneOut h6 v hce l
  have h2 : (2 : ℤ) ∣ Finset.univ.gcd (fun j : Fin 6 => v (l.succAbove j)) :=
    Finset.dvd_gcd (fun j _ => hl _ (Fin.succAbove_ne l j))
  rw [hg] at h2
  norm_num at h2

/-! ## E2: the per-prime Lemma 6/7 contract -/

/-- **E2 (VERIFIED, given the hypothesis `lemma7Check 7 p = true`).**  Reduce `v` mod `q = 8p`,
fold `r ↦ min r (q-r)` into
`[1, 4p]`, pad with odd admissible values if folding merged speeds (padding keeps
`sideOK`, since only the prime `2` divides `8`, and enlarges the covered set), apply
`lemma7Check`, and transport the uncovered `j` back with `nid_congr_mod`.  The padding values are
taken from `{1, 3, 5, 7, 9, 15, 21}` (`padding_odd`); the tuple is `admissible` filtered to the
padded set, which is a sublist by construction. -/
theorem e2_prime_dvd (p : ℕ) (hp : p.Prime) (h7 : 7 < p) (hchk : lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hpar : evenCount v ≤ 5) (hML : ML v < 1 / 8) :
    ∃ i, (p : ℤ) ∣ v i := by
  classical
  by_contra hno
  push Not at hno
  have hp0 : 0 < p := hp.pos
  choose f hf1 hf4 hfp hf2 hfc using fun i => fold_facts p hp0 (v i) (hv i) (hno i)
  set O : Finset ℕ := {1, 3, 5, 7, 9, 15, 21} with hOdef
  have hO := padding_odd p hp h7
  set T0 : Finset ℕ := Finset.univ.image f with hT0def
  have hT0 : T0.card ≤ 7 := Finset.card_image_le.trans (by simp)
  have hOc : O.card = 7 := by rw [hOdef]; rfl
  obtain ⟨T, hT0T, hTU, hTc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : T0 ⊆ T0 ∪ O) hT0
    (hOc ▸ Finset.card_le_card Finset.subset_union_right)
  have hTadm : ∀ x ∈ T, x ∈ admissible 7 p := by
    intro x hx
    rw [admissible_mem]
    rcases Finset.mem_union.mp (hTU hx) with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨hf1 i, hf4 i, hfp i⟩
    · exact ⟨(hO x h).1, (hO x h).2.1, (hO x h).2.2.1⟩
  have hTeven : (T.filter (fun x => x % 2 = 0)).card ≤ 5 := by
    have hsub : T.filter (fun x => x % 2 = 0) ⊆
        (Finset.univ.filter (fun i => (2 : ℤ) ∣ v i)).image f := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases Finset.mem_union.mp (hTU hx.1) with h | h
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf2 i hx.2⟩, rfl⟩
      · have := (hO x h).2.2.2; omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hpar)
  have hLnd : (admissible 7 p).Nodup := List.nodup_range.filter _
  set V := (admissible 7 p).filter (fun x => decide (x ∈ T)) with hVdef
  have hVnd : V.Nodup := hLnd.filter _
  have hVtf : V.toFinset = T := by
    ext x
    simp only [hVdef, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hTadm x h, h⟩⟩
  have hVlen : V.length = 7 := by
    rw [← List.toFinset_card_of_nodup hVnd, hVtf, hTc]
  have hVmem : V ∈ tuples 7 p := List.mem_sublistsLen.mpr ⟨List.filter_sublist, hVlen⟩
  have hside : sideOK 7 V = true := by
    rw [sideOK_seven, decide_eq_true_eq]
    have hnd2 : (V.filter (fun v => v % 2 == 0)).Nodup := hVnd.filter _
    rw [← List.toFinset_card_of_nodup hnd2]
    have hE : (V.filter (fun v => v % 2 == 0)).toFinset = T.filter (fun x => x % 2 = 0) := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, beq_iff_eq]
      rw [← List.mem_toFinset, hVtf]
    rw [hE]
    exact hTeven
  have hall := List.all_eq_true.mp hchk V hVmem
  rw [hside, Bool.true_and] at hall
  have hcw : coversWindow 7 p V = false := by simpa using hall
  rw [← Bool.not_eq_true, coversWindow, List.all_eq_true] at hcw
  push Not at hcw
  obtain ⟨j, -, hj⟩ := hcw
  have hunc : ∀ i, 8 * p ≤ 8 * min (j * f i % (8 * p)) (8 * p - j * f i % (8 * p)) := by
    intro i
    have hfi : f i ∈ V := by
      rw [hVdef, List.mem_filter, decide_eq_true_eq]
      have hT : f i ∈ T := hT0T (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨hTadm _ hT, hT⟩
    have hnc : ¬ coversAt 7 p j (f i) = true := fun hc =>
      hj (List.any_eq_true.mpr ⟨f i, hfi, hc⟩)
    simp only [coversAt, decide_eq_true_eq, show (7 : ℕ) + 1 = 8 from rfl] at hnc
    omega
  have hgap : (1 : ℝ) / 8 ≤ gap v (((j : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ)) := by
    apply le_gap
    intro i
    rw [show (v i : ℝ) * (((j : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ))
        = ((j : ℤ) : ℝ) * (v i : ℝ) / ((8 * p : ℕ) : ℝ) by ring]
    rcases hfc i with h | h
    · rw [nid_congr_mod (v i) (f i) (8 * p) (by omega) j h]
      exact nid_ge_of_uncovered p j (f i) hp0 (hunc i)
    · have h' : ((8 * p : ℕ) : ℤ) ∣ v i - (-(f i : ℤ)) := by rw [sub_neg_eq_add]; exact h
      rw [nid_congr_mod (v i) (-(f i : ℤ)) (8 * p) (by omega) j h']
      rw [show ((j : ℤ) : ℝ) * (((-(f i : ℤ)) : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ)
          = -(((j : ℤ) : ℝ) * ((f i : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ)) by push_cast; ring,
        nearestIntDist_neg]
      exact nid_ge_of_uncovered p j (f i) hp0 (hunc i)
  have := gap_le_ML v (((j : ℤ) : ℝ) / ((8 * p : ℕ) : ℝ))
  linarith

/-! ## E3: Lemma 4 and the divisibility assembly -/

/-- **E3a Lemma 4 (VERIFIED).** Re-proved directly at the time `1/j` (the content of
`ML_ge_LRC_of_covering`, whose module is not in this file's import closure). -/
theorem e3_small_divisor (v : Fin 7 → ℤ) (hML : ML v < 1 / 8) (j : ℕ) (hj2 : 2 ≤ j)
    (hj8 : j ≤ 8) : ∃ i, (j : ℤ) ∣ v i := by
  by_contra hno
  push Not at hno
  have hjpos : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
  have hgap : (1 : ℝ) / (j : ℝ) ≤ gap v (1 / (j : ℝ)) := by
    apply le_gap
    intro i
    rw [show (v i : ℝ) * (1 / (j : ℝ)) = (v i : ℝ) / (j : ℝ) by ring]
    by_contra hlt
    push Not at hlt
    rw [nearestIntDist_div_lt_iff (v i) j hjpos, one_div_mul_cancel hjR.ne'] at hlt
    have hr0 : v i % (j : ℤ) ≠ 0 := fun h => hno i (Int.dvd_of_emod_eq_zero h)
    have hr1 : 0 ≤ v i % (j : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hjpos.ne')
    have hr2 : v i % (j : ℤ) < j := Int.emod_lt_of_pos _ (by exact_mod_cast hjpos)
    have ha : (1 : ℤ) ≤ v i % j := by omega
    have hb : (1 : ℤ) + v i % j ≤ j := by omega
    have haR : (1 : ℝ) ≤ ((v i % (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast ha
    have hbR : (1 : ℝ) + ((v i % (j : ℤ) : ℤ) : ℝ) ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hb
    simp only [Int.cast_natCast] at hbR
    rcases min_lt_iff.mp hlt with h | h <;> linarith
  have h8 : (1 : ℝ) / 8 ≤ 1 / (j : ℝ) := one_div_le_one_div_of_le hjR (by exact_mod_cast hj8)
  linarith [gap_le_ML v (1 / (j : ℝ))]

/-- **E3 (VERIFIED).** Pairwise coprime prime powers `8, 3, 5, 7, p ∈ S` each divide some
speed, hence the product. -/
theorem e3_lcm_dvd (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hML : ML v < 1 / 8)
    (hS : ∀ p ∈ rosenfeldS, ∃ i, (p : ℤ) ∣ v i) :
    (((840 * ∏ p ∈ rosenfeldS, p : ℕ)) : ℤ) ∣ ∏ i, v i := by
  have hdv : ∀ d : ℕ, (∃ i, (d : ℤ) ∣ v i) → (d : ℤ) ∣ ∏ i, v i := by
    rintro d ⟨i, hi⟩
    exact hi.trans (Finset.dvd_prod_of_mem v (Finset.mem_univ i))
  have h8 := hdv 8 (e3_small_divisor v hML 8 (by norm_num) le_rfl)
  have h3 := hdv 3 (e3_small_divisor v hML 3 (by norm_num) (by norm_num))
  have h5 := hdv 5 (e3_small_divisor v hML 5 (by norm_num) (by norm_num))
  have h7 := hdv 7 (e3_small_divisor v hML 7 (by norm_num) (by norm_num))
  push_cast at h8 h3 h5 h7
  have c1 : IsCoprime (5 : ℤ) 7 := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have c2 : IsCoprime (3 : ℤ) (5 * 7) := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have c3 : IsCoprime (8 : ℤ) (3 * (5 * 7)) := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have h840 : (840 : ℤ) ∣ ∏ i, v i := by
    have := c3.mul_dvd h8 (c2.mul_dvd h3 (c1.mul_dvd h5 h7))
    norm_num at this
    exact this
  have hSd : (∏ p ∈ rosenfeldS, ((p : ℕ) : ℤ)) ∣ ∏ i, v i := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      simp only [Function.onFun]
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes (rosenfeldS_primes a ha).1 (rosenfeldS_primes b hb).1).mpr hab
    · intro p hp
      exact hdv p (hS p hp)
  have hcop : IsCoprime (840 : ℤ) (∏ p ∈ rosenfeldS, ((p : ℕ) : ℤ)) := by
    apply IsCoprime.prod_right
    intro p hp
    rw [show (840 : ℤ) = ((840 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    simp only [rosenfeldS, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have := hcop.mul_dvd h840 hSd
  push_cast
  exact this

/-! ## E5: MSS Theorem A at n = 7 -/

/-- **STUB, NOT ON THE MAIN PATH — contains `sorry`, superseded 2026-09-27.**
Do not cite this in place of the unconditional theorem: use
`LRSpectrumFull.EightRunners.eight_runners_unconditional`, which does not depend on this
declaration or on any `sorry`. This stub is kept only because `EightMSSImport.eight_runners`
(also superseded) still refers to it in a docstring. Reduced sorry-free in
`EightMSS.e5_sum_of_gap` to the hypothesis `EightMSS.MSSGap7` via the VERIFIED staircase lemma
`EightMSS.e5b_staircase`; that route is what `EightE5.lean` actually uses. -/
theorem e5_sum_STUB_SUPERSEDED (h6 : LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hsum : (28 : ℤ) ^ 6 < ∑ i, v i) : 1 / 8 ≤ ML v := by
  sorry

/-- AM-GM in integer form at seven variables: `7^7 ∏ v ≤ (∑ v)^7`. -/
theorem amgm7 (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 7 ^ 7 * ∏ i, v i ≤ (∑ i, v i) ^ 7 := by
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 7)), (0 : ℝ) ≤ (v i : ℝ) :=
    fun i _ => by exact_mod_cast (hv i).le
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin 7))
    (fun _ => (1 / 7 : ℝ)) (fun i => (v i : ℝ)) (fun _ _ => by norm_num) (by simp) hz
  set g := ∏ i, (v i : ℝ) ^ (1 / 7 : ℝ) with hg
  have hg0 : 0 ≤ g := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hz i (Finset.mem_univ i)) _)
  have hg7 : g ^ 7 = ∏ i, (v i : ℝ) := by
    rw [hg, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i hi)]
    norm_num
  have hsum : (∑ i, (1 / 7 : ℝ) * (v i : ℝ)) = (∑ i, (v i : ℝ)) / 7 := by
    rw [← Finset.mul_sum]; ring
  rw [hsum] at hgm
  have hpow : g ^ 7 ≤ ((∑ i, (v i : ℝ)) / 7) ^ 7 := pow_le_pow_left₀ hg0 hgm 7
  rw [hg7, div_pow] at hpow
  have hR : (7 : ℝ) ^ 7 * ∏ i, (v i : ℝ) ≤ (∑ i, (v i : ℝ)) ^ 7 := by
    rw [le_div_iff₀ (by norm_num)] at hpow
    linarith
  exact_mod_cast hR

/-- **E5-amgm (VERIFIED 2026-09-24: EXIT 0, standard axioms; AM-GM in integer form).** -/
theorem e5_amgm (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, v i) : (28 : ℤ) ^ 6 < ∑ i, v i := by
  by_contra hle
  push Not at hle
  have hs0 : 0 ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ => (hv i).le)
  have h1 := amgm7 v hv
  have h2 : (∑ i, v i) ^ 7 ≤ ((28 : ℤ) ^ 6) ^ 7 := pow_le_pow_left₀ hs0 hle 7
  have h3 : ((28 : ℤ) ^ 6) ^ 7 = 28 ^ 42 := by norm_num
  omega

/-- **STUB, NOT ON THE MAIN PATH — depends on `e5_sum_STUB_SUPERSEDED`, hence on a `sorry`.**
Use `EightE5.eight_runners_unconditional` instead. -/
theorem e5_prod_STUB_SUPERSEDED (h6 : LRC6) (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, v i) : 1 / 8 ≤ ML v :=
  e5_sum_STUB_SUPERSEDED h6 v hv hg (e5_amgm v hv hprod)

/-! ## E0 and the assembly -/

/-- **E0 (VERIFIED, via the local copy `ML_smul8` of `ML_smul`).** -/
theorem e0_primitive (h : ∀ v : Fin 7 → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 → 1 / 8 ≤ ML v)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v := by
  obtain ⟨w, hw, hg1⟩ := Finset.extract_gcd v (Finset.univ_nonempty (α := Fin 7))
  have hg0 : 0 ≤ Finset.univ.gcd v :=
    Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := v))
  generalize Finset.univ.gcd v = g at hw hg0
  have hw' : ∀ i, v i = g * w i := fun i => hw i (Finset.mem_univ i)
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h' | h'
    · exact h'
    · exfalso; have := hv 0; rw [hw' 0, ← h'] at this; simp at this
  have hwpos : ∀ i, 0 < w i := fun i => by
    have := hv i
    rw [hw' i] at this
    by_contra hn
    push Not at hn
    nlinarith
  rw [show v = fun i => g * w i from funext hw', ML_smul8 g hgpos.ne' w]
  exact h w hwpos hg1

/-- **STUB, NOT ON THE MAIN PATH — do not cite as the eight-runner theorem.**
Depends on `e5_prod_STUB_SUPERSEDED`, hence on a `sorry`, and also takes `hchk` as a raw
hypothesis rather than discharging it from `EightCert27.hchk_all`. The actual, sorry-free,
unconditionally-proved theorem is
`LRSpectrumFull.EightRunners.eight_runners_unconditional : ∀ v, (∀ i, 0 < v i) → 1/8 ≤ ML v`,
whose only non-standard axioms are the 27 compacted certificates in `EightCert27.lean`. Kept
here only so `Chen7RunnerImport.lean` (itself marked superseded) still typechecks. -/
theorem eight_runners_STUB_SUPERSEDED (h6 : LRC6) (hchk : ∀ p ∈ rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v := by
  refine e0_primitive (fun w hw hg => ?_) v hv
  by_contra hlt
  push Not at hlt
  have hce : IsCE w := ⟨hw, hg, hlt⟩
  have hpar := e4_parity h6 w hce
  have hS : ∀ p ∈ rosenfeldS, ∃ i, (p : ℤ) ∣ w i := fun p hp =>
    e2_prime_dvd p (rosenfeldS_primes p hp).1 (rosenfeldS_primes p hp).2 (hchk p hp) w hw hpar hlt
  have hdvd := e3_lcm_dvd w hw hlt hS
  have hpos : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hle := Int.le_of_dvd hpos hdvd
  have hnum : ((28 : ℕ) ^ 42 : ℤ) < ((7 ^ 7 * (840 * ∏ p ∈ rosenfeldS, p) : ℕ) : ℤ) := by
    exact_mod_cast numeric
  have hprod : (28 : ℤ) ^ 42 < 7 ^ 7 * ∏ i, w i := by
    push_cast at hnum hle
    nlinarith
  exact absurd (e5_prod_STUB_SUPERSEDED h6 w hw hg hprod) (not_le.mpr hlt)

end LRSpectrumFull.EightPlan
