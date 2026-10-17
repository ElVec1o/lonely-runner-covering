/-
# E6 session 13: `|D| = 4` (5 runners), hard case and assembly

Route (differs from the paper's case chase, see `barajasSerra_card4_hard` docstring in
`BarajasSerra.lean` and the session-13 log entry): each level-0 element `d` is summarized by
`a = q(d)`, `r = d mod 5` and the three carries of eq. (5) (`qarc_add_carry`). The finite claim
that ANY three such summaries share a good multiplier `(1 + 5^m k) * j` is decided by kernel
`decide` in `BarajasSerraCard4Table.combo` (no sign-flip WLOG and no popular-class split are
needed: the relaxed model is closed under the sign flip, and the exhaustive check covers all
residues `r ∈ {1,2,3,4}` directly). The level-`m` element is handled by `qarc_bridge_top`.
-/

import LRSpectrumFull.BarajasSerra
import LRSpectrumFull.BarajasSerraCard4Table
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull.BarajasSerra

open LRSpectrumFull
open LRSpectrumFull.BarajasSerra.Card4Table

theorem qarc_lt_five (m N x : ℕ) : qarc 5 m N x < 5 := by
  unfold qarc; exact Nat.mod_lt _ (by norm_num)

/-- `nu 5 (j * d) = 0` for `1 ≤ j ≤ 4` and `5 ∤ d`. -/
theorem nu_small_mul (j d : ℕ) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) (hd : ¬ 5 ∣ d) :
    nu 5 (j * d) = 0 := by
  unfold nu
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · exact hd h

/-- **Level-0 digit facts.** For `5 ∤ d`, the arc of `(1 + 5^m k) * (j * d)` is given by the
relaxed model `Card4Table.qj`/`good` with `a = q(d)`, `r = d mod 5` and some carries `< 2`. -/
theorem level0_model (m d : ℕ) (hd : ¬ 5 ∣ d) :
    ∃ c1 c2 c3, c1 < 2 ∧ c2 < 2 ∧ c3 < 2 ∧
      ∀ j k, 1 ≤ j → j ≤ 4 → k < 5 →
        qarc 5 m (5 ^ (m + 1)) ((1 + 5 ^ m * k) * (j * d))
          = (qj (qarc 5 m (5 ^ (m + 1)) d) c1 c2 c3 j + k * ((j * (d % 5)) % 5)) % 5 := by
  obtain ⟨c1, hc1, h2⟩ := qarc_add_carry 5 m (by norm_num) d d
  obtain ⟨c2, hc2, h3⟩ := qarc_add_carry 5 m (by norm_num) (d + d) d
  obtain ⟨c3, hc3, h4⟩ := qarc_add_carry 5 m (by norm_num) (d + d + d) d
  refine ⟨c1, c2, c3, hc1, hc2, hc3, ?_⟩
  intro j k hj1 hj4 hk
  have hnu : nu 5 (j * d) = 0 := nu_small_mul j d hj1 hj4 hd
  have hlam := qarc_mul_lam_eq 5 0 m Nat.prime_five (Nat.zero_le m) k hk (j * d) hnu
  rw [Nat.sub_zero] at hlam
  rw [hlam]
  have hrp : rp 5 (j * d) = (j * (d % 5)) % 5 := by
    unfold rp
    rw [hnu, pow_zero, Nat.div_one, Nat.mul_mod j d, Nat.mul_mod j (d % 5), Nat.mod_mod]
  rw [hrp]
  congr 2
  set a := qarc 5 m (5 ^ (m + 1)) d with ha
  have hlt : a < 5 := qarc_lt_five m _ d
  interval_cases j
  · simp only [qj, one_mul]; exact ha.symm
  · simp only [qj]; rw [show 2 * d = d + d by ring]; exact h2
  · simp only [qj]; rw [show 3 * d = d + d + d by ring, h3, h2]
  · simp only [qj]; rw [show 4 * d = d + d + d + d by ring, h4, h3, h2]

/-- A multiplier of the form `(1 + 5^m k) * j` with `m > 0`, `1 ≤ j ≤ 4` is coprime to `5`. -/
theorem lam_coprime (m k j : ℕ) (hm : 0 < m) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) :
    Nat.Coprime ((1 + 5 ^ m * k) * j) 5 := by
  have h5 : Nat.Prime 5 := Nat.prime_five
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd h5]
  intro h
  rcases (Nat.Prime.dvd_mul h5).mp h with h | h
  · have h5m : 5 ∣ 5 ^ m * k := Dvd.dvd.mul_right (dvd_pow_self 5 hm.ne') k
    have : 5 ∣ 1 := (Nat.dvd_add_left h5m).mp h
    omega
  · have := Nat.le_of_dvd (by omega) h; omega

/-- Bridge from `qarc` of `lam * d` to the real bound at `t = lam / N`. -/
theorem real_eq_div (lam N d : ℕ) :
    ((lam : ℝ) / (N : ℝ)) * (d : ℝ) = ((lam * d : ℕ) : ℝ) / (N : ℝ) := by
  push_cast; ring

/-- **Core hard case.** Three level-0 elements (`5 ∤ y i`) and one element `d4` divisible by
`5`: some `t > 0` puts all four at distance `≥ 1/5` from the integers. -/
theorem card4_hard_core (y : Fin 3 → ℕ) (hy : ∀ i, ¬ 5 ∣ y i) (d4 : ℕ) (hd4 : d4 ≠ 0)
    (h5d4 : 5 ∣ d4) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 5 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 5 : ℝ) ≤ nearestIntDist (t * d4) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set m := nu 5 d4 with hmdef
  have hm : 0 < m := one_le_padicValNat_of_dvd hd4 h5d4
  set N := 5 ^ (m + 1) with hN
  have hmod : ∀ i, 0 < y i % 5 := fun i => by
    have := hy i; omega
  choose c1 c2 c3 hc1 hc2 hc3 hq using fun i => level0_model m (y i) (hy i)
  obtain ⟨j, k, hj1, hj4, hk, g0, g1, g2⟩ := combo
    (qarc 5 m N (y 0)) (y 0 % 5) (c1 0) (c2 0) (c3 0)
    (qarc 5 m N (y 1)) (y 1 % 5) (c1 1) (c2 1) (c3 1)
    (qarc 5 m N (y 2)) (y 2 % 5) (c1 2) (c2 2) (c3 2)
    (qarc_lt_five _ _ _) (Nat.mod_lt _ (by norm_num)) (hmod 0) (hc1 0) (hc2 0) (hc3 0)
    (qarc_lt_five _ _ _) (Nat.mod_lt _ (by norm_num)) (hmod 1) (hc1 1) (hc2 1) (hc3 1)
    (qarc_lt_five _ _ _) (Nat.mod_lt _ (by norm_num)) (hmod 2) (hc1 2) (hc2 2) (hc3 2)
  have hgood : ∀ i, good (qarc 5 m N (y i)) (y i % 5) (c1 i) (c2 i) (c3 i) j k = true := by
    intro i; fin_cases i
    · exact g0
    · exact g1
    · exact g2
  set lam := (1 + 5 ^ m * k) * j with hlam
  have hlamcop : Nat.Coprime lam 5 := lam_coprime m k j hm hj1 hj4
  have hlamne : lam ≠ 0 := by
    rw [hlam]; exact Nat.mul_ne_zero (by omega) (by omega)
  have hlamR : (0:ℝ) < (lam:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hlamne
  have hNposR : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by rw [hN]; positivity
    exact_mod_cast this
  refine ⟨(lam : ℝ) / (N : ℝ), div_pos hlamR hNposR, ?_, ?_⟩
  · intro i
    have hqi := hq i j k hj1 hj4 hk
    have hmul : lam * y i = (1 + 5 ^ m * k) * (j * y i) := by rw [hlam]; ring
    have hgi := hgood i
    simp only [good, Bool.and_eq_true, bne_iff_ne, ne_eq] at hgi
    have h0 : qarc 5 m N (lam * y i) ≠ 0 := by
      rw [hmul, hN, hqi]; exact hgi.1
    have h4 : qarc 5 m N (lam * y i) ≠ 5 - 1 := by
      rw [hmul, hN, hqi]; exact hgi.2
    rw [real_eq_div]
    exact qarc_bridge_mid 5 m N (lam * y i) Nat.prime_five hN h0 h4
  · have hnu : nu 5 (lam * d4) = m := by
      rw [hmdef]; exact nu_mul_coprime 5 lam d4 hlamcop hlamne hd4
    rw [real_eq_div]
    exact qarc_bridge_top 5 m N (lam * d4) Nat.prime_five hN (Nat.mul_ne_zero hlamne hd4) hnu

/-- **Scaled hard case.** Three elements of common `5`-adic valuation `g` and one element of
strictly larger valuation. Reduces to `card4_hard_core` by dividing by `5^g`. -/
theorem card4_hard_scaled (y : Fin 3 → ℕ) (d4 g : ℕ) (hy0 : ∀ i, y i ≠ 0) (hd4 : d4 ≠ 0)
    (hyv : ∀ i, nu 5 (y i) = g) (hd4v : g < nu 5 d4) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 5 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 5 : ℝ) ≤ nearestIntDist (t * d4) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvy : ∀ i, 5 ^ g ∣ y i := fun i => by
    rw [← hyv i]; exact pow_padicValNat_dvd
  have hdvd4 : 5 ^ (g + 1) ∣ d4 := (padicValNat_dvd_iff_le hd4).mpr hd4v
  have hdvd4' : 5 ^ g ∣ d4 := Dvd.dvd.trans (pow_dvd_pow 5 (Nat.le_succ g)) hdvd4
  have hpg : 0 < 5 ^ g := by positivity
  set y' : Fin 3 → ℕ := fun i => y i / 5 ^ g with hy'
  set d4' := d4 / 5 ^ g with hd4'
  have hyeq : ∀ i, y i = 5 ^ g * y' i := fun i => (Nat.mul_div_cancel' (hdvy i)).symm
  have hd4eq : d4 = 5 ^ g * d4' := (Nat.mul_div_cancel' hdvd4').symm
  have hy'nd : ∀ i, ¬ 5 ∣ y' i := by
    intro i h
    have h1 : 5 ^ g * 5 ∣ y i := by rw [hyeq i]; exact Nat.mul_dvd_mul_left _ h
    rw [← pow_succ, ← hyv i] at h1
    exact pow_succ_padicValNat_not_dvd (hy0 i) h1
  have hd4'ne : d4' ≠ 0 := by
    intro h; rw [h, mul_zero] at hd4eq; exact hd4 hd4eq
  have h5d4' : 5 ∣ d4' := by
    rw [hd4eq, pow_succ] at hdvd4
    exact Nat.dvd_of_mul_dvd_mul_left hpg hdvd4
  obtain ⟨t, ht, hb, hb4⟩ := card4_hard_core y' hy'nd d4' hd4'ne h5d4'
  refine ⟨t / (5 ^ g : ℝ), by positivity, ?_, ?_⟩
  · intro i
    have : t / (5 ^ g : ℝ) * (y i : ℝ) = t * (y' i : ℝ) := by
      rw [hyeq i]; push_cast; field_simp
    rw [this]; exact hb i
  · have : t / (5 ^ g : ℝ) * (d4 : ℝ) = t * (d4' : ℝ) := by
      rw [hd4eq]; push_cast; field_simp
    rw [this]; exact hb4

/-- **`|D| = 4` hard case, Finset form (the statement left as `sorry` in sessions 5-12, same
hypotheses).** Level `0` has three elements, level `m > 0` one, all other levels empty. -/
theorem barajasSerra_card4_hard (D : Finset ℕ) (hDne : D.Nonempty) (hpos : ∀ d ∈ D, 0 < d)
    (m : ℕ) (hm : m = D.sup (nu 5)) (hmpos : 0 < m)
    (hcard0 : (Dlevel 5 D 0).card = 3) (hcardm : (Dlevel 5 D m).card = 1)
    (hother : ∀ j, 0 < j → j < m → Dlevel 5 D j = ∅) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 5 : ℝ) ≤ nearestIntDist (t * d) := by
  obtain ⟨a, b, c, hab, hac, hbc, h0⟩ := Finset.card_eq_three.mp hcard0
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcardm
  have hmem : ∀ x i, x ∈ Dlevel 5 D i ↔ x ∈ D ∧ nu 5 x = i := fun x i => Finset.mem_filter
  have ha : a ∈ Dlevel 5 D 0 := by rw [h0]; simp
  have hb : b ∈ Dlevel 5 D 0 := by rw [h0]; simp
  have hc : c ∈ Dlevel 5 D 0 := by rw [h0]; simp
  have hee : e ∈ Dlevel 5 D m := by rw [he]; simp
  rw [hmem] at ha hb hc hee
  obtain ⟨t, ht, hy, h4⟩ := card4_hard_scaled ![a, b, c] e 0
    (fun i => by
      fin_cases i
      · exact (hpos a ha.1).ne'
      · exact (hpos b hb.1).ne'
      · exact (hpos c hc.1).ne')
    (hpos e hee.1).ne'
    (fun i => by
      fin_cases i
      · exact ha.2
      · exact hb.2
      · exact hc.2)
    (by rw [hee.2]; exact hmpos)
  refine ⟨t, ht, fun d hd => ?_⟩
  have hle : nu 5 d ≤ m := hm ▸ Finset.le_sup (f := nu 5) hd
  rcases Nat.eq_zero_or_pos (nu 5 d) with hz | hz
  · have hd0 : d ∈ Dlevel 5 D 0 := (hmem d 0).mpr ⟨hd, hz⟩
    rw [h0] at hd0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd0
    rcases hd0 with rfl | rfl | rfl
    · simpa using hy 0
    · simpa using hy 1
    · simpa using hy 2
  · rcases lt_or_eq_of_le hle with hlt | heq
    · have hdl : d ∈ Dlevel 5 D (nu 5 d) := (hmem d _).mpr ⟨hd, rfl⟩
      rw [hother _ hz hlt] at hdl
      simp at hdl
    · have hdl : d ∈ Dlevel 5 D m := (hmem d m).mpr ⟨hd, heq⟩
      rw [he, Finset.mem_singleton] at hdl
      rw [hdl]; exact h4

/-- **Five runners (`|D| = 4`), Barajas-Serra Section 3.** Every four positive integer speeds
have maximum loneliness at least `1/5`. -/
theorem barajasSerra_card4 (u : Fin 4 → ℤ) (hpos : ∀ i, 0 < u i) : (1 / 5 : ℝ) ≤ ML u := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set x : Fin 4 → ℕ := fun i => (u i).toNat with hxdef
  have hx0 : ∀ i, 0 < x i := fun i => Int.pos_iff_toNat_pos.mp (hpos i)
  have hxcast : ∀ i, ((x i : ℕ) : ℤ) = u i := fun i => Int.toNat_of_nonneg (hpos i).le
  have key : ∃ t : ℝ, ∀ i, (1 / 5 : ℝ) ≤ nearestIntDist (t * x i) := by
    by_cases hard : ∃ i0 : Fin 4, ∀ k : Fin 3,
        nu 5 (x (i0.succAbove k)) = nu 5 (x (i0.succAbove 0)) ∧
          nu 5 (x (i0.succAbove 0)) < nu 5 (x i0)
    · obtain ⟨i0, hi0⟩ := hard
      obtain ⟨t, -, hb, hb4⟩ := card4_hard_scaled (fun k => x (i0.succAbove k)) (x i0)
        (nu 5 (x (i0.succAbove 0))) (fun k => (hx0 _).ne') (hx0 i0).ne'
        (fun k => (hi0 k).1) (hi0 0).2
      refine ⟨t, fun i => ?_⟩
      rcases Fin.eq_self_or_eq_succAbove i0 i with rfl | ⟨k, rfl⟩
      · exact hb4
      · exact hb k
    · set D := Finset.univ.image x with hD
      have hDne : D.Nonempty := Finset.univ_nonempty.image x
      have hposD : ∀ d ∈ D, 0 < d := by
        intro d hd
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
        exact hx0 i
      set m := D.sup (nu 5) with hm
      have hcard : ∀ j < m, (Dlevel 5 D j).card ≤ 2 := by
        intro j hj
        by_contra hcon
        have hcon : 2 < (Dlevel 5 D j).card := Nat.lt_of_not_le hcon
        set S := Finset.univ.filter (fun i => nu 5 (x i) = j) with hS
        have hlev : Dlevel 5 D j = S.image x := by
          unfold Dlevel; rw [hD, Finset.filter_image]
        have hS3 : 3 ≤ S.card := by
          have := Finset.card_image_le (s := S) (f := x)
          rw [← hlev] at this; omega
        obtain ⟨d0, hd0D, hd0⟩ := Finset.exists_mem_eq_sup D hDne (nu 5)
        obtain ⟨i0, -, rfl⟩ := Finset.mem_image.mp hd0D
        have hmi0 : m = nu 5 (x i0) := hd0
        have hsub : S ⊆ Finset.univ.erase i0 := by
          intro i hi
          simp only [hS, Finset.mem_filter] at hi
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          rintro rfl
          omega
        have hSeq : S = Finset.univ.erase i0 := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
          simp only [Finset.card_univ, Fintype.card_fin]
          omega
        have hk : ∀ k : Fin 3, nu 5 (x (i0.succAbove k)) = j := by
          intro k
          have hmemS : i0.succAbove k ∈ S := by
            rw [hSeq]; exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i0 k, Finset.mem_univ _⟩
          simp only [hS, Finset.mem_filter] at hmemS
          exact hmemS.2
        apply hard
        refine ⟨i0, fun k => ?_⟩
        rw [hk k, hk 0]
        exact ⟨rfl, by omega⟩
      obtain ⟨t, -, hb⟩ := barajasSerra_card4_easy D hDne hposD m rfl hcard
      exact ⟨t, fun i => hb (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))⟩
  obtain ⟨t, ht⟩ := key
  have hle : (1 / 5 : ℝ) ≤ gap u t := by
    apply le_gap
    intro i
    rw [← hxcast i]
    simpa [mul_comm] using ht i
  exact hle.trans (le_csSup (bddAbove_range_gap u) ⟨t, rfl⟩)

end LRSpectrumFull.BarajasSerra
