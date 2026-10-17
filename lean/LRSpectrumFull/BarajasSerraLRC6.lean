import LRSpectrumFull.BarajasSerraLRC6BCD
import LRSpectrumFull.BarajasSerraCaseA

/-!
# E6 session 20: LRC for six speeds (seven runners), Barajas-Serra, assembled

`lrc6 : ∀ u : Fin 6 → ℤ, (∀ i, 0 < u i) → 1/7 ≤ ML u`.
Level split on `D = image of the speeds`, `m = max ν_7(D)` (paper Section 4):
* every level `j < m` has at most 3 elements: `primeFilteringCor3Top` (Corollary 3);
* some level `j < m` has at least 4: since `|D| ≤ 6` and level `m` is nonempty, either 5 at `j`
  and 1 at `m` (case (a), `case_a`), or 4 at `j` and the rest at `m` (case (b)), or 4 at `j`, one
  at `ℓ`, one at `m`, with `j < ℓ < m` (case (c)) or `ℓ < j` (case (d)).
The scaled forms below divide by the minimal power of 7.
-/

namespace LRSpectrumFull.BarajasSerra.Sec5

open LRSpectrumFull LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.Sec6

/-! ## scaling -/

theorem nd_of_nu {x : ℕ} (hx : x ≠ 0) (h : nu 7 x = 0) : ¬ 7 ∣ x := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hd
  have := (dvd_iff_padicValNat_ne_zero hx).mp hd
  exact this h

theorem sc (g x : ℕ) (hx : x ≠ 0) (hg : g ≤ nu 7 x) :
    x / 7 ^ g ≠ 0 ∧ nu 7 (x / 7 ^ g) = nu 7 x - g ∧ ∀ t : ℝ, t / 7 ^ g * x = t * ((x / 7 ^ g : ℕ) : ℝ) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdv : 7 ^ g ∣ x := (pow_dvd_pow 7 hg).trans (by unfold nu; exact pow_padicValNat_dvd)
  have hpos : (0 : ℝ) < 7 ^ g := by positivity
  refine ⟨?_, ?_, fun t => ?_⟩
  · intro h
    have := Nat.mul_div_cancel' hdv
    rw [h, mul_zero] at this; exact hx this.symm
  · unfold nu; exact padicValNat.div_pow hdv
  · have e : (x : ℝ) = 7 ^ g * ((x / 7 ^ g : ℕ) : ℝ) := by
      have := Nat.mul_div_cancel' hdv
      exact_mod_cast this.symm
    rw [e]; field_simp

theorem case_b (g m : ℕ) (hgm : g < m) (y : Fin 4 → ℕ) (hy0 : ∀ i, y i ≠ 0) (hyv : ∀ i, nu 7 (y i) = g)
    (T : List ℕ) (hT : ∀ d ∈ T, d ≠ 0 ∧ nu 7 d = m) :
    ∃ t : ℝ, (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * y i)) ∧
      ∀ d ∈ T, (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  have sy := fun i => sc g (y i) (hy0 i) (by rw [hyv i])
  have sT := fun d (hd : d ∈ T) => sc g d (hT d hd).1 (by rw [(hT d hd).2]; omega)
  obtain ⟨t, -, h1, h2⟩ := case_b0 (m - g) (by omega) (fun i => y i / 7 ^ g)
    (fun i => nd_of_nu (sy i).1 (by rw [(sy i).2.1, hyv i]; omega)) (T.map (· / 7 ^ g))
    (by
      intro d hd
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
      exact ⟨(sT d0 hd0).1, by rw [(sT d0 hd0).2.1, (hT d0 hd0).2]⟩)
  refine ⟨t / 7 ^ g, fun i => ?_, fun d hd => ?_⟩
  · rw [(sy i).2.2]; exact h1 i
  · rw [(sT d hd).2.2]; exact h2 _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem case_c (g i0 m : ℕ) (h1 : g < i0) (h2 : i0 < m) (y : Fin 4 → ℕ) (hy0 : ∀ i, y i ≠ 0)
    (hyv : ∀ i, nu 7 (y i) = g) (e : ℕ) (he0 : e ≠ 0) (hev : nu 7 e = i0) (d : ℕ) (hd0 : d ≠ 0)
    (hdv : nu 7 d = m) :
    ∃ t : ℝ, (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * y i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * e) ∧ (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  have sy := fun i => sc g (y i) (hy0 i) (by rw [hyv i])
  have se := sc g e he0 (by omega)
  have sd := sc g d hd0 (by omega)
  obtain ⟨t, -, k1, k2, k3⟩ := case_c0 (m - g) (i0 - g) (by omega) (by omega) (fun i => y i / 7 ^ g)
    (fun i => nd_of_nu (sy i).1 (by rw [(sy i).2.1, hyv i]; omega)) _ se.1 (by rw [se.2.1, hev])
    _ sd.1 (by rw [sd.2.1, hdv])
  refine ⟨t / 7 ^ g, fun i => ?_, ?_, ?_⟩
  · rw [(sy i).2.2]; exact k1 i
  · rw [se.2.2]; exact k2
  · rw [sd.2.2]; exact k3

theorem case_d (g i0 m : ℕ) (h1 : g < i0) (h2 : i0 < m) (z : ℕ) (hz0 : z ≠ 0) (hzv : nu 7 z = g)
    (y : Fin 4 → ℕ) (hy0 : ∀ i, y i ≠ 0) (hyv : ∀ i, nu 7 (y i) = i0) (d : ℕ) (hd0 : d ≠ 0)
    (hdv : nu 7 d = m) :
    ∃ t : ℝ, (1 : ℝ) / 7 ≤ nearestIntDist (t * z) ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * y i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
  have sy := fun i => sc g (y i) (hy0 i) (by rw [hyv i]; omega)
  have sz := sc g z hz0 (by omega)
  have sd := sc g d hd0 (by omega)
  obtain ⟨t, -, k1, k2, k3⟩ := case_d0 (m - g) (i0 - g) (by omega) (by omega) (z / 7 ^ g)
    (nd_of_nu sz.1 (by rw [sz.2.1, hzv]; omega)) (fun i => y i / 7 ^ g) (fun i => (sy i).1)
    (fun i => by rw [(sy i).2.1, hyv i]) _ sd.1 (by rw [sd.2.1, hdv])
  refine ⟨t / 7 ^ g, ?_, fun i => ?_, ?_⟩
  · rw [sz.2.2]; exact k1
  · rw [(sy i).2.2]; exact k2 i
  · rw [sd.2.2]; exact k3

/-! ## enumerating a finset of known card -/

theorem fin_enum (s : Finset ℕ) (n : ℕ) (h : s.card = n) :
    ∃ y : Fin n → ℕ, (∀ i, y i ∈ s) ∧ ∀ d ∈ s, ∃ i, y i = d := by
  subst h
  refine ⟨fun i => (s.equivFin.symm i).1, fun i => (s.equivFin.symm i).2, fun d hd => ?_⟩
  exact ⟨s.equivFin ⟨d, hd⟩, by simp⟩

/-! ## the level split -/

theorem lrc6_nat (x : Fin 6 → ℕ) (hx0 : ∀ i, 0 < x i) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * x i) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set D := Finset.univ.image x with hD
  have hDne : D.Nonempty := Finset.univ_nonempty.image x
  have hposD : ∀ d ∈ D, 0 < d := by
    intro d hd; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd; exact hx0 i
  have hcardD : D.card ≤ 6 := Finset.card_image_le.trans (by simp)
  set m := D.sup (nu 7) with hm
  suffices hW : ∃ t : ℝ, ∀ d ∈ D, (1 : ℝ) / 7 ≤ nearestIntDist (t * d) by
    obtain ⟨t, ht⟩ := hW
    exact ⟨t, fun i => ht (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))⟩
  by_cases heasy : ∀ j < m, (Dlevel 7 D j).card ≤ 3
  · obtain ⟨t, -, ht⟩ := primeFilteringCor3Top 7 (by norm_num) D hDne hposD m rfl
      (fun j hj => by have := heasy j hj; simpa using this)
    exact ⟨t, fun d hd => by simpa using ht d hd⟩
  push_neg at heasy
  obtain ⟨j, hjm, hj4⟩ := heasy
  have hle : ∀ d ∈ D, nu 7 d ≤ m := fun d hd => Finset.le_sup (f := nu 7) hd
  obtain ⟨dt, hdtD, hdt⟩ := Finset.exists_mem_eq_sup D hDne (nu 7)
  -- the three parts
  set Lj := D.filter (fun d => nu 7 d = j) with hLj
  set Lm := D.filter (fun d => nu 7 d = m) with hLm
  set R := D.filter (fun d => ¬ nu 7 d = j ∧ ¬ nu 7 d = m) with hR
  have hLjD : Dlevel 7 D j = Lj := rfl
  rw [hLjD] at hj4
  have c1 : Lj.card + (D.filter (fun d => ¬ nu 7 d = j)).card = D.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have c2 : ((D.filter (fun d => ¬ nu 7 d = j)).filter (fun d => nu 7 d = m)).card +
      ((D.filter (fun d => ¬ nu 7 d = j)).filter (fun d => ¬ nu 7 d = m)).card =
      (D.filter (fun d => ¬ nu 7 d = j)).card := Finset.filter_card_add_filter_neg_card_eq_card _
  have e1 : (D.filter (fun d => ¬ nu 7 d = j)).filter (fun d => nu 7 d = m) = Lm := by
    ext d; simp only [hLm, Finset.mem_filter]; constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  have e2 : (D.filter (fun d => ¬ nu 7 d = j)).filter (fun d => ¬ nu 7 d = m) = R := by
    ext d; simp only [hR, Finset.mem_filter, and_assoc]
  rw [e1, e2] at c2
  have hLm1 : 1 ≤ Lm.card := Finset.card_pos.mpr ⟨dt, Finset.mem_filter.mpr ⟨hdtD, hdt.symm⟩⟩
  have hsum : Lj.card + Lm.card + R.card ≤ 6 := by omega
  have memLj : ∀ d, d ∈ Lj ↔ d ∈ D ∧ nu 7 d = j := fun d => Finset.mem_filter
  have memLm : ∀ d, d ∈ Lm ↔ d ∈ D ∧ nu 7 d = m := fun d => Finset.mem_filter
  have memR : ∀ d, d ∈ R ↔ d ∈ D ∧ ¬ nu 7 d = j ∧ ¬ nu 7 d = m := fun d => Finset.mem_filter
  have split : ∀ d ∈ D, d ∈ Lj ∨ d ∈ Lm ∨ d ∈ R := by
    intro d hd
    by_cases h1 : nu 7 d = j
    · exact Or.inl ((memLj d).mpr ⟨hd, h1⟩)
    by_cases h2 : nu 7 d = m
    · exact Or.inr (Or.inl ((memLm d).mpr ⟨hd, h2⟩))
    · exact Or.inr (Or.inr ((memR d).mpr ⟨hd, h1, h2⟩))
  have ne0 : ∀ d ∈ D, d ≠ 0 := fun d hd => (hposD d hd).ne'
  rcases (show Lj.card = 5 ∨ Lj.card = 4 by omega) with h5 | h4
  · -- case (a)
    have hm1 : Lm.card = 1 := by omega
    have hR0 : R.card = 0 := by omega
    obtain ⟨y, hyL, hyS⟩ := fin_enum Lj 5 h5
    obtain ⟨dm, hdm⟩ := Finset.card_eq_one.mp hm1
    have hdmL : dm ∈ Lm := by rw [hdm]; exact Finset.mem_singleton_self _
    obtain ⟨t, -, hy, hd⟩ := case_a y dm j (fun i => ne0 _ ((memLj _).mp (hyL i)).1)
      (ne0 _ ((memLm _).mp hdmL).1) (fun i => ((memLj _).mp (hyL i)).2)
      (by rw [((memLm _).mp hdmL).2]; exact hjm)
    refine ⟨t, fun d hd' => ?_⟩
    rcases split d hd' with h | h | h
    · obtain ⟨i, rfl⟩ := hyS d h; simpa using hy i
    · rw [hdm, Finset.mem_singleton] at h; subst h; simpa using hd
    · exact absurd (Finset.card_pos.mpr ⟨d, h⟩) (by omega)
  · obtain ⟨y, hyL, hyS⟩ := fin_enum Lj 4 h4
    have hy0 : ∀ i, y i ≠ 0 := fun i => ne0 _ ((memLj _).mp (hyL i)).1
    have hyv : ∀ i, nu 7 (y i) = j := fun i => ((memLj _).mp (hyL i)).2
    rcases (show R.card = 0 ∨ R.card = 1 by omega) with hR0 | hR1
    · -- case (b)
      obtain ⟨t, hy, hT⟩ := case_b j m hjm y hy0 hyv Lm.toList
        (fun d hd => by
          rw [Finset.mem_toList] at hd
          exact ⟨ne0 _ ((memLm _).mp hd).1, ((memLm _).mp hd).2⟩)
      refine ⟨t, fun d hd' => ?_⟩
      rcases split d hd' with h | h | h
      · obtain ⟨i, rfl⟩ := hyS d h; simpa using hy i
      · simpa using hT d (Finset.mem_toList.mpr h)
      · exact absurd (Finset.card_pos.mpr ⟨d, h⟩) (by omega)
    · have hm1 : Lm.card = 1 := by omega
      obtain ⟨dm, hdm⟩ := Finset.card_eq_one.mp hm1
      have hdmL : dm ∈ Lm := by rw [hdm]; exact Finset.mem_singleton_self _
      obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hR1
      have hrR : r ∈ R := by rw [hr]; exact Finset.mem_singleton_self _
      obtain ⟨hrD, hrj, hrm⟩ := (memR r).mp hrR
      have hrle := hle r hrD
      have fin : ∀ t : ℝ, (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * y i)) →
          (1 : ℝ) / 7 ≤ nearestIntDist (t * r) → (1 : ℝ) / 7 ≤ nearestIntDist (t * dm) →
          ∀ d ∈ D, (1 : ℝ) / 7 ≤ nearestIntDist (t * d) := by
        intro t hy hrr hdd d hd'
        rcases split d hd' with h | h | h
        · obtain ⟨i, rfl⟩ := hyS d h; simpa using hy i
        · rw [hdm, Finset.mem_singleton] at h; subst h; simpa using hdd
        · rw [hr, Finset.mem_singleton] at h; subst h; simpa using hrr
      rcases (show j < nu 7 r ∨ nu 7 r < j by omega) with hlt | hlt
      · -- case (c)
        obtain ⟨t, hy, hrr, hdd⟩ := case_c j (nu 7 r) m hlt (by omega) y hy0 hyv r (ne0 r hrD) rfl dm
          (ne0 _ ((memLm _).mp hdmL).1) ((memLm _).mp hdmL).2
        exact ⟨t, fin t hy hrr hdd⟩
      · -- case (d)
        obtain ⟨t, hrr, hy, hdd⟩ := case_d (nu 7 r) j m hlt hjm r (ne0 r hrD) rfl y hy0 hyv dm
          (ne0 _ ((memLm _).mp hdmL).1) ((memLm _).mp hdmL).2
        exact ⟨t, fin t hy hrr hdd⟩

/-- **LRC for six speeds (seven runners)**, Barajas-Serra (2008). -/
theorem lrc6 (u : Fin 6 → ℤ) (hpos : ∀ i, 0 < u i) : (1 / 7 : ℝ) ≤ ML u := by
  set x : Fin 6 → ℕ := fun i => (u i).toNat with hxdef
  have hx0 : ∀ i, 0 < x i := fun i => Int.pos_iff_toNat_pos.mp (hpos i)
  have hxcast : ∀ i, ((x i : ℕ) : ℤ) = u i := fun i => Int.toNat_of_nonneg (hpos i).le
  obtain ⟨t, ht⟩ := lrc6_nat x hx0
  have hle : (1 / 7 : ℝ) ≤ gap u t := by
    apply le_gap
    intro i
    rw [← hxcast i]
    simpa [mul_comm] using ht i
  exact hle.trans (le_csSup (bddAbove_range_gap u) ⟨t, rfl⟩)

end LRSpectrumFull.BarajasSerra.Sec5
