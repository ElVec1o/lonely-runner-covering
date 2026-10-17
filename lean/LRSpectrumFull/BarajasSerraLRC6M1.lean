/-
# E6 session 15: LRC6 case (a) with m = 1 (paper Section 7, recast)

Six speeds: five `y i` with `7 ∤ y i` and one `d` with `ν_7(d) = 1` (after dividing by the common
power of 7, `lrc6_m1_scaled`). Conclusion: some `t > 0` puts all six at distance `≥ 1/7` from the
integers (the seven-runner LRC bound for this configuration).

Route (differs in bookkeeping from the paper, same mathematics): the paper first searches
multipliers mod 49 and then, for three exceptional classes, mod 98, finally excluding the residual
failures because they are all even. Here all witnesses are `t = a μ / 98` at once:
* if the six speeds are all even, halve them (`lrc6_m1_core`, strong induction on `d`);
* if some `y i0` is odd, multiply by `μ` with `μ y i0 ≡ 1 (mod 98)` (case A);
* if all `y` are even then `d` is odd; multiply by `μ` with `μ y 0 ≡ 2 (mod 98)` (case B);
* the normalized residue problem is the kernel-checked table `BarajasSerraLRC6M1Table`.
Rule 3: (development file, not part of this archive) checked the residue claim over all ordered tuples
before any Lean was written.
-/

import LRSpectrumFull.BarajasSerra
import LRSpectrumFull.BarajasSerraLRC6M1Table
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull.BarajasSerra

open LRSpectrumFull
open LRSpectrumFull.BarajasSerra.LRC6M1Table

/-- The window condition `a x mod 98 ∈ [14, 84]`. -/
def W98 (a x : ℕ) : Prop := 14 ≤ a * x % 98 ∧ a * x % 98 ≤ 84

theorem mem_pairsUp (l : List ℕ) : ∀ a ∈ l, ∀ b ∈ l, ∃ q ∈ pairsUp l, q = a &&& b := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons c rest ih =>
    intro a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · refine ⟨a &&& b, ?_, rfl⟩
      simp only [pairsUp, List.mem_append, List.mem_map, List.mem_cons]
      exact Or.inl ⟨b, hb, rfl⟩
    · rcases hb with rfl | hb
      · refine ⟨b &&& a, ?_, Nat.and_comm _ _⟩
        simp only [pairsUp, List.mem_append, List.mem_map, List.mem_cons]
        exact Or.inl ⟨a, Or.inr ha, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := ih a ha b hb
        refine ⟨_, ?_, rfl⟩
        simp only [pairsUp, List.mem_append]
        exact Or.inr hq

theorem goodM_spec {b x : ℕ} (h : goodM b x = true) {a : ℕ} (ha : b.testBit a = true) :
    W98 a x := by
  unfold goodM at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hlt, hall⟩ := h
  have hb : b < 2 ^ 98 := Nat.blt_eq.mp hlt
  have ha98 : a < 98 := by
    by_contra hc
    have : b < 2 ^ a := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow this] at ha
    exact Bool.false_ne_true ha
  have := hall a (List.mem_range.mpr ha98)
  rw [ha, Bool.not_true, Bool.false_or] at this
  unfold win at this
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at this
  exact this

theorem sem_of_all {P : ℕ → Bool} {n x : ℕ} (h : (List.range n).all P = true)
    (hx : x < n) : P x = true :=
  List.all_eq_true.mp h x (List.mem_range.mpr hx)

theorem memB (x : ℕ) (hx : x < 98) (h7 : x % 7 ≠ 0) : ∃ b ∈ B, goodM b x = true := by
  have := sem_of_all semB hx
  simp only [Bool.or_eq_true, beq_iff_eq, h7, false_or, List.any_eq_true] at this
  exact this

theorem memBe (x : ℕ) (hx : x < 98) (h7 : x % 7 ≠ 0) (h2 : x % 2 = 0) :
    ∃ b ∈ Be, goodM b x = true := by
  have := sem_of_all semBe hx
  simp only [Bool.or_eq_true, beq_iff_eq, h7, h2, false_or, List.any_eq_true,
    Nat.zero_ne_one] at this
  exact this

theorem memF (e : ℕ) (he : e < 14) (h7 : e % 7 ≠ 0) : ∃ b ∈ F, goodM b (7 * e) = true := by
  have := sem_of_all semF he
  simp only [Bool.or_eq_true, beq_iff_eq, h7, false_or, List.any_eq_true] at this
  exact this

theorem memFo (e : ℕ) (he : e < 14) (h7 : e % 7 ≠ 0) (h2 : e % 2 = 1) :
    ∃ b ∈ Fo, goodM b (7 * e) = true := by
  have := sem_of_all semFo he
  simp only [Bool.or_eq_true, beq_iff_eq, h7, h2, false_or, List.any_eq_true,
    show (1 : ℕ) ≠ 0 by decide] at this
  exact this

theorem allA : ∀ q1 ∈ Qu, ∀ f ∈ F, ∀ q2 ∈ Qu, (g1 &&& f &&& q1 &&& q2) ≠ 0 := by
  have hall : (Qu.all fun q1 => F.all fun f => Qu.all fun q2 =>
      (g1 &&& f &&& q1 &&& q2) != 0) = true := by
    conv_lhs => arg 1; rw [Qu_split]
    simp only [List.all_append, chA0, chA1, chA2, chA3, chA4, chA5, chA6, chA7, chA8, chA9,
      chA10, chA11, chA12, chA13, chA14, chA15, Bool.and_self]
  intro q1 hq1 f hf q2 hq2
  have h1 := List.all_eq_true.mp hall q1 hq1
  have h2 := List.all_eq_true.mp h1 f hf
  have h3 := List.all_eq_true.mp h2 q2 hq2
  simpa using h3

theorem allB : ∀ q1 ∈ Que, ∀ f ∈ Fo, ∀ q2 ∈ Que, (g2 &&& f &&& q1 &&& q2) ≠ 0 := by
  intro q1 hq1 f hf q2 hq2
  have h1 := List.all_eq_true.mp chB q1 hq1
  have h2 := List.all_eq_true.mp h1 f hf
  have h3 := List.all_eq_true.mp h2 q2 hq2
  simpa using h3

/-- Extract a common witness bit from a nonzero five-fold AND. -/
theorem bits_of_ne_zero (g f b0 b1 b2 b3 : ℕ) (h : (g &&& f &&& (b0 &&& b1) &&& (b2 &&& b3)) ≠ 0) :
    ∃ a, g.testBit a = true ∧ f.testBit a = true ∧ b0.testBit a = true ∧ b1.testBit a = true ∧
      b2.testBit a = true ∧ b3.testBit a = true := by
  obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero h
  simp only [Nat.testBit_and, Bool.and_eq_true] at ha
  exact ⟨a, ha.1.1.1, ha.1.1.2, ha.1.2.1, ha.1.2.2, ha.2.1, ha.2.2⟩

/-- **Residue core, case A** (one speed normalized to `1`). -/
theorem coreA (x : Fin 4 → ℕ) (hx : ∀ i, x i < 98) (hx7 : ∀ i, x i % 7 ≠ 0) (e : ℕ)
    (he : e < 14) (he7 : e % 7 ≠ 0) :
    ∃ a, W98 a 1 ∧ (∀ i, W98 a (x i)) ∧ W98 a (7 * e) := by
  choose b hbB hb using fun i => memB (x i) (hx i) (hx7 i)
  obtain ⟨f, hfF, hf⟩ := memF e he he7
  obtain ⟨q1, hq1, rfl⟩ := mem_pairsUp B (b 0) (hbB 0) (b 1) (hbB 1)
  obtain ⟨q2, hq2, rfl⟩ := mem_pairsUp B (b 2) (hbB 2) (b 3) (hbB 3)
  rw [← Qu_eq] at hq1 hq2
  obtain ⟨a, h0, hf', h1, h2, h3, h4⟩ :=
    bits_of_ne_zero _ _ _ _ _ _ (allA _ hq1 f hfF _ hq2)
  refine ⟨a, goodM_spec g1good h0, fun i => ?_, goodM_spec hf hf'⟩
  fin_cases i
  · exact goodM_spec (hb 0) h1
  · exact goodM_spec (hb 1) h2
  · exact goodM_spec (hb 2) h3
  · exact goodM_spec (hb 3) h4

/-- **Residue core, case B** (all five `y` even, one normalized to `2`; `d` odd). -/
theorem coreB (x : Fin 4 → ℕ) (hx : ∀ i, x i < 98) (hx7 : ∀ i, x i % 7 ≠ 0)
    (hx2 : ∀ i, x i % 2 = 0) (e : ℕ) (he : e < 14) (he7 : e % 7 ≠ 0) (he2 : e % 2 = 1) :
    ∃ a, W98 a 2 ∧ (∀ i, W98 a (x i)) ∧ W98 a (7 * e) := by
  choose b hbB hb using fun i => memBe (x i) (hx i) (hx7 i) (hx2 i)
  obtain ⟨f, hfF, hf⟩ := memFo e he he7 he2
  obtain ⟨q1, hq1, rfl⟩ := mem_pairsUp Be (b 0) (hbB 0) (b 1) (hbB 1)
  obtain ⟨q2, hq2, rfl⟩ := mem_pairsUp Be (b 2) (hbB 2) (b 3) (hbB 3)
  rw [← Que_eq] at hq1 hq2
  obtain ⟨a, h0, hf', h1, h2, h3, h4⟩ :=
    bits_of_ne_zero _ _ _ _ _ _ (allB _ hq1 f hfF _ hq2)
  refine ⟨a, goodM_spec g2good h0, fun i => ?_, goodM_spec hf hf'⟩
  fin_cases i
  · exact goodM_spec (hb 0) h1
  · exact goodM_spec (hb 1) h2
  · exact goodM_spec (hb 2) h3
  · exact goodM_spec (hb 3) h4

/-- Real bridge: a window hit mod 98 gives distance `≥ 1/7` at `t = c / 98`. -/
theorem bridge98 (a μ y : ℕ) (h : W98 a (μ * y % 98)) :
    (1 / 7 : ℝ) ≤ nearestIntDist (((a * μ : ℕ) : ℝ) / 98 * (y : ℝ)) := by
  have hmod : (a * μ * y) % 98 = a * (μ * y % 98) % 98 := by
    rw [mul_assoc, Nat.mul_mod, Nat.mul_mod a (μ * y % 98), Nat.mod_mod]
  have heq : ((a * μ : ℕ) : ℝ) / 98 * (y : ℝ) = (((a * μ * y : ℕ) : ℤ) : ℝ) / ((98 : ℕ) : ℝ) := by
    push_cast; ring
  rw [heq]
  apply nearestIntDist_ge_of_min _ 98 (by norm_num)
  have hc : (((a * μ * y : ℕ) : ℤ) % ((98 : ℕ) : ℤ) : ℤ) = (((a * μ * y) % 98 : ℕ) : ℤ) := by
    push_cast; rfl
  rw [hc, hmod]
  obtain ⟨h1, h2⟩ := h
  set n := a * (μ * y % 98) % 98
  have h1' : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 84 := by exact_mod_cast h2
  simp only [Int.cast_natCast, Nat.cast_ofNat]
  rw [le_min_iff]; constructor <;> linarith

theorem prime7 : Nat.Prime 7 := Nat.prime_seven

theorem mod7_mul_ne {μ y : ℕ} (hμ : μ % 7 ≠ 0) (hy : y % 7 ≠ 0) : μ * y % 7 ≠ 0 := by
  intro h
  rcases (Nat.Prime.dvd_mul prime7).mp (Nat.dvd_of_mod_eq_zero h) with h' | h'
  · exact hμ (Nat.mod_eq_zero_of_dvd h')
  · exact hy (Nat.mod_eq_zero_of_dvd h')

/-- `μ d mod 98 = 7 e` with `e < 14`, `7 ∤ e`, and `e` odd when `μ` and `d` are. -/
theorem top_residue (μ d : ℕ) (hμ7 : μ % 7 ≠ 0) (hd7 : 7 ∣ d) (hd49 : ¬ 49 ∣ d) :
    ∃ e, e < 14 ∧ e % 7 ≠ 0 ∧ μ * d % 98 = 7 * e ∧ (μ % 2 = 1 → d % 2 = 1 → e % 2 = 1) := by
  obtain ⟨e', rfl⟩ := hd7
  have he'7 : e' % 7 ≠ 0 := by
    intro h; apply hd49
    obtain ⟨c, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    exact ⟨c, by ring⟩
  refine ⟨μ * e' % 14, Nat.mod_lt _ (by norm_num), ?_, ?_, ?_⟩
  · have := mod7_mul_ne hμ7 he'7; omega
  · rw [show μ * (7 * e') = 7 * (μ * e') by ring, show (98 : ℕ) = 7 * 14 by norm_num,
      Nat.mul_mod_mul_left]
  · intro hμ2 hd2
    have he2 : e' % 2 = 1 := by omega
    have : μ * e' % 2 = 1 := by rw [Nat.mul_mod, hμ2, he2]
    omega

/-- **Core, parity-normalized.** Five speeds prime to 7, one of 7-adic valuation exactly 1, not
all six even. -/
theorem lrc6_m1_odd (y : Fin 5 → ℕ) (hy : ∀ i, ¬ 7 ∣ y i) (d : ℕ) (hd7 : 7 ∣ d)
    (hd49 : ¬ 49 ∣ d) (hpar : (∃ i, y i % 2 = 1) ∨ d % 2 = 1) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 7 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 7 : ℝ) ≤ nearestIntDist (t * d) := by
  have hy7 : ∀ i, y i % 7 ≠ 0 := fun i h => hy i (Nat.dvd_of_mod_eq_zero h)
  have htpos : ∀ a μ : ℕ, W98 a 1 ∨ W98 a 2 → μ ≠ 0 → (0 : ℝ) < ((a * μ : ℕ) : ℝ) / 98 := by
    intro a μ ha hμ
    have : a ≠ 0 := by
      rintro rfl; rcases ha with h | h <;> simp [W98] at h
    have : 0 < a * μ := Nat.mul_pos (Nat.pos_of_ne_zero this) (Nat.pos_of_ne_zero hμ)
    positivity
  by_cases hA : ∃ i, y i % 2 = 1
  · obtain ⟨i0, hi0⟩ := hA
    set r := y i0 % 98 with hr
    have hinv := sem_of_all inv1 (Nat.mod_lt (y i0) (by norm_num : 0 < 98))
    have hr2 : r % 2 = 1 := by omega
    have hr7 : r % 7 ≠ 0 := by have := hy7 i0; omega
    rw [← hr] at hinv
    simp only [Bool.or_eq_true, beq_iff_eq, hr2, hr7, Bool.and_eq_true, bne_iff_ne,
      ne_eq, false_or, show (1 : ℕ) ≠ 0 by decide] at hinv
    obtain ⟨⟨hμr, -⟩, hμ7⟩ := hinv
    set μ := invT r 1
    have hμ1 : μ * y i0 % 98 = 1 := by rw [← Nat.mul_mod_mod, ← hr]; exact hμr
    obtain ⟨e, he, he7, hde, -⟩ := top_residue μ d hμ7 hd7 hd49
    obtain ⟨a, ha1, hax, hae⟩ := coreA (fun k => μ * y (i0.succAbove k) % 98)
      (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => by dsimp only; have := mod7_mul_ne hμ7 (hy7 (i0.succAbove k)); omega) e he he7
    have hμ0 : μ ≠ 0 := by rintro h; rw [h] at hμ1; simp at hμ1
    refine ⟨((a * μ : ℕ) : ℝ) / 98, htpos a μ (Or.inl ha1) hμ0, fun i => ?_, ?_⟩
    · rcases Fin.eq_self_or_eq_succAbove i0 i with rfl | ⟨k, rfl⟩
      · exact bridge98 a μ _ (by rw [hμ1]; exact ha1)
      · exact bridge98 a μ _ (hax k)
    · exact bridge98 a μ _ (by rw [hde]; exact hae)
  · push Not at hA
    have hev : ∀ i, y i % 2 = 0 := fun i => by have := hA i; omega
    have hd2 : d % 2 = 1 := by
      rcases hpar with ⟨i, hi⟩ | h
      · exact absurd hi (hA i)
      · exact h
    set r := y 0 % 98 with hr
    have hinv := sem_of_all inv2 (Nat.mod_lt (y 0) (by norm_num : 0 < 98))
    have hr2 : r % 2 = 0 := by have := hev 0; omega
    have hr7 : r % 7 ≠ 0 := by have := hy7 0; omega
    rw [← hr] at hinv
    simp only [Bool.or_eq_true, beq_iff_eq, hr2, hr7, Bool.and_eq_true, bne_iff_ne,
      ne_eq, false_or, show (0 : ℕ) ≠ 1 by decide] at hinv
    obtain ⟨⟨hμr, hμ2⟩, hμ7⟩ := hinv
    set μ := invT r 2
    have hμ1 : μ * y 0 % 98 = 2 := by rw [← Nat.mul_mod_mod, ← hr]; exact hμr
    obtain ⟨e, he, he7, hde, hodd⟩ := top_residue μ d hμ7 hd7 hd49
    have hx2 : ∀ k : Fin 4, μ * y (Fin.succ k) % 98 % 2 = 0 := by
      intro k
      have : μ * y (Fin.succ k) % 2 = 0 := by rw [Nat.mul_mod, hev]; simp
      omega
    obtain ⟨a, ha2, hax, hae⟩ := coreB (fun k => μ * y (Fin.succ k) % 98)
      (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => by dsimp only; have := mod7_mul_ne hμ7 (hy7 (Fin.succ k)); omega) hx2 e he he7
      (hodd hμ2 hd2)
    have hμ0 : μ ≠ 0 := by rintro h; rw [h] at hμ1; simp at hμ1
    refine ⟨((a * μ : ℕ) : ℝ) / 98, htpos a μ (Or.inr ha2) hμ0, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) i
      · exact bridge98 a μ _ (by rw [hμ1]; exact ha2)
      · exact bridge98 a μ _ (hax k)
    · exact bridge98 a μ _ (by rw [hde]; exact hae)

/-- **Core.** Five speeds prime to 7 and one of 7-adic valuation exactly 1 (parity removed by
halving). -/
theorem lrc6_m1_core (y : Fin 5 → ℕ) (hy : ∀ i, ¬ 7 ∣ y i) (d : ℕ) (hd7 : 7 ∣ d)
    (hd49 : ¬ 49 ∣ d) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 7 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 7 : ℝ) ≤ nearestIntDist (t * d) := by
  induction d using Nat.strong_induction_on generalizing y with
  | _ d ih =>
  by_cases hpar : (∃ i, y i % 2 = 1) ∨ d % 2 = 1
  · exact lrc6_m1_odd y hy d hd7 hd49 hpar
  · push Not at hpar
    obtain ⟨hye, hde⟩ := hpar
    have hye' : ∀ i, y i = 2 * (y i / 2) := fun i => by have := hye i; omega
    have hde' : d = 2 * (d / 2) := by omega
    have hd0 : d ≠ 0 := by rintro rfl; exact hd49 (dvd_zero _)
    obtain ⟨t, ht, hb, hbd⟩ := ih (d / 2) (by omega) (fun i => y i / 2)
      (fun i h => hy i (by rw [hye' i]; exact Dvd.dvd.mul_left h 2))
      (by
        have h7 : 7 ∣ 2 * (d / 2) := hde' ▸ hd7
        exact (Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 7 2) h7))
      (fun h => hd49 (by rw [hde']; exact Dvd.dvd.mul_left h 2))
    refine ⟨t / 2, by positivity, fun i => ?_, ?_⟩
    · have : t / 2 * (y i : ℝ) = t * ((y i / 2 : ℕ) : ℝ) := by
        conv_lhs => rw [hye' i]
        push_cast; ring
      rw [this]; exact hb i
    · have : t / 2 * (d : ℝ) = t * ((d / 2 : ℕ) : ℝ) := by
        conv_lhs => rw [hde']
        push_cast; ring
      rw [this]; exact hbd

/-- **LRC6 case (a), m = 1, scaled form.** Five speeds of common 7-adic valuation `g` and one of
valuation `g + 1`: some `t > 0` puts all six at distance `≥ 1/7` from the integers. -/
theorem lrc6_m1_scaled (y : Fin 5 → ℕ) (d g : ℕ) (hy0 : ∀ i, y i ≠ 0) (hd : d ≠ 0)
    (hyv : ∀ i, nu 7 (y i) = g) (hdv : nu 7 d = g + 1) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 7 : ℝ) ≤ nearestIntDist (t * y i)) ∧
      (1 / 7 : ℝ) ≤ nearestIntDist (t * d) := by
  haveI : Fact (Nat.Prime 7) := ⟨prime7⟩
  have hdvy : ∀ i, 7 ^ g ∣ y i := fun i => by rw [← hyv i]; exact pow_padicValNat_dvd
  have hdvd : 7 ^ (g + 1) ∣ d := by rw [← hdv]; exact pow_padicValNat_dvd
  have hndvd : ¬ 7 ^ (g + 2) ∣ d := by
    intro h
    have := pow_succ_padicValNat_not_dvd hd (p := 7)
    unfold nu at hdv; rw [hdv] at this; exact this h
  have hpg : 0 < 7 ^ g := by positivity
  set y' : Fin 5 → ℕ := fun i => y i / 7 ^ g
  set d' := d / 7 ^ g
  have hyeq : ∀ i, y i = 7 ^ g * y' i := fun i => (Nat.mul_div_cancel' (hdvy i)).symm
  have hdeq : d = 7 ^ g * d' := (Nat.mul_div_cancel' (Dvd.dvd.trans
    (pow_dvd_pow 7 (Nat.le_succ g)) hdvd)).symm
  have hy'7 : ∀ i, ¬ 7 ∣ y' i := by
    intro i h
    have h1 : 7 ^ g * 7 ∣ y i := by rw [hyeq i]; exact Nat.mul_dvd_mul_left _ h
    rw [← pow_succ, ← hyv i] at h1
    exact pow_succ_padicValNat_not_dvd (hy0 i) h1
  have hd'7 : 7 ∣ d' := by
    rw [hdeq, pow_succ] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hpg hdvd
  have hd'49 : ¬ 49 ∣ d' := by
    intro h; apply hndvd
    rw [hdeq, show g + 2 = g + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc]
    exact Nat.mul_dvd_mul_left _ (by simpa using h)
  obtain ⟨t, ht, hb, hbd⟩ := lrc6_m1_core y' hy'7 d' hd'7 hd'49
  refine ⟨t / (7 ^ g : ℝ), by positivity, fun i => ?_, ?_⟩
  · have : t / (7 ^ g : ℝ) * (y i : ℝ) = t * (y' i : ℝ) := by
      rw [hyeq i]; push_cast; field_simp
    rw [this]; exact hb i
  · have : t / (7 ^ g : ℝ) * (d : ℝ) = t * (d' : ℝ) := by
      rw [hdeq]; push_cast; field_simp
    rw [this]; exact hbd

end LRSpectrumFull.BarajasSerra
