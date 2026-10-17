import Mathlib
import LRSpectrumFull.RoomA4_compress

/-!
# ROOM A4: the smooth-certificate barrier

`floor_of_integral_unionBound` (RoomA4_compress) derives `δ ≤ ML v` from
`Σᵢ ∫_{[0,1] ∩ Bᵢ} F < ∫_{[0,1]} F` for a nonnegative weight `F`.  This file shows that no
weight absolutely continuous with respect to Lebesgue measure can certify a tight family:

* (B1) if `ML v ≤ δ` and every speed is nonzero, the good set
  `G = {t | ∀ i, δ ≤ ‖vᵢ t‖}` is countable, hence Lebesgue-null;
* (B2) consequently, for every `F ≥ 0` integrable on `[0,1]`,
  `∫_{[0,1]} F ≤ Σᵢ ∫_{[0,1] ∩ Bᵢ} F`; equivalently the integral certificate, when it fires,
  gives the strict bound `δ < ML v`;
* (B3) no `U_D` fires on a family with `ML v ≤ 1/(k+2)`; in particular on any tight family;
* (B4) the consecutive family `(1, …, k+1)` satisfies `ML ≤ 1/(k+2)`, so (B3) is not vacuous.
-/

namespace LRSpectrumFull.RoomA4Barrier

open LRSpectrumFull LRSpectrumFull.RoomA4Compress MeasureTheory Real

variable {k : ℕ}

/-- The good set at level `δ`: times where every runner is at distance at least `δ`. -/
def goodSet (v : Fin (k + 1) → ℤ) (δ : ℝ) : Set ℝ :=
  {t | ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * t)}

/-- A level set of `‖·‖` lies in `(ℤ + δ) ∪ (ℤ - δ)`. -/
theorem nearestIntDist_eq_mem (x δ : ℝ) (h : nearestIntDist x = δ) :
    ∃ n : ℤ, x = n + δ ∨ x = n - δ := by
  unfold nearestIntDist at h
  rcases min_choice (Int.fract x) (1 - Int.fract x) with hm | hm
  · refine ⟨⌊x⌋, Or.inl ?_⟩
    rw [hm] at h
    have := Int.floor_add_fract x
    linarith
  · refine ⟨⌊x⌋ + 1, Or.inr ?_⟩
    rw [hm] at h
    have := Int.floor_add_fract x
    push_cast
    linarith

/-- For `a ≠ 0` the level set `{t | ‖a t‖ = δ}` is countable. -/
theorem countable_levelSet (a δ : ℝ) (ha : a ≠ 0) :
    {t : ℝ | nearestIntDist (a * t) = δ}.Countable := by
  have hsub : {t : ℝ | nearestIntDist (a * t) = δ} ⊆
      Set.range (fun n : ℤ => ((n : ℝ) + δ) / a) ∪ Set.range (fun n : ℤ => ((n : ℝ) - δ) / a) := by
    intro t ht
    obtain ⟨n, hn | hn⟩ := nearestIntDist_eq_mem (a * t) δ ht
    · left; exact ⟨n, by simp only; rw [← hn]; field_simp⟩
    · right; exact ⟨n, by simp only; rw [← hn]; field_simp⟩
  exact ((Set.countable_range _).union (Set.countable_range _)).mono hsub

/-- **(B1)** If `ML v ≤ δ` and all speeds are nonzero, the good set is countable. -/
theorem goodSet_countable (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0) (δ : ℝ)
    (hML : ML v ≤ δ) : (goodSet v δ).Countable := by
  have hsub : goodSet v δ ⊆ ⋃ i, {t : ℝ | nearestIntDist ((v i : ℝ) * t) = δ} := by
    intro t ht
    simp only [goodSet, Set.mem_setOf_eq] at ht
    by_contra hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hn
    have hlt : ∀ i, δ < nearestIntDist ((v i : ℝ) * t) := fun i => lt_of_le_of_ne (ht i) (Ne.symm (hn i))
    have hgap : δ < gap v t := by
      simp only [gap, Finset.lt_inf'_iff]
      exact fun i _ => hlt i
    have := gap_le_ML v t
    linarith
  refine (Set.countable_iUnion fun i => countable_levelSet _ δ ?_).mono hsub
  exact_mod_cast hv i

/-- **(B1)** If `ML v ≤ δ` and all speeds are nonzero, the good set is Lebesgue-null. -/
theorem goodSet_null (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0) (δ : ℝ)
    (hML : ML v ≤ δ) : volume (goodSet v δ) = 0 := by
  exact (goodSet_countable v hv δ hML).measure_zero volume

/-- **(B2) Barrier.**  If `ML v ≤ δ` and all speeds are nonzero, then for every `F ≥ 0`
integrable on `[0,1]` the union bound is at least the total mass. -/
theorem integral_le_sum_badSet (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0) (δ : ℝ)
    (hML : ML v ≤ δ) (F : ℝ → ℝ) (hF : IntegrableOn F (Set.Icc (0 : ℝ) 1))
    (hF0 : ∀ t, 0 ≤ F t) :
    ∫ t in Set.Icc (0 : ℝ) 1, F t ≤ ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v δ i, F t := by
  have hind : ∀ i, Integrable ((badSet v δ i).indicator F) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun i => hF.integrable.indicator (measurableSet_badSet v δ i)
  have hsumint : Integrable (fun t => ∑ i, (badSet v δ i).indicator F t)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have := integrable_finsetSum (Finset.univ) (fun i _ => hind i)
    simpa [Finset.sum_apply] using this
  have hae : ∀ᵐ t ∂volume, t ∉ goodSet v δ :=
    measure_eq_zero_iff_ae_notMem.mp (goodSet_null v hv δ hML)
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      F t ≤ ∑ i, (badSet v δ i).indicator F t := by
    refine ae_restrict_of_ae (hae.mono fun t ht => ?_)
    simp only [goodSet, Set.mem_setOf_eq, not_forall, not_le] at ht
    obtain ⟨i0, hi0⟩ := ht
    have hmem : t ∈ badSet v δ i0 := hi0
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (badSet v δ i).indicator F t :=
      fun i _ => Set.indicator_nonneg (fun s _ => hF0 s) t
    calc F t = (badSet v δ i0).indicator F t := (Set.indicator_of_mem hmem F).symm
      _ ≤ ∑ i, (badSet v δ i).indicator F t :=
        Finset.single_le_sum (f := fun i => (badSet v δ i).indicator F t) hnn
          (Finset.mem_univ i0)
  have hmono := integral_mono_ae hF hsumint hpt
  have hsplit : ∫ t in Set.Icc (0 : ℝ) 1, ∑ i, (badSet v δ i).indicator F t
      = ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v δ i, F t := by
    rw [integral_finsetSum Finset.univ (fun i _ => hind i)]
    exact Finset.sum_congr rfl (fun i _ => setIntegral_indicator (measurableSet_badSet v δ i))
  rw [hsplit] at hmono
  exact hmono

/-- **(B2), strict form.**  An integral certificate that fires gives `δ < ML v`, never
`δ = ML v`. -/
theorem lt_ML_of_integral_unionBound (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0) (δ : ℝ)
    (F : ℝ → ℝ) (hF : IntegrableOn F (Set.Icc (0 : ℝ) 1)) (hF0 : ∀ t, 0 ≤ F t)
    (h : ∑ i, ∫ t in Set.Icc (0 : ℝ) 1 ∩ badSet v δ i, F t < ∫ t in Set.Icc (0 : ℝ) 1, F t) :
    δ < ML v := by
  by_contra hle
  exact absurd h (not_lt.mpr (integral_le_sum_badSet v hv δ (not_lt.mp hle) F hF hF0))

/-- **(B3)** `U_D` fires only strictly above the floor. -/
theorem lt_ML_of_UDFires (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0) (D : ℕ)
    (h : UDFires v D) : 1 / ((k : ℝ) + 2) < ML v := by
  exact lt_ML_of_integral_unionBound v hv _ (rieszWeight v D)
    (continuous_rieszWeight v D).integrableOn_Icc (rieszWeight_nonneg v D) h

/-- **(B3)** No `U_D` fires when `ML v ≤ 1/(k+2)`. -/
theorem not_UDFires_of_ML_le (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0)
    (hML : ML v ≤ 1 / ((k : ℝ) + 2)) : ∀ D : ℕ, ¬ UDFires v D := by
  intro D hD
  exact absurd hML (not_le.mpr (lt_ML_of_UDFires v hv D hD))

/-- **(B3)** Every tight family (`ML v = 1/(k+2)`) with nonzero speeds satisfies the
U-hypothesis of `FloorCruxU`. -/
theorem not_UDFires_of_tight (v : Fin (k + 1) → ℤ) (hv : ∀ i, v i ≠ 0)
    (htight : ML v = 1 / ((k : ℝ) + 2)) : ∀ D : ℕ, ¬ UDFires v D := by
  exact not_UDFires_of_ML_le v hv htight.le

/-! ### (B4) Non-vacuity: the barrier applies to the consecutive family

`nid_le_abs_sub_intCast` is copied from `Delta2GlobalPartition`, and `exists_small_multiple`,
`consec`, `gap_consec_le` from `Delta2HandlerStrike` (their import closures are not built).
The copies live in `LRSpectrumFull.RoomA4Barrier`, so they do not clash with the originals.
Only the upper bound `ML (consec n) ≤ 1/(n+2)` is needed here. -/

/-- The nearest-integer distance is bounded by the distance to any integer. -/
theorem nid_le_abs_sub_intCast (x : ℝ) (n : ℤ) :
    nearestIntDist x ≤ |x - (n : ℝ)| := by
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  have hdec : x - (n : ℝ) = Int.fract x + ((⌊x⌋ - n : ℤ) : ℝ) := by
    have h := Int.self_sub_floor x
    push_cast
    linarith
  rw [hdec]
  unfold nearestIntDist
  rcases lt_trichotomy (⌊x⌋ - n) 0 with hc | hc | hc
  · have hcR : ((⌊x⌋ - n : ℤ) : ℝ) ≤ -1 := by
      exact_mod_cast (by omega : ⌊x⌋ - n ≤ -1)
    have hneg : Int.fract x + ((⌊x⌋ - n : ℤ) : ℝ) < 0 := by linarith
    rw [abs_of_neg hneg]
    calc min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
    _ ≤ -(Int.fract x + ((⌊x⌋ - n : ℤ) : ℝ)) := by linarith
  · have hcR : ((⌊x⌋ - n : ℤ) : ℝ) = 0 := by exact_mod_cast hc
    rw [hcR, add_zero, abs_of_nonneg hf0]
    exact min_le_left _ _
  · have hcR : (1 : ℝ) ≤ ((⌊x⌋ - n : ℤ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ ⌊x⌋ - n)
    have hpos : 0 ≤ Int.fract x + ((⌊x⌋ - n : ℤ) : ℝ) := by linarith
    rw [abs_of_nonneg hpos]
    calc min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
    _ ≤ Int.fract x + ((⌊x⌋ - n : ℤ) : ℝ) := by linarith

/-- **Dirichlet's approximation (pigeonhole form):** for every `t` some multiple
`j ≤ n` satisfies `‖j t‖ ≤ 1/(n+1)`. -/
theorem exists_small_multiple (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ nearestIntDist ((j : ℝ) * t) ≤ 1 / ((n : ℝ) + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases hedge : ∃ k ∈ Finset.Icc 1 n, (⌊((n : ℝ) + 1) * Int.fract ((k : ℝ) * t)⌋ = 0 ∨
      ⌊((n : ℝ) + 1) * Int.fract ((k : ℝ) * t)⌋ = n)
  · obtain ⟨k, hk, hcase⟩ := hedge
    rw [Finset.mem_Icc] at hk
    refine ⟨k, hk.1, hk.2, ?_⟩
    set f := Int.fract ((k : ℝ) * t) with hf
    have hf0 : 0 ≤ f := Int.fract_nonneg _
    have hf1 : f < 1 := Int.fract_lt_one _
    have hnid : nearestIntDist ((k : ℝ) * t) = min f (1 - f) := by
      rw [show (k : ℝ) * t = f + (⌊(k : ℝ) * t⌋ : ℤ) from by
        have h := Int.self_sub_floor ((k : ℝ) * t)
        linarith, nearestIntDist_add_int]
      unfold nearestIntDist
      rw [Int.fract_eq_self.mpr ⟨hf0, hf1⟩]
    rcases hcase with h0 | hn'
    · have hlt : ((n : ℝ) + 1) * f < 1 := by
        have h := Int.lt_floor_add_one (((n : ℝ) + 1) * f)
        rw [h0] at h
        push_cast at h
        linarith
      rw [hnid]
      calc min f (1 - f) ≤ f := min_le_left _ _
      _ ≤ 1 / ((n : ℝ) + 1) := by
          rw [le_div_iff₀ hn1]
          nlinarith
    · have hge : (n : ℝ) ≤ ((n : ℝ) + 1) * f := by
        have h := Int.floor_le (((n : ℝ) + 1) * f)
        rw [hn'] at h
        push_cast at h
        linarith
      rw [hnid]
      calc min f (1 - f) ≤ 1 - f := min_le_right _ _
      _ ≤ 1 / ((n : ℝ) + 1) := by
          rw [le_div_iff₀ hn1]
          nlinarith
  · push Not at hedge
    have key : ∀ a b : ℕ, a ∈ Finset.Icc 1 n → b ∈ Finset.Icc 1 n → a < b →
        ⌊((n : ℝ) + 1) * Int.fract ((a : ℝ) * t)⌋
          = ⌊((n : ℝ) + 1) * Int.fract ((b : ℝ) * t)⌋ →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ nearestIntDist ((j : ℝ) * t) ≤ 1 / ((n : ℝ) + 1) := by
      intro a b ha hb hab hbox
      rw [Finset.mem_Icc] at ha hb
      refine ⟨b - a, by omega, by omega, ?_⟩
      set fa := Int.fract ((a : ℝ) * t) with hfa
      set fb := Int.fract ((b : ℝ) * t) with hfb
      have hdiff : |fb - fa| < 1 / ((n : ℝ) + 1) := by
        have h1 := Int.floor_le (((n : ℝ) + 1) * fa)
        have h2 := Int.lt_floor_add_one (((n : ℝ) + 1) * fa)
        have h3 := Int.floor_le (((n : ℝ) + 1) * fb)
        have h4 := Int.lt_floor_add_one (((n : ℝ) + 1) * fb)
        rw [hbox] at h1 h2
        have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [abs_lt]
        constructor
        · rw [neg_lt, lt_div_iff₀ hnpos]
          nlinarith
        · rw [lt_div_iff₀ hnpos]
          nlinarith
      have harg : ((b - a : ℕ) : ℝ) * t
          = (fb - fa) + ((⌊(b : ℝ) * t⌋ - ⌊(a : ℝ) * t⌋ : ℤ) : ℝ) := by
        have hsa := Int.self_sub_floor ((a : ℝ) * t)
        have hsb := Int.self_sub_floor ((b : ℝ) * t)
        rw [hfa, hfb, ← hsa, ← hsb]
        push_cast [Nat.cast_sub (le_of_lt hab)]
        ring
      rw [harg, nearestIntDist_add_int]
      calc nearestIntDist (fb - fa) ≤ |fb - fa - ((0 : ℤ) : ℝ)| := nid_le_abs_sub_intCast _ 0
      _ = |fb - fa| := by norm_num
      _ ≤ 1 / ((n : ℝ) + 1) := le_of_lt hdiff
    have hmaps : ∀ k ∈ Finset.Icc 1 n, (⌊((n : ℝ) + 1) * Int.fract ((k : ℝ) * t)⌋) ∈
        Finset.Icc (1 : ℤ) ((n : ℤ) - 1) := by
      intro k hk
      have h := hedge k hk
      have hf0 : 0 ≤ Int.fract ((k : ℝ) * t) := Int.fract_nonneg _
      have hf1 : Int.fract ((k : ℝ) * t) < 1 := Int.fract_lt_one _
      have hlb : 0 ≤ ⌊((n : ℝ) + 1) * Int.fract ((k : ℝ) * t)⌋ :=
        Int.floor_nonneg.mpr (by positivity)
      have hub : ⌊((n : ℝ) + 1) * Int.fract ((k : ℝ) * t)⌋ < (n : ℤ) + 1 := by
        rw [Int.floor_lt]
        push_cast
        nlinarith
      rw [Finset.mem_Icc]
      omega
    have hcard : (Finset.Icc (1 : ℤ) ((n : ℤ) - 1)).card < (Finset.Icc 1 n).card := by
      rw [Nat.card_Icc, Int.card_Icc]
      omega
    obtain ⟨a, ha, b, hb, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    rcases lt_or_gt_of_ne hne with hab | hab
    · exact key a b ha hb hab heq
    · exact key b a hb ha hab heq.symm

/-- The consecutive family `1, 2, …, n+1`. -/
def consec (n : ℕ) : Fin (n + 1) → ℤ := fun i => ((i : ℕ) : ℤ) + 1

/-- The Dirichlet cover: the consecutive family never exceeds `1/(n+2)`. -/
theorem gap_consec_le (n : ℕ) (t : ℝ) : gap (consec n) t ≤ 1 / ((n : ℝ) + 2) := by
  obtain ⟨j, hj1, hjn, hnid⟩ := exists_small_multiple (n + 1) (by omega) t
  have hidx : j - 1 < n + 1 := by omega
  refine le_trans (gap_le _ t ⟨j - 1, hidx⟩) ?_
  have hval : ((consec n ⟨j - 1, hidx⟩ : ℤ) : ℝ) = (j : ℝ) := by
    simp only [consec]
    push_cast [Nat.cast_sub hj1]
    ring
  rw [hval]
  calc nearestIntDist ((j : ℝ) * t) ≤ 1 / (((n : ℕ) + 1 : ℕ) + 1 : ℝ) := hnid
  _ = 1 / ((n : ℝ) + 2) := by push_cast; ring_nf

/-- `ML (1, 2, …, n+1) ≤ 1/(n+2)` (Dirichlet). -/
theorem ML_consec_le (n : ℕ) : ML (consec n) ≤ 1 / ((n : ℝ) + 2) :=
  csSup_le (Set.range_nonempty _) (by rintro y ⟨t, rfl⟩; exact gap_consec_le n t)

/-- **(B4)** The barrier applies to the consecutive family in every dimension: no `U_D` fires
on `(1, 2, …, k+1)`. -/
theorem not_UDFires_consec (k : ℕ) : ∀ D : ℕ, ¬ UDFires (consec k) D :=
  not_UDFires_of_ML_le (consec k) (fun i => by simp only [consec]; omega) (ML_consec_le k)

end LRSpectrumFull.RoomA4Barrier
