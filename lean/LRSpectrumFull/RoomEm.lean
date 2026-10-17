/-
Room E_m (2026-09-29).  Formalization of a KNOWN result, not a new one:
  Kravitz, "Barely lonely runners and very lonely runners", arXiv 1912.06034, Theorem 5.1:
  ML(1, 2, ..., n-1, n s) = s / (n s + 1); the case n := m, s := m + 1 is `E_m`.
The proof below is not Kravitz's (which uses his Prop. 4.1 on equality times); it is a direct
Dirichlet-approximation argument (Mathlib `Real.exists_int_int_abs_mul_sub_le`).

Convention (as in `RoomT2`, `RoomFCU_erdos`): `v : Fin (n + 1) → ℤ` has `m := n + 1` speeds.
`Em n` = speeds `[1, ..., n, (n+1)(n+2)]`, i.e. `E_m = [1, ..., m-1, m(m+1)]` with `m = n + 1`.

Theorem A (`ML_Em`, `ML_Em_m`): `ML(E_m) = (m+1)/(m^2+m+1)`, `m ≥ 3` (indeed `m ≥ 2` in `ML_Em`).
Theorem B (`thmB_iff`, `thmB_gt`): `(2m+1)(m+1) = 2(m^2+m+1) ↔ m = 1`, and `(2m+1) ML(E_m) > 2`.
-/
import Mathlib
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.RoomEm

open LRSpectrumFull

/-- `E_m` with `m = n + 1`: speeds `1, ..., n` and `(n+1)(n+2)`. -/
def Em (n : ℕ) : Fin (n + 1) → ℤ :=
  fun i => if (i : ℕ) < n then (i : ℤ) + 1 else ((n : ℤ) + 1) * ((n : ℤ) + 2)

/-- Core upper bound.  If every `j t` (`1 ≤ j < m`) and `m(m+1) t` stay `δ` away from `ℤ`, then
`δ ≤ (m+1)/(m^2+m+1)`. -/
theorem key (m : ℕ) (hm : 2 ≤ m) (t δ : ℝ)
    (h1 : ∀ j : ℕ, 1 ≤ j → j < m → δ ≤ nearestIntDist ((j : ℝ) * t))
    (hM : δ ≤ nearestIntDist (((m : ℝ) * ((m : ℝ) + 1)) * t)) :
    δ ≤ ((m : ℝ) + 1) / ((m : ℝ) ^ 2 + m + 1) := by
  by_contra hlt
  push_neg at hlt
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < (m : ℝ) ^ 2 + m + 1 := by positivity
  have hd : 1 / ((m : ℝ) + 1) < δ := by
    refine lt_trans ?_ hlt
    rw [div_lt_div_iff₀ (by positivity) hNpos]; nlinarith
  obtain ⟨j, k, hk0, hkm, hjk⟩ := Real.exists_int_int_abs_mul_sub_le t (n := m) (by omega)
  have hkeq : k = m := by
    by_contra hne
    obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le hk0.le
    have hkn : kn < m := by omega
    have h := h1 kn (by omega) hkn
    have h2 := nearestIntDist_le_dist ((kn : ℝ) * t) j
    have : ((kn : ℤ) : ℝ) = (kn : ℝ) := by push_cast; rfl
    rw [this] at hjk
    linarith
  subst hkeq
  push_cast at hjk
  set w : ℝ := (m : ℝ) * t - j with hw
  clear_value w
  have hWle : |w| ≤ 1 / ((m : ℝ) + 1) := hjk
  have hmt : (m : ℝ) * t = j + w := by rw [hw]; ring
  by_cases hc : IsCoprime j (m : ℤ)
  · obtain ⟨u, v, huv⟩ := hc
    set r : ℤ := u % (m : ℤ) with hr
    have hm0 : (0 : ℤ) < m := by omega
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hrm : r < m := Int.emod_lt_of_pos _ hm0
    have hemod : r + (m : ℤ) * (u / m) = u := Int.emod_add_mul_ediv u m
    set c : ℤ := -v - (u / m) * j with hc'
    have hrc : r * j = 1 + m * c := by
      have : r = u - m * (u / m) := by linarith
      rw [this, hc']; linear_combination huv
    have hr1 : 1 ≤ r := by
      by_contra h0
      have hr0' : r = 0 := by omega
      rw [hr0'] at hrc
      have hd1 : (m : ℤ) ∣ 1 := ⟨-c, by linarith⟩
      have := Int.le_of_dvd one_pos hd1
      omega
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hrmR : (r : ℝ) ≤ m - 1 := by
      have : r ≤ (m : ℤ) - 1 := by omega
      exact_mod_cast this
    have hrcR : (r : ℝ) * j = 1 + m * c := by exact_mod_cast hrc
    have hmpos : (0 : ℝ) < m := by linarith
    have hWm : |w| * ((m : ℝ) + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hWle (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    have hb1 : δ ≤ (1 - |w|) / m := by
      rcases le_total w 0 with hw0 | hw0
      · obtain ⟨rn, hrn⟩ := Int.eq_ofNat_of_zero_le hr0
        have h := h1 rn (by omega) (by omega)
        have h2 := nearestIntDist_le_dist ((rn : ℝ) * t) c
        have hrnR : (rn : ℝ) = r := by rw [hrn]; simp
        rw [hrnR] at h h2
        have e1 : (r : ℝ) * t - c = (1 + r * w) / m := by
          field_simp; nlinarith [hrcR, hmt]
        rw [e1] at h2
        have habs : |w| = -w := abs_of_nonpos hw0
        have hpos : 0 ≤ 1 + (r : ℝ) * w := by nlinarith [abs_nonneg w]
        rw [abs_of_nonneg (div_nonneg hpos hmpos.le)] at h2
        have : (1 + (r : ℝ) * w) / m ≤ (1 - |w|) / m := by
          apply div_le_div_of_nonneg_right _ hmpos.le
          rw [habs]; nlinarith
        linarith
      · have hs0 : 0 ≤ (m : ℤ) - r := by omega
        obtain ⟨sn, hsn⟩ := Int.eq_ofNat_of_zero_le hs0
        have h := h1 sn (by omega) (by omega)
        have h2 := nearestIntDist_le_dist ((sn : ℝ) * t) (j - c)
        have hsnR : (sn : ℝ) = m - r := by
          have : ((sn : ℤ) : ℝ) = ((m : ℤ) - r : ℤ) := by rw [hsn]
          push_cast at this; exact this
        rw [hsnR] at h h2
        have e1 : ((m : ℝ) - r) * t - ((j : ℝ) - c) = (-1 + (m - r) * w) / m := by
          field_simp; nlinarith [hrcR, hmt]
        push_cast at h2
        rw [e1] at h2
        have habs : |w| = w := abs_of_nonneg hw0
        have hneg : (-1 + ((m : ℝ) - r) * w) ≤ 0 := by nlinarith
        rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hneg hmpos.le)] at h2
        have : -((-1 + ((m : ℝ) - r) * w) / m) ≤ (1 - |w|) / m := by
          rw [← neg_div]
          apply div_le_div_of_nonneg_right _ hmpos.le
          rw [habs]; nlinarith
        linarith
    have hb2 : δ ≤ ((m : ℝ) + 1) * |w| := by
      have h2 := nearestIntDist_le_dist (((m : ℝ) * ((m : ℝ) + 1)) * t) (((m : ℤ) + 1) * j)
      have e2 : ((m : ℝ) * ((m : ℝ) + 1)) * t - ((((m : ℤ) + 1) * j : ℤ) : ℝ)
          = ((m : ℝ) + 1) * w := by push_cast; nlinarith [hmt]
      rw [e2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)] at h2
      linarith
    have hb1' : δ * m ≤ 1 - |w| := by rwa [le_div_iff₀ hmpos] at hb1
    have hfin : δ * ((m : ℝ) ^ 2 + m + 1) ≤ (m : ℝ) + 1 := by nlinarith [abs_nonneg w]
    have := (le_div_iff₀ hNpos).mpr hfin
    linarith
  · have hg1 : Int.gcd j m ≠ 1 := fun h => hc (Int.isCoprime_iff_gcd_eq_one.mpr h)
    have hgpos : 0 < Int.gcd j m := Int.gcd_pos_of_ne_zero_right _ (by omega)
    obtain ⟨a', ha'⟩ := Int.gcd_dvd_left (a := j) (b := (m : ℤ))
    obtain ⟨d, hd'⟩ := Int.gcd_dvd_right (a := j) (b := (m : ℤ))
    obtain ⟨g, hg⟩ : ∃ g : ℕ, g = Int.gcd j m := ⟨_, rfl⟩
    rw [← hg] at ha' hd' hg1 hgpos
    have hg2 : 2 ≤ g := by omega
    clear hg hg1 hc
    have hd1 : 1 ≤ d := by
      by_contra h0
      have : d ≤ 0 := by omega
      nlinarith
    have hdm : d < m := by nlinarith
    obtain ⟨dn, hdn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ d)
    have h := h1 dn (by omega) (by omega)
    have h2 := nearestIntDist_le_dist ((dn : ℝ) * t) a'
    have hdnR : (dn : ℝ) = d := by rw [hdn, Int.cast_natCast]
    rw [hdnR] at h h2
    have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have hjR : (j : ℝ) = g * a' := by
      have := congrArg (Int.cast : ℤ → ℝ) ha'
      push_cast at this; exact this
    have hmR' : (m : ℝ) = g * d := by
      have := congrArg (Int.cast : ℤ → ℝ) hd'
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast] at this; exact this
    have e1 : (g : ℝ) * ((d : ℝ) * t - a') = w := by
      linear_combination (-1 : ℝ) * hw - t * hmR' + hjR
    have : |(d : ℝ) * t - a'| ≤ |w| := by
      have h3 : |(g : ℝ)| * |(d : ℝ) * t - a'| = |w| := by rw [← abs_mul, e1]
      rw [abs_of_pos (by linarith : (0 : ℝ) < g)] at h3
      rw [← h3]
      exact le_mul_of_one_le_left (abs_nonneg _) (by linarith)
    exact absurd (lt_of_lt_of_le hd (h.trans (h2.trans (this.trans hWle)))) (lt_irrefl _)

theorem gap_le_key (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    gap (Em n) t ≤ (((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) + 1) := by
  apply key (n + 1) (by omega) t
  · intro j hj1 hjn
    refine le_trans (gap_le (Em n) t ⟨j - 1, by omega⟩) ?_
    have : Em n ⟨j - 1, by omega⟩ = (j : ℤ) := by
      simp only [Em]; rw [if_pos (show j - 1 < n by omega)]
      show (((j - 1 : ℕ) : ℤ)) + 1 = (j : ℤ)
      omega
    rw [this]; simp
  · refine le_trans (gap_le (Em n) t (Fin.last n)) ?_
    have : Em n (Fin.last n) = ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
      simp [Em]
    rw [this]; push_cast; apply le_of_eq; ring_nf

/-- Time attaining the value: `t0 = (m+1)/(m^2+m+1)`. -/
theorem le_gap_Em (n : ℕ) (hn : 2 ≤ n) :
    (((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) + 1)
      ≤ gap (Em n) ((((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) + 1)) := by
  set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
  have hm3 : (3 : ℝ) ≤ m := by rw [hm]; push_cast; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  have hN : (0 : ℝ) < m ^ 2 + m + 1 := by positivity
  set t : ℝ := (m + 1) / (m ^ 2 + m + 1) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hmt : (m - 1) * t ≤ 1 - t := by
    rw [ht, ← sub_nonneg]
    have : 1 - (m + 1) / (m ^ 2 + m + 1) - (m - 1) * ((m + 1) / (m ^ 2 + m + 1))
        = 1 / (m ^ 2 + m + 1) := by field_simp; ring
    rw [this]; positivity
  apply le_gap
  intro i
  simp only [Em]
  split_ifs with hi
  · have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _; linarith
    have hi2 : ((i : ℕ) : ℝ) + 1 ≤ m - 1 := by
      have : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hi
      have h2 : m - 1 = n := by rw [hm]; push_cast; ring
      linarith
    have hx : (((i : ℤ) + 1 : ℤ) : ℝ) * t = (((i : ℕ) : ℝ) + 1) * t := by push_cast; ring
    rw [hx]
    apply nearestIntDist_ge (by positivity)
    · nlinarith
    · nlinarith
    · nlinarith
  · have e : ((((n : ℤ) + 1) * ((n : ℤ) + 2) : ℤ) : ℝ) = m * (m + 1) := by
      rw [hm]; push_cast; ring
    rw [e]
    have hm1 : m + 1 = (n : ℝ) + 2 := by rw [hm]; push_cast; ring
    have hx : m * (m + 1) * t = -t + (((n : ℤ) + 2 : ℤ) : ℝ) := by
      push_cast; rw [← hm1, ht]; field_simp; ring
    rw [hx, nearestIntDist_add_int, nearestIntDist_neg]
    apply nearestIntDist_ge ht0.le
    · rw [ht, div_lt_one hN]; nlinarith
    · exact le_refl _
    · have : 2 * t ≤ 1 := by
        rw [ht, ← mul_div_assoc, div_le_one hN]; nlinarith
      linarith

/-- **Theorem A** (Kravitz 2019, Thm 5.1 with `n := m`, `s := m + 1`; known result).
`ML(E_m) = (m+1)/(m^2+m+1)` with `m = n + 1 ≥ 3`. -/
theorem ML_Em (n : ℕ) (hn : 2 ≤ n) :
    ML (Em n) = (((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) + 1) := by
  apply le_antisymm
  · unfold ML
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨t, rfl⟩
    exact gap_le_key n hn t
  · exact (le_gap_Em n hn).trans (le_csSup (bddAbove_range_gap _) ⟨_, rfl⟩)

/-- Theorem A in the `m`-indexing: `E_m` has `m` speeds, stored as `Fin ((m-1)+1)`. -/
theorem ML_Em_m (m : ℕ) (hm : 3 ≤ m) :
    ML (Em (m - 1)) = ((m : ℝ) + 1) / ((m : ℝ) ^ 2 + m + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have := ML_Em n (by omega)
  simpa using this

/-- **Theorem B, algebra**: `(2m+1)(m+1) = 2(m^2+m+1) ↔ m = 1`. -/
theorem thmB_iff (m : ℝ) :
    (2 * m + 1) * (m + 1) = 2 * (m ^ 2 + m + 1) ↔ m = 1 := by
  constructor <;> intro h <;> nlinarith

/-- **Theorem B**: for `m ≥ 3`, `(2m+1) ML(E_m) > 2`, so `E_m` is never an equality case of
`ML ≥ 2/(2m+1)`. -/
theorem thmB_gt (m : ℕ) (hm : 3 ≤ m) : 2 < (2 * (m : ℝ) + 1) * ML (Em (m - 1)) := by
  rw [ML_Em_m m hm]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (0 : ℝ) < (m : ℝ) ^ 2 + m + 1 := by positivity
  rw [← mul_div_assoc, lt_div_iff₀ hN]
  nlinarith

#print axioms ML_Em
#print axioms ML_Em_m
#print axioms thmB_iff
#print axioms thmB_gt

end LRSpectrumFull.RoomEm
