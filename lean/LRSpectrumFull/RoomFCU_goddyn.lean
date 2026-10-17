/-
# ROOM FCU, Goddyn-lens seat

Two self-contained facts used in report_goddyn.

* `gw_not_dvd` (G1): the Goddyn–Wong GCD condition of Integers 6 (2006) A38, Thm 2.3 / Thm 3.1
  (`gcd(r,b) > 1` for every `b ∈ [n-r, m(n-r)-1]`) forces `n ∤ m r`.  Hence no tight family
  produced by Goddyn–Wong accelerations (and, through Zhang 2608.13599 Thm 1.2, no tight
  one-entry modification of `[n-1]`) has a speed divisible by the runner count `n`.
  (Goddyn–Wong prove `n ∤ m_r r` on p. 9 via their Lemma 2.1; the argument here is a shorter
  complete-residue-system argument.)

* `fast_runner_floor` (G2, the special case `L = 1/(k+2)` of Kravitz 1912.06034 Prop 8.1):
  if the family without speed `v l` has ML ≥ 1/(k+2) and `v l ≥ (k+2)·v i` for all other `i`,
  then ML v ≥ 1/(k+3).  `cruxU_fast` packages it in the FloorCruxU indexing: under the crux
  induction hypothesis, every family whose top speed is at least `m` times every other speed
  satisfies the floor.
-/
import Mathlib
import LRSpectrumFull.Delta2Boundary
import LRSpectrumFull.NearestIntLipschitz
import LRSpectrumFull.DValue

namespace LRSpectrumFull.RoomFCUGoddyn

open LRSpectrumFull

/-! ### G1: the Goddyn–Wong GCD condition forbids `n ∣ m r` -/

theorem gw_not_dvd (n r m : ℕ) (hr : 1 ≤ r) (hrn : r < n) (hm : 2 ≤ m)
    (hgcd : ∀ b : ℕ, n - r ≤ b → b + 1 ≤ m * (n - r) → 1 < Nat.gcd r b) :
    ¬ n ∣ m * r := by
  intro hdvd
  obtain ⟨s, hs⟩ : ∃ s, n = r + s := ⟨n - r, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hnr : n - r = s := by omega
  rw [hnr] at hgcd
  have hsum : m * r + m * s = m * n := by rw [hs]; ring
  have hms : n ∣ m * s := by
    have h2 : n ∣ m * r + m * s := by rw [hsum]; exact dvd_mul_left n m
    exact (Nat.dvd_add_right hdvd).mp h2
  have hpos : 0 < m * s := Nat.mul_pos (by omega) hs1
  have hle : n ≤ m * s := Nat.le_of_dvd hpos hms
  have h2s : 2 * s ≤ m * s := Nat.mul_le_mul_right s hm
  generalize m * s = M at hle h2s hgcd
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · -- r = 1: gcd 1 s = 1
    have hr1 : r = 1 := by omega
    have := hgcd s le_rfl (by omega)
    rw [hr1, Nat.gcd_one_left] at this
    omega
  · have hdm := Nat.div_add_mod s r
    have hmod := Nat.mod_lt s (by omega : 0 < r)
    set q := s / r
    set k := s % r
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hg := hgcd (1 + q * r) (by rw [mul_comm] at hdm; omega) (by rw [mul_comm] at hdm; omega)
      rw [Nat.gcd_add_mul_right_right, Nat.gcd_one_right] at hg
      omega
    · have hq : (q + 1) * r = q * r + r := by ring
      have hg := hgcd (1 + (q + 1) * r) (by rw [mul_comm] at hdm; omega)
        (by rw [mul_comm] at hdm; omega)
      rw [Nat.gcd_add_mul_right_right, Nat.gcd_one_right] at hg
      omega

/-! ### G2: fast-runner floor (Kravitz Prop 8.1, `L = 1/(k+2)`) -/

/-- Window lemma: within distance `δ ≤ 1/2` of any real `x` there is a point at distance at
least `δ` from the integers. -/
theorem exists_far_near (x δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    ∃ y, |y - x| ≤ δ ∧ δ ≤ nearestIntDist y := by
  by_cases hx : δ ≤ nearestIntDist x
  · exact ⟨x, by simp [h0], hx⟩
  · push Not at hx
    have hf0 := Int.fract_nonneg x
    have hf1 := Int.fract_lt_one x
    have hfl := Int.floor_add_fract x
    unfold nearestIntDist at hx
    rcases lt_or_ge (Int.fract x) δ with hf | hf
    · refine ⟨(⌊x⌋ : ℝ) + δ, ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith
      · rw [add_comm, nearestIntDist_add_int]
        have hfd : Int.fract δ = δ := Int.fract_eq_self.mpr ⟨h0, by linarith⟩
        unfold nearestIntDist
        rw [hfd]
        exact le_min le_rfl (by linarith)
    · have h2 : 1 - Int.fract x < δ := by
        rcases min_lt_iff.mp hx with h | h
        · linarith
        · exact h
      refine ⟨(⌊x⌋ : ℝ) + (1 - δ), ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith
      · rw [add_comm, nearestIntDist_add_int]
        have hfd : Int.fract (1 - δ) = 1 - δ :=
          Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        unfold nearestIntDist
        rw [hfd]
        exact le_min (by linarith) (by linarith)

theorem fast_runner_floor {k : ℕ} (v : Fin (k + 2) → ℤ) (hv : ∀ i, 0 < v i) (l : Fin (k + 2))
    (hIH : 1 / ((k : ℝ) + 2) ≤ ML (fun j : Fin (k + 1) => v (l.succAbove j)))
    (hfast : ∀ i, i ≠ l → ((k : ℤ) + 2) * v i ≤ v l) :
    1 / ((k : ℝ) + 3) ≤ ML v := by
  set u : Fin (k + 1) → ℤ := fun j => v (l.succAbove j) with hu
  obtain ⟨t0, -, ht0⟩ := exists_gap_eq_ML u
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set δ : ℝ := 1 / ((k : ℝ) + 3) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hvl : (0 : ℝ) < v l := by exact_mod_cast hv l
  obtain ⟨y, hy, hyd⟩ := exists_far_near ((v l : ℝ) * t0) δ hδ0 hδ1
  set t : ℝ := t0 + (y - (v l : ℝ) * t0) / (v l : ℝ) with ht
  have hvlt : (v l : ℝ) * t = y := by
    rw [ht]; field_simp; ring
  refine le_trans ?_ (gap_le_ML v t)
  apply le_gap
  intro i
  by_cases hil : i = l
  · subst hil; rw [hvlt]; exact hyd
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hil
    have h1 : 1 / ((k : ℝ) + 2) ≤ nearestIntDist ((v (l.succAbove j) : ℝ) * t0) := by
      calc 1 / ((k : ℝ) + 2) ≤ ML u := hIH
        _ = gap u t0 := ht0.symm
        _ ≤ nearestIntDist ((u j : ℝ) * t0) := gap_le u t0 j
    have hlip := nearestIntDist_lipschitz ((v (l.succAbove j) : ℝ) * t)
      ((v (l.succAbove j) : ℝ) * t0)
    have hvi : (0 : ℝ) < v (l.succAbove j) := by exact_mod_cast hv _
    have hf : ((k : ℝ) + 2) * (v (l.succAbove j) : ℝ) ≤ v l := by
      have := hfast (l.succAbove j) (Fin.succAbove_ne l j)
      exact_mod_cast this
    have hA0 : 0 ≤ |y - (v l : ℝ) * t0| := abs_nonneg _
    have hdiff : |(v (l.succAbove j) : ℝ) * t - (v (l.succAbove j) : ℝ) * t0|
        ≤ δ / ((k : ℝ) + 2) := by
      have e : (v (l.succAbove j) : ℝ) * t - (v (l.succAbove j) : ℝ) * t0
          = (v (l.succAbove j) : ℝ) * ((y - (v l : ℝ) * t0) / (v l : ℝ)) := by
        rw [ht]; ring
      rw [e, abs_mul, abs_div, abs_of_pos hvi, abs_of_pos hvl, mul_div_assoc',
        div_le_div_iff₀ hvl (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hf) hA0, mul_nonneg hvl.le (sub_nonneg.mpr hy)]
    have hid : 1 / ((k : ℝ) + 2) - δ / ((k : ℝ) + 2) = δ := by
      rw [hδ]; field_simp; ring
    have hl2 := (abs_sub_le_iff.mp hlip).2
    linarith

/-- FloorCruxU indexing: under the crux induction hypothesis, a family whose speed `v l` is at
least `m = k+1` times every other speed satisfies the floor `1/(k+2)`. -/
theorem cruxU_fast (k : ℕ) (hk : 1 ≤ k)
    (ih : ∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (l : Fin (k + 1))
    (hfast : ∀ i, i ≠ l → ((k : ℤ) + 1) * v i ≤ v l) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  have hIH := ih k₀ (by omega) (fun j : Fin (k₀ + 1) => v (l.succAbove j)) (fun j => hv _)
  have h := fast_runner_floor v hv l hIH (fun i hi => by
    have := hfast i hi; push_cast at this ⊢; linarith)
  have e : ((k₀ + 1 : ℕ) : ℝ) + 2 = (k₀ : ℝ) + 3 := by push_cast; ring
  rw [e]; exact h

end LRSpectrumFull.RoomFCUGoddyn
