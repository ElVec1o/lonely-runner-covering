import Mathlib
import LRSpectrumFull.MaxLoneliness

/-!
# ROOM FCU, seat 7 (geometry-of-numbers lens): three elementary dictionary facts

* `halfdist_ge_iff_odd`: `δ ≤ ‖x/2‖ ↔ ∃ u odd, |x - u| ≤ 1 - 2δ` (0 < δ ≤ 1/2).
  Coordinatewise this is the statement that the zero-phase LRC point is the 2-torsion
  class `w = π(1)` of the projected lattice: `ML v = (1 - λ_w)/2` with
  `λ_w = min_{u odd, t} ‖u - t v‖_∞`.
* `gap_le_of_odd_relation`, `ML_le_of_odd_relation`: a relation `c ∈ {-1,0,1}^m`, `c·v = 0`,
  with odd support size `s` forces `ML v ≤ 1/2 - 1/(2s)`.  Uses the zero phase (false for shifts).
* `l1o_iff_relation`: for primitive `v`, leave-one-out primitivity at `l` iff some relation
  `c ∈ L_v` has `c l = 1` (the coordinate functional is onto on the relation lattice; dually,
  the zonotope generator `u_l` is a primitive vector of the projected lattice).
-/

namespace LRSpectrumFull.RoomFCUMss

open LRSpectrumFull

lemma near_half_of_dist {x ε : ℝ} (h : 1 / 2 - ε < nearestIntDist x) :
    ∃ n : ℤ, |x - ((n : ℝ) + 1 / 2)| < ε := by
  refine ⟨⌊x⌋, ?_⟩
  have hf := Int.floor_add_fract x
  unfold nearestIntDist at h
  have ha : 1 / 2 - ε < Int.fract x := lt_of_lt_of_le h (min_le_left _ _)
  have hb : 1 / 2 - ε < 1 - Int.fract x := lt_of_lt_of_le h (min_le_right _ _)
  rw [abs_lt]; constructor <;> linarith

lemma half_le_abs_odd_half (s : ℕ) (hs : Odd s) (M : ℤ) :
    1 / 2 ≤ |(s : ℝ) / 2 + M| := by
  obtain ⟨j, hj⟩ := hs
  have hcast : (s : ℝ) / 2 + M = ((j : ℤ) + M : ℤ) + 1 / 2 := by
    rw [hj]; push_cast; ring
  rw [hcast]
  rcases le_or_gt 0 ((j : ℤ) + M) with h | h
  · have h' : (0 : ℝ) ≤ (((j : ℤ) + M : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h' : (((j : ℤ) + M : ℤ) : ℝ) ≤ -1 := by
      have : (j : ℤ) + M ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith

/-- Odd `{-1,0,1}` relations bound every instantaneous gap. -/
theorem gap_le_of_odd_relation {k : ℕ} (v c : Fin (k + 1) → ℤ)
    (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hrel : ∑ i, c i * v i = 0)
    (hodd : Odd (Finset.univ.filter (fun i => c i ≠ 0)).card) (t : ℝ) :
    gap v t ≤ 1 / 2 - 1 / (2 * ((Finset.univ.filter (fun i => c i ≠ 0)).card : ℝ)) := by
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  set s := S.card with hsdef
  have hspos : (0 : ℝ) < s := by exact_mod_cast hodd.pos
  by_contra hcon
  push Not at hcon
  set ε := 1 / (2 * (s : ℝ)) with hε
  have key : ∀ i ∈ S, ∃ n : ℤ, |(c i : ℝ) * v i * t - ((n : ℝ) + 1 / 2)| < ε := by
    intro i hi
    apply near_half_of_dist
    have h1 : gap v t ≤ nearestIntDist ((v i : ℝ) * t) := gap_le v t i
    have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    have h2 : nearestIntDist ((c i : ℝ) * v i * t) = nearestIntDist ((v i : ℝ) * t) := by
      rcases hc i with h | h | h
      · rw [h]; push_cast
        rw [show (-1 : ℝ) * v i * t = -((v i : ℝ) * t) by ring, nearestIntDist_neg]
      · exact absurd h hci
      · rw [h]; push_cast; ring_nf
    rw [h2]; linarith
  choose! n hn using key
  have hsum0 : ∑ i ∈ S, (c i : ℝ) * v i * t = 0 := by
    have hall : ∑ i, (c i : ℝ) * v i * t = 0 := by
      rw [← Finset.sum_mul]
      have : (∑ i, (c i : ℝ) * v i) = 0 := by exact_mod_cast hrel
      rw [this, zero_mul]
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : c i = 0 := by
      by_contra hne; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [this]
  have hne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hodd.pos)
  have hlt : |∑ i ∈ S, ((c i : ℝ) * v i * t - ((n i : ℝ) + 1 / 2))| < s * ε := by
    calc |∑ i ∈ S, ((c i : ℝ) * v i * t - ((n i : ℝ) + 1 / 2))|
        ≤ ∑ i ∈ S, |(c i : ℝ) * v i * t - ((n i : ℝ) + 1 / 2)| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i ∈ S, ε := Finset.sum_lt_sum_of_nonempty hne hn
      _ = s * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsε : (s : ℝ) * ε = 1 / 2 := by rw [hε]; field_simp
  have hexp : ∑ i ∈ S, ((c i : ℝ) * v i * t - ((n i : ℝ) + 1 / 2))
      = -((s : ℝ) / 2 + ((∑ i ∈ S, n i : ℤ) : ℝ)) := by
    rw [Finset.sum_sub_distrib, hsum0, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [hexp, abs_neg, hsε] at hlt
  have := half_le_abs_odd_half s hodd (∑ i ∈ S, n i)
  linarith

/-- The same bound for the maximum loneliness. -/
theorem ML_le_of_odd_relation {k : ℕ} (v c : Fin (k + 1) → ℤ)
    (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hrel : ∑ i, c i * v i = 0)
    (hodd : Odd (Finset.univ.filter (fun i => c i ≠ 0)).card) :
    ML v ≤ 1 / 2 - 1 / (2 * ((Finset.univ.filter (fun i => c i ≠ 0)).card : ℝ)) := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨t, rfl⟩
  exact gap_le_of_odd_relation v c hc hrel hodd t

/-- Odd-lattice form of one runner at time `x/2`. -/
theorem halfdist_ge_iff_odd (x δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    δ ≤ nearestIntDist (x / 2) ↔ ∃ u : ℤ, Odd u ∧ |x - u| ≤ 1 - 2 * δ := by
  constructor
  · intro h
    refine ⟨2 * ⌊x / 2⌋ + 1, ⟨⌊x / 2⌋, rfl⟩, ?_⟩
    have hf := Int.floor_add_fract (x / 2)
    unfold nearestIntDist at h
    have ha : δ ≤ Int.fract (x / 2) := le_trans h (min_le_left _ _)
    have hb : δ ≤ 1 - Int.fract (x / 2) := le_trans h (min_le_right _ _)
    push_cast
    rw [abs_le]; constructor <;> linarith
  · rintro ⟨u, ⟨j, rfl⟩, hu⟩
    rw [abs_le] at hu
    set e := (x - (2 * j + 1 : ℤ)) / 2 with he
    have hx : x / 2 = (1 / 2 + e) + (j : ℤ) := by rw [he]; push_cast; ring
    rw [hx, nearestIntDist_add_int]
    have he1 : e ≤ 1 / 2 - δ := by rw [he]; push_cast at hu ⊢; linarith [hu.2]
    have he2 : -(1 / 2 - δ) ≤ e := by rw [he]; push_cast at hu ⊢; linarith [hu.1]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)

/-- Leave-one-out primitivity at `l` is surjectivity of the `l`-th coordinate on the
relation lattice. -/
theorem l1o_iff_relation {k : ℕ} (v : Fin (k + 2) → ℤ) (hprim : Finset.univ.gcd v = 1)
    (l : Fin (k + 2)) :
    Finset.univ.gcd (fun j : Fin (k + 1) => v (l.succAbove j)) = 1 ↔
      ∃ c : Fin (k + 2) → ℤ, ∑ i, c i * v i = 0 ∧ c l = 1 := by
  constructor
  · intro h1
    obtain ⟨b, hb⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin (k + 1)))
      (fun j : Fin (k + 1) => v (l.succAbove j))
    rw [h1] at hb
    refine ⟨Fin.insertNth l 1 (fun j => -(v l) * b j), ?_, by simp⟩
    rw [Fin.sum_univ_succAbove _ l]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have : ∑ j : Fin (k + 1), -(v l) * b j * v (l.succAbove j)
        = -(v l) * ∑ j : Fin (k + 1), v (l.succAbove j) * b j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, ← hb]; ring
  · rintro ⟨c, hrel, hcl⟩
    set g := Finset.univ.gcd (fun j : Fin (k + 1) => v (l.succAbove j)) with hg
    have hdj : ∀ j : Fin (k + 1), g ∣ v (l.succAbove j) := fun j =>
      Finset.gcd_dvd (Finset.mem_univ j)
    have hdl : g ∣ v l := by
      rw [Fin.sum_univ_succAbove _ l, hcl, one_mul] at hrel
      have hs : g ∣ ∑ j : Fin (k + 1), c (l.succAbove j) * v (l.succAbove j) :=
        Finset.dvd_sum (fun j _ => Dvd.dvd.mul_left (hdj j) _)
      have : v l = -∑ j : Fin (k + 1), c (l.succAbove j) * v (l.succAbove j) := by linarith
      rw [this]; exact (dvd_neg).mpr hs
    have hall : ∀ i, g ∣ v i := by
      intro i
      rcases Fin.eq_self_or_eq_succAbove l i with h | ⟨j, rfl⟩
      · rw [h]; exact hdl
      · exact hdj j
    have hg1 : g ∣ 1 := by
      rw [← hprim]; exact Finset.dvd_gcd (fun i _ => hall i)
    have hnn : 0 ≤ g := by
      rw [hg]
      exact Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hg1) with h | h
    · exact h
    · omega


/-! ### Half-shift counterexample (m = 6, seven runners)

Speeds `(1,2,3,4,6,9)`, starting phases `(0,1/2,1/2,1/2,1/2,0)`: at every time some runner is
within `7/50 < 1/7` of the origin (the exact supremum is `3/22`, attained at `t = 7/22`,
computed exactly by (development file, not part of this archive)).  The zero-phase family has `ML = 1/5`.
So LRC restricted to phases in `{0,1/2}` is false: the zero phase cannot be used only
through the fact that it is a nonzero 2-torsion class of the projected lattice. -/

lemma piece {a b t w φ c : ℝ} (n : ℤ) (hw : 0 ≤ w) (ha : a ≤ t) (hb : t ≤ b)
    (h1 : |w * a - φ - n| ≤ c) (h2 : |w * b - φ - n| ≤ c) :
    nearestIntDist (w * t - φ) ≤ c := by
  refine le_trans (nearestIntDist_le_dist _ n) ?_
  have hwa : w * a ≤ w * t := mul_le_mul_of_nonneg_left ha hw
  have hwb : w * t ≤ w * b := mul_le_mul_of_nonneg_left hb hw
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Some runner of the half-shifted family is within `7/50` of the origin at time `t`. -/
def HSClose (t : ℝ) : Prop :=
  nearestIntDist (((1 : ℤ) : ℝ) * t - 0) ≤ 7 / 50 ∨
  nearestIntDist (((2 : ℤ) : ℝ) * t - 1 / 2) ≤ 7 / 50 ∨
  nearestIntDist (((3 : ℤ) : ℝ) * t - 1 / 2) ≤ 7 / 50 ∨
  nearestIntDist (((4 : ℤ) : ℝ) * t - 1 / 2) ≤ 7 / 50 ∨
  nearestIntDist (((6 : ℤ) : ℝ) * t - 1 / 2) ≤ 7 / 50 ∨
  nearestIntDist (((9 : ℤ) : ℝ) * t - 0) ≤ 7 / 50

theorem hs_cover (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : HSClose t := by
  unfold HSClose
  by_cases hc0 : t ≤ (7/50 : ℝ)
  · left; exact piece (0 : ℤ) (by norm_num) (show (0 : ℝ) ≤ t by linarith) (show t ≤ (7/50 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc0
  by_cases hc1 : t ≤ (16/75 : ℝ)
  · right; right; left; exact piece (0 : ℤ) (by norm_num) (show (7/50 : ℝ) ≤ t by linarith) (show t ≤ (16/75 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc1
  by_cases hc2 : t ≤ (8/25 : ℝ)
  · right; left; exact piece (0 : ℤ) (by norm_num) (show (16/75 : ℝ) ≤ t by linarith) (show t ≤ (8/25 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc2
  by_cases hc3 : t ≤ (157/450 : ℝ)
  · right; right; right; right; right; exact piece (3 : ℤ) (by norm_num) (show (8/25 : ℝ) ≤ t by linarith) (show t ≤ (157/450 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc3
  by_cases hc4 : t ≤ (41/100 : ℝ)
  · right; right; right; left; exact piece (1 : ℤ) (by norm_num) (show (157/450 : ℝ) ≤ t by linarith) (show t ≤ (41/100 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc4
  by_cases hc5 : t ≤ (11/25 : ℝ)
  · right; right; right; right; left; exact piece (2 : ℤ) (by norm_num) (show (41/100 : ℝ) ≤ t by linarith) (show t ≤ (11/25 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc5
  by_cases hc6 : t ≤ (23/50 : ℝ)
  · right; right; right; right; right; exact piece (4 : ℤ) (by norm_num) (show (11/25 : ℝ) ≤ t by linarith) (show t ≤ (23/50 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc6
  by_cases hc7 : t ≤ (41/75 : ℝ)
  · right; right; left; exact piece (1 : ℤ) (by norm_num) (show (23/50 : ℝ) ≤ t by linarith) (show t ≤ (41/75 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc7
  by_cases hc8 : t ≤ (257/450 : ℝ)
  · right; right; right; right; right; exact piece (5 : ℤ) (by norm_num) (show (41/75 : ℝ) ≤ t by linarith) (show t ≤ (257/450 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc8
  by_cases hc9 : t ≤ (91/150 : ℝ)
  · right; right; right; right; left; exact piece (3 : ℤ) (by norm_num) (show (257/450 : ℝ) ≤ t by linarith) (show t ≤ (91/150 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc9
  by_cases hc10 : t ≤ (33/50 : ℝ)
  · right; right; right; left; exact piece (2 : ℤ) (by norm_num) (show (91/150 : ℝ) ≤ t by linarith) (show t ≤ (33/50 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc10
  by_cases hc11 : t ≤ (307/450 : ℝ)
  · right; right; right; right; right; exact piece (6 : ℤ) (by norm_num) (show (33/50 : ℝ) ≤ t by linarith) (show t ≤ (307/450 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc11
  by_cases hc12 : t ≤ (41/50 : ℝ)
  · right; left; exact piece (1 : ℤ) (by norm_num) (show (307/450 : ℝ) ≤ t by linarith) (show t ≤ (41/50 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc12
  by_cases hc13 : t ≤ (22/25 : ℝ)
  · right; right; left; exact piece (2 : ℤ) (by norm_num) (show (41/50 : ℝ) ≤ t by linarith) (show t ≤ (22/25 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])
  push Not at hc13
  left; exact piece (1 : ℤ) (by norm_num) (show (22/25 : ℝ) ≤ t by linarith) (show t ≤ (57/50 : ℝ) by linarith) (by norm_num [abs_le]) (by norm_num [abs_le])


lemma period_fract (w : ℤ) (φ t : ℝ) :
    nearestIntDist ((w : ℝ) * t - φ) = nearestIntDist ((w : ℝ) * Int.fract t - φ) := by
  have h := Int.floor_add_fract t
  have : (w : ℝ) * t - φ = ((w : ℝ) * Int.fract t - φ) + ((w * ⌊t⌋ : ℤ) : ℝ) := by
    push_cast; linear_combination (-(w : ℝ)) * h
  rw [this, nearestIntDist_add_int]

theorem hs_close_all (t : ℝ) : HSClose t := by
  have h := hs_cover (Int.fract t) (Int.fract_nonneg t) (Int.fract_lt_one t).le
  unfold HSClose at h ⊢
  simp only [period_fract _ _ t]
  exact h

/-- Half-shift LRC fails for seven runners. -/
theorem halfShift_not_lonely :
    ¬ ∃ t : ℝ, 1 / 7 ≤ nearestIntDist (((1 : ℤ) : ℝ) * t - 0) ∧
      1 / 7 ≤ nearestIntDist (((2 : ℤ) : ℝ) * t - 1 / 2) ∧
      1 / 7 ≤ nearestIntDist (((3 : ℤ) : ℝ) * t - 1 / 2) ∧
      1 / 7 ≤ nearestIntDist (((4 : ℤ) : ℝ) * t - 1 / 2) ∧
      1 / 7 ≤ nearestIntDist (((6 : ℤ) : ℝ) * t - 1 / 2) ∧
      1 / 7 ≤ nearestIntDist (((9 : ℤ) : ℝ) * t - 0) := by
  rintro ⟨t, h1, h2, h3, h4, h5, h6⟩
  rcases hs_close_all t with h | h | h | h | h | h <;> linarith

end LRSpectrumFull.RoomFCUMss
