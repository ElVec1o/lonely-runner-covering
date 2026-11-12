/-
# R7-partial, module K: general-modulus tools (window of bad integers, coincidence, counting)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Theorem R7-partial" (proof sketch), generalised
from modulus 5 (`RFiveBase`, `TPFour*`) to a general modulus `q`.  Nothing here is specific to `q = 7`.

Time is `t = (j + x) / q`.  For a runner `i` of the same class as a base runner `a` (`v_a - ε v_i = q D`) the bad
integers in the coordinate `z = v_a j` lie in the open interval of radius `q/5` around the centre
`u_i = -ε (v_i x + q φ_i) - q n_i`, and `u_i - u_a = q (D x + (φ_a - ε φ_i) - n_i)` (lifted real difference).

* `not_good_of_near`  : converse of `near_to_int`.
* `centre_diff`       : the centre difference formula.
* `good_of_win`       : if no integer within `q/5` of `u_i` is congruent to `N`, then `j = N A` is good for runner `i`.
* `win_ne_dvd`, `window_gap3` : three centres pairwise within `3q/5 - 1`: one window `(N, N + q)`.
* `bad_transfer`, `exact_pair` : two same-class runners with exactly coinciding centres have the same bad `j`;
  with a third runner the counting bound `2 (⌊(2q-1)/5⌋ + 1) < q` leaves a common good `j`.
-/
import LRSpectrumFull.RQG24
import LRSpectrumFull.RQPigeon

namespace LRSpectrumFull

lemma not_good_of_near (q : ℕ) (hq : 0 < q) (v : ℕ) (φ x : ℝ) (j n : ℤ)
    (h : |((((v : ℤ) * j - q * n : ℤ)) : ℝ) - (-((v : ℝ) * x + q * φ))| < (q : ℝ) / 5) :
    ¬ GoodR v φ (((j : ℝ) + x) / q) := by
  intro hg
  unfold GoodR at hg
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : (q : ℝ) * (((j : ℝ) + x) / q) = j + x := mul_div_cancel₀ _ hq0
  have e : ((((v : ℤ) * j - q * n : ℤ)) : ℝ) - (-((v : ℝ) * x + q * φ))
      = q * ((v : ℝ) * (((j : ℝ) + x) / q) + φ - n) := by
    push_cast
    linear_combination (-(v : ℝ)) * ht
  rw [e, abs_mul, abs_of_pos hqp] at h
  have h' : (q : ℝ) * |(v : ℝ) * (((j : ℝ) + x) / q) + φ - n| < (q : ℝ) * (1 / 5) := by linarith
  have h2 := lt_of_mul_lt_mul_left h' hqp.le
  have h3 := round_le ((v : ℝ) * (((j : ℝ) + x) / q) + φ) n
  unfold tpDist at hg
  linarith

lemma centre_diff (q : ℕ) (va vi : ℕ) (φa φi x : ℝ) (ε D : ℤ) (hD : (va : ℤ) - ε * vi = q * D)
    (ni : ℤ) :
    (-((ε : ℝ) * ((vi : ℝ) * x + q * φi)) - q * (ni : ℝ)) - (-((va : ℝ) * x + q * φa))
      = q * ((D : ℝ) * x + (φa - ε * φi) - ni) := by
  have hDR : (va : ℝ) - ε * vi = q * D := by exact_mod_cast hD
  linear_combination x * hDR

/-- Runner `i` of the class of the base runner `a` (`v_a - ε v_i = q D`, `A v_a + B q = 1`): if no integer within `q/5`
of its centre `u` is congruent to `N` modulo `q`, then `j = N A` is good for `i`. -/
lemma good_of_win (q : ℕ) (hq : 0 < q) (va vi : ℕ) (A B : ℤ) (hAB : A * (va : ℤ) + B * q = 1)
    (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vi = q * D) (φi x : ℝ) (ni N : ℤ)
    (u : ℝ) (hu : u = -((ε : ℝ) * ((vi : ℝ) * x + q * φi)) - q * (ni : ℝ))
    (hN : ∀ m : ℤ, |(m : ℝ) - u| < (q : ℝ) / 5 → ¬ (q : ℤ) ∣ m - N) :
    GoodR vi φi ((((N * A : ℤ) : ℝ) + x) / q) := by
  by_contra hbad
  unfold GoodR at hbad
  obtain ⟨n2, hn2⟩ := exists_near_of_not_good hbad
  have h2 := near_to_int q hq vi φi x (N * A) n2 hn2
  have hε1 : |(ε : ℝ)| = 1 := by rcases hε with rfl | rfl <;> simp
  have h3 : |((ε * ((vi : ℤ) * (N * A) - q * n2) - q * ni : ℤ) : ℝ) - u| < (q : ℝ) / 5 := by
    have e : ((ε * ((vi : ℤ) * (N * A) - q * n2) - q * ni : ℤ) : ℝ) - u
        = ε * ((((vi : ℤ) * (N * A) - q * n2 : ℤ) : ℝ) - (-((vi : ℝ) * x + q * φi))) := by
      rw [hu]
      push_cast
      ring
    rw [e, abs_mul, hε1, one_mul]
    exact h2
  apply hN _ h3
  refine ⟨-(N * B) - D * (N * A) - ε * n2 - ni, ?_⟩
  linear_combination (-(N * A)) * hD + N * hAB

lemma win_ne_dvd (q N m : ℤ) (hq : 0 < q) (h1 : N < m) (h2 : m < N + q) : ¬ q ∣ m - N := by
  rintro ⟨k, hk⟩
  exact no_mult_between q k hq (by linarith) (by linarith)

lemma window_gap3 (q : ℕ) (u1 u2 u3 : ℝ) (h12 : |u1 - u2| ≤ (3 / 5 : ℝ) * q - 1)
    (h13 : |u1 - u3| ≤ (3 / 5 : ℝ) * q - 1) (h23 : |u2 - u3| ≤ (3 / 5 : ℝ) * q - 1) :
    ∃ N : ℤ, ∀ m : ℤ, (|(m : ℝ) - u1| < (q : ℝ) / 5 ∨ |(m : ℝ) - u2| < (q : ℝ) / 5 ∨
      |(m : ℝ) - u3| < (q : ℝ) / 5) → N < m ∧ m < N + q := by
  obtain ⟨lo, l1, l2, l3, hmin⟩ : ∃ lo : ℝ, lo ≤ u1 ∧ lo ≤ u2 ∧ lo ≤ u3 ∧
      (lo = u1 ∨ lo = u2 ∨ lo = u3) := by
    refine ⟨min u1 (min u2 u3), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _), ?_⟩
    rcases min_choice u1 (min u2 u3) with h | h
    · exact Or.inl h
    · rcases min_choice u2 u3 with h2 | h2
      · exact Or.inr (Or.inl (h.trans h2))
      · exact Or.inr (Or.inr (h.trans h2))
  obtain ⟨a12, b12⟩ := abs_le.mp h12
  obtain ⟨a13, b13⟩ := abs_le.mp h13
  obtain ⟨a23, b23⟩ := abs_le.mp h23
  have hup : u1 ≤ lo + ((3 / 5 : ℝ) * q - 1) ∧ u2 ≤ lo + ((3 / 5 : ℝ) * q - 1) ∧
      u3 ≤ lo + ((3 / 5 : ℝ) * q - 1) := by
    rcases hmin with h | h | h <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
  have f1 := Int.floor_le (lo - (q : ℝ) / 5)
  have f2 := Int.lt_floor_add_one (lo - (q : ℝ) / 5)
  refine ⟨⌊lo - (q : ℝ) / 5⌋, fun m hm => ?_⟩
  have hm' : lo - (q : ℝ) / 5 < m ∧ (m : ℝ) < lo + ((3 / 5 : ℝ) * q - 1) + (q : ℝ) / 5 := by
    rcases hm with hm | hm | hm
    · obtain ⟨c1, c2⟩ := abs_lt.mp hm
      constructor <;> linarith [hup.1]
    · obtain ⟨c1, c2⟩ := abs_lt.mp hm
      constructor <;> linarith [hup.2.1]
    · obtain ⟨c1, c2⟩ := abs_lt.mp hm
      constructor <;> linarith [hup.2.2]
  constructor
  · have : ((⌊lo - (q : ℝ) / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
    exact_mod_cast this
  · have : (m : ℝ) < ((⌊lo - (q : ℝ) / 5⌋ : ℤ) : ℝ) + q := by linarith [hm'.2]
    exact_mod_cast this

/-- two same-class runners with exactly coinciding centres: the bad `j` of the second are bad for the first -/
lemma bad_transfer (q : ℕ) (hq : 0 < q) (vp vr : ℕ) (φp φr x : ℝ) (ε D M : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hD : (vp : ℤ) - ε * vr = q * D)
    (hM : (D : ℝ) * x + (φp - ε * φr) = M) (j : ℤ)
    (hbad : ¬ GoodR vr φr (((j : ℝ) + x) / q)) : ¬ GoodR vp φp (((j : ℝ) + x) / q) := by
  unfold GoodR at hbad
  obtain ⟨n, hn⟩ := exists_near_of_not_good hbad
  have h1 := near_to_int q hq vr φr x j n hn
  apply not_good_of_near q hq vp φp x j (D * j + ε * n + M)
  have hε1 : |(ε : ℝ)| = 1 := by rcases hε with rfl | rfl <;> simp
  have hDR : (vp : ℝ) - ε * vr = q * D := by exact_mod_cast hD
  have e : ((((vp : ℤ) * j - q * (D * j + ε * n + M) : ℤ)) : ℝ) - (-((vp : ℝ) * x + q * φp))
      = ε * ((((vr : ℤ) * j - q * n : ℤ) : ℝ) - (-((vr : ℝ) * x + q * φr))) := by
    push_cast
    linear_combination ((j : ℝ) + x) * hDR + (q : ℝ) * hM
  rw [e, abs_mul, hε1, one_mul]
  exact h1

/-- Two same-class runners `p, r` with coinciding centres and one more coprime runner `o`: counting
(`2 (⌊(2q-1)/5⌋ + 1) < q`) leaves a common good `j`. -/
lemma exact_pair (q : ℕ) (hq : 2 * ((2 * q - 1) / 5 + 1) < q) (vp vr vo : ℕ)
    (hp : Nat.Coprime vp q) (ho : Nat.Coprime vo q) (φp φr φo x : ℝ) (ε D M : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hD : (vp : ℤ) - ε * vr = q * D)
    (hM : (D : ℝ) * x + (φp - ε * φr) = M) :
    ∃ j : ℤ, GoodR vp φp (((j : ℝ) + x) / q) ∧ GoodR vr φr (((j : ℝ) + x) / q) ∧
      GoodR vo φo (((j : ℝ) + x) / q) := by
  classical
  have hq0 : 0 < q := by omega
  have h3 := card_bad_le q hq0 vp hp φp x
  have h4 := card_bad_le q hq0 vo ho φo x
  have hcard : (badSet q vp φp x ∪ badSet q vo φo x).card < (Finset.range q).card := by
    rw [Finset.card_range]
    have := Finset.card_union_le (badSet q vp φp x) (badSet q vo φo x)
    omega
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjq : j < q := Finset.mem_range.mp hj
  have gp : GoodR vp φp ((((j : ℤ) : ℝ) + x) / q) := by
    by_contra h
    exact hjn (Finset.mem_union_left _ (mem_badSet.mpr ⟨hjq, h⟩))
  have go : GoodR vo φo ((((j : ℤ) : ℝ) + x) / q) := by
    by_contra h
    exact hjn (Finset.mem_union_right _ (mem_badSet.mpr ⟨hjq, h⟩))
  refine ⟨(j : ℤ), gp, ?_, go⟩
  by_contra h
  exact bad_transfer q hq0 vp vr φp φr x ε D M hε hD hM (j : ℤ) h gp

end LRSpectrumFull
