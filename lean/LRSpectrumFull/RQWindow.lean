/-
# RQ, module W: the window lemma for a general modulus `q` (real phases)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 2, "Lemma B (window)".

Time is written `t = (j + x) / q`, `j : ℤ`, `x : ℝ`.  A runner `(v, φ)` is bad at `t` iff some integer `m ≡ v j (mod q)`
(here `m = v j - q n`) has `|m + β| < q / 5`, `β = v x + q φ`.  Two runners of one class (`v_a ≡ ε v_b`) have bad
integer sets in the coordinate `z = v_a j` that are open intervals of length `2q/5` with centres
`q ‖D x + σ‖` apart; both fit in one open interval of length `≤ q - 1`, which misses a residue.

* `goodR_mulq`        : a speed `q u` at time `(j + x)/q` is the speed `u` at time `x` (general `q`, `j : ℤ`).
* `near_to_int`       : bad runner => integer `m = v j - q n` with `|m - (-β)| < q/5`.
* `window_gap`        : two centres `≤ 3q/5 - 1` apart: a residue `N` misses both intervals.
* `window_lemma`      : Lemma B.
* `exists_free_j`     : one free runner (`q ∤ v`) is good at some `t = (j + x)/q`  (Section 1, `|F| = 1`).
* `tpDist_neg`, `exists_int_of_far` : sign / half-shift facts used to feed Lemma B.
-/
import LRSpectrumFull.RFiveWindow

namespace LRSpectrumFull

lemma goodR_mulq (q u : ℕ) (hq : 0 < q) (φ x : ℝ) (j : ℤ) :
    GoodR (q * u) φ (((j : ℝ) + x) / q) ↔ GoodR u φ x := by
  unfold GoodR
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht : (q : ℝ) * (((j : ℝ) + x) / q) = j + x := mul_div_cancel₀ _ hq0
  have h : ((q * u : ℕ) : ℝ) * (((j : ℝ) + x) / q) + φ = ((u : ℝ) * x + φ) + ((u * j : ℤ) : ℝ) := by
    push_cast
    linear_combination (u : ℝ) * ht
  rw [h, tpDist_add_int]

lemma near_to_int (q : ℕ) (hq : 0 < q) (v : ℕ) (φ x : ℝ) (j n : ℤ)
    (h : |(v : ℝ) * (((j : ℝ) + x) / q) + φ - n| < 1 / 5) :
    |((((v : ℤ) * j - q * n : ℤ)) : ℝ) - (-((v : ℝ) * x + q * φ))| < (q : ℝ) / 5 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : (q : ℝ) * (((j : ℝ) + x) / q) = j + x := mul_div_cancel₀ _ hq0
  have e : ((((v : ℤ) * j - q * n : ℤ)) : ℝ) - (-((v : ℝ) * x + q * φ))
      = q * ((v : ℝ) * (((j : ℝ) + x) / q) + φ - n) := by
    push_cast
    linear_combination (-(v : ℝ)) * ht
  rw [e, abs_mul, abs_of_pos hqp]
  have := mul_lt_mul_of_pos_left h hqp
  linarith

lemma window_gap (q : ℕ) (u w : ℝ) (huw : |u - w| ≤ (3 / 5 : ℝ) * q - 1) :
    ∃ N : ℤ, ∀ m : ℤ, (|(m : ℝ) - u| < (q : ℝ) / 5 ∨ |(m : ℝ) - w| < (q : ℝ) / 5) →
      N < m ∧ m < N + q := by
  obtain ⟨huw1, huw2⟩ := abs_le.mp huw
  rcases le_total u w with h | h
  · refine ⟨⌊u - (q : ℝ) / 5⌋, fun m hm => ?_⟩
    have h1 := Int.floor_le (u - (q : ℝ) / 5)
    have h2 := Int.lt_floor_add_one (u - (q : ℝ) / 5)
    have hm' : u - (q : ℝ) / 5 < m ∧ (m : ℝ) < w + (q : ℝ) / 5 := by
      rcases hm with hm | hm
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
    constructor
    · have : ((⌊u - (q : ℝ) / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
      exact_mod_cast this
    · have : (m : ℝ) < ((⌊u - (q : ℝ) / 5⌋ : ℤ) : ℝ) + q := by linarith [hm'.2]
      exact_mod_cast this
  · refine ⟨⌊w - (q : ℝ) / 5⌋, fun m hm => ?_⟩
    have h1 := Int.floor_le (w - (q : ℝ) / 5)
    have h2 := Int.lt_floor_add_one (w - (q : ℝ) / 5)
    have hm' : w - (q : ℝ) / 5 < m ∧ (m : ℝ) < u + (q : ℝ) / 5 := by
      rcases hm with hm | hm
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := abs_lt.mp hm
        constructor <;> linarith
    constructor
    · have : ((⌊w - (q : ℝ) / 5⌋ : ℤ) : ℝ) < m := by linarith [hm'.1]
      exact_mod_cast this
    · have : (m : ℝ) < ((⌊w - (q : ℝ) / 5⌋ : ℤ) : ℝ) + q := by linarith [hm'.2]
      exact_mod_cast this

lemma no_mult_between (q k : ℤ) (hq : 0 < q) (h1 : 0 < q * k) (h2 : q * k < q) : False := by
  rcases le_or_gt k 0 with hk | hk
  · nlinarith
  · nlinarith

/-- Lemma B (window), general modulus `q ≥ 2`, real phases.  `va` is a unit mod `q`; `vb ≡ ε va`,
`va - ε vb = q D`; if `D x + (φa - ε φb)` is within `3/5 - 1/q` of an integer then some `j` is good for both. -/
theorem window_lemma (q : ℕ) (hq : 2 ≤ q) (va vb : ℕ) (hcop : Nat.Coprime va q)
    (ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : (va : ℤ) - ε * vb = q * D)
    (φa φb x : ℝ) (n : ℤ)
    (hn : |(D : ℝ) * x + (φa - ε * φb) - n| ≤ 3 / 5 - 1 / q) :
    ∃ j : ℤ, GoodR va φa (((j : ℝ) + x) / q) ∧ GoodR vb φb (((j : ℝ) + x) / q) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqR' : (q : ℝ) ≠ 0 := hqR.ne'
  have hDR : (va : ℝ) - ε * vb = q * D := by exact_mod_cast hD
  have huw : |(-((va : ℝ) * x + q * φa)) - (-((ε : ℝ) * ((vb : ℝ) * x + q * φb)) - q * n)|
      ≤ (3 / 5 : ℝ) * q - 1 := by
    have e : (-((va : ℝ) * x + q * φa)) - (-((ε : ℝ) * ((vb : ℝ) * x + q * φb)) - q * n)
        = -(q * ((D : ℝ) * x + (φa - ε * φb) - n)) := by
      linear_combination (-x) * hDR
    rw [e, abs_neg, abs_mul, abs_of_pos hqR]
    calc (q : ℝ) * |(D : ℝ) * x + (φa - ε * φb) - n| ≤ q * (3 / 5 - 1 / q) :=
          mul_le_mul_of_nonneg_left hn hqR.le
      _ = 3 / 5 * q - 1 := by rw [mul_sub, mul_one_div_cancel hqR']; ring
  obtain ⟨N, hN⟩ := window_gap q _ _ huw
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hj : (va : ℤ) * (N * A) - N = q * (-(N * B)) := by linear_combination N * hAB
  refine ⟨N * A, ?_, ?_⟩
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n1, hn1⟩ := exists_near_of_not_good hbad
    have h1 := near_to_int q hq0 va φa x (N * A) n1 hn1
    obtain ⟨h1a, h1b⟩ := hN _ (Or.inl h1)
    have e : ((va : ℤ) * (N * A) - q * n1) - N = q * (-(N * B) - n1) := by linear_combination hj
    exact no_mult_between q (-(N * B) - n1) (by exact_mod_cast hq0) (by linarith) (by linarith)
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n2, hn2⟩ := exists_near_of_not_good hbad
    have h2 := near_to_int q hq0 vb φb x (N * A) n2 hn2
    have hε1 : |(ε : ℝ)| = 1 := by rcases hε with rfl | rfl <;> simp
    have h3 : |(((ε * ((vb : ℤ) * (N * A) - q * n2) - q * n : ℤ)) : ℝ)
        - (-((ε : ℝ) * ((vb : ℝ) * x + q * φb)) - q * n)| < (q : ℝ) / 5 := by
      have e : (((ε * ((vb : ℤ) * (N * A) - q * n2) - q * n : ℤ)) : ℝ)
          - (-((ε : ℝ) * ((vb : ℝ) * x + q * φb)) - q * n)
          = ε * ((((vb : ℤ) * (N * A) - q * n2 : ℤ) : ℝ) - (-((vb : ℝ) * x + q * φb))) := by
        push_cast
        ring
      rw [e, abs_mul, hε1, one_mul]
      exact h2
    obtain ⟨h3a, h3b⟩ := hN _ (Or.inr h3)
    have e2 : (ε * ((vb : ℤ) * (N * A) - q * n2) - q * n) - N
        = q * (-(N * B) - D * (N * A) - ε * n2 - n) := by
      linear_combination hj - (N * A) * hD
    exact no_mult_between q (-(N * B) - D * (N * A) - ε * n2 - n) (by exact_mod_cast hq0)
      (by linarith) (by linarith)

/-- One free runner (`q ∤ v`) is good at some time `(j + x)/q`. -/
lemma exists_free_j (q : ℕ) (hq : 0 < q) (v : ℕ) (hv : ¬ q ∣ v) (φ x : ℝ) :
    ∃ j : ℤ, GoodR v φ (((j : ℝ) + x) / q) := by
  have hdvd : ¬ ((q : ℤ) ∣ (v : ℤ)) := by exact_mod_cast hv
  obtain ⟨k, hk⟩ := coset_branchR (q : ℤ) (by exact_mod_cast hq) v hdvd (-x) φ
  refine ⟨k, ?_⟩
  unfold GoodR
  have e : ((k : ℝ) + x) / q = ((k : ℝ) - (-x)) / (((q : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [e]
  exact hk

lemma tpDist_neg (y : ℝ) : tpDist (-y) = tpDist y := by
  have h1 : ∀ z : ℝ, tpDist (-z) ≤ tpDist z := by
    intro z
    unfold tpDist
    have h := round_le (-z) (-(round z))
    have e : -z - ((-(round z) : ℤ) : ℝ) = -(z - (round z : ℝ)) := by push_cast; ring
    rw [e, abs_neg] at h
    exact h
  refine le_antisymm (h1 y) ?_
  have := h1 (-y)
  rwa [neg_neg] at this

/-- If `y + 1/2` is at distance `≥ 1/5` from `ℤ`, then `y` is within `3/10` of `ℤ`. -/
lemma exists_int_of_far (y : ℝ) (h : 1 / 5 ≤ tpDist (y + 1 / 2)) : ∃ n : ℤ, |y - n| ≤ 3 / 10 := by
  unfold tpDist at h
  have hle := abs_sub_round (y + 1 / 2)
  generalize round (y + 1 / 2) = r at h hle
  rcases le_or_gt 0 (y + 1 / 2 - r) with h0 | h0
  · refine ⟨r, ?_⟩
    rw [abs_of_nonneg h0] at h hle
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨r - 1, ?_⟩
    rw [abs_of_neg h0] at h hle
    push_cast
    rw [abs_le]
    constructor <;> linarith

end LRSpectrumFull
