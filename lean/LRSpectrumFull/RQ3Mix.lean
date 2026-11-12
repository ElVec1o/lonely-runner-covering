/-
# RQ3, module M: the mixed-threshold three-runner lemma (real phases)

`q3Mix3`: three pairwise distinct positive speeds `p, q, d`, arbitrary real phases: some `x` has
`‖p x + α‖ ≥ 1/5`, `‖q x + β‖ ≥ 1/5`, `‖d x + γ‖ ≥ 7/30` (the window runner is the third).

Route (R7_LEAN_AND_Q3_COST, Task B, Route 2; probe in Q3_LEAN_2026_11_12.md):
* sorted primitive triple other than `(1, 2, 3)`: the real-phase `1/4` results `sweepCase` (gcd(a,b) = 1, `c ≥ 4`
  by `ineqL4`) and `shiftCase` (gcd(a,b) ≥ 2) of `TPThreeA`, thresholds weakened from `1/4`;
* the triple `(1, 2, 3)`: `q3Sweep123` (mixed thresholds, the three placements of the `7/30` runner);
* general triple: rescale by the gcd (`split3`, phase-independent), six orderings.
-/
import LRSpectrumFull.RQ3Sweep

namespace LRSpectrumFull

lemma q3MixPrim (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (τa τb τc : ℝ) (hτ : Q3Pat τa τb τc) (α β γ : ℝ) :
    ∃ t : ℝ, τa ≤ tpDist ((a : ℝ) * t + α) ∧ τb ≤ tpDist ((b : ℝ) * t + β) ∧
      τc ≤ tpDist ((c : ℝ) * t + γ) := by
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, ⟨hc0, hc1⟩⟩ := q3Pat_le hτ
  by_cases h123 : a = 1 ∧ b = 2 ∧ c = 3
  · obtain ⟨rfl, rfl, rfl⟩ := h123
    obtain ⟨x, h1, h2, h3⟩ := q3Sweep123 τa τb τc hτ α β γ
    exact ⟨x, q3_tpDist_of_goodT h1 ha0 (by linarith), q3_tpDist_of_goodT h2 hb0 (by linarith),
      q3_tpDist_of_goodT h3 hc0 (by linarith)⟩
  · have hc4 : 4 ≤ c := by
      by_contra hlt
      exact h123 ⟨by omega, by omega, by omega⟩
    have key : ∃ τ : ℝ, GoodQ ((a : ℝ) * τ + α) ∧ GoodQ ((b : ℝ) * τ + β) ∧
        GoodQ ((c : ℝ) * τ + γ) := by
      rcases Nat.lt_or_ge (Nat.gcd a b) 2 with h | h
      · have hg1 : Nat.gcd a b = 1 := by
          have := Nat.gcd_pos_of_pos_left b ha
          omega
        exact sweepCase a b c ha hab hbc hg1 (ineqL4 a b c ha hab hbc hc4) _ _ _
      · exact shiftCase a b c ha hab h hg _ _ _
    obtain ⟨t, h1, h2, h3⟩ := key
    exact ⟨t, le_trans ha1 (tpDist_of_goodQ h1), le_trans hb1 (tpDist_of_goodQ h2),
      le_trans hc1 (tpDist_of_goodQ h3)⟩

lemma q3MixSorted (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (τa τb τc : ℝ)
    (hτ : Q3Pat τa τb τc) (α β γ : ℝ) :
    ∃ t : ℝ, τa ≤ tpDist ((a : ℝ) * t + α) ∧ τb ≤ tpDist ((b : ℝ) * t + β) ∧
      τc ≤ tpDist ((c : ℝ) * t + γ) := by
  obtain ⟨g, a', b', c', hgpos, hprim, rfl, rfl, rfl⟩ := split3 a b c ha
  have ha' : 0 < a' := Nat.pos_of_mul_pos_left ha
  have hab' : a' < b' := Nat.lt_of_mul_lt_mul_left hab
  have hbc' : b' < c' := Nat.lt_of_mul_lt_mul_left hbc
  obtain ⟨t, h1, h2, h3⟩ := q3MixPrim a' b' c' ha' hab' hbc' hprim τa τb τc hτ α β γ
  have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  refine ⟨t / g, ?_, ?_, ?_⟩
  · have : ((g * a' : ℕ) : ℝ) * (t / g) = (a' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h1
  · have : ((g * b' : ℕ) : ℝ) * (t / g) = (b' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h2
  · have : ((g * c' : ℕ) : ℝ) * (t / g) = (c' : ℝ) * t := by push_cast; field_simp
    rw [this]; exact h3

lemma q3MixAny (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (τa τb τc : ℝ) (hτ : Q3Pat τa τb τc) (α β γ : ℝ) :
    ∃ t : ℝ, τa ≤ tpDist ((a : ℝ) * t + α) ∧ τb ≤ tpDist ((b : ℝ) * t + β) ∧
      τc ≤ tpDist ((c : ℝ) * t + γ) := by
  obtain ⟨p12, p23, p231, p312, p321⟩ := q3Pat_perm hτ
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3
  · exact q3MixSorted a b c ha h1 h3 τa τb τc hτ α β γ
  · -- a<c<b
    obtain ⟨t, x, y, z⟩ := q3MixSorted a c b ha h2 h3 τa τc τb p23 α γ β
    exact ⟨t, x, z, y⟩
  · omega
  · -- c<a<b
    obtain ⟨t, x, y, z⟩ := q3MixSorted c a b hc h2 h1 τc τa τb p312 γ α β
    exact ⟨t, y, z, x⟩
  · -- b<a<c
    obtain ⟨t, x, y, z⟩ := q3MixSorted b a c hb h1 h2 τb τa τc p12 β α γ
    exact ⟨t, y, x, z⟩
  · omega
  · -- b<c<a
    obtain ⟨t, x, y, z⟩ := q3MixSorted b c a hb h3 h2 τb τc τa p231 β γ α
    exact ⟨t, z, x, y⟩
  · -- c<b<a
    obtain ⟨t, x, y, z⟩ := q3MixSorted c b a hc h3 h1 τc τb τa p321 γ β α
    exact ⟨t, z, y, x⟩

/-- Mixed three-runner lemma: distinct positive speeds `p, q, d`, real phases; thresholds `1/5, 1/5` and `7/30`
for the window runner `d`. -/
theorem q3Mix3 (p q d : ℕ) (pp : 0 < p) (pq : 0 < q) (pd : 0 < d) (hpq : p ≠ q) (hpd : p ≠ d)
    (hqd : q ≠ d) (α β γ : ℝ) :
    ∃ x : ℝ, 1 / 5 ≤ tpDist ((p : ℝ) * x + α) ∧ 1 / 5 ≤ tpDist ((q : ℝ) * x + β) ∧
      7 / 30 ≤ tpDist ((d : ℝ) * x + γ) :=
  q3MixAny p q d pp pq pd hpq hpd hqd (1 / 5) (1 / 5) (7 / 30) (Or.inl ⟨rfl, rfl, rfl⟩) α β γ

end LRSpectrumFull
