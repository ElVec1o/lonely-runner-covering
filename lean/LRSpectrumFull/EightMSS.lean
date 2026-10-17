/-
# E5b: the lattice-point (staircase + pigeonhole) part of MSS Theorem A

Statement `e5b_staircase`: for `v : Fin n → ℤ` positive with `gcd v = 1`, and `l ≥ 1` with
`l ^ (n - 1) < ∑ v`, there are an integer vector `z`, not parallel to `v`, and a rational `σ`
with `|l * z i - σ * v i| ≤ 1` for every `i`.

Proof (no path is built explicitly).  Events `e = (i, a)` with `a < v i` (there are `∑ v` of them),
time `τ e = (2a+1)/(2 v i) ∈ (0,1)`.  The point before event `e` is
`q e j = ⌊τ v j + 1/2⌋` for `j < i` and `⌈τ v j + 1/2⌉ - 1` for `j ≥ i`
(the monotone staircase from `0` to `v` sampled with ties broken by index).
Facts: `|q e j - τ e v j| ≤ 1/2`, `0 ≤ q e j`, `q e i = a < v i`, and `e ↦ q e` is injective
(lexicographic order on `(τ, i)`).  Pigeonhole on `(e, c) ↦ (q e + c v) mod l` for `c < l`:
`l * ∑ v > l ^ n` pairs, `l ^ n` classes.  A collision with `e = e'` forces `l ∣ c - c'` by
`gcd v = 1`; with `e ≠ e'` it gives `q e - q e' = l z + c'' v`, and `z ∥ v` would force
`q e - q e' = s v` with `s ∈ ℤ`, impossible for distinct points of the box `[0, v]` that each
have a coordinate `< v`.
-/

import Mathlib
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.EightMSS

open Finset

variable {n : ℕ} (v : Fin n → ℤ)

/-- Events: `(i, a)` with `a < v i`. -/
abbrev Ev := Σ i : Fin n, Fin (v i).toNat

/-- Time of an event. -/
def tau (e : Ev v) : ℚ := (2 * (e.2 : ℚ) + 1) / (2 * (v e.1 : ℚ))

/-- The staircase point just before event `e`. -/
def qpt (e : Ev v) (j : Fin n) : ℤ :=
  if j < e.1 then ⌊tau v e * v j + 1 / 2⌋ else ⌈tau v e * v j + 1 / 2⌉ - 1

variable {v}

lemma tau_mul_self (hv : ∀ i, 0 < v i) (e : Ev v) :
    tau v e * v e.1 + 1 / 2 = ((e.2 : ℕ) : ℚ) + 1 := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  unfold tau
  field_simp
  ring

lemma tau_pos (hv : ∀ i, 0 < v i) (e : Ev v) : 0 < tau v e := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  unfold tau
  positivity

lemma tau_lt_one (hv : ∀ i, 0 < v i) (e : Ev v) : tau v e < 1 := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  have ha : ((e.2 : ℕ) : ℤ) < v e.1 := by
    have := e.2.isLt
    omega
  have ha' : ((e.2 : ℕ) : ℚ) + 1 ≤ v e.1 := by exact_mod_cast ha
  unfold tau
  rw [div_lt_one (by positivity)]
  linarith

lemma qpt_self (hv : ∀ i, 0 < v i) (e : Ev v) : qpt v e e.1 = (e.2 : ℕ) := by
  unfold qpt
  rw [if_neg (lt_irrefl _), tau_mul_self hv]
  have : ⌈((e.2 : ℕ) : ℚ) + 1⌉ = ((e.2 : ℕ) : ℤ) + 1 := by
    rw [show ((e.2 : ℕ) : ℚ) + 1 = (((e.2 : ℕ) + 1 : ℤ) : ℚ) by push_cast; ring, Int.ceil_intCast]
  rw [this]; ring

lemma qpt_self_lt (hv : ∀ i, 0 < v i) (e : Ev v) : qpt v e e.1 < v e.1 := by
  rw [qpt_self hv]
  have := e.2.isLt
  omega

lemma qpt_eps (e : Ev v) (j : Fin n) : |(qpt v e j : ℚ) - tau v e * v j| ≤ 1 / 2 := by
  rw [abs_le]
  unfold qpt
  split_ifs
  · have h1 := Int.floor_le (tau v e * v j + 1 / 2)
    have h2 := Int.lt_floor_add_one (tau v e * v j + 1 / 2)
    constructor <;> linarith
  · have h1 := Int.le_ceil (tau v e * v j + 1 / 2)
    have h2 := Int.ceil_lt_add_one (tau v e * v j + 1 / 2)
    push_cast
    constructor <;> linarith

lemma qpt_nonneg (hv : ∀ i, 0 < v i) (e : Ev v) (j : Fin n) : 0 ≤ qpt v e j := by
  have ht := tau_pos hv e
  have hj : (0 : ℚ) < v j := by exact_mod_cast hv j
  have hx : 0 < tau v e * v j := mul_pos ht hj
  unfold qpt
  split_ifs
  · exact Int.floor_nonneg.mpr (by linarith)
  · have : (0 : ℤ) < ⌈tau v e * v j + 1 / 2⌉ := Int.ceil_pos.mpr (by linarith)
    omega

/-- Domination: a later event sees strictly more steps in the coordinate of an earlier one. -/
lemma qpt_dom (hv : ∀ i, 0 < v i) (e e' : Ev v)
    (h : tau v e < tau v e' ∨ (tau v e = tau v e' ∧ e.1 < e'.1)) :
    qpt v e e.1 < qpt v e' e.1 := by
  rw [qpt_self hv]
  have hi : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  have hle : tau v e ≤ tau v e' := by rcases h with h | h; exact h.le; exact h.1.le
  have hmono : tau v e * v e.1 ≤ tau v e' * v e.1 := mul_le_mul_of_nonneg_right hle hi.le
  have hs := tau_mul_self hv e
  unfold qpt
  split_ifs with hlt
  · have : ((e.2 : ℕ) : ℤ) + 1 ≤ ⌊tau v e' * v e.1 + 1 / 2⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    omega
  · have hstrict : tau v e < tau v e' := by
      rcases h with h | h
      · exact h
      · exact absurd h.2 hlt
    have hm : tau v e * v e.1 < tau v e' * v e.1 := mul_lt_mul_of_pos_right hstrict hi
    have : ((e.2 : ℕ) : ℤ) + 1 < ⌈tau v e' * v e.1 + 1 / 2⌉ := by
      rw [Int.lt_ceil]; push_cast; linarith
    omega

lemma qpt_inj (hv : ∀ i, 0 < v i) {e e' : Ev v} (hne : e ≠ e') : qpt v e ≠ qpt v e' := by
  intro heq
  rcases lt_trichotomy (tau v e) (tau v e') with h | h | h
  · have := qpt_dom hv e e' (Or.inl h); rw [heq] at this; exact lt_irrefl _ this
  · rcases lt_trichotomy e.1 e'.1 with hi | hi | hi
    · have := qpt_dom hv e e' (Or.inr ⟨h, hi⟩); rw [heq] at this; exact lt_irrefl _ this
    · apply hne
      obtain ⟨i, a⟩ := e
      obtain ⟨i', a'⟩ := e'
      simp only at hi
      subst hi
      have hvi : (0 : ℚ) < v i := by exact_mod_cast hv i
      unfold tau at h
      simp only at h
      rw [div_left_inj' (by positivity)] at h
      have : (a : ℕ) = a' := by exact_mod_cast (by linarith : ((a : ℕ) : ℚ) = a')
      rw [Fin.ext this]
    · have := qpt_dom hv e' e (Or.inr ⟨h.symm, hi⟩); rw [heq] at this; exact lt_irrefl _ this
  · have := qpt_dom hv e' e (Or.inl h); rw [heq] at this; exact lt_irrefl _ this

/-- `gcd v = 1` and `a ∣ c * v j` for all `j` give `a ∣ c`. -/
lemma dvd_of_dvd_mul_all (hg : Finset.univ.gcd v = 1) (a c : ℤ) (h : ∀ j, a ∣ c * v j) :
    a ∣ c := by
  have : a ∣ Finset.univ.gcd (fun j => c * v j) := Finset.dvd_gcd (fun j _ => h j)
  rw [Finset.gcd_mul_left, hg, mul_one] at this
  exact dvd_normalize_iff.mp this

/-- **E5b (staircase + pigeonhole).** -/
theorem e5b_staircase (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1) (l : ℕ) (hl : 0 < l)
    (hsum : (l : ℤ) ^ (n - 1) < ∑ i, v i) :
    ∃ z : Fin n → ℤ, ∃ σ : ℚ, (∃ a b, z a * v b ≠ z b * v a) ∧
      ∀ i, |(l : ℚ) * z i - σ * v i| ≤ 1 := by
  haveI : NeZero l := ⟨hl.ne'⟩
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hsum
  -- card of events
  have hcardE : (Fintype.card (Ev v) : ℤ) = ∑ i, v i := by
    rw [Fintype.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by simp [Fintype.card_fin, Int.toNat_of_nonneg (hv i).le])
  have hcard : Fintype.card (Fin n → ZMod l) < Fintype.card (Ev v × Fin l) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
    have h1 : ((l ^ (n - 1) : ℕ) : ℤ) < (Fintype.card (Ev v) : ℤ) := by
      rw [hcardE]; exact_mod_cast hsum
    have h2 : l ^ (n - 1) < Fintype.card (Ev v) := by exact_mod_cast h1
    have h3 : l ^ n = l ^ (n - 1) * l := by
      rw [← pow_succ]; congr 1; omega
    rw [h3]
    exact Nat.mul_lt_mul_of_pos_right h2 hl
  obtain ⟨⟨e, c⟩, ⟨e', c'⟩, hne, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Ev v × Fin l => fun j => ((qpt v p.1 j + (p.2 : ℤ) * v j : ℤ) : ZMod l)) hcard
  have hdvd : ∀ j, (l : ℤ) ∣ (qpt v e' j + (c' : ℤ) * v j) - (qpt v e j + (c : ℤ) * v j) :=
    fun j => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hcol j)
  -- the case e = e'
  by_cases hee : e = e'
  · exfalso
    subst hee
    have hcc : c ≠ c' := fun h => hne (by rw [h])
    have : (l : ℤ) ∣ ((c' : ℤ) - c) := by
      apply dvd_of_dvd_mul_all hg
      intro j
      have := hdvd j
      rwa [show qpt v e j + (c' : ℤ) * v j - (qpt v e j + (c : ℤ) * v j) = ((c' : ℤ) - c) * v j
        by ring] at this
    obtain ⟨k, hk⟩ := this
    have hc1 := c.isLt
    have hc2 := c'.isLt
    have hne' : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (l : ℤ) * k ≤ -l := by nlinarith
      omega
    · subst hk0; simp at hk; omega
    · have : (l : ℤ) ≤ l * k := by nlinarith
      omega
  -- the case e ≠ e'
  set d : Fin n → ℤ := fun j => qpt v e j - qpt v e' j with hd
  set z : Fin n → ℤ := fun j => (d j - ((c' : ℤ) - c) * v j) / l with hz
  have hlz : ∀ j, (l : ℤ) * z j = d j - ((c' : ℤ) - c) * v j := by
    intro j
    apply Int.mul_ediv_cancel'
    have := dvd_neg.mpr (hdvd j)
    convert this using 1
    simp only [hd]; ring
  refine ⟨z, tau v e - tau v e' - ((c' : ℚ) - c), ?_, ?_⟩
  · by_contra hpar
    push Not at hpar
    have hdpar : ∀ a b, d a * v b = d b * v a := by
      intro a b
      have ha := hlz a
      have hb := hlz b
      have hab := hpar a b
      have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      apply mul_left_cancel₀ hl0
      linear_combination -((l : ℤ) * v b) * ha + ((l : ℤ) * v a) * hb + ((l : ℤ) * l) * hab
    set i0 := e.1
    have hvi0 := hv i0
    have hdiv : v i0 ∣ d i0 := by
      apply dvd_of_dvd_mul_all hg
      intro j
      exact ⟨d j, by rw [hdpar i0 j]; ring⟩
    obtain ⟨s, hs⟩ := hdiv
    have hds : ∀ j, d j = s * v j := by
      intro j
      apply mul_left_cancel₀ hvi0.ne'
      linear_combination v j * hs - hdpar i0 j
    rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
    · -- q e' = q e - s v ≥ v at e'.1
      have h1 := hds e'.1
      have h2 := qpt_self_lt hv e'
      have h3 := qpt_nonneg hv e e'.1
      have h4 := hv e'.1
      simp only [hd] at h1
      nlinarith
    · apply qpt_inj hv hee
      funext j
      have := hds j
      simp only [hd, hs0, zero_mul] at this
      omega
    · have h1 := hds e.1
      have h2 := qpt_self_lt hv e
      have h3 := qpt_nonneg hv e' e.1
      have h4 := hv e.1
      simp only [hd] at h1
      nlinarith
  · intro i
    have h := hlz i
    have hq : ((l : ℤ) : ℚ) * (z i : ℚ) = ((d i - ((c' : ℤ) - c) * v i : ℤ) : ℚ) := by
      exact_mod_cast h
    push_cast at hq
    have e1 := qpt_eps e i
    have e2 := qpt_eps e' i
    rw [abs_le] at e1 e2 ⊢
    simp only [hd] at hq
    push_cast at hq
    constructor <;> linarith

/-! ## The remaining gap (MSS Theorem A' induction step), carried as a hypothesis

CHECKED 2026-09-25 against the full paper (Malikiosis-Santos-Schymura, arXiv:2411.06903v2,
downloaded PDF, read in full: title through end of Section 3, i.e. Introduction, Section 2
"Preliminaries" (Thm 2.1/Cor 2.3, Lemma 2.5, Prop 2.7/2.8/2.9), and Section 3 "Projections of
Lonely Runner Zonotopes" in full, including the complete proof of Theorem 3.1 via Prop 3.3/3.4
and Remark 3.5 (Gale duality) and the proof of Theorem A' (their main induction) via Lemma 3.6.
Sections 4-7 (sLRC / Lonely Vector Property, cosimple zonotopes, and the low-dimension d=2,3
results) were only skimmed for their statements (Def 1.2, Conjecture B/B', Theorem C-F), because
they are NOT needed for plain (unshifted) LRC at `n = 7`, see the correction below.

**Correction 1 (important, resolves the biggest open risk noted in the previous docstring).**
The earlier reconstruction worried that the MSS argument needs the Lonely Vector Property (LVP),
proved by MSS only for `n ≤ 4` points, which would have made `n = 7` out of reach.  Reading the
paper shows this fear was misplaced: LVP is needed only for Theorem B' (the *shifted* LRC).  Their
Theorem A' (plain LRC, which is what `MSSGap7` needs) is proved in Section 3 alone, by an
unconditional, self-contained induction that never invokes LVP.  This removes what looked like the
main obstruction.

**Correction 2 (the actual MSS induction step, precisely).**  For a primitive `v : Fin n → ℤ`
(`n = 7` here) forming the lonely-runner zonotope `Z_v ⊆ ℝ^{n-1}` with generators `u_1,…,u_n` and
center `x_v`, MSS's Theorem A' proof runs as follows (their §3.2, using their Lemma 2.5, Prop 2.7,
Theorem 3.1, Lemma 3.6):
1. `K_v := (n-1)/(n+1) · (Z_v - x_v)`.  A counterexample would need `K_v ∩ (x_v + ℤ^{n-1}) ≠ ∅`.
2. If `|Z_v ∩ ℤ^{n-1}| = ∑_S v_S > C(n+1,2)^{n-1}` (their point-count identity, Cor. 2.3, proved
   via Thm 2.1 + Lemma 2.2), pigeonhole (Lemma 2.5) gives `λ₁(Z_v - Z_v) ≤ 1/C(n+1,2)`, hence
   (their eq. 3.7) `λ₁(K_v) ≤ 4/((n-1)n)`.
3. Let `w` be primitive attaining `λ₁(K_v)`.  Project `T` along `w` to `ℝ^{n-2}`.  **Theorem 3.1**
   (proved for *any* nonzero primitive `w`, not only the `λ₁`-minimizer — this is the part with a
   real, elementary proof, see below) says the image `T(Z_v)` contains, as a lattice translate, a
   lonely-runner zonotope `Z'` on `n-1` of `n^2` candidate generator sets (drop one generator, or
   merge two, `(3.2)`-`(3.4)`), with the *same* center `z ≡ T(x_v) mod ℤ^{n-2}`.
4. Apply the inductive hypothesis (LRC true for `n-1` runners, i.e. Conjecture A' in dimension
   `n-2`) to `Z'`, getting a point of `(n-2)/n · (Z' - z) ∩ (z + ℤ^{n-2})`.
5. **Lemma 3.6**: pull that point back along the line `a + ℝw` through `T⁻¹`; because `λ₁(K_v)` is
   small (step 2), the segment `K_v ∩ (a + ℝw)` has lattice length `≥ 1`, so it contains a point of
   `x_v + ℤ^{n-1}`, finishing the induction.

**Theorem 3.1's own proof (the part with real mathematical content).**  It is *not* a deep
covering-radius / geometry-of-numbers argument and does *not* need the general zonotope machinery.
Write `w = ∑ ρ_i u_i` and `p_i = (ρ_i, v_i) ∈ ℚ × ℤ` (Gale dual to `u_1,…,u_n,w`, Remark 3.5).
Choose the index `n-1` maximizing `ρ_i/v_i` and `n` minimizing it (these ratios are not all equal
since `w ≠ 0`).  Prop 3.3/3.4 compute the relevant candidate-generator-set volumes as exactly the
2×2 determinants `|ρ'_j ρ'_n; v'_j v'_n|` etc.  A short case split (`v_{n-1} = v_n` vs `≠`, using
only that the max ratio is *strictly* greater than the min ratio) shows `p_{n-1} - p_n` (or
`p_{n-1} + p_n`) is not parallel to any `p_k`, which is exactly the nondegeneracy Theorem 3.1
needs.  This is elementary rational-number comparison plus 2×2 determinant algebra; see Route (b)
in `MSSGap7`'s status note below for how this maps onto our `e5b_staircase`.

**Comparison with `e5b_staircase`.**  Our staircase lemma is a direct, time-language
reimplementation of MSS's *whole* points-2/3 pipeline above (Cor 2.3's point count, Lemma 2.5's
pigeonhole, and the resulting short-vector bound) done in `v`-coordinates instead of `u`/zonotope
coordinates, with the *same* modulus `l = C(8,2) = 28` and the *same* pigeonhole cardinality
inequality `∑ v_i > l^{n-1} = 28^6` (MSS: `∑_S v_S > C(n+1,2)^{n-1}`, and `∑_S v_S ≥ ∑_i v_i`).
Structurally the correspondence is: our `z` plays the role of MSS's `ρ` (via `p_i = (ρ_i, v_i)`,
our `z` is `ρ` after clearing denominators by `l`), our `σ` is the common offset making
`z_i / v_i ≈ σ / l` the shared approximate ratio, and "`z` not parallel to `v`" is exactly "not
all `ρ_i / v_i` equal", which is what MSS needs so `p_1,…,p_n` are not all parallel (their proof
of Theorem 3.1, second paragraph). This match was checked structurally (same cardinality argument,
same role for each piece of data) but the precise *quantitative* correspondence — whether our
exact bound `|l z_i - σ v_i| ≤ 1` is strong enough to reproduce MSS's `λ₁(K_v) ≤ 4/((n-1)n)` via
the Gale/`ρ`-`z` dictionary, which is what Lemma 3.6's "lattice length ≥ 1" step actually consumes
— was NOT independently re-derived line by line here; it is HEURISTIC, supported only by the
structural match, not by a checked derivation. That quantitative check is the concrete next atom
(see below).

STATUS of `MSSGap7`: still CONJECTURE (unproved), but no longer a blind reconstruction from
summaries — it now reflects the paper's actual Theorem A' induction, read in full, with the LVP
false alarm removed. It is carried as a `Prop` hypothesis, not a `sorry`, so this module stays
sorry-free. -/

/-- The MSS gap at `n = 7` (hypothesis; see the section docstring). -/
def MSSGap7 : Prop :=
  (∀ u : Fin (5 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((5 : ℝ) + 2) ≤ ML u) →
  ∀ v : Fin 7 → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 →
    (∃ z : Fin 7 → ℤ, ∃ σ : ℚ, (∃ a b, z a * v b ≠ z b * v a) ∧
      ∀ i, |(28 : ℚ) * z i - σ * v i| ≤ 1) →
    1 / 8 ≤ ML v

/-- **E5-sum from the gap (bridge, sorry-free).**  Same statement as `EightPlan.e5_sum_STUB_SUPERSEDED` with the
LRC6 hypothesis inlined and `MSSGap7` as an extra hypothesis. -/
theorem e5_sum_of_gap (hgap : MSSGap7)
    (h6 : ∀ u : Fin (5 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((5 : ℝ) + 2) ≤ ML u)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1)
    (hsum : (28 : ℤ) ^ 6 < ∑ i, v i) : 1 / 8 ≤ ML v :=
  hgap h6 v hv hg (e5b_staircase hv hg 28 (by norm_num) (by simpa using hsum))

/-! ## MSS Theorem 3.1, atom E5 continued (2026-09-25)

CORRECTED 2026-09-25 against a direct read of arXiv:2411.06903v2, Section 3 (Prop 3.3, Prop 3.4,
Remark 3.5, proof of Theorem 3.1, proof of Theorem A'), pages 13-17 of the PDF, read in full this
session (the earlier reconstruction in `thm31_notes.md` was explicitly flagged there as unchecked
against the actual proof text; this pass does that check and finds two errors).

**Error 1 (index picker).** `thm31_notes.md` guessed `a := argmax_i (l z_i - σ v_i)`,
`b := argmin_i (l z_i - σ v_i)`. The paper's actual picker (proof of Theorem 3.1, using
`p_i = (ρ_i, v_i)`, `w = Σ ρ_i u_i`) is `a := argmax_i (ρ_i / v_i)`, `b := argmin_i (ρ_i / v_i)`,
i.e. argmax/argmin of the *ratio*, not of the affine form `l z_i - σ v_i`. Since
`l z_i - σ v_i = l v_i (z_i/v_i - σ/l)`, the extra factor `v_i` can reorder indices relative to
ranking by `z_i / v_i` alone, so the two pickers are not the same rule. `vprime` below still takes
`a b` as free parameters (as before), so this error affects only the informal dictionary in the
notes file, not `vprime`'s Lean statement; it is recorded here so the eventual index-picker lemma
(still not formalized, see below) uses the right ranking.

**Error 2 (merge rule; this DOES change `vprime`).** `thm31_notes.md` guessed a case split: merge
`v_a + v_b` when `v_a = v_b`, else "drop" `|v_a - v_b|`. Reading Prop 3.3/3.4 and the proof of
Theorem 3.1 directly: the "drop" (`|v_a - v_b|`) branch corresponds to zonotope type (3.4) and is
never invoked by the theorem's proof. The proof shows, in all three subcases
(`v_{n-1} = v_n`, `v_{n-1} > v_n`, `v_{n-1} < v_n`), that `p_{n-1} - p_n` (or `p_n - p_{n-1}`) is
not parallel to any `p_k`; by Prop 3.4's sign correspondence between the zonotope's combined
generator (`u'_{n-1} ± u'_n`) and the volume formula's opposite sign (`∓`), a nonzero
`p_{n-1} - p_n`-type determinant certifies the `u'_{n-1} + u'_n` (SUM/merge) zonotope, type (3.3),
not the difference type (3.4). So the merge is **always** the sum `v_a + v_b`, unconditionally;
there is no case split on whether `v_a = v_b`. `vprime` is corrected accordingly below.

The center-match and Lemma 3.6 pullback (the steps needed to actually discharge `MSSGap7`) are
still not attempted here and remain `sorry` in `bridge31`. -/

/-- The MSS Theorem 3.1 projection `v ↦ v'` at `n = 7 → n = 6`: drop index `b`, and replace the
surviving image of `a` by the merged value `v a + v b` (MSS's zonotope type `(3.3)`, the unique
branch used by the proof of Theorem 3.1 — see the corrected docstring above; the earlier
conditional "drop `|v_a - v_b|` else merge" was wrong, checked against the paper). -/
def vprime (v : Fin 7 → ℤ) (a b : Fin 7) : Fin 6 → ℤ :=
  fun i =>
    let j := Fin.succAbove b i
    if j = a then v a + v b else v j

/-- **PROVED** (pure arithmetic): `vprime` is positive whenever `v` is, for any choice of `a b`.
No geometric content. -/
theorem vprime_pos (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (a b : Fin 7) :
    ∀ i, 0 < vprime v a b i := by
  intro i
  unfold vprime
  set j := Fin.succAbove b i with hj
  by_cases hja : j = a
  · simp only [hja, if_true]
    have := hv a
    have := hv b
    linarith
  · simp only [hja, if_false]
    exact hv j

/- CORRECTION on the earlier "no argmax in Mathlib" claim: that grep targeted the wrong path
(`a local cache directory`, a stale/unrelated cache). The project's actual Mathlib checkout is
`lean-mathlib/.lake/packages/mathlib`, and it DOES have the needed existence lemmas:
`Finset.exists_max_image` and `Finset.exists_min_image`
(`Mathlib/Data/Finset/Max.lean:525,531`), stated as
`∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` (resp. `≥`) for `s : Finset β` nonempty, `f : β → α`,
`[LinearOrder α]`. `extremalPair` below uses these directly on the ratio `(z i : ℚ) / (v i : ℚ)`
(the correct ranking per the correction above, not `l * z i - σ * v i`) to produce `a b`
existentially, per Mathlib's own (non-computable, `Classical.choice`-backed) style rather than a
computable argmax function. -/

/-- **Existence of the extremal pair** (index picker, per the corrected docstring above):
`a` maximizes and `b` minimizes the ratio `z i / v i` over `Fin 7`. Existential, not computable
(uses `Finset.exists_max_image`/`exists_min_image`), matching how Mathlib itself provides argmax. -/
theorem extremalPair (v z : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) :
    ∃ a, (∀ i, (z i : ℚ) / v i ≤ (z a : ℚ) / v a) ∧
      ∃ b, (∀ i, (z b : ℚ) / v b ≤ (z i : ℚ) / v i) := by
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 7))
      (fun i => (z i : ℚ) / v i) Finset.univ_nonempty
  obtain ⟨b, -, hb⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin 7))
      (fun i => (z i : ℚ) / v i) Finset.univ_nonempty
  exact ⟨a, fun i => ha i (Finset.mem_univ i), b, fun i => hb i (Finset.mem_univ i)⟩

/-- **Dream lemma (CONJECTURE, `sorry`).** The actual content MSS's Theorem 3.1 + Lemma 3.6
supply: the 6-runner instance `vprime v a b` (for the extremal pair) inherits `1/7 ≤ ML` from
the induction hypothesis, and pulls back to `1/8 ≤ ML v`. Center-matching (MSS's `z ≡ T(x_v)`) and
the pullback inequality (margin loss `1/7 → 1/8`) are NOT proved; this states exactly the two gaps
left open by `thm31_notes.md` §4 items 2-3, with item 1 (index rule) absorbed into the statement
via explicit `a b` parameters and `vprime` so the remaining `sorry` is only the bridge, not the
construction.

SESSION NOTE 2026-09-25 (see (development file, not part of this archive) for the full derivation):
re-read arXiv:2411.06903 Section 3 in full (Lemma 3.2, Prop 3.3/3.4, Remark 3.5, proof of
Theorem 3.1, proof of Theorem A' including the full proof of Lemma 3.6). Finding: Lemma 3.6's
pullback has NO numeric margin loss between `1/(n+1)` and `1/(n+2)` (the `1/7 -> 1/8` step is
exact, not lossy) -- but the pullback is stated and proved entirely in terms of the zonotope
`Z_v ⊆ ℝ^{n-1}`, its explicit generators `u_1,…,u_n` (Def 1.4, eq 1.2), the projection
`T : ℝ^{n-1} → ℝ^{n-2}` with `ker T = ℝw` for `w` a vector attaining `λ₁(K_v)`, and points in
these real zonotopes (`a`, `a'`, `b`). None of this apparatus (zonotopes as geometric objects,
successive minima, the map `T`) exists anywhere in this file or in `MaxLoneliness.lean`, which
work purely in scalar-time language (`ML`, `gap`). Center-matching (task item (a)) was checked
to be structurally impossible to state in `v/z/σ/t` terms alone: recovering a lattice point of
`Z_v` from a scalar time `t` requires inverting the linear map built from `u_1,…,u_n`, which is
not determined by `v` (only by `v` together with a choice of basis of `v^⊥ ∩ ℤ^7`, Prop 1.5).
Closing `bridge31` therefore requires first formalizing MSS's zonotope/successive-minima
apparatus (items (i)-(v) in the notes file) as new Lean machinery, not a short bridge proof in
the current vocabulary. Kill criterion fired for "prove bridge31 directly, scalar-time-only"
(I18); state DEAD for that approach. The statement below is left as originally written (not
mutated) to avoid repeating the guess-then-correct pattern already hit twice on this atom today;
a future session reopening this needs the new zonotope machinery, not a patched signature. -/
theorem bridge31 (v z : Fin 7 → ℤ) (σ : ℚ) (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1)
    (hz : ∃ a b, z a * v b ≠ z b * v a) (hbound : ∀ i, |(28 : ℚ) * z i - σ * v i| ≤ 1)
    (a b : Fin 7)
    (h6 : ∀ u : Fin (5 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((5 : ℝ) + 2) ≤ ML u) :
    1 / 8 ≤ ML v := by
  sorry

end LRSpectrumFull.EightMSS
