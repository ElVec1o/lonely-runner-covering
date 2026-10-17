/-
# The Riesz product mass identity (the analytic core of Bedert's Lemma 4.1)

Bedert (arXiv:2511.16636, Lemma 4.1) proves `ML(V) ≫ 1/√n` for a dissociated set `V` by
building the **Riesz product** `R(x) = ∏_{v∈V}(1 − cos 2πvx) ≥ 0` and showing its mean is
`1` (its constant Fourier coefficient `R̂(0) = 1`), so `dμ = R dx` is a probability measure.

This file formalizes that **mean-value identity** in its exact discrete form — for a
`StrongFree` (= dissociated) tuple `v` and any modulus `Q` exceeding `∑|v_i|`, the average of
the Riesz product over the `Q`-point grid is exactly `1`:
  `∑_{j<Q} ∏_i (1 − cos(2π v_i j / Q)) = Q`.
The proof is pure discrete Fourier analysis: expand the product over `{−1,0,1}^m`, and root-of-
unity orthogonality kills every frequency `∑ε_i v_i` except the one dissociativity forces to be
unique — the empty combination, contributing `1`.

**Scope (honest):** this is the *mass* half of Lemma 4.1. The `1/√n` lower bound itself needs
the second-moment / Fourier-coefficient decay step, which carries only an *implicit* constant in
Bedert and is not formalized here. So this does not by itself discharge the Separation
hypothesis `separation_of_riesz.hR` (which needs an explicit constant `≥ 1/4`). It is the
machine-checked analytic foundation on which such a bound would be built.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import LRSpectrumFull.Delta2FreeGrowth

open Complex Real

namespace LRSpectrumFull

/-- **Discrete root-of-unity orthogonality.**  The `Q`-point exponential sum at integer
frequency `k` is `Q` when `Q ∣ k` and `0` otherwise. -/
theorem exp_geom_sum (Q : ℕ) (hQ : 0 < Q) (k : ℤ) :
    ∑ j ∈ Finset.range Q, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑j / ↑Q)
      = if (Q : ℤ) ∣ k then (Q : ℂ) else 0 := by
  have hQC : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  set w : ℂ := Complex.exp (2 * ↑π * Complex.I * ↑k / ↑Q) with hw
  have h2pi : (2 : ℂ) * ↑π * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hwj : ∀ j : ℕ, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑j / ↑Q) = w ^ j := by
    intro j
    rw [hw, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hwj j)]
  by_cases hdvd : (Q : ℤ) ∣ k
  · have hw1 : w = 1 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hw, hc]
      rw [show (2 : ℂ) * ↑π * Complex.I * ↑((Q : ℤ) * c) / ↑Q = ↑c * (2 * ↑π * Complex.I) by
        push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I c
    rw [hw1]
    simp [hdvd]
  · have hwne : w ≠ 1 := by
      rw [hw, Ne, Complex.exp_eq_one_iff]
      rintro ⟨n, hn⟩
      apply hdvd
      refine ⟨n, ?_⟩
      have hkC : (k : ℂ) = ↑Q * ↑n := by
        have e : (2 * ↑π * Complex.I) * (k : ℂ) = (2 * ↑π * Complex.I) * (↑Q * ↑n) := by
          have hh := hn
          rw [div_eq_iff hQC] at hh
          linear_combination hh
        exact mul_left_cancel₀ h2pi e
      exact_mod_cast hkC
    have hwQ : w ^ Q = 1 := by
      rw [hw, ← Complex.exp_nat_mul]
      rw [show (↑Q : ℂ) * (2 * ↑π * Complex.I * ↑k / ↑Q) = ↑k * (2 * ↑π * Complex.I) by
        field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [geom_sum_eq hwne, hwQ]
    simp [hdvd]

/-- **Dirichlet-kernel bound** (sub-lemma B, analytic core).  A partial `Q`-point exponential sum
at a frequency `k` not divisible by `Q` is bounded by `2/‖1 − e(k/Q)‖`, independently of the number
of terms `N`.  This is the decay that beats the trivial `N`; with a coprime modulus the bad-set
Fourier coefficient `1̂_{Bᵢ}` reduces to exactly such a sum. -/
theorem exp_partial_sum_bound (Q N : ℕ) (hQ0 : 0 < Q) (k : ℤ) (hk : ¬ (Q : ℤ) ∣ k) :
    ‖∑ j ∈ Finset.range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑j / ↑Q)‖
      ≤ 2 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑k / ↑Q)‖ := by
  have hQC : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0.ne'
  set w : ℂ := Complex.exp (2 * ↑π * Complex.I * ↑k / ↑Q) with hw
  have h2pi : (2 : ℂ) * ↑π * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hwj : ∀ j : ℕ, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑j / ↑Q) = w ^ j := by
    intro j; rw [hw, ← Complex.exp_nat_mul]; congr 1; ring
  have hwne : w ≠ 1 := by
    rw [hw, Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    apply hk
    refine ⟨n, ?_⟩
    have hkC : (k : ℂ) = ↑Q * ↑n := by
      have e : (2 * ↑π * Complex.I) * (k : ℂ) = (2 * ↑π * Complex.I) * (↑Q * ↑n) := by
        have hh := hn; rw [div_eq_iff hQC] at hh; linear_combination hh
      exact mul_left_cancel₀ h2pi e
    exact_mod_cast hkC
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, show (2 * ↑π * Complex.I * ↑k / ↑Q : ℂ) = ↑(2 * π * (k : ℝ) / Q) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
  rw [Finset.sum_congr rfl (fun j _ => hwj j), geom_sum_eq hwne, norm_div, norm_sub_rev 1 w,
    div_le_div_iff_of_pos_right hpos]
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hwnorm]; norm_num

/-- **`Q`-periodicity of the grid exponential** (Bedert §4, sub-lemma B-connect).  `e(a/Q)` depends
only on `a mod Q`.  This is the value-matching step of the Fourier reindexing: under the coprime
bijection `j ↦ v_i·j mod Q =: r`, the summand `e(k·j/Q)` equals `e(m·r/Q)` because `m·r ≡ k·j (Q)`. -/
theorem exp_qperiodic (Q : ℕ) (hQ0 : 0 < Q) (a b : ℤ) (h : (Q : ℤ) ∣ (a - b)) :
    Complex.exp (2 * ↑π * Complex.I * ↑a / ↑Q) = Complex.exp (2 * ↑π * Complex.I * ↑b / ↑Q) := by
  have hQC : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0.ne'
  obtain ⟨t, ht⟩ := h
  have haz : a = b + (Q : ℤ) * t := by linarith
  have hab : (a : ℂ) = (b : ℂ) + (Q : ℂ) * (t : ℂ) := by exact_mod_cast haz
  rw [hab, show (2 * ↑π * Complex.I * ((b : ℂ) + ↑Q * ↑t) / ↑Q : ℂ)
      = 2 * ↑π * Complex.I * ↑b / ↑Q + ↑t * (2 * ↑π * Complex.I) by field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Modular inverse** (Bedert §4, sub-lemma B-connect step ②.1).  A coprime residue has an
inverse mod `Q`: `∃ w, Q ∣ (a·w − 1)`, i.e. `a·w ≡ 1 (Q)`.  This `w` is the multiplier of the
inverse bijection `r ↦ w·r mod Q` in the Fourier reindexing.  Via Bézout (`Int.gcd_eq_gcd_ab`). -/
theorem exists_mod_inverse (a : ℤ) (Q : ℕ) (hcop : Nat.Coprime a.natAbs Q) :
    ∃ w : ℤ, (Q : ℤ) ∣ (a * w - 1) := by
  have hg : Int.gcd a (Q : ℤ) = 1 := by simpa [Int.gcd, Int.natAbs_natCast, Nat.Coprime] using hcop
  have hbez := Int.gcd_eq_gcd_ab a (Q : ℤ)
  rw [hg, Nat.cast_one] at hbez
  exact ⟨Int.gcdA a (Q : ℤ), -Int.gcdB a (Q : ℤ), by linear_combination -hbez⟩

/-- The `{−1,0,1}` representative of each of the three terms in a Riesz factor. -/
private def reps : Fin 3 → ℤ := fun t => if t = 1 then 1 else if t = 2 then -1 else 0

/-- The complex coefficient of each of the three terms in a Riesz factor. -/
private noncomputable def rcoeff : Fin 3 → ℂ := fun t => if t = 0 then 1 else -1 / 2

private lemma reps_zero : reps 0 = 0 := rfl
private lemma reps_one : reps 1 = 1 := rfl
private lemma reps_two : reps 2 = -1 := rfl
private lemma rcoeff_zero : rcoeff 0 = 1 := rfl
private lemma rcoeff_one : rcoeff 1 = -1 / 2 := rfl
private lemma rcoeff_two : rcoeff 2 = -1 / 2 := rfl

private lemma reps_abs_le (t : Fin 3) : (reps t).natAbs ≤ 1 := by
  fin_cases t <;> decide

private lemma reps_mem (t : Fin 3) : reps t = -1 ∨ reps t = 0 ∨ reps t = 1 := by
  fin_cases t <;> decide

private lemma reps_eq_zero {t : Fin 3} (h : reps t = 0) : t = 0 := by
  fin_cases t <;> simp_all [reps]

/-- Each Riesz factor `1 − cos(2π v x)` expands as a three-term exponential sum indexed by
`{−1,0,1}`. -/
private lemma riesz_factor (Q : ℕ) (v : ℤ) (j : ℕ) :
    (1 - Complex.cos (2 * ↑π * ↑v * ↑j / ↑Q))
      = ∑ t : Fin 3, rcoeff t * Complex.exp (2 * ↑π * Complex.I * ↑(reps t * v) * ↑j / ↑Q) := by
  rw [Fin.sum_univ_three, Complex.cos, reps_zero, reps_one, reps_two,
    rcoeff_zero, rcoeff_one, rcoeff_two]
  have e0 : (2 * ↑π * Complex.I * ↑((0 : ℤ) * v) * ↑j / ↑Q : ℂ) = 0 := by push_cast; ring
  have e1 : (2 * ↑π * Complex.I * ↑((1 : ℤ) * v) * ↑j / ↑Q : ℂ)
      = (2 * ↑π * ↑v * ↑j / ↑Q) * Complex.I := by push_cast; ring
  have e2 : (2 * ↑π * Complex.I * ↑((-1 : ℤ) * v) * ↑j / ↑Q : ℂ)
      = -(2 * ↑π * ↑v * ↑j / ↑Q) * Complex.I := by push_cast; ring
  rw [e0, e1, e2, Complex.exp_zero]
  ring

/-- **The Riesz product mass identity** (the mean-value core of Bedert's Lemma 4.1).
For a `StrongFree` (dissociated) tuple `v` and any modulus `Q > ∑|v_i|`, the average of the
Riesz product `∏(1 − cos 2πv_i x)` over the `Q`-point grid is exactly `1`:
`∑_{j<Q} ∏_i (1 − cos(2π v_i j/Q)) = Q`.  The mass concentrates entirely on the empty
frequency, which dissociativity makes the unique vanishing `{−1,0,1}`-combination. -/
theorem riesz_mass (m : ℕ) (v : Fin m → ℤ) (hv : StrongFree v) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) = (Q : ℂ) := by
  set F : (Fin m → Fin 3) → ℤ := fun σ => ∑ i, reps (σ i) * v i with hF
  -- expand each factor, distribute the product over sections `σ : Fin m → Fin 3`
  have step1 : ∀ j ∈ Finset.range Q,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)))
        = ∑ σ : Fin m → Fin 3,
            (∏ i, rcoeff (σ i)) * Complex.exp (2 * ↑π * Complex.I * ↑(F σ) * ↑j / ↑Q) := by
    intro j _
    rw [Finset.prod_congr rfl (fun i _ => riesz_factor Q (v i) j), Finset.prod_univ_sum,
      show (Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Fin 3)))
        = Finset.univ from Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [hF]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  -- pull the coefficient out of the `j`-sum and apply orthogonality
  have step2 : ∀ σ : Fin m → Fin 3,
      (∑ j ∈ Finset.range Q, (∏ i, rcoeff (σ i)) * Complex.exp (2 * ↑π * Complex.I * ↑(F σ) * ↑j / ↑Q))
        = (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ F σ then (Q : ℂ) else 0) := by
    intro σ
    rw [← Finset.mul_sum, exp_geom_sum Q hQ0 (F σ)]
  rw [Finset.sum_congr rfl (fun σ _ => step2 σ)]
  -- only the zero section survives; it contributes `Q`
  rw [Finset.sum_eq_single_of_mem (fun _ => (0 : Fin 3)) (Finset.mem_univ _)]
  · have hF0 : F (fun _ => (0 : Fin 3)) = 0 := by
      simp only [hF, reps_zero, zero_mul, Finset.sum_const_zero]
    rw [hF0]
    simp [rcoeff_zero]
  · intro σ _ hσ
    have hbound : (F σ).natAbs < Q := by
      calc (F σ).natAbs = (∑ i, reps (σ i) * v i).natAbs := by rw [hF]
        _ ≤ ∑ i, (reps (σ i) * v i).natAbs := Int.natAbs_sum_le _ _
        _ = ∑ i, (reps (σ i)).natAbs * (v i).natAbs := by
              apply Finset.sum_congr rfl; intro i _; rw [Int.natAbs_mul]
        _ ≤ ∑ i, (v i).natAbs := Finset.sum_le_sum (fun i _ => by
              have h1 : (reps (σ i)).natAbs ≤ 1 := reps_abs_le _
              calc (reps (σ i)).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
                _ = (v i).natAbs := one_mul _)
        _ < Q := hQ
    have hnotdvd : ¬ (Q : ℤ) ∣ F σ := by
      intro hd
      have habs : |F σ| < (Q : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast hbound
      have hF0 : F σ = 0 := Int.eq_zero_of_abs_lt_dvd hd habs
      apply hσ
      funext i
      exact reps_eq_zero (hv (fun i => reps (σ i)) (fun i => reps_mem (σ i)) hF0 i)
    rw [if_neg hnotdvd, mul_zero]

/-- **The Riesz mass, before evaluating dissociativity.**  The discrete Riesz mass equals the
signed section sum `∑_σ (∏ rcoeff)·[Q if Q ∣ F(σ) else 0]`, where `F(σ) = ∑ reps(σ_i) v_i`.
This is the algebraic core shared by `riesz_mass` (only `σ=0` survives) and
`riesz_mass_single_relation` (three sections survive). -/
theorem riesz_mass_expand (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = ∑ σ : Fin m → Fin 3,
          (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ (∑ i, reps (σ i) * v i) then (Q : ℂ) else 0) := by
  set F : (Fin m → Fin 3) → ℤ := fun σ => ∑ i, reps (σ i) * v i with hF
  have step1 : ∀ j ∈ Finset.range Q,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)))
        = ∑ σ : Fin m → Fin 3,
            (∏ i, rcoeff (σ i)) * Complex.exp (2 * ↑π * Complex.I * ↑(F σ) * ↑j / ↑Q) := by
    intro j _
    rw [Finset.prod_congr rfl (fun i _ => riesz_factor Q (v i) j), Finset.prod_univ_sum,
      show (Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Fin 3)))
        = Finset.univ from Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [hF]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_sum, exp_geom_sum Q hQ0 (F σ)]

/-- The section realizing a `{−1,0,1}`-combination `c` (`reps ∘ sect c = c`). -/
private def sect {m : ℕ} (c : Fin m → ℤ) : Fin m → Fin 3 :=
  fun i => if c i = 1 then 1 else if c i = -1 then 2 else 0

private lemma reps_injective : Function.Injective (reps : Fin 3 → ℤ) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [reps]

private lemma reps_sect {m : ℕ} (c : Fin m → ℤ) (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (i : Fin m) : reps (sect c i) = c i := by
  simp only [sect]; rcases hc i with h | h | h <;> simp [h, reps_zero, reps_one, reps_two]

private lemma sect_reps {m : ℕ} (σ : Fin m → Fin 3) : sect (fun i => reps (σ i)) = σ := by
  funext i; apply reps_injective
  rw [reps_sect (fun i => reps (σ i)) (fun i => reps_mem (σ i)) i]

private lemma sect_inj {m : ℕ} (c c' : Fin m → ℤ) (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hc' : ∀ i, c' i = -1 ∨ c' i = 0 ∨ c' i = 1) (h : sect c = sect c') : c = c' := by
  funext i; rw [← reps_sect c hc i, ← reps_sect c' hc' i, h]

private lemma rcoeff_sect {m : ℕ} (c : Fin m → ℤ) (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (i : Fin m) : rcoeff (sect c i) = if c i = 0 then (1 : ℂ) else -1 / 2 := by
  simp only [sect]; rcases hc i with h | h | h <;> simp [h, rcoeff_zero, rcoeff_one, rcoeff_two]

/-- **Riesz mass for a single-relation tuple.**  If the only vanishing `{−1,0,1}`-combinations
of `v` are `0` and `±r` (`r ≠ 0`, `∑ r_i v_i = 0`), then the Riesz mass is
`Q·(1 + 2·∏_i(r_i = 0 ? 1 : −½))` — positive, and `= 3Q/4` when `r` has support `3`.  So
relations do **not** kill the Riesz weight; the mass degrades only with the *number* of
relations.  (Overturns the earlier "no Riesz weight for relations" reading.) -/
theorem riesz_mass_single_relation (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) (r : Fin m → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * v i) = 0)
    (hchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c = r ∨ c = -r) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * (1 + 2 * ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2)) := by
  classical
  set F : (Fin m → Fin 3) → ℤ := fun σ => ∑ i, reps (σ i) * v i with hF
  have h0mem : ∀ i, (0 : Fin m → ℤ) i = -1 ∨ (0 : Fin m → ℤ) i = 0 ∨ (0 : Fin m → ℤ) i = 1 :=
    fun i => Or.inr (Or.inl rfl)
  have hrneg : ∀ i, (-r) i = -1 ∨ (-r) i = 0 ∨ (-r) i = 1 := by
    intro i; rcases hrmem i with h | h | h <;> simp [Pi.neg_apply, h]
  -- the mass on a section equals the combination sum
  have hFsect : ∀ (c : Fin m → ℤ), (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) →
      F (sect c) = ∑ i, c i * v i := fun c hc => by
    simp only [hF]; exact Finset.sum_congr rfl (fun i _ => by rw [reps_sect c hc i])
  have hF_0 : F (sect (0 : Fin m → ℤ)) = 0 := by rw [hFsect 0 h0mem]; simp
  have hF_r : F (sect r) = 0 := by rw [hFsect r hrmem]; exact hrel
  have hF_nr : F (sect (-r)) = 0 := by
    rw [hFsect (-r) hrneg, Finset.sum_congr rfl (fun i _ => by
      simp only [Pi.neg_apply]; ring : ∀ i ∈ Finset.univ, (-r) i * v i = -(r i * v i))]
    rw [Finset.sum_neg_distrib, hrel, neg_zero]
  -- bound and divisibility
  have hbound : ∀ σ : Fin m → Fin 3, (F σ).natAbs < Q := by
    intro σ
    calc (F σ).natAbs = (∑ i, reps (σ i) * v i).natAbs := by rw [hF]
      _ ≤ ∑ i, (reps (σ i) * v i).natAbs := Int.natAbs_sum_le _ _
      _ = ∑ i, (reps (σ i)).natAbs * (v i).natAbs := by
            apply Finset.sum_congr rfl; intro i _; rw [Int.natAbs_mul]
      _ ≤ ∑ i, (v i).natAbs := Finset.sum_le_sum (fun i _ => by
            have h1 : (reps (σ i)).natAbs ≤ 1 := reps_abs_le _
            calc (reps (σ i)).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
              _ = (v i).natAbs := one_mul _)
      _ < Q := hQ
  have hdvd_iff : ∀ σ : Fin m → Fin 3, (Q : ℤ) ∣ F σ ↔ F σ = 0 := by
    intro σ
    refine ⟨fun hd => ?_, fun h => by rw [h]; exact dvd_zero _⟩
    have habs : |F σ| < (Q : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbound σ
    exact Int.eq_zero_of_abs_lt_dvd hd habs
  -- surviving sections
  have hfilter : (Finset.univ.filter (fun σ : Fin m → Fin 3 => F σ = 0))
      = {sect 0, sect r, sect (-r)} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hFσ
      have hc := hchar (fun i => reps (σ i)) (fun i => reps_mem (σ i)) hFσ
      have hsr := (sect_reps σ).symm
      rcases hc with h | h | h
      · exact Or.inl (by rw [h] at hsr; exact hsr)
      · exact Or.inr (Or.inl (by rw [h] at hsr; exact hsr))
      · exact Or.inr (Or.inr (by rw [h] at hsr; exact hsr))
    · rintro (h | h | h) <;> subst h
      · exact hF_0
      · exact hF_r
      · exact hF_nr
  -- distinctness of the three sections
  have d0r : sect (0 : Fin m → ℤ) ≠ sect r := fun h => hr0 (sect_inj 0 r h0mem hrmem h).symm
  have d0nr : sect (0 : Fin m → ℤ) ≠ sect (-r) := fun h =>
    hr0 (neg_eq_zero.mp (sect_inj 0 (-r) h0mem hrneg h).symm)
  have drnr : sect r ≠ sect (-r) := by
    intro h
    apply hr0
    have hrr := sect_inj r (-r) hrmem hrneg h
    funext i
    have hi := congrFun hrr i
    simp only [Pi.neg_apply] at hi
    simp only [Pi.zero_apply]
    omega
  -- assemble
  rw [riesz_mass_expand m v Q hQ0,
    Finset.sum_congr rfl (fun σ _ => show (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ F σ then (Q : ℂ) else 0)
        = if F σ = 0 then (∏ i, rcoeff (σ i)) * (Q : ℂ) else 0 from by
      by_cases hd : (Q : ℤ) ∣ F σ
      · rw [if_pos hd, if_pos ((hdvd_iff σ).mp hd)]
      · rw [if_neg hd, if_neg (fun h => hd ((hdvd_iff σ).mpr h))]; ring),
    ← Finset.sum_filter, hfilter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d0r, d0nr⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact drnr), Finset.sum_singleton]
  rw [show (∏ i, rcoeff (sect (0 : Fin m → ℤ) i)) = 1 from
        Finset.prod_eq_one (fun i _ => by rw [rcoeff_sect 0 h0mem i]; simp),
      show (∏ i, rcoeff (sect r i)) = ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2) from
        Finset.prod_congr rfl (fun i _ => rcoeff_sect r hrmem i),
      show (∏ i, rcoeff (sect (-r) i)) = ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2) from
        Finset.prod_congr rfl (fun i _ => by
          rw [rcoeff_sect (-r) hrneg i]; simp [Pi.neg_apply, neg_eq_zero])]
  ring

/-- **Riesz mass for a two-relation tuple** (two *disjoint-support* relations).  If the only
vanishing `{−1,0,1}`-combinations of `v` are the nine `reps a·r + reps b·s` (`a,b ∈ {−1,0,1}`) —
the `ℤ`-span of two `±1`-relations `r, s` with disjoint support — then the Riesz mass **factorizes**:
`Q·(1 + 2P_r)(1 + 2P_s)` with `P_r = ∏(r_i = 0 ? 1 : −½)`.  Equivalently `M_r·M_s/Q`: disjoint
relations are independent, so their masses multiply.  For support-`3` `r, s` this is `9Q/16`.
The nine-term section sum **separates** as a product over `{−1,0,1}²`, so no pairwise-distinctness
enumeration is needed — one injectivity of `(a,b) ↦ sect(reps a·r + reps b·s)` and `sum_mul_sum`. -/
theorem riesz_mass_two_relations (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (r s : Fin m → ℤ) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1)
    (hsmem : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hrel_r : (∑ i, r i * v i) = 0) (hrel_s : (∑ i, s i * v i) = 0)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * ((1 + 2 * ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
                 * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2))) := by
  classical
  set F : (Fin m → Fin 3) → ℤ := fun σ => ∑ i, reps (σ i) * v i with hF
  set combo : Fin 3 × Fin 3 → (Fin m → ℤ) := fun ab i => reps ab.1 * r i + reps ab.2 * s i
    with hcombo
  -- the nine combinations are `{−1,0,1}`-valued (disjoint support)
  have hcombo_mem : ∀ ab i, combo ab i = -1 ∨ combo ab i = 0 ∨ combo ab i = 1 := by
    intro ab i
    simp only [hcombo]
    rcases hdisj i with h | h
    · rw [h, mul_zero, zero_add]
      rcases reps_mem ab.2 with h2 | h2 | h2 <;> rcases hsmem i with hs | hs | hs <;>
        simp [h2, hs]
    · rw [h, mul_zero, add_zero]
      rcases reps_mem ab.1 with h1 | h1 | h1 <;> rcases hrmem i with hr | hr | hr <;>
        simp [h1, hr]
  -- every combination section vanishes under `F`
  have hF_combo : ∀ ab, F (sect (combo ab)) = 0 := by
    intro ab
    have hrw : F (sect (combo ab)) = ∑ i, combo ab i * v i :=
      Finset.sum_congr rfl (fun i _ => by rw [reps_sect (combo ab) (hcombo_mem ab) i])
    rw [hrw]
    have hexp : ∀ i ∈ Finset.univ, combo ab i * v i
        = reps ab.1 * (r i * v i) + reps ab.2 * (s i * v i) := by
      intro i _; simp only [hcombo]; ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hrel_r, hrel_s, mul_zero, mul_zero, add_zero]
  -- the mass bound and divisibility test (shared with the single-relation proof)
  have hbound : ∀ σ : Fin m → Fin 3, (F σ).natAbs < Q := by
    intro σ
    calc (F σ).natAbs = (∑ i, reps (σ i) * v i).natAbs := by rw [hF]
      _ ≤ ∑ i, (reps (σ i) * v i).natAbs := Int.natAbs_sum_le _ _
      _ = ∑ i, (reps (σ i)).natAbs * (v i).natAbs := by
            apply Finset.sum_congr rfl; intro i _; rw [Int.natAbs_mul]
      _ ≤ ∑ i, (v i).natAbs := Finset.sum_le_sum (fun i _ => by
            have h1 : (reps (σ i)).natAbs ≤ 1 := reps_abs_le _
            calc (reps (σ i)).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
              _ = (v i).natAbs := one_mul _)
      _ < Q := hQ
  have hdvd_iff : ∀ σ : Fin m → Fin 3, (Q : ℤ) ∣ F σ ↔ F σ = 0 := by
    intro σ
    refine ⟨fun hd => ?_, fun h => by rw [h]; exact dvd_zero _⟩
    have habs : |F σ| < (Q : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbound σ
    exact Int.eq_zero_of_abs_lt_dvd hd habs
  -- surviving sections are exactly the image of the nine combinations
  have hfilter2 : (Finset.univ.filter (fun σ : Fin m → Fin 3 => F σ = 0))
      = Finset.image (fun ab => sect (combo ab)) Finset.univ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hFσ
      obtain ⟨α, β, hα, hβ, hab⟩ := hchar2 (fun i => reps (σ i)) (fun i => reps_mem (σ i)) hFσ
      obtain ⟨a, ha⟩ : ∃ a : Fin 3, reps a = α := by
        rcases hα with h | h | h
        · exact ⟨2, by rw [reps_two, h]⟩
        · exact ⟨0, by rw [reps_zero, h]⟩
        · exact ⟨1, by rw [reps_one, h]⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin 3, reps b = β := by
        rcases hβ with h | h | h
        · exact ⟨2, by rw [reps_two, h]⟩
        · exact ⟨0, by rw [reps_zero, h]⟩
        · exact ⟨1, by rw [reps_one, h]⟩
      have hcab : combo (a, b) = fun i => α * r i + β * s i := by
        funext i
        show reps a * r i + reps b * s i = α * r i + β * s i
        rw [ha, hb]
      exact ⟨(a, b), by rw [hcab, ← hab]; exact sect_reps σ⟩
    · rintro ⟨ab, rfl⟩; exact hF_combo ab
  -- injectivity of `(a,b) ↦ sect(combo a b)`
  have hcombo_inj : Function.Injective (fun ab : Fin 3 × Fin 3 => sect (combo ab)) := by
    intro ab ab' hEq
    have hc : combo ab = combo ab' := sect_inj _ _ (hcombo_mem ab) (hcombo_mem ab') hEq
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hr0 (funext hcon)
    obtain ⟨i', hi'⟩ : ∃ i', s i' ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hs0 (funext hcon)
    have hsi : s i = 0 := (hdisj i).resolve_left hi
    have hri' : r i' = 0 := (hdisj i').resolve_right hi'
    have ea : reps ab.1 = reps ab'.1 := by
      have hci := congrFun hc i
      simp only [hcombo, hsi, mul_zero, add_zero] at hci
      rcases hrmem i with h | h | h
      · rw [h] at hci; simpa using hci
      · exact absurd h hi
      · rw [h] at hci; simpa using hci
    have eb : reps ab.2 = reps ab'.2 := by
      have hci := congrFun hc i'
      simp only [hcombo, hri', mul_zero, zero_add] at hci
      rcases hsmem i' with h | h | h
      · rw [h] at hci; simpa using hci
      · exact absurd h hi'
      · rw [h] at hci; simpa using hci
    exact Prod.ext (reps_injective ea) (reps_injective eb)
  -- factorization of each section's `rcoeff` product over the disjoint supports
  have hfact : ∀ ab, (∏ i, rcoeff (sect (combo ab) i))
      = (if reps ab.1 = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
        * (if reps ab.2 = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)) := by
    intro ab
    rw [Finset.prod_congr rfl (fun i _ => rcoeff_sect (combo ab) (hcombo_mem ab) i)]
    have hpt : ∀ i, (if combo ab i = 0 then (1 : ℂ) else -1 / 2)
        = (if r i = 0 then (1 : ℂ) else if reps ab.1 = 0 then 1 else -1 / 2)
          * (if s i = 0 then (1 : ℂ) else if reps ab.2 = 0 then 1 else -1 / 2) := by
      intro i
      rcases hdisj i with h | h
      · have hc : combo ab i = reps ab.2 * s i := by simp only [hcombo, h, mul_zero, zero_add]
        rw [hc, if_pos h, one_mul]
        rcases reps_mem ab.2 with h2 | h2 | h2 <;> rcases hsmem i with hs | hs | hs <;>
          rw [h2, hs] <;> norm_num
      · have hc : combo ab i = reps ab.1 * r i := by simp only [hcombo, h, mul_zero, add_zero]
        rw [hc, if_pos h, mul_one]
        rcases reps_mem ab.1 with h1 | h1 | h1 <;> rcases hrmem i with hr | hr | hr <;>
          rw [h1, hr] <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib]
    have hfr : (∏ i, (if r i = 0 then (1 : ℂ) else if reps ab.1 = 0 then 1 else -1 / 2))
        = if reps ab.1 = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2) := by
      by_cases ha : reps ab.1 = 0
      · conv_rhs => rw [if_pos ha]
        refine Finset.prod_eq_one fun i _ => ?_
        rcases eq_or_ne (r i) 0 with h | h
        · rw [if_pos h]
        · rw [if_neg h, if_pos ha]
      · conv_rhs => rw [if_neg ha]
        refine Finset.prod_congr rfl fun i _ => ?_
        rcases eq_or_ne (r i) 0 with h | h
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, if_neg ha]
    have hfs : (∏ i, (if s i = 0 then (1 : ℂ) else if reps ab.2 = 0 then 1 else -1 / 2))
        = if reps ab.2 = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2) := by
      by_cases hb : reps ab.2 = 0
      · conv_rhs => rw [if_pos hb]
        refine Finset.prod_eq_one fun i _ => ?_
        rcases eq_or_ne (s i) 0 with h | h
        · rw [if_pos h]
        · rw [if_neg h, if_pos hb]
      · conv_rhs => rw [if_neg hb]
        refine Finset.prod_congr rfl fun i _ => ?_
        rcases eq_or_ne (s i) 0 with h | h
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, if_neg hb]
    rw [hfr, hfs]
  -- assemble: expand, restrict to the surviving image, separate the product
  rw [riesz_mass_expand m v Q hQ0,
    Finset.sum_congr rfl (fun σ _ => show (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ F σ then (Q : ℂ) else 0)
        = if F σ = 0 then (∏ i, rcoeff (σ i)) * (Q : ℂ) else 0 from by
      by_cases hd : (Q : ℤ) ∣ F σ
      · rw [if_pos hd, if_pos ((hdvd_iff σ).mp hd)]
      · rw [if_neg hd, if_neg (fun h => hd ((hdvd_iff σ).mpr h))]; ring),
    ← Finset.sum_filter, hfilter2, Finset.sum_image (fun ab _ ab' _ h => hcombo_inj h)]
  simp only [hfact]
  rw [← Finset.sum_mul]
  -- the nine-term section sum separates as a product over `{−1,0,1}²`
  have hSA : (∑ a : Fin 3,
        if reps a = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
      = 1 + 2 * ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2) := by
    rw [Fin.sum_univ_three, reps_zero, reps_one, reps_two, if_pos rfl,
      if_neg (by norm_num : (1 : ℤ) ≠ 0), if_neg (by norm_num : (-1 : ℤ) ≠ 0)]; ring
  have hSB : (∑ b : Fin 3,
        if reps b = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2))
      = 1 + 2 * ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2) := by
    rw [Fin.sum_univ_three, reps_zero, reps_one, reps_two, if_pos rfl,
      if_neg (by norm_num : (1 : ℤ) ≠ 0), if_neg (by norm_num : (-1 : ℤ) ≠ 0)]; ring
  have hsep : (∑ ab : Fin 3 × Fin 3,
        (if reps ab.1 = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
          * (if reps ab.2 = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)))
      = (1 + 2 * ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
        * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)) := by
    calc (∑ ab : Fin 3 × Fin 3,
            (if reps ab.1 = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
              * (if reps ab.2 = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)))
        = ∑ a : Fin 3, ∑ b : Fin 3,
            (if reps a = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
              * (if reps b = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)) :=
          Fintype.sum_prod_type _
      _ = (∑ a : Fin 3,
            if reps a = 0 then (1 : ℂ) else ∏ i, (if r i = 0 then (1 : ℂ) else -1 / 2))
          * (∑ b : Fin 3,
            if reps b = 0 then (1 : ℂ) else ∏ i, (if s i = 0 then (1 : ℂ) else -1 / 2)) :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ = _ := by rw [hSA, hSB]
  rw [hsep]; ring

/-- The section-frequency `F σ = ∑ reps(σ_i) v_i` is `Q`-divisible iff it vanishes, when
`Q > ∑|v_i|`.  (The mass bound shared by every section-sum argument.) -/
private lemma F_dvd_iff {m : ℕ} (v : Fin m → ℤ) (Q : ℕ)
    (hQ : (∑ i, (v i).natAbs) < Q) (σ : Fin m → Fin 3) :
    (Q : ℤ) ∣ (∑ i, reps (σ i) * v i) ↔ (∑ i, reps (σ i) * v i) = 0 := by
  refine ⟨fun hd => ?_, fun h => by rw [h]; exact dvd_zero _⟩
  have hbound : (∑ i, reps (σ i) * v i).natAbs < Q := by
    calc (∑ i, reps (σ i) * v i).natAbs
        ≤ ∑ i, (reps (σ i) * v i).natAbs := Int.natAbs_sum_le _ _
      _ = ∑ i, (reps (σ i)).natAbs * (v i).natAbs := by
            apply Finset.sum_congr rfl; intro i _; rw [Int.natAbs_mul]
      _ ≤ ∑ i, (v i).natAbs := Finset.sum_le_sum (fun i _ => by
            have h1 : (reps (σ i)).natAbs ≤ 1 := reps_abs_le _
            calc (reps (σ i)).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
              _ = (v i).natAbs := one_mul _)
      _ < Q := hQ
  have habs : |∑ i, reps (σ i) * v i| < (Q : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hbound
  exact Int.eq_zero_of_abs_lt_dvd hd habs

/-- **The Riesz mass is the relation enumerator at `-1/2`.**  For `Q > ∑|v_i|`,
`∑_j ∏_i (1 − cos 2π v_i j/Q) = Q · ∑_{σ : F σ = 0} ∏_i rcoeff(σ_i)`, the sum ranging over the
`{−1,0,1}`-relations `σ` (as `Fin 3` sections).  Since `∏ rcoeff(σ_i) = (−1/2)^{|supp σ|}`, the
right side is `Q·f(−1/2)` with `f(t)=∑_σ t^{|supp σ|}` the relation size enumerator. -/
theorem riesz_mass_sections (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * ∑ σ ∈ Finset.univ.filter (fun σ : Fin m → Fin 3 => (∑ i, reps (σ i) * v i) = 0),
          ∏ i, rcoeff (σ i) := by
  rw [riesz_mass_expand m v Q hQ0]
  rw [Finset.sum_congr rfl (fun σ _ =>
      show (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ (∑ i, reps (σ i) * v i) then (Q : ℂ) else 0)
        = if (∑ i, reps (σ i) * v i) = 0 then (∏ i, rcoeff (σ i)) * (Q : ℂ) else 0 from by
      by_cases hd : (Q : ℤ) ∣ (∑ i, reps (σ i) * v i)
      · rw [if_pos hd, if_pos ((F_dvd_iff v Q hQ σ).mp hd)]
      · rw [if_neg hd, if_neg (fun h => hd ((F_dvd_iff v Q hQ σ).mpr h))]; ring)]
  rw [← Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

/-- **The sum of leave-one-out masses, as an enumerator.**  `∑ᵢ Mᵢ = Q·∑_{σ:Fσ=0} c(σ)·∏rcoeff(σ)`
where `c(σ) = #{i : σ_i = 0} = n − |supp σ|`.  With `riesz_mass_sections` (`M = Q·∑ ∏rcoeff`) this
gives `∑Mᵢ/M = n + ½ f'(−1/2)/f(−1/2)` — the identity behind every `∑Mᵢ = (k+2)M`, `(k+3)M`,
`(n+T)M` computation. -/
theorem riesz_sumMi_sections (m : ℕ) (v : Fin (m + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ i : Fin (m + 1), ∑ j ∈ Finset.range Q, ∏ j' : Fin m,
        (1 - Complex.cos (2 * ↑π * ↑(v (i.succAbove j')) * ↑j / ↑Q))
      = (Q : ℂ) * ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin (m + 1) → Fin 3 => (∑ i, reps (σ i) * v i) = 0),
          (((Finset.univ.filter (fun i => σ i = 0)).card : ℕ) : ℂ) * ∏ i, rcoeff (σ i) := by
  -- each leave-one-out mass is the subfamily enumerator, reindexed to full sections with `σ i = 0`
  have hstep1 : ∀ i : Fin (m + 1),
      (∑ j ∈ Finset.range Q, ∏ j' : Fin m,
          (1 - Complex.cos (2 * ↑π * ↑(v (i.succAbove j')) * ↑j / ↑Q)))
        = (Q : ℂ) * ∑ σ ∈ Finset.univ.filter
            (fun σ : Fin (m + 1) → Fin 3 => (∑ i', reps (σ i') * v i') = 0 ∧ σ i = 0),
            ∏ i', rcoeff (σ i') := by
    intro i
    have hQ' : (∑ j', (v (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    rw [riesz_mass_sections m (fun j' => v (i.succAbove j')) Q hQ0 hQ']
    congr 1
    refine Finset.sum_nbij' (fun σ' => i.insertNth 0 σ') (fun σ => fun j' => σ (i.succAbove j'))
      (f := fun σ' => ∏ i', rcoeff (σ' i')) (g := fun σ => ∏ i', rcoeff (σ i'))
      ?_ ?_ ?_ ?_ ?_
    · intro σ' hσ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ' ⊢
      refine ⟨?_, by simp⟩
      rw [Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, reps_zero, zero_mul,
        zero_add]
      exact hσ'
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      have hF := hσ.1
      rw [Fin.sum_univ_succAbove (fun w => reps (σ w) * v w) i] at hF
      simp only [hσ.2, reps_zero, zero_mul, zero_add] at hF
      exact hF
    · intro σ' _
      funext j'
      simp
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      funext w
      refine Fin.succAboveCases i ?_ (fun j' => ?_) w
      · simp [hσ.2]
      · simp
    · intro σ' _
      dsimp only
      rw [Fin.prod_univ_succAbove _ i]
      simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, rcoeff_zero]
  rw [Finset.sum_congr rfl (fun i _ => hstep1 i), ← Finset.mul_sum]
  congr 1
  -- rewrite each `A ∧ (σ i = 0)` filter as an `if`, swap sums, count `#{i : σ i = 0}`
  have key : ∀ i : Fin (m + 1),
      (∑ σ ∈ Finset.univ.filter (fun σ : Fin (m + 1) → Fin 3 =>
          (∑ i', reps (σ i') * v i') = 0 ∧ σ i = 0), ∏ i', rcoeff (σ i'))
        = ∑ σ ∈ Finset.univ.filter (fun σ : Fin (m + 1) → Fin 3 =>
            (∑ i', reps (σ i') * v i') = 0),
            (if σ i = 0 then (∏ i', rcoeff (σ i')) else 0) := by
    intro i
    rw [← Finset.filter_filter (fun σ : Fin (m + 1) → Fin 3 => (∑ i', reps (σ i') * v i') = 0)
        (fun σ => σ i = 0), Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **The bad-set enumerator** (the setup for the sharp constant / Bedert §4).  Over *any* index
set `S` — in particular the bad set `Bᵢ = {j : ‖v_i j/Q‖ < δ}` — the Riesz weight expands as
`∑_{j∈S} ∏(1−cos) = ∑_σ (∏rcoeff(σ))·D_S(F σ)` where `D_S(k) = ∑_{j∈S} e(2πi k j/Q)` is the
discrete Fourier coefficient of `S` at the section frequency `F σ = ∑ reps(σ_i) v_i`.  This is
`riesz_mass_expand` *before* orthogonality collapses the `j`-sum; the exact bad-set weight is thus
a relation enumerator paired with `D_{Bᵢ}` (the interval-indicator Fourier coefficients).  Bounding
`D_{Bᵢ}` is the one remaining analytic step toward the sharp Lonely-Runner constant. -/
theorem riesz_badset_expand (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (S : Finset ℕ) :
    ∑ j ∈ S, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = ∑ σ : Fin m → Fin 3, (∏ i, rcoeff (σ i)) *
          ∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, reps (σ i) * v i) * ↑j / ↑Q) := by
  have step1 : ∀ j : ℕ,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)))
        = ∑ σ : Fin m → Fin 3, (∏ i, rcoeff (σ i)) *
            Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, reps (σ i) * v i) * ↑j / ↑Q) := by
    intro j
    rw [Finset.prod_congr rfl (fun i _ => riesz_factor Q (v i) j), Finset.prod_univ_sum,
      show (Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Fin 3)))
        = Finset.univ from Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl (fun j _ => step1 j), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun σ _ => (Finset.mul_sum _ _ _).symm)

/-- **Coprime-modulus reduction** (the tractable case of the bad-set Fourier bound).  For any
velocity tuple there is a *prime* modulus `Q > ∑|v_i|`.  Being prime and larger than every `|v_i|`,
it is coprime to each nonzero `v_i`, so `j ↦ v_i j mod Q` is a bijection of `ℤ/Q` and the bad set
`B_i = {j : ‖v_i j/Q‖ < δ}` is a single arithmetic progression — its indicator's Fourier coefficient
`D_{B_i}(k)` is then a genuine Dirichlet kernel `sin((2R+1)πm/Q)/sin(πm/Q)`, the clean case in which
sub-lemma B (decay of `1̂_{B_i}`) is a classical geometric-sum estimate.  The Riesz mass identity
holds for any modulus exceeding `∑|v_i|`, so this choice is without loss of generality. -/
theorem exists_coprime_modulus (m : ℕ) (v : Fin m → ℤ) :
    ∃ Q : ℕ, Q.Prime ∧ (∑ i, (v i).natAbs) < Q ∧
      ∀ i, (v i).natAbs ≠ 0 → Nat.Coprime (v i).natAbs Q := by
  obtain ⟨Q, hQge, hQp⟩ := Nat.exists_infinite_primes ((∑ i, (v i).natAbs) + 1)
  refine ⟨Q, hQp, by omega, fun i hi => ?_⟩
  have hlt : (v i).natAbs < Q := by
    have hle : (v i).natAbs ≤ ∑ i', (v i').natAbs :=
      Finset.single_le_sum (f := fun i' => (v i').natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  exact (hQp.coprime_iff_not_dvd.mpr
    (fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h) (not_le.mpr hlt))).symm

end LRSpectrumFull

-- axiom audit
#print axioms LRSpectrumFull.exp_geom_sum
#print axioms LRSpectrumFull.riesz_mass
#print axioms LRSpectrumFull.riesz_mass_expand
#print axioms LRSpectrumFull.riesz_mass_single_relation
#print axioms LRSpectrumFull.riesz_mass_sections
#print axioms LRSpectrumFull.riesz_sumMi_sections
#print axioms LRSpectrumFull.riesz_badset_expand
#print axioms LRSpectrumFull.exists_coprime_modulus
#print axioms LRSpectrumFull.exp_partial_sum_bound
#print axioms LRSpectrumFull.exp_qperiodic
#print axioms LRSpectrumFull.exists_mod_inverse

namespace LRSpectrumFull

/-- **The general web mass identity** (T1-W).  For any tuple `v` and any modulus `Q > ∑|v_i|`,
with `W` the set of *nonzero* vanishing `{−1,0,1}`-combinations (the web), the Riesz mass is

  `∑_{j<Q} ∏_i (1 − cos 2πv_i j/Q) = Q·(1 + ∑_{c ∈ W} ∏_i (c_i = 0 ? 1 : −½))`.

`riesz_mass` is the case `W = ∅`; `riesz_mass_single_relation` the case `W = {r, −r}`.  Every
section of the expansion survives exactly when its combination vanishes, and the surviving
sections are the image of `W ∪ {0}` under `sect`. -/
theorem riesz_mass_web (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (W : Finset (Fin m → ℤ)) (hW0 : (0 : Fin m → ℤ) ∉ W)
    (hWmem : ∀ c ∈ W, ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hWrel : ∀ c ∈ W, (∑ i, c i * v i) = 0)
    (hWchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c ∈ W) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * (1 + ∑ c ∈ W, ∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2)) := by
  classical
  set F : (Fin m → Fin 3) → ℤ := fun σ => ∑ i, reps (σ i) * v i with hF
  have h0mem : ∀ i, (0 : Fin m → ℤ) i = -1 ∨ (0 : Fin m → ℤ) i = 0 ∨ (0 : Fin m → ℤ) i = 1 :=
    fun i => Or.inr (Or.inl rfl)
  have hFsect : ∀ (c : Fin m → ℤ), (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) →
      F (sect c) = ∑ i, c i * v i := fun c hc => by
    simp only [hF]; exact Finset.sum_congr rfl (fun i _ => by rw [reps_sect c hc i])
  have hF_0 : F (sect (0 : Fin m → ℤ)) = 0 := by rw [hFsect 0 h0mem]; simp
  have hbound : ∀ σ : Fin m → Fin 3, (F σ).natAbs < Q := by
    intro σ
    calc (F σ).natAbs = (∑ i, reps (σ i) * v i).natAbs := by rw [hF]
      _ ≤ ∑ i, (reps (σ i) * v i).natAbs := Int.natAbs_sum_le _ _
      _ = ∑ i, (reps (σ i)).natAbs * (v i).natAbs := by
            apply Finset.sum_congr rfl; intro i _; rw [Int.natAbs_mul]
      _ ≤ ∑ i, (v i).natAbs := Finset.sum_le_sum (fun i _ => by
            have h1 : (reps (σ i)).natAbs ≤ 1 := reps_abs_le _
            calc (reps (σ i)).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := by gcongr
              _ = (v i).natAbs := one_mul _)
      _ < Q := hQ
  have hdvd_iff : ∀ σ : Fin m → Fin 3, (Q : ℤ) ∣ F σ ↔ F σ = 0 := by
    intro σ
    refine ⟨fun hd => ?_, fun h => by rw [h]; exact dvd_zero _⟩
    have habs : |F σ| < (Q : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbound σ
    exact Int.eq_zero_of_abs_lt_dvd hd habs
  -- surviving sections: the image of `W ∪ {0}` under `sect`
  have hfilter : (Finset.univ.filter (fun σ : Fin m → Fin 3 => F σ = 0))
      = insert (sect (0 : Fin m → ℤ)) (W.image sect) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · intro hFσ
      have hsr := (sect_reps σ).symm
      rcases hWchar (fun i => reps (σ i)) (fun i => reps_mem (σ i)) hFσ with h | h
      · exact Or.inl (by rw [h] at hsr; exact hsr)
      · exact Or.inr ⟨fun i => reps (σ i), h, (sect_reps σ)⟩
    · rintro (h | ⟨c, hcW, h⟩)
      · subst h; exact hF_0
      · subst h; rw [hFsect c (hWmem c hcW)]; exact hWrel c hcW
  have h0notin : sect (0 : Fin m → ℤ) ∉ W.image sect := by
    intro hmem
    obtain ⟨c, hcW, hc⟩ := Finset.mem_image.mp hmem
    have := sect_inj c 0 (hWmem c hcW) h0mem hc
    exact hW0 (this ▸ hcW)
  have hinj : ∀ c ∈ W, ∀ c' ∈ W, sect c = sect c' → c = c' := fun c hc c' hc' h =>
    sect_inj c c' (hWmem c hc) (hWmem c' hc') h
  rw [riesz_mass_expand m v Q hQ0,
    Finset.sum_congr rfl (fun σ _ =>
      show (∏ i, rcoeff (σ i)) * (if (Q : ℤ) ∣ F σ then (Q : ℂ) else 0)
        = if F σ = 0 then (∏ i, rcoeff (σ i)) * (Q : ℂ) else 0 from by
      by_cases hd : (Q : ℤ) ∣ F σ
      · rw [if_pos hd, if_pos ((hdvd_iff σ).mp hd)]
      · rw [if_neg hd, if_neg (fun h => hd ((hdvd_iff σ).mpr h))]; ring),
    ← Finset.sum_filter, hfilter, Finset.sum_insert h0notin, Finset.sum_image hinj]
  rw [show (∏ i, rcoeff (sect (0 : Fin m → ℤ) i)) = 1 from
      Finset.prod_eq_one (fun i _ => by rw [rcoeff_sect 0 h0mem i]; simp)]
  rw [Finset.sum_congr rfl (fun c hc =>
      show (∏ i, rcoeff (sect c i)) * (Q : ℂ)
        = (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2)) * (Q : ℂ) from by
      rw [Finset.prod_congr rfl (fun i _ => rcoeff_sect c (hWmem c hc) i)])]
  rw [← Finset.sum_mul]
  ring

end LRSpectrumFull
