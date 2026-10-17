/-
# `T` disjoint relations: the Riesz mass factorization

For `T` pairwise-disjoint `±1`-relations whose combinations exhaust the vanishing
`{−1,0,1}`-combinations, the Riesz mass factorizes:
`M = Q·∏_t (1 + 2·∏_i wt(R_t i))` — for `T` support-`3` relations, `M = Q(3/4)^T`.

The section machinery of `Delta2RieszMass` is private, so this file re-derives a
public expansion indexed by the `{−1,0,1}`-combinations themselves
(`riesz_mass_expand_pub`), which is also the natural index set for the `T`-fold
evaluation: the surviving combinations are exactly the image of
`α ↦ ∑_t α_t R_t` over `α ∈ {−1,0,1}^T`, the weight factorizes pointwise across
the disjoint supports, and the `α`-sum separates into a product of `T`
three-term sums.
-/
import LRSpectrumFull.Delta2RieszMass
import LRSpectrumFull.Delta2SeparationWindow

namespace LRSpectrumFull

local notation "π" => Real.pi

/-- The three-term exponential expansion of a single Riesz factor, indexed by
`{−1,0,1} ⊆ ℤ`. -/
private lemma cos_factor_pub (z : ℂ) :
    1 - Complex.cos z
      = ∑ a ∈ ({-1, 0, 1} : Finset ℤ),
          (if a = 0 then (1 : ℂ) else -1 / 2) * Complex.exp ((a : ℂ) * z * Complex.I) := by
  have hset : ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) := rfl
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [if_neg (by decide : ¬ (-1 : ℤ) = 0), if_pos rfl, if_neg (by decide : ¬ (1 : ℤ) = 0)]
  rw [show ((-1 : ℤ) : ℂ) * z * Complex.I = (-z) * Complex.I by push_cast; ring,
    show ((0 : ℤ) : ℂ) * z * Complex.I = 0 by push_cast; ring,
    show ((1 : ℤ) : ℂ) * z * Complex.I = z * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.exp_zero, Complex.cos_neg, Complex.sin_neg]
  ring

/-- **Public Riesz mass expansion**, indexed by `{−1,0,1}`-combinations: the mass
is the signed sum over combinations `c` of `∏ wt(c_i)` times `Q·[Q ∣ ∑ c_i v_i]`. -/
theorem riesz_mass_expand_pub (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
          (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2))
            * (if (Q : ℤ) ∣ (∑ i, c i * v i) then (Q : ℂ) else 0) := by
  have step1 : ∀ j ∈ Finset.range Q,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)))
        = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
            (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2))
              * Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, c i * v i) * ↑j / ↑Q) := by
    intro j _
    rw [Finset.prod_congr rfl
      (fun i _ => cos_factor_pub (2 * ↑π * ↑(v i) * ↑j / ↑Q)), Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum, exp_geom_sum Q hQ0 (∑ i, c i * v i)]

set_option maxHeartbeats 1000000 in
/-- **The Riesz mass for `T` pairwise-disjoint relations.**  If the vanishing
`{−1,0,1}`-combinations of `v` are exactly the `{−1,0,1}`-span of `T`
pairwise-disjoint nonzero relations `R_t`, the mass factorizes:
`M = Q·∏_t (1 + 2·∏_i wt(R_t i))`. -/
theorem riesz_mass_disjoint (m T : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (R : Fin T → Fin m → ℤ)
    (hmem : ∀ t i, R t i = -1 ∨ R t i = 0 ∨ R t i = 1)
    (hrel : ∀ t, (∑ i, R t i * v i) = 0)
    (hne : ∀ t, ∃ i, R t i ≠ 0)
    (hdisj : ∀ t t', t ≠ t' → ∀ i, R t i = 0 ∨ R t' i = 0)
    (hchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        ∃ α : Fin T → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
          c = fun i => ∑ t, α t * R t i) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
  classical
  rw [riesz_mass_expand_pub m v Q hQ0]
  -- helpers: at each runner at most one relation is active
  have hzero : ∀ (α : Fin T → ℤ) (i : Fin m), (∀ t, R t i = 0) →
      (∑ t, α t * R t i) = 0 :=
    fun α i h => Finset.sum_eq_zero fun t _ => by rw [h t, mul_zero]
  have hsingle : ∀ (α : Fin T → ℤ) (i : Fin m) (t₀ : Fin T), R t₀ i ≠ 0 →
      (∑ t, α t * R t i) = α t₀ * R t₀ i := by
    intro α i t₀ h0
    rw [Finset.sum_eq_single t₀]
    · intro t _ hne'
      rcases hdisj t t₀ hne' i with h | h
      · rw [h, mul_zero]
      · exact absurd h h0
    · intro h; exact absurd (Finset.mem_univ t₀) h
  -- the combination map and its pairing
  have hφrel : ∀ α : Fin T → ℤ, (∑ i, (∑ t, α t * R t i) * v i) = 0 := by
    intro α
    have h1 : ∀ i : Fin m, (∑ t, α t * R t i) * v i = ∑ t, α t * (R t i * v i) := by
      intro i; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun t _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    have h2 : ∑ i, α t * (R t i * v i) = α t * ∑ i, R t i * v i := by
      rw [Finset.mul_sum]
    rw [h2, hrel t, mul_zero]
  have hφmem : ∀ α : Fin T → ℤ, α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)) →
      (fun i => ∑ t, α t * R t i) ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)) := by
    intro α hα
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : ∀ t, R t i = 0
    · rw [hzero α i hi]; decide
    · push_neg at hi
      obtain ⟨t₀, ht₀⟩ := hi
      rw [hsingle α i t₀ ht₀]
      have hαt := (Fintype.mem_piFinset.mp hα) t₀
      have hR := hmem t₀ i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hαt ⊢
      rcases hαt with h | h | h <;> rcases hR with h' | h' | h' <;>
        first
          | (exact absurd h' ht₀)
          | (rw [h, h']; norm_num)
  -- combinations with vanishing pairing are exactly the image of the span map
  have habs : ∀ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
      (Q : ℤ) ∣ (∑ i, c i * v i) → (∑ i, c i * v i) = 0 := by
    intro c hc hdvd
    have hb : (∑ i, c i * v i).natAbs ≤ ∑ i, (v i).natAbs := by
      calc (∑ i, c i * v i).natAbs ≤ ∑ i, (c i * v i).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ i, (v i).natAbs := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Int.natAbs_mul]
            have hci : (c i).natAbs ≤ 1 := by
              have := (Fintype.mem_piFinset.mp hc) i
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h | h <;> simp [h]
            calc (c i).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs :=
                  Nat.mul_le_mul_right _ hci
              _ = (v i).natAbs := one_mul _
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_le_of_lt hb hQ
  have hset : (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
        (fun c => (Q : ℤ) ∣ (∑ i, c i * v i))
      = (Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ))).image
          (fun α => fun i => ∑ t, α t * R t i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hc, hdvd⟩
      have h0 : (∑ i, c i * v i) = 0 := habs c hc hdvd
      have hcmem : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1 := by
        intro i
        have := (Fintype.mem_piFinset.mp hc) i
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      obtain ⟨α, hαmem, hceq⟩ := hchar c hcmem h0
      refine ⟨α, ?_, hceq.symm⟩
      rw [Fintype.mem_piFinset]
      intro t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hαmem t
    · rintro ⟨α, hα, rfl⟩
      exact ⟨hφmem α hα, by rw [hφrel α]; exact dvd_zero _⟩
  have hinj : ∀ α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
      ∀ α' ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
      (fun i => ∑ t, α t * R t i) = (fun i => ∑ t, α' t * R t i) → α = α' := by
    intro α _ α' _ h
    funext t
    obtain ⟨i, hi⟩ := hne t
    have hh := congrFun h i
    simp only at hh
    rw [hsingle α i t hi, hsingle α' i t hi] at hh
    exact mul_right_cancel₀ hi hh
  -- restrict to the surviving combinations, reindex, and factorize
  have hsplit : ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
        (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2))
          * (if (Q : ℤ) ∣ (∑ i, c i * v i) then (Q : ℂ) else 0)
      = ∑ c ∈ (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
          (fun c => (Q : ℤ) ∣ (∑ i, c i * v i)),
          (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2)) * (Q : ℂ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_ite, mul_zero]
  rw [hsplit, hset, Finset.sum_image hinj]
  -- pointwise weight factorization across the disjoint supports
  have hpoint : ∀ (α : Fin T → ℤ) (i : Fin m),
      (if (∑ t, α t * R t i) = 0 then (1 : ℂ) else -1 / 2)
        = ∏ t, (if α t * R t i = 0 then (1 : ℂ) else -1 / 2) := by
    intro α i
    by_cases hi : ∀ t, R t i = 0
    · rw [hzero α i hi, if_pos rfl]
      symm
      apply Finset.prod_eq_one
      intro t _
      rw [hi t, mul_zero, if_pos rfl]
    · push_neg at hi
      obtain ⟨t₀, ht₀⟩ := hi
      rw [hsingle α i t₀ ht₀]
      symm
      rw [Finset.prod_eq_single t₀]
      · intro t _ htne
        rcases hdisj t t₀ htne i with h | h
        · rw [h, mul_zero, if_pos rfl]
        · exact absurd h ht₀
      · intro h; exact absurd (Finset.mem_univ t₀) h
  have hcollapse : ∀ (α : Fin T → ℤ) (t : Fin T),
      (∏ i, (if α t * R t i = 0 then (1 : ℂ) else -1 / 2))
        = (if α t = 0 then (1 : ℂ) else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
    intro α t
    by_cases h0 : α t = 0
    · rw [if_pos h0]
      apply Finset.prod_eq_one
      intro i _
      rw [h0, zero_mul, if_pos rfl]
    · rw [if_neg h0]
      apply Finset.prod_congr rfl
      intro i _
      simp [mul_eq_zero, h0]
  have hweights : ∀ α : Fin T → ℤ,
      (∏ i, (if (∑ t, α t * R t i) = 0 then (1 : ℂ) else -1 / 2))
        = ∏ t, (if α t = 0 then (1 : ℂ)
            else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
    intro α
    calc (∏ i, (if (∑ t, α t * R t i) = 0 then (1 : ℂ) else -1 / 2))
        = ∏ i, ∏ t, (if α t * R t i = 0 then (1 : ℂ) else -1 / 2) :=
          Finset.prod_congr rfl fun i _ => hpoint α i
      _ = ∏ t, ∏ i, (if α t * R t i = 0 then (1 : ℂ) else -1 / 2) := Finset.prod_comm
      _ = ∏ t, (if α t = 0 then (1 : ℂ)
            else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) :=
          Finset.prod_congr rfl fun t _ => hcollapse α t
  -- separate the α-sum into a product of three-term sums
  have hsep : ∑ α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
        (∏ t, (if α t = 0 then (1 : ℂ)
          else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)))
      = ∏ t : Fin T, ∑ a ∈ ({-1, 0, 1} : Finset ℤ),
          (if a = 0 then (1 : ℂ) else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
    rw [Finset.prod_univ_sum]
  have hthree : ∀ t : Fin T,
      (∑ a ∈ ({-1, 0, 1} : Finset ℤ),
        (if a = 0 then (1 : ℂ) else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)))
      = 1 + 2 * ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2) := by
    intro t
    rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_neg (by decide : ¬ (-1 : ℤ) = 0), if_pos rfl, if_neg (by decide : ¬ (1 : ℤ) = 0)]
    ring
  calc ∑ α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
        (∏ i, (if (∑ t, α t * R t i) = 0 then (1 : ℂ) else -1 / 2)) * (Q : ℂ)
      = ∑ α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
        (∏ t, (if α t = 0 then (1 : ℂ)
          else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2))) * (Q : ℂ) := by
        apply Finset.sum_congr rfl
        intro α _
        rw [hweights α]
    _ = (∑ α ∈ Fintype.piFinset (fun _ : Fin T => ({-1, 0, 1} : Finset ℤ)),
        ∏ t, (if α t = 0 then (1 : ℂ)
          else ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2))) * (Q : ℂ) := by
        rw [Finset.sum_mul]
    _ = (∏ t : Fin T, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2))) * (Q : ℂ) := by
        rw [hsep, Finset.prod_congr rfl fun t _ => hthree t]
    _ = (Q : ℂ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
        ring

/-- Real form of `riesz_mass_disjoint`. -/
theorem riesz_mass_disjoint_real (m T : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (R : Fin T → Fin m → ℤ)
    (hmem : ∀ t i, R t i = -1 ∨ R t i = 0 ∨ R t i = 1)
    (hrel : ∀ t, (∑ i, R t i * v i) = 0)
    (hne : ∀ t, ∃ i, R t i ≠ 0)
    (hdisj : ∀ t t', t ≠ t' → ∀ i, R t i = 0 ∨ R t' i = 0)
    (hchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        ∃ α : Fin T → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
          c = fun i => ∑ t, α t * R t i) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)) := by
  have h := riesz_mass_disjoint m T v Q hQ0 hQ R hmem hrel hne hdisj hchar
  have hcs :
      ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hrhs :
      (((Q : ℝ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)) : ℝ) : ℂ)
      = (Q : ℂ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℂ) else -1 / 2)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_prod]
    congr 2
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs
    · exact Complex.ofReal_one
    · norm_num
  have cast_eq :
      ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = (((Q : ℝ) * ∏ t, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)) : ℝ) : ℂ) := by
    rw [hcs, h, hrhs]
  exact_mod_cast cast_eq

/-- Removing a runner outside every support keeps the `T`-relation character. -/
theorem disjoint_subfamily_passive {k T : ℕ} (u : Fin (k + 1) → ℤ)
    (R : Fin T → Fin (k + 1) → ℤ)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α : Fin T → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
          c = fun i => ∑ t, α t * R t i)
    (i₀ : Fin (k + 1)) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i₀.succAbove j')) = 0 →
      ∃ α : Fin T → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
        c' = fun j' => ∑ t, α t * R t (i₀.succAbove j') := by
  intro c' hc' hsum'
  let d : Fin (k + 1) → ℤ := i₀.insertNth 0 c'
  have hd_same : d i₀ = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i₀.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmemd : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i₀ ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove (fun w => d w * u w) i₀, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  obtain ⟨α, hα, hd_eq⟩ := hchar d hmemd hsumd
  refine ⟨α, hα, ?_⟩
  funext j'
  rw [← hd_succ j', hd_eq]

/-- Removing a runner inside the support of `R t₀` deletes exactly that relation:
the restricted family has the `T`-minus-one character over `t₀.succAbove`. -/
theorem disjoint_subfamily_active {k T' : ℕ} (u : Fin (k + 1) → ℤ)
    (R : Fin (T' + 1) → Fin (k + 1) → ℤ)
    (hdisj : ∀ t t', t ≠ t' → ∀ i, R t i = 0 ∨ R t' i = 0)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α : Fin (T' + 1) → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
          c = fun i => ∑ t, α t * R t i)
    (i₀ : Fin (k + 1)) (t₀ : Fin (T' + 1)) (ht₀ : R t₀ i₀ ≠ 0) :
    ∀ c' : Fin k → ℤ, (∀ j', c' j' = -1 ∨ c' j' = 0 ∨ c' j' = 1) →
      (∑ j', c' j' * u (i₀.succAbove j')) = 0 →
      ∃ α' : Fin T' → ℤ, (∀ s, α' s = -1 ∨ α' s = 0 ∨ α' s = 1) ∧
        c' = fun j' => ∑ s, α' s * R (t₀.succAbove s) (i₀.succAbove j') := by
  intro c' hc' hsum'
  let d : Fin (k + 1) → ℤ := i₀.insertNth 0 c'
  have hd_same : d i₀ = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i₀.succAbove j') = c' j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmemd : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
    intro w
    refine Fin.succAboveCases i₀ ?_ (fun j' => ?_) w
    · rw [hd_same]; right; left; rfl
    · rw [hd_succ]; exact hc' j'
  have hsumd : (∑ w, d w * u w) = 0 := by
    rw [Fin.sum_univ_succAbove (fun w => d w * u w) i₀, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum'
  obtain ⟨α, hα, hd_eq⟩ := hchar d hmemd hsumd
  have hα₀ : α t₀ = 0 := by
    have hcf := congrFun hd_eq i₀
    rw [hd_same] at hcf
    have hsing : (∑ t, α t * R t i₀) = α t₀ * R t₀ i₀ := by
      rw [Finset.sum_eq_single t₀]
      · intro t _ htne
        rcases hdisj t t₀ htne i₀ with h | h
        · rw [h, mul_zero]
        · exact absurd h ht₀
      · intro hmem'; exact absurd (Finset.mem_univ t₀) hmem'
    rw [hsing] at hcf
    rcases mul_eq_zero.mp hcf.symm with h | h
    · exact h
    · exact absurd h ht₀
  refine ⟨fun s => α (t₀.succAbove s), fun s => hα _, ?_⟩
  funext j'
  rw [← hd_succ j', hd_eq]
  show (∑ t, α t * R t (i₀.succAbove j'))
      = ∑ s, α (t₀.succAbove s) * R (t₀.succAbove s) (i₀.succAbove j')
  rw [Fin.sum_univ_succAbove (fun t => α t * R t (i₀.succAbove j')) t₀, hα₀, zero_mul,
    zero_add]

set_option maxHeartbeats 1000000 in
/-- **The Bridge, all disjoint-triple rungs at once.**  A `(k+1)`-runner family
carrying `T` pairwise-disjoint support-`3` relations — whose `{−1,0,1}`-span
exhausts the vanishing combinations — meets its Lonely-Runner floor for every
`k ≥ 15`, *uniformly in `T`*.  Mass `M = Q(3/4)^T`, leave-one-out masses
`M` (passive) or `Q(3/4)^{T−1}` (support runner), `∑Mᵢ = (k+1+T)M`, and the
sharp condition `(k+2+2T)(1 − cos 2πδ) < 2` holds at `δ = 1/(k+2)` since
`3T ≤ k+1` gives `δ(k+2+2T) ≤ 5/3` and `10π²/51 < 2`. -/
theorem bridge_disjoint_triples {k T : ℕ} (hk : 15 ≤ k)
    (u : Fin (k + 1) → ℤ)
    (R : Fin T → Fin (k + 1) → ℤ)
    (hmem : ∀ t i, R t i = -1 ∨ R t i = 0 ∨ R t i = 1)
    (hrel : ∀ t, (∑ i, R t i * u i) = 0)
    (hdisj : ∀ t t', t ≠ t' → ∀ i, R t i = 0 ∨ R t' i = 0)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α : Fin T → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
          c = fun i => ∑ t, α t * R t i)
    (hsupp : ∀ t, (Finset.univ.filter (fun i => R t i ≠ 0)).card = 3) :
    1 / ((k : ℝ) + 2) ≤ ML u := by
  classical
  set Q : ℕ := (∑ i, (u i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (u i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hne : ∀ t, ∃ i, R t i ≠ 0 := by
    intro t
    have hpos : 0 < (Finset.univ.filter (fun i => R t i ≠ 0)).card := by
      rw [hsupp t]; norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hPt : ∀ t, (∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)) = -1 / 8 := by
    intro t
    have hthis : (∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => R t i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _; by_cases h : R t i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp t]; norm_num
  have hprodT : (∏ t : Fin T, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)))
      = (3 / 4 : ℝ) ^ T := by
    calc (∏ t : Fin T, (1 + 2 * ∏ i, (if R t i = 0 then (1 : ℝ) else -1 / 2)))
        = ∏ _t : Fin T, ((3 : ℝ) / 4) :=
          Finset.prod_congr rfl fun t _ => by rw [hPt t]; norm_num
      _ = (3 / 4 : ℝ) ^ T := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * (3 / 4 : ℝ) ^ T := by
    rw [riesz_mass_disjoint_real (k + 1) T u Q hQ0 hQsum R hmem hrel hne hdisj hchar, hprodT]
  set Mi : Fin (k + 1) → ℝ := fun i =>
    if ∀ t, R t i = 0 then (Q : ℝ) * (3 / 4 : ℝ) ^ T
    else (Q : ℝ) * (3 / 4 : ℝ) ^ T * (4 / 3) with hMidef
  have hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (u (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i := by
    intro i
    have hv'sum : (∑ j', (u (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (u (i.succAbove j')).natAbs) ≤ ∑ w, (u w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (u w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    simp only [hMidef]
    by_cases hi : ∀ t, R t i = 0
    · rw [if_pos hi]
      have hrel' : ∀ t, (∑ j', R t (i.succAbove j') * u (i.succAbove j')) = 0 := by
        intro t
        have h := Fin.sum_univ_succAbove (fun w => R t w * u w) i
        rw [hi t, zero_mul, zero_add] at h
        rw [← h]; exact hrel t
      have hne' : ∀ t, ∃ j', R t (i.succAbove j') ≠ 0 := by
        intro t
        obtain ⟨w, hw⟩ := hne t
        have hwi : w ≠ i := fun h => hw (h ▸ hi t)
        obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hwi
        exact ⟨j', by rw [hj']; exact hw⟩
      rw [riesz_mass_disjoint_real k T (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun t j' => R t (i.succAbove j')) (fun t j' => hmem t _) hrel' hne'
        (fun t t' htne j' => hdisj t t' htne _)
        (disjoint_subfamily_passive u R hchar i)]
      congr 1
      calc (∏ t : Fin T, (1 + 2 * ∏ j', (if R t (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2)))
          = ∏ t : Fin T, (1 + 2 * ∏ w, (if R t w = 0 then (1 : ℝ) else -1 / 2)) := by
            refine Finset.prod_congr rfl fun t _ => ?_
            congr 2
            have hfull : (∏ w, (if R t w = 0 then (1 : ℝ) else -1 / 2))
                = (if R t i = 0 then (1 : ℝ) else -1 / 2)
                  * ∏ j', (if R t (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2) :=
              Fin.prod_univ_succAbove (fun w => (if R t w = 0 then (1 : ℝ) else -1 / 2)) i
            rw [hfull, if_pos (hi t), one_mul]
        _ = (3 / 4 : ℝ) ^ T := hprodT
    · rw [if_neg hi]
      push_neg at hi
      obtain ⟨t₀, ht₀⟩ := hi
      cases T with
      | zero => exact t₀.elim0
      | succ T' =>
        have hRi0 : ∀ s : Fin T', R (t₀.succAbove s) i = 0 := by
          intro s
          rcases hdisj (t₀.succAbove s) t₀ (Fin.succAbove_ne t₀ s) i with h | h
          · exact h
          · exact absurd h ht₀
        have hrel' : ∀ s : Fin T',
            (∑ j', R (t₀.succAbove s) (i.succAbove j') * u (i.succAbove j')) = 0 := by
          intro s
          have h := Fin.sum_univ_succAbove (fun w => R (t₀.succAbove s) w * u w) i
          rw [hRi0 s, zero_mul, zero_add] at h
          rw [← h]; exact hrel _
        have hne' : ∀ s : Fin T', ∃ j', R (t₀.succAbove s) (i.succAbove j') ≠ 0 := by
          intro s
          obtain ⟨w, hw⟩ := hne (t₀.succAbove s)
          have hwi : w ≠ i := fun h => hw (h ▸ hRi0 s)
          obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hwi
          exact ⟨j', by rw [hj']; exact hw⟩
        have hdisj' : ∀ s s' : Fin T', s ≠ s' →
            ∀ j', R (t₀.succAbove s) (i.succAbove j') = 0
              ∨ R (t₀.succAbove s') (i.succAbove j') = 0 := by
          intro s s' hss j'
          exact hdisj _ _ (fun h => hss (Fin.succAbove_right_injective h)) _
        rw [riesz_mass_disjoint_real k T' (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
          (fun s j' => R (t₀.succAbove s) (i.succAbove j')) (fun s j' => hmem _ _) hrel' hne'
          hdisj' (disjoint_subfamily_active u R hdisj hchar i t₀ ht₀)]
        have hPs : ∀ s : Fin T',
            (∏ j', (if R (t₀.succAbove s) (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
            = -1 / 8 := by
          intro s
          have hfull : (∏ w, (if R (t₀.succAbove s) w = 0 then (1 : ℝ) else -1 / 2))
              = (if R (t₀.succAbove s) i = 0 then (1 : ℝ) else -1 / 2)
                * ∏ j', (if R (t₀.succAbove s) (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2) :=
            Fin.prod_univ_succAbove
              (fun w => (if R (t₀.succAbove s) w = 0 then (1 : ℝ) else -1 / 2)) i
          have h8 := hPt (t₀.succAbove s)
          rw [hfull, if_pos (hRi0 s), one_mul] at h8
          exact h8
        have hprodT' : (∏ s : Fin T',
            (1 + 2 * ∏ j', (if R (t₀.succAbove s) (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2)))
            = (3 / 4 : ℝ) ^ T' := by
          calc (∏ s : Fin T', (1 + 2 * ∏ j',
                (if R (t₀.succAbove s) (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2)))
              = ∏ _s : Fin T', ((3 : ℝ) / 4) :=
                Finset.prod_congr rfl fun s _ => by rw [hPs s]; norm_num
            _ = (3 / 4 : ℝ) ^ T' := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [hprodT']
        rw [pow_succ]
        ring
  -- cardinalities: 3T support runners, k+1−3T passive
  have hcard_active : (Finset.univ.filter (fun i => ¬ (∀ t, R t i = 0))).card = 3 * T := by
    have heq : Finset.univ.filter (fun i : Fin (k + 1) => ¬ (∀ t, R t i = 0))
        = Finset.univ.biUnion (fun t => Finset.univ.filter (fun i => R t i ≠ 0)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, not_forall]
    rw [heq, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun t _ => hsupp t), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm]
    · intro t _ t' _ htne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro i hi hi'
      rcases hdisj t t' htne i with h | h
      · exact (Finset.mem_filter.mp hi).2 h
      · exact (Finset.mem_filter.mp hi').2 h
  have h3T : 3 * T ≤ k + 1 := by
    rw [← hcard_active]
    calc (Finset.univ.filter (fun i : Fin (k + 1) => ¬ (∀ t, R t i = 0))).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = k + 1 := by simp
  have hcard_passive : (Finset.univ.filter (fun i : Fin (k + 1) => ∀ t, R t i = 0)).card
      = k + 1 - 3 * T := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => ∀ t, R t i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hsumMi : (∑ i, Mi i) = ((k : ℝ) + 1 + T) * ((Q : ℝ) * (3 / 4 : ℝ) ^ T) := by
    simp only [hMidef]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard_passive, hcard_active]
    have hks : ((k + 1 - 3 * T : ℕ) : ℝ) = (k : ℝ) + 1 - 3 * (T : ℝ) := by
      rw [Nat.cast_sub h3T]; push_cast; ring
    rw [hks]
    push_cast
    ring
  -- the sharp union call at the floor
  have hkR : (15 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hT3R : 3 * (T : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast h3T
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ17 : δ ≤ 1 / 17 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  refine riesz_union_general_sharp u Q hQ0 δ hδ0 hδ2 ((Q : ℝ) * (3 / 4 : ℝ) ^ T) hmass
    Mi hsubmass ?_
  have hM0 : (0 : ℝ) < (Q : ℝ) * (3 / 4 : ℝ) ^ T := by positivity
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδT3 : δ * (T : ℝ) ≤ 1 / 3 := by
    rw [hδdef, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hkey : ((k : ℝ) + 2 + 2 * T) * (1 - Real.cos (2 * π * δ)) < 2 := by
    have h1 : ((k : ℝ) + 2 + 2 * T) * (1 - Real.cos (2 * π * δ))
        < ((k : ℝ) + 2 + 2 * T) * (2 * (π * δ) ^ 2) := by
      refine mul_lt_mul_of_pos_left hu ?_
      have : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      linarith
    have hδk : δ * ((k : ℝ) + 2 + 2 * T) ≤ 5 / 3 := by
      have hexp : δ * ((k : ℝ) + 2 + 2 * T) = δ * ((k : ℝ) + 2) + 2 * (δ * (T : ℝ)) := by ring
      rw [hexp, hδval]
      linarith
    have h2 : ((k : ℝ) + 2 + 2 * T) * (2 * (π * δ) ^ 2)
        = 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 2 + 2 * T)) := by ring
    rw [h2] at h1
    have h3 : 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 2 + 2 * T)) ≤ 2 * π ^ 2 * δ * (5 / 3) :=
      mul_le_mul_of_nonneg_left hδk (by positivity)
    have h5 : 2 * π ^ 2 * δ ≤ 2 * π ^ 2 * (1 / 17) :=
      mul_le_mul_of_nonneg_left hδ17 (by positivity)
    have h4 : 2 * π ^ 2 * δ * (5 / 3) ≤ 2 * π ^ 2 * (1 / 17) * (5 / 3) :=
      mul_le_mul_of_nonneg_right h5 (by norm_num)
    nlinarith [h1, h3, h4, hπ2]
  rw [hsumMi]
  have hexp2 : 2 * (((k : ℝ) + 1 + T) * ((Q : ℝ) * (3 / 4 : ℝ) ^ T))
      - ((k : ℝ) + 1) * ((Q : ℝ) * (3 / 4 : ℝ) ^ T)
      = ((k : ℝ) + 1 + 2 * T) * ((Q : ℝ) * (3 / 4 : ℝ) ^ T) := by ring
  rw [hexp2]
  have hstep : ((k : ℝ) + 1 + 2 * T) * (1 - Real.cos (2 * π * δ))
      < 1 + Real.cos (2 * π * δ) := by linarith [hkey]
  have hMlt : ((Q : ℝ) * (3 / 4 : ℝ) ^ T) * (((k : ℝ) + 1 + 2 * T) * (1 - Real.cos (2 * π * δ)))
      < ((Q : ℝ) * (3 / 4 : ℝ) ^ T) * (1 + Real.cos (2 * π * δ)) :=
    mul_lt_mul_of_pos_left hstep hM0
  nlinarith [hMlt]

/-! ### Atoms for the bad-set Fourier program (the extremal wall)

Three self-contained pieces of the interval-Fourier route: the `1/sin` norm
formula (absent from Mathlib), the pure-`ℕ` modular reindexing of `range Q`
sums (dodging the recorded `sum_nbij'`-over-`ℤ`/`toNat` elaborator dead-ends),
and the bad-set version of the public mass expansion. -/

/-- `‖1 − e^{iθ}‖ = 2|sin(θ/2)|`, by the factorization
`1 − e^{iθ} = e^{iθ/2}·(−2i·sin(θ/2))` — no `normSq` bookkeeping. -/
theorem norm_one_sub_exp (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.sin (θ / 2)| := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I)
      = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show ((θ / 2 : ℝ) : ℂ) * Complex.I + ((-(θ / 2) : ℝ) : ℂ) * Complex.I = 0 by
        push_cast; ring]
    exact Complex.exp_zero
  have h3 : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)
      = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I,
      show ((-(θ / 2) : ℝ) : ℂ) = -((θ / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  have hfac : 1 - Complex.exp ((θ : ℂ) * Complex.I)
      = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
        * (-(((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I)) := by
    calc 1 - Complex.exp ((θ : ℂ) * Complex.I)
        = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by rw [h2, ← h1]
      _ = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
            * -(Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
                - Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [h3]
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_neg, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-- **Pure-`ℕ` modular reindexing**: multiplication by `a` (with inverse `b`
mod `Q`) permutes the residues, so summing any `F` of the residue over
`range Q` is reindexing-invariant. -/
theorem sum_range_mul_mod (Q : ℕ) (hQ0 : 0 < Q) (a b : ℕ) (hab : a * b ≡ 1 [MOD Q])
    (F : ℕ → ℂ) :
    ∑ j ∈ Finset.range Q, F (a * j % Q) = ∑ r ∈ Finset.range Q, F r := by
  refine Finset.sum_nbij' (fun j => a * j % Q) (fun r => b * r % Q) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr (Nat.mod_lt _ hQ0)
  · intro r hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ hQ0)
  · intro j hj
    have hj' : j < Q := Finset.mem_range.mp hj
    have hcong : b * (a * j % Q) ≡ j [MOD Q] := by
      calc b * (a * j % Q) ≡ b * (a * j) [MOD Q] :=
            Nat.ModEq.mul_left b (Nat.mod_modEq (a * j) Q)
        _ = a * b * j := by ring
        _ ≡ 1 * j [MOD Q] := Nat.ModEq.mul_right j hab
        _ = j := one_mul j
    calc b * (a * j % Q) % Q = j % Q := hcong
      _ = j := Nat.mod_eq_of_lt hj'
  · intro r hr
    have hr' : r < Q := Finset.mem_range.mp hr
    have hcong : a * (b * r % Q) ≡ r [MOD Q] := by
      calc a * (b * r % Q) ≡ a * (b * r) [MOD Q] :=
            Nat.ModEq.mul_left a (Nat.mod_modEq (b * r) Q)
        _ = a * b * r := by ring
        _ ≡ 1 * r [MOD Q] := Nat.ModEq.mul_right r hab
        _ = r := one_mul r
    calc a * (b * r % Q) % Q = r % Q := hcong
      _ = r := Nat.mod_eq_of_lt hr'
  · intro j hj
    rfl

/-- **Bad-set version of the public mass expansion**: over any grid subset `S`,
the subfamily weight expands into combination-indexed exponential sums. -/
theorem riesz_badset_expand_pub (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (S : Finset ℕ) :
    ∑ j ∈ S, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
          (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2))
            * ∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, c i * v i) * ↑j / ↑Q) := by
  have step1 : ∀ j ∈ S,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)))
        = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
            (∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2))
              * Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, c i * v i) * ↑j / ↑Q) := by
    intro j _
    rw [Finset.prod_congr rfl
      (fun i _ => cos_factor_pub (2 * ↑π * ↑(v i) * ↑j / ↑Q)), Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm

/-- **The bad-set exponential-sum reindex** (the ②.2 core, assembled): pulling the
bad set back through multiplication by `a` (inverse `b` mod `Q`) turns the
frequency-`h` sum over `{j : P(a·j mod Q)}` into the frequency-`h·b` sum over
`{r : P r}`. -/
theorem badset_reindex (Q : ℕ) (hQ0 : 0 < Q) (a b : ℕ) (hab : a * b ≡ 1 [MOD Q]) (h : ℤ)
    (P : ℕ → Prop) [DecidablePred P] :
    ∑ j ∈ (Finset.range Q).filter (fun j => P (a * j % Q)),
        Complex.exp (2 * ↑π * Complex.I * ↑h * ↑j / ↑Q)
      = ∑ r ∈ (Finset.range Q).filter (fun r => P r),
          Complex.exp (2 * ↑π * Complex.I * ↑(h * (b : ℤ)) * ↑r / ↑Q) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have hmain := sum_range_mul_mod Q hQ0 a b hab
    (fun r => if P r then Complex.exp (2 * ↑π * Complex.I * ↑(h * (b : ℤ)) * ↑r / ↑Q) else 0)
  rw [← hmain]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hP : P (a * j % Q)
  · rw [if_pos hP, if_pos hP]
    have e1 : Complex.exp (2 * ↑π * Complex.I * ↑h * ↑j / ↑Q)
        = Complex.exp (2 * ↑π * Complex.I * ↑(h * (j : ℤ)) / ↑Q) := by
      congr 1
      push_cast
      ring
    have e2 : Complex.exp (2 * ↑π * Complex.I * ↑(h * (b : ℤ)) * ↑(a * j % Q) / ↑Q)
        = Complex.exp (2 * ↑π * Complex.I
            * ↑(h * (b : ℤ) * ((a * j % Q : ℕ) : ℤ)) / ↑Q) := by
      congr 1
      conv_rhs => rw [Int.cast_mul, Int.cast_natCast]
      ring
    rw [e1, e2]
    apply exp_qperiodic Q hQ0
    have hcong1 : ((a * j % Q : ℕ) : ℤ) ≡ (a : ℤ) * (j : ℤ) [ZMOD (Q : ℤ)] := by
      show ((a * j % Q : ℕ) : ℤ) % (Q : ℤ) = ((a : ℤ) * (j : ℤ)) % (Q : ℤ)
      rw [Int.natCast_mod, Int.emod_emod_of_dvd _ dvd_rfl]
      congr 1
    have hab' : (a : ℤ) * (b : ℤ) ≡ 1 [ZMOD (Q : ℤ)] := by
      show ((a : ℤ) * (b : ℤ)) % (Q : ℤ) = (1 : ℤ) % (Q : ℤ)
      have hc := congrArg (fun n : ℕ => (n : ℤ)) hab
      simp only at hc
      rw [Int.natCast_mod, Int.natCast_mod] at hc
      push_cast at hc
      exact hc
    have hfinal : h * (b : ℤ) * ((a * j % Q : ℕ) : ℤ) ≡ h * (j : ℤ) [ZMOD (Q : ℤ)] := by
      calc h * (b : ℤ) * ((a * j % Q : ℕ) : ℤ)
          ≡ h * (b : ℤ) * ((a : ℤ) * (j : ℤ)) [ZMOD (Q : ℤ)] :=
            Int.ModEq.mul_left _ hcong1
        _ = h * (j : ℤ) * ((a : ℤ) * (b : ℤ)) := by ring
        _ ≡ h * (j : ℤ) * 1 [ZMOD (Q : ℤ)] := Int.ModEq.mul_left _ hab'
        _ = h * (j : ℤ) := by ring
    exact Int.ModEq.dvd hfinal
  · rw [if_neg hP, if_neg hP]

/-- **The two-interval Dirichlet bound**: the frequency-`w` exponential sum over
the near-integer residue set `{r : min(r, Q−r) < δQ}` is at most
`4/‖1 − e(2πi·w/Q)‖`, by an initial segment plus the complement trick (the full
geometric sum vanishes for `Q ∤ w`). -/
theorem interval_exp_bound (Q : ℕ) (hQ0 : 0 < Q) (w : ℤ) (hw : ¬ (Q : ℤ) ∣ w)
    (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    ‖∑ r ∈ (Finset.range Q).filter
        (fun r : ℕ => min (r : ℝ) ((Q : ℝ) - (r : ℝ)) < δ * Q),
        Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q)‖
      ≤ 4 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖ := by
  classical
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hsplit : (Finset.range Q).filter
        (fun r : ℕ => min (r : ℝ) ((Q : ℝ) - (r : ℝ)) < δ * Q)
      = ((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q))
        ∪ ((Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_union, min_lt_iff]
    tauto
  have hdisj : Disjoint ((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q))
      ((Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    rw [Finset.mem_filter] at h1 h2
    nlinarith [h1.2, h2.2, hδ, hQR]
  rw [hsplit, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) ?_
  have hA1 : (Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)
      = Finset.range (min Q ⌈δ * Q⌉₊) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Nat.lt_ceil.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Nat.lt_ceil.mp h2⟩
  have hb1 : ‖∑ r ∈ (Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q),
      Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q)‖
      ≤ 2 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖ := by
    rw [hA1]
    exact exp_partial_sum_bound Q _ hQ0 w hw
  have hfull : ∑ r ∈ Finset.range Q, Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q) = 0 := by
    rw [exp_geom_sum Q hQ0 w, if_neg hw]
  have hcompl := Finset.sum_filter_add_sum_filter_not (Finset.range Q)
    (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)
    (fun r => Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q))
  rw [hfull] at hcompl
  have hA2sum : ∑ r ∈ (Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q),
      Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q)
      = -(∑ r ∈ (Finset.range Q).filter (fun r : ℕ => ¬ ((Q : ℝ) - (r : ℝ) < δ * Q)),
          Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q)) :=
    eq_neg_of_add_eq_zero_left hcompl
  have h0Qδ : (0 : ℝ) ≤ (Q : ℝ) - δ * Q := by nlinarith [hδ, hQR]
  have hnotfilter : (Finset.range Q).filter (fun r : ℕ => ¬ ((Q : ℝ) - (r : ℝ) < δ * Q))
      = Finset.range (min Q (⌊(Q : ℝ) - δ * Q⌋₊ + 1)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Nat.lt_succ_of_le (Nat.le_floor ?_)⟩
      linarith
    · rintro ⟨h1, h2⟩
      have hr : r ≤ ⌊(Q : ℝ) - δ * Q⌋₊ := Nat.lt_succ_iff.mp h2
      have hrr := (Nat.le_floor_iff h0Qδ).mp hr
      exact ⟨h1, by linarith⟩
  have hb2 : ‖∑ r ∈ (Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q),
      Complex.exp (2 * ↑π * Complex.I * ↑w * ↑r / ↑Q)‖
      ≤ 2 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖ := by
    rw [hA2sum, norm_neg, hnotfilter]
    exact exp_partial_sum_bound Q _ hQ0 w hw
  have h4 : 2 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖
      + 2 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖
      = 4 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑w / ↑Q)‖ := by ring
  linarith [hb1, hb2, h4]

set_option maxHeartbeats 1000000 in
/-- **The bad-set Fourier bound** (the ②.2 target): for a positive velocity `v`
with modular inverse `b` of its residue, the frequency-`h` exponential sum over
the bad set `{j : ‖v·j/Q‖ < δ}` is bounded by the Dirichlet-kernel value
`4/‖1 − e(2πi·h·b/Q)‖`. -/
theorem badset_fourier_bound (Q : ℕ) (hQ0 : 0 < Q) (v : ℤ) (hv0 : 0 < v)
    (b : ℕ) (hab : (v.toNat % Q) * b ≡ 1 [MOD Q])
    (h : ℤ) (hw : ¬ (Q : ℤ) ∣ h * (b : ℤ)) (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    ‖∑ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        Complex.exp (2 * ↑π * Complex.I * ↑h * ↑j / ↑Q)‖
      ≤ 4 / ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑(h * (b : ℤ)) / ↑Q)‖ := by
  classical
  have hfilter_eq : (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)
      = (Finset.range Q).filter (fun j : ℕ =>
          min ((v.toNat % Q * j % Q : ℕ) : ℝ)
            ((Q : ℝ) - ((v.toNat % Q * j % Q : ℕ) : ℝ)) < δ * Q) := by
    apply Finset.filter_congr
    intro j _
    have harg : (v : ℝ) * (j : ℝ) / (Q : ℝ) = (((v * (j : ℤ)) : ℤ) : ℝ) / (Q : ℝ) := by
      push_cast
      ring
    rw [harg, nearestIntDist_div_lt_iff (v * (j : ℤ)) Q hQ0 δ]
    have hmodeq : (v * (j : ℤ)) % (Q : ℤ) = ((v.toNat % Q * j % Q : ℕ) : ℤ) := by
      have hv : v = ((v.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hv0.le).symm
      rw [hv, ← Int.natCast_mul, ← Int.natCast_mod]
      congr 1
      exact (Nat.mod_mul_mod _ _ _).symm
    rw [hmodeq]
    push_cast
    tauto
  rw [hfilter_eq]
  rw [badset_reindex Q hQ0 (v.toNat % Q) b hab h
    (fun r : ℕ => min (r : ℝ) ((Q : ℝ) - (r : ℝ)) < δ * Q)]
  exact interval_exp_bound Q hQ0 (h * (b : ℤ)) hw δ hδ

/-- Multiplication by a unit's inverse preserves non-divisibility. -/
theorem not_dvd_mul_inv (Q a b : ℕ) (hab : a * b ≡ 1 [MOD Q]) (h : ℤ)
    (hh : ¬ (Q : ℤ) ∣ h) : ¬ (Q : ℤ) ∣ h * (b : ℤ) := by
  intro hdvd
  apply hh
  have hab' : (a : ℤ) * (b : ℤ) ≡ 1 [ZMOD (Q : ℤ)] := by
    show ((a : ℤ) * (b : ℤ)) % (Q : ℤ) = (1 : ℤ) % (Q : ℤ)
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hab
    simp only at hc
    rw [Int.natCast_mod, Int.natCast_mod] at hc
    push_cast at hc
    exact hc
  have h1 : h * ((a : ℤ) * (b : ℤ)) ≡ h * 1 [ZMOD (Q : ℤ)] := Int.ModEq.mul_left _ hab'
  have h2 : (Q : ℤ) ∣ h * (b : ℤ) * (a : ℤ) := Dvd.dvd.mul_right hdvd _
  have h3 : h * (b : ℤ) * (a : ℤ) = h * ((a : ℤ) * (b : ℤ)) := by ring
  rw [h3] at h2
  have h4 : (Q : ℤ) ∣ h * 1 - h * ((a : ℤ) * (b : ℤ)) := Int.ModEq.dvd h1
  have h5 : h = (h * 1 - h * ((a : ℤ) * (b : ℤ))) + h * ((a : ℤ) * (b : ℤ)) := by ring
  rw [h5]
  exact dvd_add h4 h2

set_option maxHeartbeats 1000000 in
/-- **Union engine with supplied bad-set weights**: if per-runner bounds `W i` on
the bad-set subfamily weights are given as data and `(∑W_i)(1−cos 2πδ) < M`,
the floor `δ` clears. -/
theorem riesz_union_weights {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℝ)
    (hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = M)
    (W : Fin (k + 1) → ℝ)
    (hW : ∀ i, ∑ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
        ≤ W i)
    (hcond : (∑ i, W i) * (1 - Real.cos (2 * π * δ)) < M) :
    δ ≤ ML v := by
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * W i := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hsubnn : ∀ j, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        = ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          Finset.sum_congr rfl (fun j _ => hRsplit j)
      _ ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * δ))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
          rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
              = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
          have hcosle : Real.cos (2 * π * δ)
              ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
            Real.cos_le_cos_of_nonneg_of_le_pi
              (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
              (by nlinarith [Real.pi_pos, hδ2])
              (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
          linarith
      _ = (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - Real.cos (2 * π * δ)) * W i :=
          mul_le_mul_of_nonneg_left (hW i) hcosδ
  have hgood : ∃ j ∈ Finset.range Q, ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hcover : ∑ j ∈ Finset.range Q, R j
        ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := by
      have hrw : (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          = ∑ j ∈ Finset.range Q, ∑ i : Fin (k + 1),
              (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
        simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      rw [hrw]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨i, hi⟩ := hcon j hj
      calc R j = (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
              rw [if_pos hi]
        _ ≤ ∑ i' : Fin (k + 1),
              (if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0) := by
            refine Finset.single_le_sum
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : M ≤ (∑ i, W i) * (1 - Real.cos (2 * π * δ)) := by
      calc M = ∑ j ∈ Finset.range Q, R j := hmass.symm
        _ ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j := hcover
        _ ≤ ∑ i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * W i :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = (∑ i, W i) * (1 - Real.cos (2 * π * δ)) := by
            rw [← Finset.mul_sum]; ring
    linarith [hfinal, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

set_option maxHeartbeats 1000000 in
/-- **The bad-set weight through the Fourier expansion** (③, assembled): the
subfamily weight of runner `i`'s bad set is at most the bad-set *count* plus the
inverse-sine lattice sum — every combination `c ≠ 0` contributes its weight
`(1/2)^{|supp c|}` times the Dirichlet value `4/‖1 − e(2πi·F(c)·b/Q)‖`.  The
remaining open content of the extremal program is precisely the estimation of
the right-hand sum. -/
theorem badset_weight_fourier {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQsum : (∑ w, (v w).natAbs) < Q) (i : Fin (k + 1)) (hvpos : 0 < v i)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q])
    (hSF : StrongFree (fun j' : Fin k => v (i.succAbove j')))
    (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    ∑ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ (((Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        + ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
              * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := by
  classical
  set S := (Finset.range Q).filter
    (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ) with hSdef
  set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
  -- cast the real weight to the complex expansion
  have hcs : ((∑ j ∈ S, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ S, ∏ j' : Fin k, (1 - Complex.cos (2 * ↑π * ↑(v' j') * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun j' _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hnn : 0 ≤ ∑ j ∈ S, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
    refine Finset.sum_nonneg fun j _ => Finset.prod_nonneg fun j' _ => ?_
    have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hnorm : (∑ j ∈ S, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
      = ‖(∑ j ∈ S, ∏ j' : Fin k, (1 - Complex.cos (2 * ↑π * ↑(v' j') * ↑j / ↑Q)) : ℂ)‖ := by
    rw [← hcs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, riesz_badset_expand_pub k v' Q S]
  -- 0 is a combination
  have h0mem : (0 : Fin k → ℤ) ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)) := by
    rw [Fintype.mem_piFinset]
    intro j'
    simp
  -- split off the zero combination
  rw [← Finset.add_sum_erase _ _ h0mem]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- the zero term is the bad-set count
    have hwt0 : (∏ j' : Fin k, (if (0 : Fin k → ℤ) j' = 0 then (1 : ℂ) else -1 / 2)) = 1 :=
      Finset.prod_eq_one fun j' _ => if_pos rfl
    have hF0 : (∑ j', (0 : Fin k → ℤ) j' * v' j') = 0 :=
      Finset.sum_eq_zero fun j' _ => zero_mul _
    have hexp0 : ∀ j : ℕ, Complex.exp (2 * ↑π * Complex.I
        * ↑(∑ j', (0 : Fin k → ℤ) j' * v' j') * ↑j / ↑Q) = 1 := by
      intro j
      rw [hF0]
      norm_num
    rw [hwt0, one_mul, Finset.sum_congr rfl (fun j _ => hexp0 j), Finset.sum_const,
      nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
  · -- the nonzero combinations: triangle + the bad-set Fourier bound
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro c hc
    rw [Finset.mem_erase] at hc
    obtain ⟨hc0, hcmem⟩ := hc
    rw [norm_mul]
    have hwt : ‖∏ j' : Fin k, (if c j' = 0 then (1 : ℂ) else -1 / 2)‖
        = ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun j' _ => ?_
      split_ifs
      · exact norm_one
      · rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs]
        norm_num
    rw [hwt]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j' _ => by positivity)
    -- ‖D_i(F c)‖ ≤ 4/‖1 − e(F(c)·b/Q)‖
    have hFne : (∑ j', c j' * v' j') ≠ 0 := by
      intro hF
      apply hc0
      funext j'
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j''
        have := (Fintype.mem_piFinset.mp hcmem) j''
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      exact hSF c hcmem' hF j'
    have hFabs : (∑ j', c j' * v' j').natAbs < Q := by
      have hb : (∑ j', c j' * v' j').natAbs ≤ ∑ j', (v' j').natAbs := by
        calc (∑ j', c j' * v' j').natAbs ≤ ∑ j', (c j' * v' j').natAbs :=
              Int.natAbs_sum_le _ _
          _ ≤ ∑ j', (v' j').natAbs := by
              refine Finset.sum_le_sum fun j' _ => ?_
              rw [Int.natAbs_mul]
              have hcj : (c j').natAbs ≤ 1 := by
                have := (Fintype.mem_piFinset.mp hcmem) j'
                simp only [Finset.mem_insert, Finset.mem_singleton] at this
                rcases this with h | h | h <;> simp [h]
              calc (c j').natAbs * (v' j').natAbs ≤ 1 * (v' j').natAbs :=
                    Nat.mul_le_mul_right _ hcj
                _ = (v' j').natAbs := one_mul _
      have hsub : (∑ j', (v' j').natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        simp only [hv'def]
        exact Nat.le_add_left _ _
      omega
    have hFdvd : ¬ (Q : ℤ) ∣ (∑ j', c j' * v' j') := by
      intro hdvd
      apply hFne
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hFabs
    have hw : ¬ (Q : ℤ) ∣ (∑ j', c j' * v' j') * (b : ℤ) :=
      not_dvd_mul_inv Q ((v i).toNat % Q) b hab _ hFdvd
    exact badset_fourier_bound Q hQ0 (v i) hvpos b hab
      (∑ j', c j' * v' j') hw δ hδ

/-- **The bad-set count**: `|B_i(δ)| ≤ 2δQ + 2` — the residue reindex is a
bijection, and the near-integer residue set is two intervals of length `< δQ+1`. -/
theorem badset_card_bound (Q : ℕ) (hQ0 : 0 < Q) (a b : ℕ) (hab : a * b ≡ 1 [MOD Q])
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    (((Finset.range Q).filter
        (fun j : ℕ => min ((a * j % Q : ℕ) : ℝ) ((Q : ℝ) - ((a * j % Q : ℕ) : ℝ)) < δ * Q)).card : ℝ)
      ≤ 2 * δ * Q + 2 := by
  classical
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the reindex is a bijection on `range Q`, so the card equals the residue-set card
  have hcard : ((Finset.range Q).filter
        (fun j : ℕ => min ((a * j % Q : ℕ) : ℝ) ((Q : ℝ) - ((a * j % Q : ℕ) : ℝ)) < δ * Q)).card
      = ((Finset.range Q).filter
        (fun r : ℕ => min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q)).card := by
    have hsum := sum_range_mul_mod Q hQ0 a b hab
      (fun r => if min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q then (1 : ℂ) else 0)
    rw [← Finset.sum_filter, ← Finset.sum_filter] at hsum
    have h1 : (∑ _j ∈ (Finset.range Q).filter
        (fun j : ℕ => min ((a * j % Q : ℕ) : ℝ) ((Q : ℝ) - ((a * j % Q : ℕ) : ℝ)) < δ * Q),
        (1 : ℂ)) = (((Finset.range Q).filter
        (fun j : ℕ => min ((a * j % Q : ℕ) : ℝ) ((Q : ℝ) - ((a * j % Q : ℕ) : ℝ)) < δ * Q)).card : ℂ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (∑ _r ∈ (Finset.range Q).filter
        (fun r : ℕ => min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q),
        (1 : ℂ)) = (((Finset.range Q).filter
        (fun r : ℕ => min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q)).card : ℂ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2] at hsum
    exact_mod_cast hsum
  rw [hcard]
  -- split the residue set into the two intervals
  have hsplit : (Finset.range Q).filter
        (fun r : ℕ => min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q)
      ⊆ ((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q))
        ∪ ((Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)) := by
    intro r hr
    rw [Finset.mem_filter, min_lt_iff] at hr
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    tauto
  have hA1card : (((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)).card : ℝ)
      < δ * Q + 1 := by
    have hA1 : (Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)
        = Finset.range (min Q ⌈δ * Q⌉₊) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.lt_ceil.mpr h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.lt_ceil.mp h2⟩
    rw [hA1, Finset.card_range]
    calc ((min Q ⌈δ * Q⌉₊ : ℕ) : ℝ) ≤ ((⌈δ * Q⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast min_le_right Q ⌈δ * Q⌉₊
      _ < δ * Q + 1 := Nat.ceil_lt_add_one (mul_nonneg hδ0 hQR.le)
  have hA2card : (((Finset.range Q).filter
        (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)).card : ℝ) < δ * Q + 1 := by
    have hcard2 : ((Finset.range Q).filter
          (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)).card
        ≤ ((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)).card := by
      refine Finset.card_le_card_of_injOn (fun r => Q - 1 - r) ?_ ?_
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        have hr1 : r ≤ Q - 1 := by omega
        constructor
        · omega
        · have hcast : ((Q - 1 - r : ℕ) : ℝ) = (Q : ℝ) - 1 - (r : ℝ) := by
            rw [Nat.cast_sub hr1, Nat.cast_sub (by omega : 1 ≤ Q)]
            push_cast
            ring
          rw [hcast]
          linarith [hr.2]
      · intro r hr r' hr' hrr
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hr hr'
        have hrr' : Q - 1 - r = Q - 1 - r' := hrr
        omega
    calc (((Finset.range Q).filter
          (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)).card : ℝ)
        ≤ (((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)).card : ℝ) := by
          exact_mod_cast hcard2
      _ < δ * Q + 1 := hA1card
  have hunion : (((Finset.range Q).filter
        (fun r : ℕ => min ((r : ℕ) : ℝ) ((Q : ℝ) - ((r : ℕ) : ℝ)) < δ * Q)).card : ℝ)
      ≤ (((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q)).card : ℝ)
        + (((Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q)).card : ℝ) := by
    have h := Finset.card_le_card hsplit
    have h2 := Finset.card_union_le
      ((Finset.range Q).filter (fun r : ℕ => (r : ℝ) < δ * Q))
      ((Finset.range Q).filter (fun r : ℕ => (Q : ℝ) - (r : ℝ) < δ * Q))
    exact_mod_cast le_trans h h2
  linarith [hunion, hA1card, hA2card]

/-- `exists_coprime_modulus` with an additional lower threshold. -/
theorem exists_coprime_modulus_ge (m : ℕ) (v : Fin m → ℤ) (N : ℕ) :
    ∃ Q : ℕ, Q.Prime ∧ N < Q ∧ (∑ i, (v i).natAbs) < Q ∧
      ∀ i, (v i).natAbs ≠ 0 → Nat.Coprime (v i).natAbs Q := by
  obtain ⟨Q, hQge, hQp⟩ := Nat.exists_infinite_primes (max N (∑ i, (v i).natAbs) + 1)
  have h1 := le_max_left N (∑ i, (v i).natAbs)
  have h2 := le_max_right N (∑ i, (v i).natAbs)
  refine ⟨Q, hQp, by omega, by omega, fun i hi => ?_⟩
  have hlt : (v i).natAbs < Q := by
    have hle : (v i).natAbs ≤ ∑ i', (v i').natAbs :=
      Finset.single_le_sum (f := fun i' => (v i').natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  exact (hQp.coprime_iff_not_dvd.mpr
    (fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h) (not_le.mpr hlt))).symm

/-- A natural-number modular inverse from coprimality (via the Bézout witness). -/
theorem exists_nat_inverse (a Q : ℕ) (hQ0 : 0 < Q) (hcop : Nat.Coprime a Q) :
    ∃ b : ℕ, a * b ≡ 1 [MOD Q] := by
  obtain ⟨w, hw⟩ := exists_mod_inverse (a : ℤ) Q (by simpa [Int.natAbs_natCast] using hcop)
  have hQZ : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ0
  have hnn : 0 ≤ w % (Q : ℤ) := Int.emod_nonneg w hQZ.ne'
  refine ⟨(w % (Q : ℤ)).toNat, ?_⟩
  show (a * (w % (Q : ℤ)).toNat) % Q = 1 % Q
  have hcast : ((a * (w % (Q : ℤ)).toNat : ℕ) : ℤ) % (Q : ℤ) = ((1 : ℕ) : ℤ) % (Q : ℤ) := by
    push_cast [Int.toNat_of_nonneg hnn]
    have h1 : (a : ℤ) * (w % (Q : ℤ)) ≡ (a : ℤ) * w [ZMOD (Q : ℤ)] :=
      Int.ModEq.mul_left _ (Int.emod_emod_of_dvd _ dvd_rfl)
    have h2 : (a : ℤ) * w ≡ 1 [ZMOD (Q : ℤ)] := by
      have := Int.modEq_iff_dvd.mpr
        (show (Q : ℤ) ∣ 1 - (a : ℤ) * w by
          rw [show (1 : ℤ) - (a : ℤ) * w = -((a : ℤ) * w - 1) by ring]
          exact dvd_neg.mpr hw)
      exact this
    exact h1.trans h2
  have h3 : (((a * (w % (Q : ℤ)).toNat) % Q : ℕ) : ℤ) = ((1 % Q : ℕ) : ℤ) := by
    rw [Int.natCast_mod, Int.natCast_mod]
    exact hcast
  exact_mod_cast h3

/-- The bad set in residue form (standalone version of the transport used in
`badset_fourier_bound`). -/
theorem badset_filter_eq (Q : ℕ) (hQ0 : 0 < Q) (v : ℤ) (hv0 : 0 < v) (δ : ℝ) :
    (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)
      = (Finset.range Q).filter (fun j : ℕ =>
          min ((v.toNat % Q * j % Q : ℕ) : ℝ)
            ((Q : ℝ) - ((v.toNat % Q * j % Q : ℕ) : ℝ)) < δ * Q) := by
  classical
  apply Finset.filter_congr
  intro j _
  have harg : (v : ℝ) * (j : ℝ) / (Q : ℝ) = (((v * (j : ℤ)) : ℤ) : ℝ) / (Q : ℝ) := by
    push_cast
    ring
  rw [harg, nearestIntDist_div_lt_iff (v * (j : ℤ)) Q hQ0 δ]
  have hmodeq : (v * (j : ℤ)) % (Q : ℤ) = ((v.toNat % Q * j % Q : ℕ) : ℤ) := by
    have hv : v = ((v.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hv0.le).symm
    rw [hv, ← Int.natCast_mul, ← Int.natCast_mod]
    congr 1
    exact (Nat.mod_mul_mod _ _ _).symm
  rw [hmodeq]
  push_cast
  tauto

/-- The chord length as a sine of the nearest-integer distance:
`‖1 − e(2πi·H/Q)‖ = 2·sin(π·‖H/Q‖)`. -/
theorem norm_one_sub_exp_nid (Q : ℕ) (hQ0 : 0 < Q) (H : ℤ) :
    ‖1 - Complex.exp (2 * ↑π * Complex.I * ↑H / ↑Q)‖
      = 2 * Real.sin (π * nearestIntDist ((H : ℝ) / Q)) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have harg : (2 * ↑π * Complex.I * ↑H / ↑Q : ℂ)
      = ((2 * π * (H : ℝ) / Q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, norm_one_sub_exp]
  have hhalf : (2 * π * (H : ℝ) / Q) / 2 = π * ((H : ℝ) / Q) := by ring
  rw [hhalf]
  -- |sin(πx)| = sin(π·nid x)
  set x : ℝ := (H : ℝ) / Q with hx
  have hnid0 : 0 ≤ nearestIntDist x := nearestIntDist_nonneg x
  have hnid2 : nearestIntDist x ≤ 1 / 2 := nearestIntDist_le_half x
  have hsq : Real.sin (π * x) ^ 2 = Real.sin (π * nearestIntDist x) ^ 2 := by
    have h1 : Real.sin (π * x) ^ 2 = 1 / 2 - Real.cos (2 * π * x) / 2 := by
      have := Real.sin_sq_add_cos_sq (π * x)
      have hc := Real.cos_two_mul (π * x)
      rw [show 2 * (π * x) = 2 * π * x by ring] at hc
      nlinarith [this, hc]
    have h2 : Real.sin (π * nearestIntDist x) ^ 2
        = 1 / 2 - Real.cos (2 * π * nearestIntDist x) / 2 := by
      have := Real.sin_sq_add_cos_sq (π * nearestIntDist x)
      have hc := Real.cos_two_mul (π * nearestIntDist x)
      rw [show 2 * (π * nearestIntDist x) = 2 * π * nearestIntDist x by ring] at hc
      nlinarith [this, hc]
    rw [h1, h2, cos_two_pi_nid x]
  have hsin_nn : 0 ≤ Real.sin (π * nearestIntDist x) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos, hnid2]
  have habs : |Real.sin (π * x)| = Real.sin (π * nearestIntDist x) := by
    rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq hsin_nn]
  rw [habs]

set_option maxHeartbeats 1000000 in
/-- **The window dichotomy** (the A-free heart): if the family is strongly free
and `i`-torsion-free up to `A`, then for every nonzero combination `c` the
reindexed frequency stays `(A+1)/Q`-far from the integers — a small residue
would force the *exact* relation `F(c) = ρ·v_i`. -/
theorem afree_nid_lower'' {k : ℕ} (v : Fin (k + 1) → ℤ) (i : Fin (k + 1))
    (A : ℕ)
    (Q : ℕ) (hQ0 : 0 < Q) (hQbig : (A + 1) * (∑ w, (v w).natAbs) < Q)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q]) (hvpos : 0 < v i)
    (c : Fin k → ℤ) (hc : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) (hc0 : c ≠ 0)
    (hAF : ∀ ρ : ℤ, |ρ| ≤ (A : ℤ) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i) :
    ((A : ℝ) + 1) / Q
      ≤ nearestIntDist ((((∑ j', c j' * v (i.succAbove j')) * (b : ℤ) : ℤ) : ℝ) / Q) := by
  set F : ℤ := ∑ j', c j' * v (i.succAbove j') with hF
  set a : ℕ := (v i).toNat % Q with ha
  by_contra hcon
  push_neg at hcon
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hlt := (nearestIntDist_div_lt_iff (F * (b : ℤ)) Q hQ0 (((A : ℝ) + 1) / Q)).mp hcon
  have hAQ : ((A : ℝ) + 1) / Q * Q = (A : ℝ) + 1 := by field_simp
  rw [hAQ] at hlt
  set r : ℤ := (F * (b : ℤ)) % (Q : ℤ) with hr
  have hQZ : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ0
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hQZ.ne'
  have hrQ : r < Q := Int.emod_lt_of_pos _ hQZ
  have hrmod : r % (Q : ℤ) = r := by
    rw [hr]
    exact Int.emod_emod_of_dvd _ dvd_rfl
  obtain ⟨ρ, hρA, hρcong⟩ :
      ∃ ρ : ℤ, |ρ| ≤ (A : ℤ) ∧ F * (b : ℤ) ≡ ρ [ZMOD (Q : ℤ)] := by
    rcases min_lt_iff.mp hlt with h | h
    · refine ⟨r, ?_, ?_⟩
      · rw [abs_of_nonneg hr0]
        have h2 : r < (A : ℤ) + 1 := by exact_mod_cast h
        omega
      · show (F * (b : ℤ)) % (Q : ℤ) = r % (Q : ℤ)
        rw [← hr, hrmod]
    · refine ⟨r - Q, ?_, ?_⟩
      · have h2 : (Q : ℤ) - r < (A : ℤ) + 1 := by exact_mod_cast h
        rw [abs_of_neg (by omega : r - (Q : ℤ) < 0)]
        omega
      · show (F * (b : ℤ)) % (Q : ℤ) = (r - (Q : ℤ)) % (Q : ℤ)
        rw [← hr]
        rw [show r - (Q : ℤ) = r + (Q : ℤ) * (-1) by ring, Int.add_mul_emod_self_left,
          hrmod]
  have hab' : (a : ℤ) * (b : ℤ) ≡ 1 [ZMOD (Q : ℤ)] := by
    show ((a : ℤ) * (b : ℤ)) % (Q : ℤ) = (1 : ℤ) % (Q : ℤ)
    have hc' := congrArg (fun n : ℕ => (n : ℤ)) hab
    simp only at hc'
    rw [Int.natCast_mod, Int.natCast_mod] at hc'
    push_cast at hc'
    exact hc'
  have havi : (a : ℤ) ≡ v i [ZMOD (Q : ℤ)] := by
    show (a : ℤ) % (Q : ℤ) = v i % (Q : ℤ)
    rw [ha, Int.natCast_mod, Int.toNat_of_nonneg hvpos.le]
    exact Int.emod_emod_of_dvd _ dvd_rfl
  have hchain : F ≡ ρ * v i [ZMOD (Q : ℤ)] := by
    calc F = F * 1 := by ring
      _ ≡ F * ((a : ℤ) * (b : ℤ)) [ZMOD (Q : ℤ)] := (Int.ModEq.mul_left F hab').symm
      _ = (F * (b : ℤ)) * (a : ℤ) := by ring
      _ ≡ ρ * (a : ℤ) [ZMOD (Q : ℤ)] := Int.ModEq.mul_right _ hρcong
      _ ≡ ρ * v i [ZMOD (Q : ℤ)] := Int.ModEq.mul_left _ havi
  have hdvd : (Q : ℤ) ∣ (ρ * v i - F) := Int.ModEq.dvd hchain
  have hFabs : F.natAbs ≤ ∑ w, (v w).natAbs := by
    have h1 : F.natAbs ≤ ∑ j', (v (i.succAbove j')).natAbs := by
      rw [hF]
      calc (∑ j', c j' * v (i.succAbove j')).natAbs
          ≤ ∑ j', (c j' * v (i.succAbove j')).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ j', (v (i.succAbove j')).natAbs := by
            refine Finset.sum_le_sum fun j' _ => ?_
            rw [Int.natAbs_mul]
            have hcj : (c j').natAbs ≤ 1 := by
              rcases hc j' with h | h | h <;> simp [h]
            calc (c j').natAbs * (v (i.succAbove j')).natAbs
                ≤ 1 * (v (i.succAbove j')).natAbs := Nat.mul_le_mul_right _ hcj
              _ = (v (i.succAbove j')).natAbs := one_mul _
    have h2 : (∑ j', (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
      rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
      exact Nat.le_add_left _ _
    omega
  have habs : (ρ * v i - F).natAbs < Q := by
    have h1 : (ρ * v i - F).natAbs ≤ (ρ * v i).natAbs + F.natAbs :=
      Int.natAbs_sub_le _ _
    have h2 : (ρ * v i).natAbs ≤ A * (v i).natAbs := by
      rw [Int.natAbs_mul]
      have hρn : ρ.natAbs ≤ A := by
        have h3 := hρA
        rw [Int.abs_eq_natAbs] at h3
        exact_mod_cast h3
      exact Nat.mul_le_mul_right _ hρn
    have h4 : (v i).natAbs ≤ ∑ w, (v w).natAbs :=
      Finset.single_le_sum (f := fun w => (v w).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h5 : A * (v i).natAbs ≤ A * (∑ w, (v w).natAbs) := Nat.mul_le_mul_left A h4
    have h6 : A * (∑ w, (v w).natAbs) + (∑ w, (v w).natAbs)
        = (A + 1) * (∑ w, (v w).natAbs) := by ring
    omega
  have hFeq : F = ρ * v i := by
    have h0 : ρ * v i - F = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      rw [Int.abs_eq_natAbs]
      exact_mod_cast habs
    linarith
  have heq : (∑ j', c j' * v (i.succAbove j')) = ρ * v i := by
    rw [← hF]
    exact hFeq
  exact hAF ρ hρA heq

/-- The window dichotomy with strong freeness discharging the `|ρ| ≤ 1` cases. -/
theorem afree_nid_lower' {k : ℕ} (v : Fin (k + 1) → ℤ) (i : Fin (k + 1))
    (hSF : StrongFree v) (A : ℕ)
    (Q : ℕ) (hQ0 : 0 < Q) (hQbig : (A + 1) * (∑ w, (v w).natAbs) < Q)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q]) (hvpos : 0 < v i)
    (c : Fin k → ℤ) (hc : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) (hc0 : c ≠ 0)
    (hAF : ∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ (A : ℤ) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i) :
    ((A : ℝ) + 1) / Q
      ≤ nearestIntDist ((((∑ j', c j' * v (i.succAbove j')) * (b : ℤ) : ℤ) : ℝ) / Q) := by
  refine afree_nid_lower'' v i A Q hQ0 hQbig b hab hvpos c hc hc0 ?_
  intro ρ hρA heq
  by_cases hρ2 : 2 ≤ |ρ|
  · exact hAF ρ hρ2 hρA heq
  · have hρmem : ρ = -1 ∨ ρ = 0 ∨ ρ = 1 := by
      have h1 := abs_le.mp (by omega : |ρ| ≤ 1)
      omega
    set d : Fin (k + 1) → ℤ := i.insertNth (-ρ) c with hd
    have hd_same : d i = -ρ := by simp only [hd, Fin.insertNth_apply_same]
    have hd_succ : ∀ j', d (i.succAbove j') = c j' := fun j' => by
      simp only [hd, Fin.insertNth_apply_succAbove]
    have hdmem : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := by
      intro w
      refine Fin.succAboveCases i ?_ (fun j' => ?_) w
      · rw [hd_same]
        rcases hρmem with h | h | h <;> simp [h]
      · rw [hd_succ]
        exact hc j'
    have hsum0 : (∑ w, d w * v w) = 0 := by
      rw [Fin.sum_univ_succAbove (fun w => d w * v w) i, hd_same]
      have hrest : (∑ j', d (i.succAbove j') * v (i.succAbove j'))
          = ∑ j', c j' * v (i.succAbove j') :=
        Finset.sum_congr rfl fun j' _ => by rw [hd_succ]
      rw [hrest, heq]
      ring
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hc0
    have hz := hSF d hdmem hsum0 (i.succAbove j₀)
    rw [hd_succ] at hz
    exact hj₀ hz

/-- The window dichotomy, quantified over all combinations (the A-free form). -/
theorem afree_nid_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (i : Fin (k + 1))
    (hSF : StrongFree v) (A : ℕ)
    (hAF : ∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ (A : ℤ) → ∀ c : Fin k → ℤ,
        (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i)
    (Q : ℕ) (hQ0 : 0 < Q) (hQbig : (A + 1) * (∑ w, (v w).natAbs) < Q)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q]) (hvpos : 0 < v i)
    (c : Fin k → ℤ) (hc : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) (hc0 : c ≠ 0) :
    ((A : ℝ) + 1) / Q
      ≤ nearestIntDist ((((∑ j', c j' * v (i.succAbove j')) * (b : ℤ) : ℤ) : ℝ) / Q) :=
  afree_nid_lower' v i hSF A Q hQ0 hQbig b hab hvpos c hc hc0
    (fun ρ h1 h2 => hAF ρ h1 h2 c hc)

set_option maxHeartbeats 1000000 in
/-- **The floor for A-free strongly free families of at least five runners.**
With `A = 2^k(k+2)³` and a prime modulus `Q > (A+1)∑|v|`, every nonzero
combination's frequency is `(A+1)/Q`-far from the integers (`afree_nid_lower`),
so the lattice sum contributes at most `δ³Q` and the union clears the floor for
every `k ≥ 4`.  The free side of the all-`N` program reduces to `m = 4` plus
the explicit `a`-torsion classes. -/
theorem riesz_clears_floor_afree {k : ℕ} (hk : 4 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i) (hSF : StrongFree v)
    (hAF : ∀ i : Fin (k + 1), ∀ ρ : ℤ, 2 ≤ |ρ| →
        |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set A : ℕ := 2 ^ k * (k + 2) ^ 3 with hA
  obtain ⟨Q, hQp, hQN, hQsum, hQcop⟩ :=
    exists_coprime_modulus_ge (k + 1) v ((A + 1) * (∑ w, (v w).natAbs))
  have hQ0 : 0 < Q := hQp.pos
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
    riesz_mass_real (k + 1) v hSF Q hQ0 hQsum
  -- the per-runner weight bound
  have hWbound : ∀ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
      (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
      ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
    intro i
    have hvpos := hpos i
    have hvnA : (v i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hvpos)
    have hcop := hQcop i hvnA
    have htoNat : (v i).toNat = (v i).natAbs := by
      have h1 : ((v i).toNat : ℤ) = ((v i).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg hvpos.le, Int.natAbs_of_nonneg hvpos.le]
      exact_mod_cast h1
    have hcop2 : Nat.Coprime ((v i).toNat % Q) Q := by
      rw [htoNat]
      show Nat.gcd ((v i).natAbs % Q) Q = 1
      rw [← Nat.gcd_rec Q (v i).natAbs, Nat.gcd_comm]
      exact hcop
    obtain ⟨b, hab⟩ := exists_nat_inverse _ Q hQ0 hcop2
    have hSFsub : StrongFree (fun j' : Fin k => v (i.succAbove j')) :=
      strongFree_succAbove v hSF i
    have hWF := badset_weight_fourier v Q hQ0 hQsum i hvpos b hab hSFsub δ hδ2
    -- count term
    have hfeq := badset_filter_eq Q hQ0 (v i) hvpos δ
    have hcard := badset_card_bound Q hQ0 ((v i).toNat % Q) b hab δ hδ0.le hδ2
    have hcard' : (((Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        ≤ 2 * δ * Q + 2 := by
      rw [hfeq]
      exact hcard
    -- per-combination bound
    have hperc : ∀ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
            * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
          ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
      intro c hc
      rw [Finset.mem_erase] at hc
      obtain ⟨hc0, hcmem⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have hnid := afree_nid_lower v i hSF A (hAF i) Q hQ0 hQN b hab hvpos c hcmem' hc0
      have hnorm := norm_one_sub_exp_nid Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ))
      set t : ℝ := nearestIntDist
        ((((∑ j', c j' * v (i.succAbove j')) * (b : ℤ) : ℤ) : ℝ) / Q) with ht
      have ht2 : t ≤ 1 / 2 := nearestIntDist_le_half _
      have ht0 : 0 ≤ t := nearestIntDist_nonneg _
      have hsin : 2 * t ≤ Real.sin (π * t) := by
        have hj := Real.mul_le_sin (x := π * t) (by positivity)
          (by nlinarith [Real.pi_pos, ht2])
        have hππ : 2 / π * (π * t) = 2 * t := by
          field_simp
        linarith [hj, hππ.symm.le, hππ.le]
      have hnormge : 4 * (((A : ℝ) + 1) / Q) ≤ ‖1 - Complex.exp (2 * ↑π * Complex.I
          * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖ := by
        rw [hnorm]
        calc 4 * (((A : ℝ) + 1) / Q) ≤ 4 * t := by linarith [hnid]
          _ = 2 * (2 * t) := by ring
          _ ≤ 2 * Real.sin (π * t) := by linarith [hsin]
      have hpos4 : (0 : ℝ) < 4 * (((A : ℝ) + 1) / Q) := by positivity
      calc 4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
            * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
          ≤ 4 / (4 * (((A : ℝ) + 1) / Q)) := by
            have h1 := one_div_le_one_div_of_le hpos4 hnormge
            calc (4 : ℝ) / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
                = 4 * (1 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := by ring
              _ ≤ 4 * (1 / (4 * (((A : ℝ) + 1) / Q))) := by linarith [h1]
              _ = 4 / (4 * (((A : ℝ) + 1) / Q)) := by ring
        _ = (Q : ℝ) / ((A : ℝ) + 1) := by
            rw [div_eq_iff (by positivity : (4 : ℝ) * (((A : ℝ) + 1) / Q) ≠ 0)]
            field_simp
      
    -- the weight sum
    have hwtnn : ∀ c : Fin k → ℤ, (0 : ℝ) ≤ ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
      fun c => Finset.prod_nonneg fun j' _ => by positivity
    have hsum_wt : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (2 ^ k : ℝ) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ ∑ c ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun c _ _ => hwtnn c)
        _ = ∏ _j' : Fin k, ∑ a ∈ ({-1, 0, 1} : Finset ℤ), (if a = 0 then (1 : ℝ) else 1 / 2) := by
            rw [Finset.prod_univ_sum]
        _ = (2 ^ k : ℝ) := by
            have hthree : ∑ a ∈ ({-1, 0, 1} : Finset ℤ), (if a = 0 then (1 : ℝ) else 1 / 2)
                = 2 := by
              rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
                Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              norm_num
            rw [Finset.prod_congr rfl fun _ _ => hthree, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    have hLsum : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
              * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
        ≤ (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
              * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
          ≤ ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
            Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
        _ = (∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
            rw [Finset.sum_mul]
        _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hsum_wt (by positivity)
        _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
    calc ∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
        ≤ (((Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
          + ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                    * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hWF
      _ ≤ (2 * δ * Q + 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := add_le_add hcard' hLsum
      _ = 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
  refine riesz_union_weights v Q hQ0 δ hδ0 hδ2 (Q : ℝ) hmass
    (fun _ => 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) hWbound ?_
  -- the union arithmetic
  have hsumW : (∑ _i : Fin (k + 1), (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)))
      = ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumW]
  -- lattice term ≤ δ³Q
  have hA3 : (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) ≤ δ ^ 3 * Q := by
    have hAval : ((A : ℝ) + 1) = (2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1 := by
      rw [hA]
      push_cast
      ring
    have hδ3 : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by
      rw [hδdef]
      field_simp
    rw [div_le_iff₀ (by rw [hAval]; positivity)]
    rw [hAval]
    have hexp : δ ^ 3 * (Q : ℝ) * ((2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1)
        = (2 ^ k : ℝ) * Q * (((k : ℝ) + 2) ^ 3 * δ ^ 3) + δ ^ 3 * Q := by ring
    rw [hexp, hδ3, mul_one]
    nlinarith [pow_pos hδ0 3, hQR]
  -- cosine bound
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  -- key numeric facts
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hδ3' : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by rw [hδdef]; field_simp
  have hδ2'' : ((k : ℝ) + 2) ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp
  have h216 : 216 * ((k : ℝ) + 1) ≤ 5 * ((k : ℝ) + 2) ^ 3 := by
    have hfac : 5 * ((k : ℝ) + 2) ^ 3 - 216 * ((k : ℝ) + 1)
        = ((k : ℝ) - 4) * (5 * (k : ℝ) ^ 2 + 50 * (k : ℝ) + 44) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 4)
      (by nlinarith [hkR] : (0 : ℝ) ≤ 5 * (k : ℝ) ^ 2 + 50 * (k : ℝ) + 44)]
  have hT1 : ((k : ℝ) + 1) * δ ^ 3 ≤ 5 / 216 := by
    have h2 : 216 * (((k : ℝ) + 1) * δ ^ 3) ≤ 5 * (((k : ℝ) + 2) ^ 3 * δ ^ 3) := by
      nlinarith [h216, pow_pos hδ0 3]
    rw [hδ3'] at h2
    linarith
  have h6 : 6 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [hkR]
  have hT3 : ((k : ℝ) + 1) * δ ^ 2 ≤ 1 / 6 := by
    have h2 : 6 * (((k : ℝ) + 1) * δ ^ 2) ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
      nlinarith [h6, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  have hδ36 : δ ^ 2 ≤ 1 / 36 := by
    have h2 : 36 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
      nlinarith [hkR, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  -- Q is large
  have hsum1 : k + 1 ≤ ∑ w, (v w).natAbs := by
    calc k + 1 = ∑ _w : Fin (k + 1), 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ ≤ ∑ w, (v w).natAbs := by
          refine Finset.sum_le_sum fun w _ => ?_
          have := hpos w
          have h1 : (v w).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt this)
          omega
  have hQ97 : (97 : ℝ) ≤ (Q : ℝ) := by
    have hA1 : 3456 ≤ A := by
      rw [hA]
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have h2 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 3456 = 2 ^ 4 * 6 ^ 3 := by norm_num
        _ ≤ 2 ^ k * (k + 2) ^ 3 := Nat.mul_le_mul h1 h2
    have hQbig : 97 ≤ Q := by
      have h3 : (A + 1) * (∑ w, (v w).natAbs) ≥ 3457 * 5 := by
        have h4 : 5 ≤ ∑ w, (v w).natAbs := by omega
        exact Nat.mul_le_mul (by omega) h4
      omega
    exact_mod_cast hQbig
  -- assemble
  have hmid : ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
      ≤ ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith [hA3]
  have hpos1 : (0 : ℝ) < ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) := by positivity
  calc ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        * (1 - Real.cos (2 * π * δ))
      ≤ ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) * (1 - Real.cos (2 * π * δ)) :=
        mul_le_mul_of_nonneg_right hmid hcosnn
    _ < ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) * (2 * (π * δ) ^ 2) :=
        mul_lt_mul_of_pos_left hu hpos1
    _ ≤ (Q : ℝ) * (4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3))
        + 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2)
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2) := by
        have hexp : ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) * (2 * (π * δ) ^ 2)
            = (Q : ℝ) * (4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3))
              + 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2)
              + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2) := by ring
        rw [hexp]
    _ < (Q : ℝ) := by
        have hb1 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) ≤ 4 * 9.9225 * (5 / 216) := by
          nlinarith [hT1, hπ2, Real.pi_pos, pow_pos hδ0 3,
            mul_pos (by linarith : (0:ℝ) < (k:ℝ)+1) (pow_pos hδ0 3)]
        have hb2 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2) ≤ 4 * 9.9225 * (1 / 6) := by
          nlinarith [hT3, hπ2, Real.pi_pos,
            mul_pos (by linarith : (0:ℝ) < (k:ℝ)+1) (pow_pos hδ0 2)]
        have hb3 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2
            ≤ 2 * 9.9225 * (5 / 216) * (1 / 36) := by
          nlinarith [hT1, hπ2, hδ36, Real.pi_pos, pow_pos hδ0 2, pow_pos hδ0 3,
            mul_pos (by linarith : (0:ℝ) < (k:ℝ)+1) (pow_pos hδ0 3)]
        nlinarith [hb1, hb2, hb3, hQ97, hQR]


/-! ### The torsion side: resonant combinations and the single-torsion floor -/

/-- **The per-combination inversion**: an `(A+1)/Q` nearest-integer lower bound
turns into the `Q/(A+1)` Fourier-denominator bound, via `‖1−e(θ)‖ = 2 sin(π‖θ‖)`
and Jordan's inequality. -/
theorem afree_perc_bound (Q : ℕ) (hQ0 : 0 < Q) (H : ℤ) (A : ℕ)
    (hnid : ((A : ℝ) + 1) / Q ≤ nearestIntDist ((H : ℝ) / Q)) :
    4 / ‖1 - Complex.exp (2 * ↑π * Complex.I * (H : ℂ) / ↑Q)‖
      ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hnorm := norm_one_sub_exp_nid Q hQ0 H
  set t : ℝ := nearestIntDist ((H : ℝ) / Q) with ht
  have ht2 : t ≤ 1 / 2 := nearestIntDist_le_half _
  have ht0 : 0 ≤ t := nearestIntDist_nonneg _
  have hsin : 2 * t ≤ Real.sin (π * t) := by
    have hj := Real.mul_le_sin (x := π * t) (by positivity)
      (by nlinarith [Real.pi_pos, ht2])
    have hππ : 2 / π * (π * t) = 2 * t := by
      field_simp
    linarith [hj, hππ.symm.le, hππ.le]
  have hnormge : 4 * (((A : ℝ) + 1) / Q)
      ≤ ‖1 - Complex.exp (2 * ↑π * Complex.I * (H : ℂ) / ↑Q)‖ := by
    rw [hnorm]
    calc 4 * (((A : ℝ) + 1) / Q) ≤ 4 * t := by linarith [hnid]
      _ = 2 * (2 * t) := by ring
      _ ≤ 2 * Real.sin (π * t) := by linarith [hsin]
  have hpos4 : (0 : ℝ) < 4 * (((A : ℝ) + 1) / Q) := by positivity
  calc 4 / ‖1 - Complex.exp (2 * ↑π * Complex.I * (H : ℂ) / ↑Q)‖
      ≤ 4 / (4 * (((A : ℝ) + 1) / Q)) := by
        have h1 := one_div_le_one_div_of_le hpos4 hnormge
        calc (4 : ℝ) / ‖1 - Complex.exp (2 * ↑π * Complex.I * (H : ℂ) / ↑Q)‖
            = 4 * (1 / ‖1 - Complex.exp (2 * ↑π * Complex.I * (H : ℂ) / ↑Q)‖) := by ring
          _ ≤ 4 * (1 / (4 * (((A : ℝ) + 1) / Q))) := by linarith [h1]
          _ = 4 / (4 * (((A : ℝ) + 1) / Q)) := by ring
    _ = (Q : ℝ) / ((A : ℝ) + 1) := by
        rw [div_eq_iff (by positivity : (4 : ℝ) * (((A : ℝ) + 1) / Q) ≠ 0)]
        field_simp

set_option maxHeartbeats 1000000 in
/-- **The bad-set weight bound with a resonant exception set.**  Combinations in
`R` keep the trivial bound `|S(c)| ≤ |B_i|`; the rest get the geometric-sum
Fourier bound.  With `R = ∅` this recovers `badset_weight_fourier`. -/
theorem badset_weight_split' {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQsum : (∑ w, (v w).natAbs) < Q) (i : Fin (k + 1)) (hvpos : 0 < v i)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q])
    (δ : ℝ) (hδ : δ ≤ 1 / 2) (R : Finset (Fin k → ℤ))
    (hR : R ⊆ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
    (hF0 : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) \ R,
        (∑ j', c j' * v (i.succAbove j')) ≠ 0) :
    ∑ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ (((Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
          * (1 + ∑ c ∈ R, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
        + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) \ R,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
              * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := by
  classical
  set S := (Finset.range Q).filter
    (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ) with hSdef
  set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
  have hcs : ((∑ j ∈ S, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ S, ∏ j' : Fin k, (1 - Complex.cos (2 * ↑π * ↑(v' j') * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun j' _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hnn : 0 ≤ ∑ j ∈ S, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
    refine Finset.sum_nonneg fun j _ => Finset.prod_nonneg fun j' _ => ?_
    have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hnorm : (∑ j ∈ S, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
      = ‖(∑ j ∈ S, ∏ j' : Fin k, (1 - Complex.cos (2 * ↑π * ↑(v' j') * ↑j / ↑Q)) : ℂ)‖ := by
    rw [← hcs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, riesz_badset_expand_pub k v' Q S]
  have h0mem : (0 : Fin k → ℤ) ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)) := by
    rw [Fintype.mem_piFinset]
    intro j'
    simp
  rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.sum_sdiff hR]
  have hT0 : ‖(∏ j' : Fin k, (if (0 : Fin k → ℤ) j' = 0 then (1 : ℂ) else -1 / 2))
      * ∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I
          * ↑(∑ j', (0 : Fin k → ℤ) j' * v' j') * ↑j / ↑Q)‖ ≤ (S.card : ℝ) := by
    have hwt0 : (∏ j' : Fin k, (if (0 : Fin k → ℤ) j' = 0 then (1 : ℂ) else -1 / 2)) = 1 :=
      Finset.prod_eq_one fun j' _ => if_pos rfl
    have hF0 : (∑ j', (0 : Fin k → ℤ) j' * v' j') = 0 :=
      Finset.sum_eq_zero fun j' _ => zero_mul _
    have hexp0 : ∀ j : ℕ, Complex.exp (2 * ↑π * Complex.I
        * ↑(∑ j', (0 : Fin k → ℤ) j' * v' j') * ↑j / ↑Q) = 1 := by
      intro j
      rw [hF0]
      norm_num
    rw [hwt0, one_mul, Finset.sum_congr rfl (fun j _ => hexp0 j), Finset.sum_const,
      nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hunit : ∀ (H : ℤ) (j : ℕ),
      ‖Complex.exp (2 * ↑π * Complex.I * (H : ℂ) * (j : ℂ) / (Q : ℂ))‖ = 1 := by
    intro H j
    rw [show (2 * (π : ℂ) * Complex.I * (H : ℂ) * (j : ℂ) / (Q : ℂ))
        = ((2 * π * (H : ℝ) * (j : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hres : ‖∑ c ∈ R, (∏ j' : Fin k, (if c j' = 0 then (1 : ℂ) else -1 / 2))
      * ∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I * ↑(∑ j', c j' * v' j') * ↑j / ↑Q)‖
      ≤ (∑ c ∈ R, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * (S.card : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [norm_mul]
    have hwt : ‖∏ j' : Fin k, (if c j' = 0 then (1 : ℂ) else -1 / 2)‖
        = ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun j' _ => ?_
      split_ifs
      · exact norm_one
      · rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs]
        norm_num
    rw [hwt]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j' _ => by positivity)
    calc ‖∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I * ↑(∑ j', c j' * v' j') * ↑j / ↑Q)‖
        ≤ ∑ j ∈ S, ‖Complex.exp (2 * ↑π * Complex.I * ↑(∑ j', c j' * v' j') * ↑j / ↑Q)‖ :=
          norm_sum_le _ _
      _ = ∑ _j ∈ S, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hunit _ j
      _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsdiff : ‖∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) \ R,
      (∏ j' : Fin k, (if c j' = 0 then (1 : ℂ) else -1 / 2))
        * ∑ j ∈ S, Complex.exp (2 * ↑π * Complex.I * ↑(∑ j', c j' * v' j') * ↑j / ↑Q)‖
      ≤ ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) \ R,
          (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
            * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                * ↑((∑ j', c j' * v' j') * (b : ℤ)) / ↑Q)‖) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro c hc
    have hFne : (∑ j', c j' * v' j') ≠ 0 := hF0 c hc
    rw [Finset.mem_sdiff] at hc
    obtain ⟨hcE, _⟩ := hc
    rw [Finset.mem_erase] at hcE
    obtain ⟨hc0, hcmem⟩ := hcE
    rw [norm_mul]
    have hwt : ‖∏ j' : Fin k, (if c j' = 0 then (1 : ℂ) else -1 / 2)‖
        = ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun j' _ => ?_
      split_ifs
      · exact norm_one
      · rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs]
        norm_num
    rw [hwt]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j' _ => by positivity)
    have hFabs : (∑ j', c j' * v' j').natAbs < Q := by
      have hb : (∑ j', c j' * v' j').natAbs ≤ ∑ j', (v' j').natAbs := by
        calc (∑ j', c j' * v' j').natAbs ≤ ∑ j', (c j' * v' j').natAbs :=
              Int.natAbs_sum_le _ _
          _ ≤ ∑ j', (v' j').natAbs := by
              refine Finset.sum_le_sum fun j' _ => ?_
              rw [Int.natAbs_mul]
              have hcj : (c j').natAbs ≤ 1 := by
                have := (Fintype.mem_piFinset.mp hcmem) j'
                simp only [Finset.mem_insert, Finset.mem_singleton] at this
                rcases this with h | h | h <;> simp [h]
              calc (c j').natAbs * (v' j').natAbs ≤ 1 * (v' j').natAbs :=
                    Nat.mul_le_mul_right _ hcj
                _ = (v' j').natAbs := one_mul _
      have hsub : (∑ j', (v' j').natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        simp only [hv'def]
        exact Nat.le_add_left _ _
      omega
    have hFdvd : ¬ (Q : ℤ) ∣ (∑ j', c j' * v' j') := by
      intro hdvd
      apply hFne
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hFabs
    have hw : ¬ (Q : ℤ) ∣ (∑ j', c j' * v' j') * (b : ℤ) :=
      not_dvd_mul_inv Q ((v i).toNat % Q) b hab _ hFdvd
    exact badset_fourier_bound Q hQ0 (v i) hvpos b hab
      (∑ j', c j' * v' j') hw δ hδ
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hT0 (le_trans (norm_add_le _ _) (add_le_add hsdiff hres)))
    (le_of_eq (by ring))

/-- `badset_weight_split'` with the nonvanishing of nonresonant combinations
supplied by strong freeness of the subfamily. -/
theorem badset_weight_split {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQsum : (∑ w, (v w).natAbs) < Q) (i : Fin (k + 1)) (hvpos : 0 < v i)
    (b : ℕ) (hab : ((v i).toNat % Q) * b ≡ 1 [MOD Q])
    (hSF : StrongFree (fun j' : Fin k => v (i.succAbove j')))
    (δ : ℝ) (hδ : δ ≤ 1 / 2) (R : Finset (Fin k → ℤ))
    (hR : R ⊆ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) :
    ∑ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ (((Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
          * (1 + ∑ c ∈ R, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
        + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) \ R,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
              * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                  * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := by
  refine badset_weight_split' v Q hQ0 hQsum i hvpos b hab δ hδ R hR ?_
  intro c hc hF
  rw [Finset.mem_sdiff, Finset.mem_erase] at hc
  obtain ⟨⟨hc0, hcmem⟩, _⟩ := hc
  apply hc0
  funext j'
  have hcmem' : ∀ j'', c j'' = -1 ∨ c j'' = 0 ∨ c j'' = 1 := by
    intro j''
    have := (Fintype.mem_piFinset.mp hcmem) j''
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  exact hSF c hcmem' hF j'

set_option maxHeartbeats 4000000 in
/-- **The floor for single-torsion families.**  If the family is strongly free
and carries exactly one torsion relation `a·v_{i₀} = ∑ c₀·v` (all other runners
torsion-free, no second relation at `i₀`), then the resonant combinations are
exactly `±c₀`; keeping their trivial bound, the union clears the floor whenever
`k ≥ 5`, or `k ≥ 4` and the relation has support at least `3`. -/
theorem riesz_clears_floor_torsion_single {k : ℕ} (hk : 4 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i) (hSF : StrongFree v)
    (i₀ : Fin (k + 1)) (a : ℤ) (c₀ : Fin k → ℤ) (ha0 : a ≠ 0)
    (hc₀ : ∀ j', c₀ j' = -1 ∨ c₀ j' = 0 ∨ c₀ j' = 1)
    (hrel : (∑ j', c₀ j' * v (i₀.succAbove j')) = a * v i₀)
    (hAFo : ∀ i : Fin (k + 1), i ≠ i₀ → ∀ ρ : ℤ, 2 ≤ |ρ| →
        |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i)
    (huniq : ∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i₀.succAbove j')) = ρ * v i₀ → c = c₀ ∨ c = -c₀)
    (hks : 5 ≤ k ∨ 3 ≤ (Finset.univ.filter (fun j' => c₀ j' ≠ 0)).card) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set A : ℕ := 2 ^ k * (k + 2) ^ 3 with hA
  obtain ⟨Q, hQp, hQN, hQsum, hQcop⟩ :=
    exists_coprime_modulus_ge (k + 1) v ((A + 1) * (∑ w, (v w).natAbs))
  have hQ0 : 0 < Q := hQp.pos
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
    riesz_mass_real (k + 1) v hSF Q hQ0 hQsum
  -- the distinguished combination is nonzero, with its weight
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    rw [h0] at hrel
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hrel
    have hne : a * v i₀ ≠ 0 := mul_ne_zero ha0 (ne_of_gt (hpos i₀))
    exact hne hrel.symm
  set w₀ : ℝ := ∏ j', (if c₀ j' = 0 then (1 : ℝ) else 1 / 2) with hw₀def
  have hw₀nn : 0 ≤ w₀ := by
    rw [hw₀def]
    exact Finset.prod_nonneg fun _ _ => by positivity
  have hw₀pow : ∀ n : ℕ, n ≤ (Finset.univ.filter (fun j' : Fin k => c₀ j' ≠ 0)).card →
      w₀ ≤ (1 / 2 : ℝ) ^ n := by
    intro n hn
    have hTeq : w₀ = (1 / 2 : ℝ) ^ (Finset.univ.filter (fun j' : Fin k => c₀ j' ≠ 0)).card := by
      rw [hw₀def]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j' => c₀ j' ≠ 0)
        (fun j' => (if c₀ j' = 0 then (1 : ℝ) else 1 / 2))]
      have h1 : ∀ j' ∈ Finset.univ.filter (fun j' : Fin k => c₀ j' ≠ 0),
          (if c₀ j' = 0 then (1 : ℝ) else 1 / 2) = 1 / 2 := by
        intro j' hj'
        rw [Finset.mem_filter] at hj'
        rw [if_neg hj'.2]
      have h2 : ∀ j' ∈ Finset.univ.filter (fun j' : Fin k => ¬ c₀ j' ≠ 0),
          (if c₀ j' = 0 then (1 : ℝ) else 1 / 2) = 1 := by
        intro j' hj'
        rw [Finset.mem_filter] at hj'
        have h3 : c₀ j' = 0 := not_not.mp hj'.2
        rw [if_pos h3]
      rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const,
        Finset.prod_const, one_pow, mul_one]
    rw [hTeq]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hw₀le : w₀ ≤ 1 / 2 := by
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hc₀0
    have hj₀' : c₀ j₀ ≠ 0 := by simpa using hj₀
    have h1 : 1 ≤ (Finset.univ.filter (fun j' : Fin k => c₀ j' ≠ 0)).card :=
      Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀'⟩⟩
    calc w₀ ≤ (1 / 2 : ℝ) ^ 1 := hw₀pow 1 h1
      _ = 1 / 2 := pow_one _
  set W : Fin (k + 1) → ℝ := fun i => if i = i₀
      then (2 * δ * Q + 2) * (1 + 2 * w₀) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)
      else 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) with hW
  -- the per-runner weight bounds
  have hWbound : ∀ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
      (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
      ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ W i := by
    intro i
    have hvpos := hpos i
    have hvnA : (v i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hvpos)
    have hcop := hQcop i hvnA
    have htoNat : (v i).toNat = (v i).natAbs := by
      have h1 : ((v i).toNat : ℤ) = ((v i).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg hvpos.le, Int.natAbs_of_nonneg hvpos.le]
      exact_mod_cast h1
    have hcop2 : Nat.Coprime ((v i).toNat % Q) Q := by
      rw [htoNat]
      show Nat.gcd ((v i).natAbs % Q) Q = 1
      rw [← Nat.gcd_rec Q (v i).natAbs, Nat.gcd_comm]
      exact hcop
    obtain ⟨b, hab⟩ := exists_nat_inverse _ Q hQ0 hcop2
    have hSFsub : StrongFree (fun j' : Fin k => v (i.succAbove j')) :=
      strongFree_succAbove v hSF i
    have hfeq := badset_filter_eq Q hQ0 (v i) hvpos δ
    have hcard := badset_card_bound Q hQ0 ((v i).toNat % Q) b hab δ hδ0.le hδ2
    have hcard' : (((Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        ≤ 2 * δ * Q + 2 := by
      rw [hfeq]
      exact hcard
    have hwtnn : ∀ c : Fin k → ℤ, (0 : ℝ) ≤ ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
      fun c => Finset.prod_nonneg fun j' _ => by positivity
    have hsum_wt : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (2 ^ k : ℝ) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ ∑ c ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun c _ _ => hwtnn c)
        _ = ∏ _j' : Fin k, ∑ a' ∈ ({-1, 0, 1} : Finset ℤ), (if a' = 0 then (1 : ℝ) else 1 / 2) := by
            rw [Finset.prod_univ_sum]
        _ = (2 ^ k : ℝ) := by
            have hthree : ∑ a' ∈ ({-1, 0, 1} : Finset ℤ), (if a' = 0 then (1 : ℝ) else 1 / 2)
                = 2 := by
              rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
                Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              norm_num
            rw [Finset.prod_congr rfl fun _ _ => hthree, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    by_cases hii : i = i₀
    · subst hii
      -- the torsion runner: resonant pair `±c₀`
      have hRsub : ({c₀, -c₀} : Finset (Fin k → ℤ)) ⊆
          (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0 := by
        intro c hc
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        rw [Finset.mem_erase]
        rcases hc with h | h
        · subst h
          refine ⟨hc₀0, ?_⟩
          rw [Fintype.mem_piFinset]
          intro j'
          rcases hc₀ j' with h | h | h <;> simp [h]
        · subst h
          refine ⟨fun h0 => hc₀0 (neg_eq_zero.mp h0), ?_⟩
          rw [Fintype.mem_piFinset]
          intro j'
          rcases hc₀ j' with h | h | h <;> simp [Pi.neg_apply, h]
      have hsplit := badset_weight_split v Q hQ0 hQsum i hvpos b hab hSFsub δ hδ2
        ({c₀, -c₀} : Finset (Fin k → ℤ)) hRsub
      have hwneg : (∏ j', (if (-c₀) j' = 0 then (1 : ℝ) else 1 / 2)) = w₀ := by
        rw [hw₀def]
        refine Finset.prod_congr rfl fun j' _ => ?_
        simp [Pi.neg_apply, neg_eq_zero]
      have hRsum : ∑ c ∈ ({c₀, -c₀} : Finset (Fin k → ℤ)),
          (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 2 * w₀ := by
        by_cases hcc : c₀ = -c₀
        · have hpair : ({c₀, -c₀} : Finset (Fin k → ℤ)) = {-c₀} := by
            rw [← hcc]
            exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
          rw [hpair, Finset.sum_singleton, hwneg]
          linarith [hw₀nn]
        · rw [Finset.sum_pair hcc, hwneg, ← hw₀def]
          linarith [hw₀nn]
      have hperc : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
          \ ({c₀, -c₀} : Finset (Fin k → ℤ)),
          4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
              * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
            ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
        intro c hc
        rw [Finset.mem_sdiff] at hc
        obtain ⟨hcE, hcR⟩ := hc
        rw [Finset.mem_erase] at hcE
        obtain ⟨hc0, hcmem⟩ := hcE
        have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
          intro j'
          have := (Fintype.mem_piFinset.mp hcmem) j'
          simpa only [Finset.mem_insert, Finset.mem_singleton] using this
        have hEX : ∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ (A : ℤ) →
            (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i := by
          intro ρ h1 h2 heq
          rcases huniq ρ h1 h2 c hcmem' heq with h | h
          · exact hcR (by rw [h]; exact Finset.mem_insert_self _ _)
          · exact hcR (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hnid := afree_nid_lower' v i hSF A Q hQ0 hQN b hab hvpos c hcmem' hc0 hEX
        exact afree_perc_bound Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) A hnid
      calc ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
          ≤ (((Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
              * (1 + ∑ c ∈ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                  ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
            + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                \ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                  * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                      * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hsplit
        _ ≤ (2 * δ * Q + 2) * (1 + 2 * w₀) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
            refine add_le_add ?_ ?_
            · have hRnn : (0 : ℝ) ≤ ∑ c ∈ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                  ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
                Finset.sum_nonneg fun c _ => hwtnn c
              refine mul_le_mul hcard' (by linarith [hRsum]) (by linarith [hRnn]) ?_
              positivity
            · calc ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                    \ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                    (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                      * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                          * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
                  ≤ ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                    \ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                    (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
                    Finset.sum_le_sum fun c hc =>
                      mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
                _ = (∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                    \ ({c₀, -c₀} : Finset (Fin k → ℤ)),
                    (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                    rw [Finset.sum_mul]
                _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                      Finset.sdiff_subset (fun c _ _ => hwtnn c)) hsum_wt
                _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
        _ = W i := by simp [hW]
    · -- torsion-free runner: the A-free chain
      have hperc : ∀ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
          4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
              * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
            ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
        intro c hc
        rw [Finset.mem_erase] at hc
        obtain ⟨hc0, hcmem⟩ := hc
        have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
          intro j'
          have := (Fintype.mem_piFinset.mp hcmem) j'
          simpa only [Finset.mem_insert, Finset.mem_singleton] using this
        have hnid := afree_nid_lower' v i hSF A Q hQ0 hQN b hab hvpos c hcmem' hc0
          (fun ρ h1 h2 => hAFo i hii ρ h1 h2 c hcmem')
        exact afree_perc_bound Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) A hnid
      have hWF := badset_weight_fourier v Q hQ0 hQsum i hvpos b hab hSFsub δ hδ2
      have hLsum : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
          (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
            * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
          ≤ (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
        calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                    * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
            ≤ ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
              Finset.sum_le_sum fun c hc =>
                mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
          _ = (∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
              rw [Finset.sum_mul]
          _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hsum_wt (by positivity)
          _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
      calc ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
          ≤ (((Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
            + ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
                (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                  * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                      * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hWF
        _ ≤ 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := add_le_add hcard' hLsum
        _ = W i := by simp only [hW]; rw [if_neg hii]
  refine riesz_union_weights v Q hQ0 δ hδ0 hδ2 (Q : ℝ) hmass W hWbound ?_
  -- the union arithmetic with the resonant surcharge
  have hsumW : ∑ i, W i
      = ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        + 2 * w₀ * (2 * δ * Q + 2) := by
    have hsplit2 : ∑ i, W i = W i₀ + ∑ i ∈ Finset.univ.erase i₀, W i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    have hWi₀ : W i₀ = (2 * δ * Q + 2) * (1 + 2 * w₀) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
      simp [hW]
    have hWe : ∀ i ∈ Finset.univ.erase i₀,
        W i = 2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
      intro i hi
      simp only [hW]
      rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [hsplit2, hWi₀, Finset.sum_congr rfl hWe, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumW]
  have hA3 : (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) ≤ δ ^ 3 * Q := by
    have hAval : ((A : ℝ) + 1) = (2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1 := by
      rw [hA]
      push_cast
      ring
    have hδ3 : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by
      rw [hδdef]
      field_simp
    rw [div_le_iff₀ (by rw [hAval]; positivity)]
    rw [hAval]
    have hexp : δ ^ 3 * (Q : ℝ) * ((2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1)
        = (2 ^ k : ℝ) * Q * (((k : ℝ) + 2) ^ 3 * δ ^ 3) + δ ^ 3 * Q := by ring
    rw [hexp, hδ3, mul_one]
    nlinarith [pow_pos hδ0 3, hQR]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hδ3' : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by rw [hδdef]; field_simp
  have hδ2'' : ((k : ℝ) + 2) ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp
  have hsum1 : k + 1 ≤ ∑ w, (v w).natAbs := by
    calc k + 1 = ∑ _w : Fin (k + 1), 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ ≤ ∑ w, (v w).natAbs := by
          refine Finset.sum_le_sum fun w _ => ?_
          have := hpos w
          have h1 : (v w).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt this)
          omega
  have hQ340 : (340 : ℝ) ≤ (Q : ℝ) := by
    have hA1 : 3456 ≤ A := by
      rw [hA]
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have h2 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 3456 = 2 ^ 4 * 6 ^ 3 := by norm_num
        _ ≤ 2 ^ k * (k + 2) ^ 3 := Nat.mul_le_mul h1 h2
    have hQbig : 340 ≤ Q := by
      have h3 : (A + 1) * (∑ w, (v w).natAbs) ≥ 3457 * 5 := by
        have h4 : 5 ≤ ∑ w, (v w).natAbs := by omega
        exact Nat.mul_le_mul (by omega) h4
      omega
    exact_mod_cast hQbig
  have hmid : ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        + 2 * w₀ * (2 * δ * Q + 2)
      ≤ ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) + 2 * w₀ * (2 * δ * Q + 2) := by
    have h1 : ((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        ≤ ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) :=
      mul_le_mul_of_nonneg_left (by linarith [hA3]) (by linarith)
    linarith
  have hpos1 : (0 : ℝ) < ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q)
      + 2 * w₀ * (2 * δ * Q + 2) := by
    have h2 : (0 : ℝ) ≤ 2 * w₀ * (2 * δ * Q + 2) := by
      have h3 : (0 : ℝ) ≤ 2 * δ * Q + 2 := by positivity
      nlinarith [hw₀nn]
    have h4 : (0 : ℝ) < ((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) := by positivity
    linarith
  calc (((k : ℝ) + 1) * (2 * δ * Q + 2 + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        + 2 * w₀ * (2 * δ * Q + 2)) * (1 - Real.cos (2 * π * δ))
      ≤ (((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) + 2 * w₀ * (2 * δ * Q + 2))
          * (1 - Real.cos (2 * π * δ)) :=
        mul_le_mul_of_nonneg_right hmid hcosnn
    _ < (((k : ℝ) + 1) * (2 * δ * Q + 2 + δ ^ 3 * Q) + 2 * w₀ * (2 * δ * Q + 2))
          * (2 * (π * δ) ^ 2) :=
        mul_lt_mul_of_pos_left hu hpos1
    _ = (Q : ℝ) * (4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3))
        + 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2)
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2)
        + ((Q : ℝ) * (4 * π ^ 2 * (2 * w₀ * δ ^ 3)) + 4 * π ^ 2 * (2 * w₀ * δ ^ 2)) := by
        ring
    _ < (Q : ℝ) := by
        rcases hks with hk5 | hs3
        · -- six or more runners: the resonant pair fits inside one extra runner
          have hk5R : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
          have h343 : 343 * ((k : ℝ) + 1) ≤ 6 * ((k : ℝ) + 2) ^ 3 := by
            have hfac : 6 * ((k : ℝ) + 2) ^ 3 - 343 * ((k : ℝ) + 1)
                = ((k : ℝ) - 5) * (6 * (k : ℝ) ^ 2 + 66 * (k : ℝ) + 59) := by ring
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
              (by nlinarith [hk5R] : (0 : ℝ) ≤ 6 * (k : ℝ) ^ 2 + 66 * (k : ℝ) + 59)]
          have hT1' : ((k : ℝ) + 1) * δ ^ 3 ≤ 6 / 343 := by
            have h2 : 343 * (((k : ℝ) + 1) * δ ^ 3) ≤ 6 * (((k : ℝ) + 2) ^ 3 * δ ^ 3) := by
              nlinarith [h343, pow_pos hδ0 3]
            rw [hδ3'] at h2
            linarith
          have h3433 : 343 ≤ ((k : ℝ) + 2) ^ 3 := by
            have hfac : ((k : ℝ) + 2) ^ 3 - 343 = ((k : ℝ) - 5) * ((k : ℝ) ^ 2 + 11 * (k : ℝ) + 67) := by
              ring
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
              (by nlinarith [hk5R] : (0 : ℝ) ≤ (k : ℝ) ^ 2 + 11 * (k : ℝ) + 67)]
          have hδ343 : δ ^ 3 ≤ 1 / 343 := by
            have h2 : 343 * δ ^ 3 ≤ ((k : ℝ) + 2) ^ 3 * δ ^ 3 := by
              nlinarith [h3433, pow_pos hδ0 3]
            rw [hδ3'] at h2
            linarith
          have h49 : 49 ≤ ((k : ℝ) + 2) ^ 2 := by
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
              (by linarith : (0 : ℝ) ≤ (k : ℝ) + 9)]
          have hδ49 : δ ^ 2 ≤ 1 / 49 := by
            have h2 : 49 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
              nlinarith [h49, pow_pos hδ0 2]
            rw [hδ2''] at h2
            linarith
          have h649 : 49 * ((k : ℝ) + 1) ≤ 6 * ((k : ℝ) + 2) ^ 2 := by
            have hfac : 6 * ((k : ℝ) + 2) ^ 2 - 49 * ((k : ℝ) + 1)
                = ((k : ℝ) - 5) * (6 * (k : ℝ) + 5) := by ring
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
              (by linarith : (0 : ℝ) ≤ 6 * (k : ℝ) + 5)]
          have hT3' : ((k : ℝ) + 1) * δ ^ 2 ≤ 6 / 49 := by
            have h2 : 49 * (((k : ℝ) + 1) * δ ^ 2) ≤ 6 * (((k : ℝ) + 2) ^ 2 * δ ^ 2) := by
              nlinarith [h649, pow_pos hδ0 2]
            rw [hδ2''] at h2
            linarith
          have hw₀3 : 2 * w₀ * δ ^ 3 ≤ 1 / 343 := by
            nlinarith [hδ343, pow_pos hδ0 3,
              mul_nonneg (by linarith [hw₀le] : (0 : ℝ) ≤ 1 / 2 - w₀) (pow_pos hδ0 3).le]
          have hw₀2 : 2 * w₀ * δ ^ 2 ≤ 1 / 49 := by
            nlinarith [hδ49, pow_pos hδ0 2,
              mul_nonneg (by linarith [hw₀le] : (0 : ℝ) ≤ 1 / 2 - w₀) (pow_pos hδ0 2).le]
          have hb1 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) ≤ 4 * 9.9225 * (6 / 343) := by
            nlinarith [hT1', hπ2, Real.pi_pos,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
          have hb2 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2
              ≤ 2 * 9.9225 * (6 / 343) * (1 / 49) := by
            nlinarith [hT1', hπ2, hδ49, Real.pi_pos, pow_pos hδ0 2, pow_pos hδ0 3,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
          have hb3 : 4 * π ^ 2 * (2 * w₀ * δ ^ 3) ≤ 4 * 9.9225 * (1 / 343) := by
            nlinarith [hw₀3, hπ2, Real.pi_pos,
              mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw₀nn) (pow_pos hδ0 3).le]
          have hbC1 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2) ≤ 4 * 9.9225 * (6 / 49) := by
            nlinarith [hT3', hπ2, Real.pi_pos,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 2)]
          have hbC2 : 4 * π ^ 2 * (2 * w₀ * δ ^ 2) ≤ 4 * 9.9225 * (1 / 49) := by
            nlinarith [hw₀2, hπ2, Real.pi_pos,
              mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw₀nn) (pow_pos hδ0 2).le]
          have hm1 := mul_le_mul_of_nonneg_left hb1 hQR.le
          have hm2 := mul_le_mul_of_nonneg_left hb2 hQR.le
          have hm3 := mul_le_mul_of_nonneg_left hb3 hQR.le
          linarith [hm1, hm2, hm3, hbC1, hbC2, hQ340]
        · -- five runners, support at least three: the pair costs an eighth
          have hw₀8 : w₀ ≤ 1 / 8 := by
            have h := hw₀pow 3 hs3
            norm_num at h
            exact h
          have h216 : 216 * ((k : ℝ) + 1) ≤ 5 * ((k : ℝ) + 2) ^ 3 := by
            have hfac : 5 * ((k : ℝ) + 2) ^ 3 - 216 * ((k : ℝ) + 1)
                = ((k : ℝ) - 4) * (5 * (k : ℝ) ^ 2 + 50 * (k : ℝ) + 44) := by ring
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 4)
              (by nlinarith [hkR] : (0 : ℝ) ≤ 5 * (k : ℝ) ^ 2 + 50 * (k : ℝ) + 44)]
          have hT1 : ((k : ℝ) + 1) * δ ^ 3 ≤ 5 / 216 := by
            have h2 : 216 * (((k : ℝ) + 1) * δ ^ 3) ≤ 5 * (((k : ℝ) + 2) ^ 3 * δ ^ 3) := by
              nlinarith [h216, pow_pos hδ0 3]
            rw [hδ3'] at h2
            linarith
          have h6 : 6 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [hkR]
          have hT3 : ((k : ℝ) + 1) * δ ^ 2 ≤ 1 / 6 := by
            have h2 : 6 * (((k : ℝ) + 1) * δ ^ 2) ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
              nlinarith [h6, pow_pos hδ0 2]
            rw [hδ2''] at h2
            linarith
          have hδ36 : δ ^ 2 ≤ 1 / 36 := by
            have h2 : 36 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
              nlinarith [hkR, pow_pos hδ0 2]
            rw [hδ2''] at h2
            linarith
          have h216' : 216 ≤ ((k : ℝ) + 2) ^ 3 := by
            have hfac : ((k : ℝ) + 2) ^ 3 - 216 = ((k : ℝ) - 4) * ((k : ℝ) ^ 2 + 10 * (k : ℝ) + 52) := by
              ring
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 4)
              (by nlinarith [hkR] : (0 : ℝ) ≤ (k : ℝ) ^ 2 + 10 * (k : ℝ) + 52)]
          have hδ216 : δ ^ 3 ≤ 1 / 216 := by
            have h2 : 216 * δ ^ 3 ≤ ((k : ℝ) + 2) ^ 3 * δ ^ 3 := by
              nlinarith [h216', pow_pos hδ0 3]
            rw [hδ3'] at h2
            linarith
          have hw₀3 : 2 * w₀ * δ ^ 3 ≤ 1 / 864 := by
            nlinarith [hδ216, pow_pos hδ0 3,
              mul_nonneg (by linarith [hw₀8] : (0 : ℝ) ≤ 1 / 8 - w₀) (pow_pos hδ0 3).le]
          have hw₀2 : 2 * w₀ * δ ^ 2 ≤ 1 / 144 := by
            nlinarith [hδ36, pow_pos hδ0 2,
              mul_nonneg (by linarith [hw₀8] : (0 : ℝ) ≤ 1 / 8 - w₀) (pow_pos hδ0 2).le]
          have hb1 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) ≤ 4 * 9.9225 * (5 / 216) := by
            nlinarith [hT1, hπ2, Real.pi_pos,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
          have hb2 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2
              ≤ 2 * 9.9225 * (5 / 216) * (1 / 36) := by
            nlinarith [hT1, hπ2, hδ36, Real.pi_pos, pow_pos hδ0 2, pow_pos hδ0 3,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
          have hb3 : 4 * π ^ 2 * (2 * w₀ * δ ^ 3) ≤ 4 * 9.9225 * (1 / 864) := by
            nlinarith [hw₀3, hπ2, Real.pi_pos,
              mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw₀nn) (pow_pos hδ0 3).le]
          have hbC1 : 4 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2) ≤ 4 * 9.9225 * (1 / 6) := by
            nlinarith [hT3, hπ2, Real.pi_pos,
              mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 2)]
          have hbC2 : 4 * π ^ 2 * (2 * w₀ * δ ^ 2) ≤ 4 * 9.9225 * (1 / 144) := by
            nlinarith [hw₀2, hπ2, Real.pi_pos,
              mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw₀nn) (pow_pos hδ0 2).le]
          have hm1 := mul_le_mul_of_nonneg_left hb1 hQR.le
          have hm2 := mul_le_mul_of_nonneg_left hb2 hQR.le
          have hm3 := mul_le_mul_of_nonneg_left hb3 hQR.le
          linarith [hm1, hm2, hm3, hbC1, hbC2, hQ340]

/-! ### The Separation wiring: the strongly-free side splits into the A-free
bulk, the single-torsion classes, and the deep-torsion residual -/

/-- **`A`-torsion-freeness** at level `A(k) = 2^k(k+2)³`: no small multiple of a
runner is a `{−1,0,1}`-combination of the others. -/
def ATorsionFree {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ i : Fin (k + 1), ∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
    ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
    (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i

/-- **The four-runner window**: the single remaining fully classical rung. -/
def WindowFour : Prop :=
  ∀ v : Fin 4 → ℤ, (∀ i, 0 < v i) → StrongFree v → 1 / (5 : ℝ) ≤ ML v

/-- **The torsion residual**: strongly free positive families of `5`–`8` runners
carrying a torsion relation `ρ·v_i = ∑ε_j v_j` with `2 ≤ |ρ| ≤ 2^k(k+2)³`. -/
def TorsionResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ATorsionFree v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- **The A-free split of the small window**: `m = 4` classical; `m = 5..8`
either `A`-free (machine-checked floor) or in the torsion residual. -/
theorem smallWindow_of_four_and_torsion (h1 : WindowFour) (h2 : TorsionResidual) :
    StrongFreeWindowSmall := by
  intro k hk3 hk7 v hv hSF
  by_cases hk3' : k = 3
  · subst hk3'
    have h := h1 v hv hSF
    have hc : 1 / (((3 : ℕ) : ℝ) + 2) = 1 / (5 : ℝ) := by norm_num
    rw [hc]
    exact h
  · have hk4 : 4 ≤ k := by omega
    by_cases hAF : ATorsionFree v
    · exact riesz_clears_floor_afree hk4 v hv hSF hAF
    · exact h2 k hk4 hk7 v hv hSF hAF

/-- **Separation from the four-runner window and the torsion residual** — the
free side of the all-`N` program after the A-free floor theorem. -/
theorem separationSF_of_four_and_torsion (h1 : WindowFour) (h2 : TorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_smallWindow (smallWindow_of_four_and_torsion h1 h2)

/-- **The single-torsion package** at level `A(k)`: one distinguished relation
`a·v_{i₀} = ∑ c₀·v`, torsion-freeness at every other runner, uniqueness of the
relation at `i₀`, and the size gate (`k ≥ 5`, or support at least `3`). -/
def SingleTorsionData {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∃ (i₀ : Fin (k + 1)) (a : ℤ) (c₀ : Fin k → ℤ),
    a ≠ 0 ∧
    (∀ j', c₀ j' = -1 ∨ c₀ j' = 0 ∨ c₀ j' = 1) ∧
    (∑ j', c₀ j' * v (i₀.succAbove j')) = a * v i₀ ∧
    (∀ i : Fin (k + 1), i ≠ i₀ → ∀ ρ : ℤ, 2 ≤ |ρ| →
        |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i) ∧
    (∀ ρ : ℤ, 2 ≤ |ρ| → |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i₀.succAbove j')) = ρ * v i₀ → c = c₀ ∨ c = -c₀) ∧
    (5 ≤ k ∨ 3 ≤ (Finset.univ.filter (fun j' => c₀ j' ≠ 0)).card)

/-- **The deep-torsion residual**: torsion families outside the single-torsion
floor theorem — either a second bounded relation, or five runners with a
support-`≤ 2` relation. -/
def DeepTorsionResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ATorsionFree v → ¬ SingleTorsionData v →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- The single-torsion floor theorem shrinks the torsion residual to its deep part. -/
theorem torsionResidual_of_deep (h : DeepTorsionResidual) : TorsionResidual := by
  classical
  intro k hk4 hk7 v hv hSF hAF
  by_cases hst : SingleTorsionData v
  · obtain ⟨i₀, a, c₀, ha0, hc₀, hrel, hAFo, huniq, hks⟩ := hst
    exact riesz_clears_floor_torsion_single hk4 v hv hSF i₀ a c₀ ha0 hc₀ hrel hAFo huniq hks
  · exact h k hk4 hk7 v hv hSF hAF hst

/-- **Separation from: the four-runner window + the deep-torsion residual.**
The free side after both the A-free and the single-torsion floor theorems. -/
theorem separationSF_of_four_and_deep (h1 : WindowFour) (h2 : DeepTorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_four_and_torsion h1 (torsionResidual_of_deep h2)



/-! ### The Fourier Bridge: single-relation families via the dichotomy -/

/-- A `{−1,0,1}`-combination's Riesz weight is at most `2^{−n}` once its support
has at least `n` elements. -/
theorem combo_weight_pow {m : ℕ} (c : Fin m → ℤ) (n : ℕ)
    (hn : n ≤ (Finset.univ.filter (fun j' : Fin m => c j' ≠ 0)).card) :
    (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (1 / 2 : ℝ) ^ n := by
  classical
  have hTeq : (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
      = (1 / 2 : ℝ) ^ (Finset.univ.filter (fun j' : Fin m => c j' ≠ 0)).card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j' => c j' ≠ 0)
      (fun j' => (if c j' = 0 then (1 : ℝ) else 1 / 2))]
    have h1 : ∀ j' ∈ Finset.univ.filter (fun j' : Fin m => c j' ≠ 0),
        (if c j' = 0 then (1 : ℝ) else 1 / 2) = 1 / 2 := by
      intro j' hj'
      rw [Finset.mem_filter] at hj'
      rw [if_neg hj'.2]
    have h2 : ∀ j' ∈ Finset.univ.filter (fun j' : Fin m => ¬ c j' ≠ 0),
        (if c j' = 0 then (1 : ℝ) else 1 / 2) = 1 := by
      intro j' hj'
      rw [Finset.mem_filter] at hj'
      have h3 : c j' = 0 := not_not.mp hj'.2
      rw [if_pos h3]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const,
      Finset.prod_const, one_pow, mul_one]
  rw [hTeq]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

set_option maxHeartbeats 4000000 in
/-- **The Fourier Bridge for single-relation families.**  A positive family of
`k + 1 ≥ 8` runners carrying one vanishing `{−1,0,1}`-relation `r` of support
`≥ 3` — with every bounded resonance a multiple of `r` (`hres`) — meets the
Lonely-Runner floor `1/(k+2)`.  The relation's support may be even or odd: the
mass `Q(1 + 2(−1/2)^s) ≥ 3Q/4` enters as data, and each runner's resonant pair
`±r|_i` costs at most half a runner.  This closes the `s = 3` small-`k`
(SumStep) cells `k ∈ {8, 9}` left open by the Markov bridges. -/
theorem bridge_single_relation_fourier {k : ℕ} (hk : 7 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i)
    (r : Fin (k + 1) → ℤ) (hr : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hsupp : 3 ≤ (Finset.univ.filter (fun w => r w ≠ 0)).card)
    (hres : ∀ i : Fin (k + 1), ∀ ρ : ℤ, |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) = ρ * v i →
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = 0 ∨
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = r ∨
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = -r) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set A : ℕ := 2 ^ k * (k + 2) ^ 3 with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨Q, hQp, hQN, hQsum, hQcop⟩ :=
    exists_coprime_modulus_ge (k + 1) v ((A + 1) * (∑ w, (v w).natAbs))
  have hQ0 : 0 < Q := hQp.pos
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- the mass: single-relation classification via the resonance hypothesis
  have hchar : ∀ c : Fin (k + 1) → ℤ, (∀ w, c w = -1 ∨ c w = 0 ∨ c w = 1) →
      (∑ w, c w * v w) = 0 → c = 0 ∨ c = r ∨ c = -r := by
    intro c hcm hcv
    set i₁ : Fin (k + 1) := 0 with hi₁
    have hsplit3 : (∑ j', c (i₁.succAbove j') * v (i₁.succAbove j'))
        = (-(c i₁)) * v i₁ := by
      have h := Fin.sum_univ_succAbove (fun w => c w * v w) i₁
      rw [hcv] at h
      linarith [h]
    have hρb : |(-(c i₁))| ≤ ((A : ℕ) : ℤ) := by
      have h1 : |(-(c i₁))| ≤ 1 := by
        rcases hcm i₁ with h | h | h <;> simp [h]
      have h2 : (1 : ℤ) ≤ ((A : ℕ) : ℤ) := by exact_mod_cast hA0
      omega
    have hins : i₁.insertNth (c i₁) (fun j' => c (i₁.succAbove j')) = c := by
      funext w
      refine Fin.succAboveCases i₁ ?_ (fun j' => ?_) w
      · rw [Fin.insertNth_apply_same]
      · rw [Fin.insertNth_apply_succAbove]
    have h := hres i₁ (-(c i₁)) hρb (fun j' => c (i₁.succAbove j'))
      (fun j' => hcm _) hsplit3
    rw [neg_neg, hins] at h
    exact h
  have hmass := riesz_mass_disjoint_real (k + 1) 1 v Q hQ0 hQsum (fun _ => r)
    (fun _ w => hr w) (fun _ => hrel)
    (fun _ => by
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 <
        (Finset.univ.filter (fun w => r w ≠ 0)).card)
      exact ⟨w, (Finset.mem_filter.mp hw).2⟩)
    (fun t t' h => absurd (Subsingleton.elim t t') h)
    (by
      intro c hcm hcv
      rcases hchar c hcm hcv with h | h | h
      · exact ⟨fun _ => 0, fun _ => Or.inr (Or.inl rfl), by
          funext w; rw [h]; simp⟩
      · exact ⟨fun _ => 1, fun _ => Or.inr (Or.inr rfl), by
          funext w; rw [h]; simp⟩
      · exact ⟨fun _ => -1, fun _ => Or.inl rfl, by
          funext w; rw [h]; simp⟩)
  rw [Fin.prod_univ_one] at hmass
  -- the mass is at least three quarters of the grid
  set wr : ℝ := ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) with hwr
  have habswr : |wr| ≤ 1 / 8 := by
    have h1 : |wr| = ∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2) := by
      rw [hwr, Finset.abs_prod]
      refine Finset.prod_congr rfl fun w _ => ?_
      split_ifs
      · exact abs_one
      · rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
        norm_num
    rw [h1]
    have h2 := combo_weight_pow r 3 hsupp
    calc (∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2)) ≤ (1 / 2 : ℝ) ^ 3 := h2
      _ = 1 / 8 := by norm_num
  have hMlow : (3 / 4 : ℝ) * Q ≤ (Q : ℝ) * (1 + 2 * wr) := by
    have h1 : -(1 / 8 : ℝ) ≤ wr := by
      have := abs_le.mp habswr
      linarith [this.1]
    nlinarith [hQR]
  -- the per-runner weight bound (uniform: the resonant pair costs ≤ 1/2)
  have hWbound : ∀ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
      (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
      ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ (2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
    intro i
    have hvpos := hpos i
    have hvnA : (v i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hvpos)
    have hcop := hQcop i hvnA
    have htoNat : (v i).toNat = (v i).natAbs := by
      have h1 : ((v i).toNat : ℤ) = ((v i).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg hvpos.le, Int.natAbs_of_nonneg hvpos.le]
      exact_mod_cast h1
    have hcop2 : Nat.Coprime ((v i).toNat % Q) Q := by
      rw [htoNat]
      show Nat.gcd ((v i).natAbs % Q) Q = 1
      rw [← Nat.gcd_rec Q (v i).natAbs, Nat.gcd_comm]
      exact hcop
    obtain ⟨b, hab⟩ := exists_nat_inverse _ Q hQ0 hcop2
    have hfeq := badset_filter_eq Q hQ0 (v i) hvpos δ
    have hcard := badset_card_bound Q hQ0 ((v i).toNat % Q) b hab δ hδ0.le hδ2
    have hcard' : (((Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        ≤ 2 * δ * Q + 2 := by
      rw [hfeq]
      exact hcard
    have hwtnn : ∀ c : Fin k → ℤ, (0 : ℝ) ≤ ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
      fun c => Finset.prod_nonneg fun j' _ => by positivity
    have hsum_wt : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (2 ^ k : ℝ) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ ∑ c ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun c _ _ => hwtnn c)
        _ = ∏ _j' : Fin k, ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
              (if a' = 0 then (1 : ℝ) else 1 / 2) := by
            rw [Finset.prod_univ_sum]
        _ = (2 ^ k : ℝ) := by
            have hthree : ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
                (if a' = 0 then (1 : ℝ) else 1 / 2) = 2 := by
              rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
                Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              norm_num
            rw [Finset.prod_congr rfl fun _ _ => hthree, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    -- the restricted relation and its two support witnesses away from `i`
    set rr : Fin k → ℤ := fun j' => r (i.succAbove j') with hrr
    have hcard2 : 2 ≤ ((Finset.univ.filter (fun w => r w ≠ 0)) \ {i}).card := by
      have h1 := Finset.le_card_sdiff ({i} : Finset (Fin (k + 1)))
        (Finset.univ.filter (fun w => r w ≠ 0))
      have h2 : (({i} : Finset (Fin (k + 1)))).card = 1 := Finset.card_singleton i
      omega
    obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ := Finset.one_lt_card.mp
      (by omega : 1 < ((Finset.univ.filter (fun w => r w ≠ 0)) \ {i}).card)
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton,
      Finset.mem_univ, true_and] at hw₁ hw₂
    obtain ⟨j₁, hj₁⟩ := Fin.exists_succAbove_eq hw₁.2
    obtain ⟨j₂, hj₂⟩ := Fin.exists_succAbove_eq hw₂.2
    have hj₁0 : rr j₁ ≠ 0 := by
      simp only [hrr]
      rw [hj₁]
      exact hw₁.1
    have hj₂0 : rr j₂ ≠ 0 := by
      simp only [hrr]
      rw [hj₂]
      exact hw₂.1
    have hjj : j₁ ≠ j₂ := by
      intro h
      apply hww
      rw [← hj₁, ← hj₂, h]
    have hsupp2 : 2 ≤ (Finset.univ.filter (fun j' => rr j' ≠ 0)).card :=
      Finset.one_lt_card.mpr ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁0⟩,
        j₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₂0⟩, hjj⟩
    have hwt4 : (∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1 / 4 := by
      have h := combo_weight_pow rr 2 hsupp2
      calc (∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (1 / 2 : ℝ) ^ 2 := h
        _ = 1 / 4 := by norm_num
    have hrr0 : rr ≠ 0 := by
      intro h0
      exact hj₁0 (by rw [h0]; rfl)
    have hrrmem : ∀ j', rr j' = -1 ∨ rr j' = 0 ∨ rr j' = 1 := fun j' => hr _
    have hRsub : ({rr, -rr} : Finset (Fin k → ℤ)) ⊆
        (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0 := by
      intro c hc
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      rw [Finset.mem_erase]
      rcases hc with h | h
      · subst h
        refine ⟨hrr0, ?_⟩
        rw [Fintype.mem_piFinset]
        intro j'
        rcases hrrmem j' with h | h | h <;> simp [h]
      · subst h
        refine ⟨fun h0 => hrr0 (neg_eq_zero.mp h0), ?_⟩
        rw [Fintype.mem_piFinset]
        intro j'
        rcases hrrmem j' with h | h | h <;> simp [Pi.neg_apply, h]
    -- resonance classification at runner `i`, for every bounded `ρ`
    have hEXgen : ∀ c : Fin k → ℤ, c ≠ 0 → (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        c ∉ ({rr, -rr} : Finset (Fin k → ℤ)) →
        ∀ ρ : ℤ, |ρ| ≤ (A : ℤ) → (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i := by
      intro c hc0 hcmem' hcR ρ hρA heq
      rcases hres i ρ hρA c hcmem' heq with h | h | h
      · apply hc0
        funext j'
        have h2 := congrFun h (i.succAbove j')
        rw [Fin.insertNth_apply_succAbove] at h2
        simpa using h2
      · apply hcR
        have hceq : c = rr := by
          funext j'
          have h2 := congrFun h (i.succAbove j')
          rw [Fin.insertNth_apply_succAbove] at h2
          simp only [hrr]
          exact h2
        rw [hceq]
        exact Finset.mem_insert_self _ _
      · apply hcR
        have hceq : c = -rr := by
          funext j'
          have h2 := congrFun h (i.succAbove j')
          rw [Fin.insertNth_apply_succAbove] at h2
          simp only [Pi.neg_apply] at h2 ⊢
          simp only [hrr]
          exact h2
        rw [hceq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hF0 : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ ({rr, -rr} : Finset (Fin k → ℤ)),
        (∑ j', c j' * v (i.succAbove j')) ≠ 0 := by
      intro c hc hF
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have h1 : (1 : ℤ) ≤ ((A : ℕ) : ℤ) := by exact_mod_cast hA0
      exact hEXgen c hc0 hcmem' hcR 0 (by rw [abs_zero]; omega)
        (by rw [hF, zero_mul])
    have hsplit := badset_weight_split' v Q hQ0 hQsum i hvpos b hab δ hδ2
      ({rr, -rr} : Finset (Fin k → ℤ)) hRsub hF0
    have hwneg : (∏ j', (if (-rr) j' = 0 then (1 : ℝ) else 1 / 2))
        = ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := by
      refine Finset.prod_congr rfl fun j' _ => ?_
      simp [Pi.neg_apply, neg_eq_zero]
    have hRsum : ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1 / 2 := by
      have hb : ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
          (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ 2 * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := by
        by_cases hcc : rr = -rr
        · have hpair : ({rr, -rr} : Finset (Fin k → ℤ)) = {-rr} := by
            rw [← hcc]
            exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
          rw [hpair, Finset.sum_singleton, hwneg]
          linarith [hwtnn rr]
        · rw [Finset.sum_pair hcc, hwneg]
          linarith [hwtnn rr]
      calc ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ 2 * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := hb
        _ ≤ 2 * (1 / 4) := by linarith [hwt4]
        _ = 1 / 2 := by norm_num
    have hperc : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ ({rr, -rr} : Finset (Fin k → ℤ)),
        4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
            * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
          ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have hnid := afree_nid_lower'' v i A Q hQ0 hQN b hab hvpos c hcmem' hc0
        (hEXgen c hc0 hcmem' hcR)
      exact afree_perc_bound Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) A hnid
    calc ∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
        ≤ (((Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
            * (1 + ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
                ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
              \ ({rr, -rr} : Finset (Fin k → ℤ)),
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                    * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hsplit
      _ ≤ (2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
          refine add_le_add ?_ ?_
          · have hRnn : (0 : ℝ) ≤ ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
                ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
              Finset.sum_nonneg fun c _ => hwtnn c
            refine mul_le_mul hcard' (by linarith [hRsum]) (by linarith [hRnn]) ?_
            positivity
          · calc ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                    * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                        * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
                ≤ ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
                  Finset.sum_le_sum fun c hc =>
                    mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
              _ = (∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  rw [Finset.sum_mul]
              _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                    Finset.sdiff_subset (fun c _ _ => hwtnn c)) hsum_wt
              _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
  refine riesz_union_weights v Q hQ0 δ hδ0 hδ2 ((Q : ℝ) * (1 + 2 * wr)) hmass
    (fun _ => (2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) hWbound ?_
  -- the union arithmetic against the three-quarter mass
  have hsumW : (∑ _i : Fin (k + 1),
      ((2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)))
      = ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumW]
  have hA3 : (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) ≤ δ ^ 3 * Q := by
    have hAval : ((A : ℝ) + 1) = (2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1 := by
      rw [hA]
      push_cast
      ring
    have hδ3 : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by
      rw [hδdef]
      field_simp
    rw [div_le_iff₀ (by rw [hAval]; positivity)]
    rw [hAval]
    have hexp : δ ^ 3 * (Q : ℝ) * ((2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1)
        = (2 ^ k : ℝ) * Q * (((k : ℝ) + 2) ^ 3 * δ ^ 3) + δ ^ 3 * Q := by ring
    rw [hexp, hδ3, mul_one]
    nlinarith [pow_pos hδ0 3, hQR]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hδ3' : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by rw [hδdef]; field_simp
  have hδ2'' : ((k : ℝ) + 2) ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp
  have hsum1 : k + 1 ≤ ∑ w, (v w).natAbs := by
    calc k + 1 = ∑ _w : Fin (k + 1), 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ ≤ ∑ w, (v w).natAbs := by
          refine Finset.sum_le_sum fun w _ => ?_
          have := hpos w
          have h1 : (v w).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt this)
          omega
  have hQ340 : (340 : ℝ) ≤ (Q : ℝ) := by
    have hA1 : 3456 ≤ A := by
      rw [hA]
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 3456 = 2 ^ 4 * 6 ^ 3 := by norm_num
        _ ≤ 2 ^ k * (k + 2) ^ 3 := Nat.mul_le_mul h1 h2
    have hQbig : 340 ≤ Q := by
      have h3 : (A + 1) * (∑ w, (v w).natAbs) ≥ 3457 * 5 := by
        have h4 : 5 ≤ ∑ w, (v w).natAbs := by omega
        exact Nat.mul_le_mul (by omega) h4
      omega
    exact_mod_cast hQbig
  -- the `k ≥ 7` bounds
  have h729 : 729 * ((k : ℝ) + 1) ≤ 8 * ((k : ℝ) + 2) ^ 3 := by
    have hfac : 8 * ((k : ℝ) + 2) ^ 3 - 729 * ((k : ℝ) + 1)
        = ((k : ℝ) - 7) * (8 * (k : ℝ) ^ 2 + 104 * (k : ℝ) + 95) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 7)
      (by nlinarith [hkR] : (0 : ℝ) ≤ 8 * (k : ℝ) ^ 2 + 104 * (k : ℝ) + 95)]
  have hT1 : ((k : ℝ) + 1) * δ ^ 3 ≤ 8 / 729 := by
    have h2 : 729 * (((k : ℝ) + 1) * δ ^ 3) ≤ 8 * (((k : ℝ) + 2) ^ 3 * δ ^ 3) := by
      nlinarith [h729, pow_pos hδ0 3]
    rw [hδ3'] at h2
    linarith
  have h81 : 81 ≤ ((k : ℝ) + 2) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 7)
      (by linarith : (0 : ℝ) ≤ (k : ℝ) + 11)]
  have hδ81 : δ ^ 2 ≤ 1 / 81 := by
    have h2 : 81 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
      nlinarith [h81, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  have h881 : 81 * ((k : ℝ) + 1) ≤ 8 * ((k : ℝ) + 2) ^ 2 := by
    have hfac : 8 * ((k : ℝ) + 2) ^ 2 - 81 * ((k : ℝ) + 1)
        = ((k : ℝ) - 7) * (8 * (k : ℝ) + 7) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 7)
      (by linarith : (0 : ℝ) ≤ 8 * (k : ℝ) + 7)]
  have hT3 : ((k : ℝ) + 1) * δ ^ 2 ≤ 8 / 81 := by
    have h2 : 81 * (((k : ℝ) + 1) * δ ^ 2) ≤ 8 * (((k : ℝ) + 2) ^ 2 * δ ^ 2) := by
      nlinarith [h881, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  have hmid : ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
      ≤ ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + δ ^ 3 * Q) :=
    mul_le_mul_of_nonneg_left (by linarith [hA3]) (by linarith)
  have hpos1 : (0 : ℝ) < ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + δ ^ 3 * Q) := by
    positivity
  calc ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        * (1 - Real.cos (2 * π * δ))
      ≤ ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + δ ^ 3 * Q)
          * (1 - Real.cos (2 * π * δ)) :=
        mul_le_mul_of_nonneg_right hmid hcosnn
    _ < ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (3 / 2) + δ ^ 3 * Q) * (2 * (π * δ) ^ 2) :=
        mul_lt_mul_of_pos_left hu hpos1
    _ = (Q : ℝ) * (6 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3))
        + 6 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2)
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2) := by
        ring
    _ < (Q : ℝ) * (1 + 2 * wr) := by
        have hb1 : 6 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) ≤ 6 * 9.9225 * (8 / 729) := by
          nlinarith [hT1, hπ2, Real.pi_pos,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
        have hb2 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2
            ≤ 2 * 9.9225 * (8 / 729) * (1 / 81) := by
          nlinarith [hT1, hπ2, hδ81, Real.pi_pos, pow_pos hδ0 2, pow_pos hδ0 3,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
        have hbC1 : 6 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2) ≤ 6 * 9.9225 * (8 / 81) := by
          nlinarith [hT3, hπ2, Real.pi_pos,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 2)]
        have hm1 := mul_le_mul_of_nonneg_left hb1 hQR.le
        have hm2 := mul_le_mul_of_nonneg_left hb2 hQR.le
        have hM34 : (3 / 4 : ℝ) * Q ≤ (Q : ℝ) * (1 + 2 * wr) := hMlow
        linarith [hm1, hm2, hbC1, hQ340, hM34]



set_option maxHeartbeats 1600000 in
/-- **The wide-support Fourier Bridge.**  For a single vanishing `±1`-relation
of support at least *five*, the mass is `≥ 15Q/16` and each runner's resonant
pair costs at most an eighth, so the union closes already at `k ≥ 5` (six
runners) — three sizes below the support-three threshold.  The restricted
relation loses at most one support element (`∏ rr ≤ 2 ∏ r`), so no witness
extraction is needed. -/
theorem bridge_single_relation_fourier_wide {k : ℕ} (hk : 5 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i)
    (r : Fin (k + 1) → ℤ) (hr : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hsupp : 5 ≤ (Finset.univ.filter (fun w => r w ≠ 0)).card)
    (hres : ∀ i : Fin (k + 1), ∀ ρ : ℤ, |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        ∀ c : Fin k → ℤ, (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        (∑ j', c j' * v (i.succAbove j')) = ρ * v i →
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = 0 ∨
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = r ∨
        (i.insertNth (-ρ) c : Fin (k + 1) → ℤ) = -r) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set A : ℕ := 2 ^ k * (k + 2) ^ 3 with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨Q, hQp, hQN, hQsum, hQcop⟩ :=
    exists_coprime_modulus_ge (k + 1) v ((A + 1) * (∑ w, (v w).natAbs))
  have hQ0 : 0 < Q := hQp.pos
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- the mass: single-relation classification via the resonance hypothesis
  have hchar : ∀ c : Fin (k + 1) → ℤ, (∀ w, c w = -1 ∨ c w = 0 ∨ c w = 1) →
      (∑ w, c w * v w) = 0 → c = 0 ∨ c = r ∨ c = -r := by
    intro c hcm hcv
    set i₁ : Fin (k + 1) := 0 with hi₁
    have hsplit3 : (∑ j', c (i₁.succAbove j') * v (i₁.succAbove j'))
        = (-(c i₁)) * v i₁ := by
      have h := Fin.sum_univ_succAbove (fun w => c w * v w) i₁
      rw [hcv] at h
      linarith [h]
    have hρb : |(-(c i₁))| ≤ ((A : ℕ) : ℤ) := by
      have h1 : |(-(c i₁))| ≤ 1 := by
        rcases hcm i₁ with h | h | h <;> simp [h]
      have h2 : (1 : ℤ) ≤ ((A : ℕ) : ℤ) := by exact_mod_cast hA0
      omega
    have hins : i₁.insertNth (c i₁) (fun j' => c (i₁.succAbove j')) = c := by
      funext w
      refine Fin.succAboveCases i₁ ?_ (fun j' => ?_) w
      · rw [Fin.insertNth_apply_same]
      · rw [Fin.insertNth_apply_succAbove]
    have h := hres i₁ (-(c i₁)) hρb (fun j' => c (i₁.succAbove j'))
      (fun j' => hcm _) hsplit3
    rw [neg_neg, hins] at h
    exact h
  have hmass := riesz_mass_disjoint_real (k + 1) 1 v Q hQ0 hQsum (fun _ => r)
    (fun _ w => hr w) (fun _ => hrel)
    (fun _ => by
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 <
        (Finset.univ.filter (fun w => r w ≠ 0)).card)
      exact ⟨w, (Finset.mem_filter.mp hw).2⟩)
    (fun t t' h => absurd (Subsingleton.elim t t') h)
    (by
      intro c hcm hcv
      rcases hchar c hcm hcv with h | h | h
      · exact ⟨fun _ => 0, fun _ => Or.inr (Or.inl rfl), by
          funext w; rw [h]; simp⟩
      · exact ⟨fun _ => 1, fun _ => Or.inr (Or.inr rfl), by
          funext w; rw [h]; simp⟩
      · exact ⟨fun _ => -1, fun _ => Or.inl rfl, by
          funext w; rw [h]; simp⟩)
  rw [Fin.prod_univ_one] at hmass
  -- the mass is at least three quarters of the grid
  set wr : ℝ := ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) with hwr
  have habswr : |wr| ≤ 1 / 32 := by
    have h1 : |wr| = ∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2) := by
      rw [hwr, Finset.abs_prod]
      refine Finset.prod_congr rfl fun w _ => ?_
      split_ifs
      · exact abs_one
      · rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
        norm_num
    rw [h1]
    have h2 := combo_weight_pow r 5 hsupp
    calc (∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2)) ≤ (1 / 2 : ℝ) ^ 5 := h2
      _ = 1 / 32 := by norm_num
  have hMlow : (15 / 16 : ℝ) * Q ≤ (Q : ℝ) * (1 + 2 * wr) := by
    have h1 : -(1 / 32 : ℝ) ≤ wr := by
      have := abs_le.mp habswr
      linarith [this.1]
    nlinarith [hQR]
  -- the per-runner weight bound (uniform: the resonant pair costs ≤ 1/2)
  have hWbound : ∀ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
      (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
      ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ (2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
    intro i
    have hvpos := hpos i
    have hvnA : (v i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hvpos)
    have hcop := hQcop i hvnA
    have htoNat : (v i).toNat = (v i).natAbs := by
      have h1 : ((v i).toNat : ℤ) = ((v i).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg hvpos.le, Int.natAbs_of_nonneg hvpos.le]
      exact_mod_cast h1
    have hcop2 : Nat.Coprime ((v i).toNat % Q) Q := by
      rw [htoNat]
      show Nat.gcd ((v i).natAbs % Q) Q = 1
      rw [← Nat.gcd_rec Q (v i).natAbs, Nat.gcd_comm]
      exact hcop
    obtain ⟨b, hab⟩ := exists_nat_inverse _ Q hQ0 hcop2
    have hfeq := badset_filter_eq Q hQ0 (v i) hvpos δ
    have hcard := badset_card_bound Q hQ0 ((v i).toNat % Q) b hab δ hδ0.le hδ2
    have hcard' : (((Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        ≤ 2 * δ * Q + 2 := by
      rw [hfeq]
      exact hcard
    have hwtnn : ∀ c : Fin k → ℤ, (0 : ℝ) ≤ ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
      fun c => Finset.prod_nonneg fun j' _ => by positivity
    have hsum_wt : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (2 ^ k : ℝ) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ ∑ c ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun c _ _ => hwtnn c)
        _ = ∏ _j' : Fin k, ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
              (if a' = 0 then (1 : ℝ) else 1 / 2) := by
            rw [Finset.prod_univ_sum]
        _ = (2 ^ k : ℝ) := by
            have hthree : ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
                (if a' = 0 then (1 : ℝ) else 1 / 2) = 2 := by
              rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
                Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              norm_num
            rw [Finset.prod_congr rfl fun _ _ => hthree, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    -- the restricted relation keeps all but at most one of its support
    set rr : Fin k → ℤ := fun j' => r (i.succAbove j') with hrr
    have hrr0 : rr ≠ 0 := by
      intro h0
      have hsub : (Finset.univ.filter (fun w => r w ≠ 0)) ⊆ {i} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [Finset.mem_singleton]
        by_contra hwi
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hwi
        exact hw.2 (by have := congrFun h0 j'; simpa only [hrr] using this)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hc
      omega
    have hrrmem : ∀ j', rr j' = -1 ∨ rr j' = 0 ∨ rr j' = 1 := fun j' => hr _
    have hwt_rr : (∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1 / 16 := by
      have hfull : (∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2))
          = (if r i = 0 then (1 : ℝ) else 1 / 2)
              * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := by
        rw [Fin.prod_univ_succAbove (fun w => (if r w = 0 then (1 : ℝ) else 1 / 2)) i]
      have hhalf : (1 / 2 : ℝ) ≤ (if r i = 0 then (1 : ℝ) else 1 / 2) := by
        split_ifs <;> norm_num
      have hrrnn : (0 : ℝ) ≤ ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) :=
        Finset.prod_nonneg fun j' _ => by positivity
      have hprodr : (∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2)) ≤ (1 / 2 : ℝ) ^ 5 :=
        combo_weight_pow r 5 hsupp
      have hstep : (1 / 2 : ℝ) * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2)
          ≤ ∏ w, (if r w = 0 then (1 : ℝ) else 1 / 2) := by
        rw [hfull]; exact mul_le_mul_of_nonneg_right hhalf hrrnn
      have hchain : (1 / 2 : ℝ) * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2)
          ≤ (1 / 2 : ℝ) ^ 5 := le_trans hstep hprodr
      rw [show (1 / 2 : ℝ) ^ 5 = 1 / 32 by norm_num] at hchain
      linarith [hchain]
    have hRsub : ({rr, -rr} : Finset (Fin k → ℤ)) ⊆
        (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0 := by
      intro c hc
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      rw [Finset.mem_erase]
      rcases hc with h | h
      · subst h
        refine ⟨hrr0, ?_⟩
        rw [Fintype.mem_piFinset]
        intro j'
        rcases hrrmem j' with h | h | h <;> simp [h]
      · subst h
        refine ⟨fun h0 => hrr0 (neg_eq_zero.mp h0), ?_⟩
        rw [Fintype.mem_piFinset]
        intro j'
        rcases hrrmem j' with h | h | h <;> simp [Pi.neg_apply, h]
    -- resonance classification at runner `i`, for every bounded `ρ`
    have hEXgen : ∀ c : Fin k → ℤ, c ≠ 0 → (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) →
        c ∉ ({rr, -rr} : Finset (Fin k → ℤ)) →
        ∀ ρ : ℤ, |ρ| ≤ (A : ℤ) → (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i := by
      intro c hc0 hcmem' hcR ρ hρA heq
      rcases hres i ρ hρA c hcmem' heq with h | h | h
      · apply hc0
        funext j'
        have h2 := congrFun h (i.succAbove j')
        rw [Fin.insertNth_apply_succAbove] at h2
        simpa using h2
      · apply hcR
        have hceq : c = rr := by
          funext j'
          have h2 := congrFun h (i.succAbove j')
          rw [Fin.insertNth_apply_succAbove] at h2
          simp only [hrr]
          exact h2
        rw [hceq]
        exact Finset.mem_insert_self _ _
      · apply hcR
        have hceq : c = -rr := by
          funext j'
          have h2 := congrFun h (i.succAbove j')
          rw [Fin.insertNth_apply_succAbove] at h2
          simp only [Pi.neg_apply] at h2 ⊢
          simp only [hrr]
          exact h2
        rw [hceq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hF0 : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ ({rr, -rr} : Finset (Fin k → ℤ)),
        (∑ j', c j' * v (i.succAbove j')) ≠ 0 := by
      intro c hc hF
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have h1 : (1 : ℤ) ≤ ((A : ℕ) : ℤ) := by exact_mod_cast hA0
      exact hEXgen c hc0 hcmem' hcR 0 (by rw [abs_zero]; omega)
        (by rw [hF, zero_mul])
    have hsplit := badset_weight_split' v Q hQ0 hQsum i hvpos b hab δ hδ2
      ({rr, -rr} : Finset (Fin k → ℤ)) hRsub hF0
    have hwneg : (∏ j', (if (-rr) j' = 0 then (1 : ℝ) else 1 / 2))
        = ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := by
      refine Finset.prod_congr rfl fun j' _ => ?_
      simp [Pi.neg_apply, neg_eq_zero]
    have hRsum : ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1 / 8 := by
      have hb : ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
          (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ 2 * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := by
        by_cases hcc : rr = -rr
        · have hpair : ({rr, -rr} : Finset (Fin k → ℤ)) = {-rr} := by
            rw [← hcc]
            exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
          rw [hpair, Finset.sum_singleton, hwneg]
          linarith [hwtnn rr]
        · rw [Finset.sum_pair hcc, hwneg]
          linarith [hwtnn rr]
      calc ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ 2 * ∏ j', (if rr j' = 0 then (1 : ℝ) else 1 / 2) := hb
        _ ≤ 2 * (1 / 16) := by linarith [hwt_rr]
        _ = 1 / 8 := by norm_num
    have hperc : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ ({rr, -rr} : Finset (Fin k → ℤ)),
        4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
            * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
          ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have hnid := afree_nid_lower'' v i A Q hQ0 hQN b hab hvpos c hcmem' hc0
        (hEXgen c hc0 hcmem' hcR)
      exact afree_perc_bound Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) A hnid
    calc ∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
        ≤ (((Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
            * (1 + ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
                ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
              \ ({rr, -rr} : Finset (Fin k → ℤ)),
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                    * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hsplit
      _ ≤ (2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
          refine add_le_add ?_ ?_
          · have hRnn : (0 : ℝ) ≤ ∑ c ∈ ({rr, -rr} : Finset (Fin k → ℤ)),
                ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
              Finset.sum_nonneg fun c _ => hwtnn c
            refine mul_le_mul hcard' (by linarith [hRsum]) (by linarith [hRnn]) ?_
            positivity
          · calc ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                    * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                        * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
                ≤ ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
                  Finset.sum_le_sum fun c hc =>
                    mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
              _ = (∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ ({rr, -rr} : Finset (Fin k → ℤ)),
                  (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  rw [Finset.sum_mul]
              _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                    Finset.sdiff_subset (fun c _ _ => hwtnn c)) hsum_wt
              _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
  refine riesz_union_weights v Q hQ0 δ hδ0 hδ2 ((Q : ℝ) * (1 + 2 * wr)) hmass
    (fun _ => (2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) hWbound ?_
  -- the union arithmetic against the three-quarter mass
  have hsumW : (∑ _i : Fin (k + 1),
      ((2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)))
      = ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumW]
  have hA3 : (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) ≤ δ ^ 3 * Q := by
    have hAval : ((A : ℝ) + 1) = (2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1 := by
      rw [hA]
      push_cast
      ring
    have hδ3 : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by
      rw [hδdef]
      field_simp
    rw [div_le_iff₀ (by rw [hAval]; positivity)]
    rw [hAval]
    have hexp : δ ^ 3 * (Q : ℝ) * ((2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1)
        = (2 ^ k : ℝ) * Q * (((k : ℝ) + 2) ^ 3 * δ ^ 3) + δ ^ 3 * Q := by ring
    rw [hexp, hδ3, mul_one]
    nlinarith [pow_pos hδ0 3, hQR]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hδ3' : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by rw [hδdef]; field_simp
  have hδ2'' : ((k : ℝ) + 2) ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp
  have hsum1 : k + 1 ≤ ∑ w, (v w).natAbs := by
    calc k + 1 = ∑ _w : Fin (k + 1), 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ ≤ ∑ w, (v w).natAbs := by
          refine Finset.sum_le_sum fun w _ => ?_
          have := hpos w
          have h1 : (v w).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt this)
          omega
  have hQ340 : (340 : ℝ) ≤ (Q : ℝ) := by
    have hA1 : 3456 ≤ A := by
      rw [hA]
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 3456 = 2 ^ 4 * 6 ^ 3 := by norm_num
        _ ≤ 2 ^ k * (k + 2) ^ 3 := Nat.mul_le_mul h1 h2
    have hQbig : 340 ≤ Q := by
      have h3 : (A + 1) * (∑ w, (v w).natAbs) ≥ 3457 * 5 := by
        have h4 : 5 ≤ ∑ w, (v w).natAbs := by omega
        exact Nat.mul_le_mul (by omega) h4
      omega
    exact_mod_cast hQbig
  -- the k ≥ 5 bounds
  have h343 : 343 * ((k : ℝ) + 1) ≤ 6 * ((k : ℝ) + 2) ^ 3 := by
    have hfac : 6 * ((k : ℝ) + 2) ^ 3 - 343 * ((k : ℝ) + 1)
        = ((k : ℝ) - 5) * (6 * (k : ℝ) ^ 2 + 66 * (k : ℝ) + 59) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
      (by nlinarith [hkR] : (0 : ℝ) ≤ 6 * (k : ℝ) ^ 2 + 66 * (k : ℝ) + 59)]
  have hT1 : ((k : ℝ) + 1) * δ ^ 3 ≤ 6 / 343 := by
    have h2 : 343 * (((k : ℝ) + 1) * δ ^ 3) ≤ 6 * (((k : ℝ) + 2) ^ 3 * δ ^ 3) := by
      nlinarith [h343, pow_pos hδ0 3]
    rw [hδ3'] at h2
    linarith
  have h49 : 49 ≤ ((k : ℝ) + 2) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
      (by linarith : (0 : ℝ) ≤ (k : ℝ) + 9)]
  have hδ49 : δ ^ 2 ≤ 1 / 49 := by
    have h2 : 49 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
      nlinarith [h49, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  have h449 : 49 * ((k : ℝ) + 1) ≤ 6 * ((k : ℝ) + 2) ^ 2 := by
    have hfac : 6 * ((k : ℝ) + 2) ^ 2 - 49 * ((k : ℝ) + 1)
        = ((k : ℝ) - 5) * (6 * (k : ℝ) + 5) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 5)
      (by linarith : (0 : ℝ) ≤ 6 * (k : ℝ) + 5)]
  have hT3 : ((k : ℝ) + 1) * δ ^ 2 ≤ 6 / 49 := by
    have h2 : 49 * (((k : ℝ) + 1) * δ ^ 2) ≤ 6 * (((k : ℝ) + 2) ^ 2 * δ ^ 2) := by
      nlinarith [h449, pow_pos hδ0 2]
    rw [hδ2''] at h2
    linarith
  have hmid : ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
      ≤ ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + δ ^ 3 * Q) :=
    mul_le_mul_of_nonneg_left (by linarith [hA3]) (by linarith)
  have hpos1 : (0 : ℝ) < ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + δ ^ 3 * Q) := by
    positivity
  calc ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1))
        * (1 - Real.cos (2 * π * δ))
      ≤ ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + δ ^ 3 * Q)
          * (1 - Real.cos (2 * π * δ)) :=
        mul_le_mul_of_nonneg_right hmid hcosnn
    _ < ((k : ℝ) + 1) * ((2 * δ * Q + 2) * (9 / 8) + δ ^ 3 * Q) * (2 * (π * δ) ^ 2) :=
        mul_lt_mul_of_pos_left hu hpos1
    _ = (Q : ℝ) * (9 / 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3))
        + 9 / 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2)
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2) := by
        ring
    _ < (Q : ℝ) * (1 + 2 * wr) := by
        have hb1 : 9 / 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) ≤ 9 / 2 * 9.9225 * (6 / 343) := by
          nlinarith [hT1, hπ2, Real.pi_pos,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
        have hb2 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 3) * δ ^ 2
            ≤ 2 * 9.9225 * (6 / 343) * (1 / 49) := by
          nlinarith [hT1, hπ2, hδ49, Real.pi_pos, pow_pos hδ0 2, pow_pos hδ0 3,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 3)]
        have hbC1 : 9 / 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 2) ≤ 9 / 2 * 9.9225 * (6 / 49) := by
          nlinarith [hT3, hπ2, Real.pi_pos,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 2)]
        have hm1 := mul_le_mul_of_nonneg_left hb1 hQR.le
        have hm2 := mul_le_mul_of_nonneg_left hb2 hQR.le
        have hM34 : (15 / 16 : ℝ) * Q ≤ (Q : ℝ) * (1 + 2 * wr) := hMlow
        linarith [hm1, hm2, hbC1, hQ340, hM34]



set_option maxHeartbeats 4000000 in
/-- **The floor for multi-torsion strongly free families of at least six runners.**
The resonant-set method at full strength: at each runner `i` every bounded
resonance lies in a set `Res i`, and the *total* resonant weight
`∑_i ∑_{Res i} 2^{−|supp|}` is at most `1`.  Non-resonant combinations are
`(A+1)/Q`-far from the integers (`afree_nid_lower''`), the family is strongly
free so the Riesz mass is exactly `Q`, and the union closes at
`4π²/(k+2)² < 1` for every `k ≥ 5`.  A single torsion relation is the case
`Res i₀ = {±c₀}`; several relations — up to total weight one — are covered at
once. -/
theorem riesz_clears_floor_torsion_multi {k : ℕ} (hk : 5 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i) (hSF : StrongFree v)
    (Res : Fin (k + 1) → Finset (Fin k → ℤ))
    (hResSub : ∀ i, Res i ⊆
        (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
    (hResClass : ∀ i : Fin (k + 1), ∀ c : Fin k → ℤ,
        (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) → c ≠ 0 → c ∉ Res i →
        ∀ ρ : ℤ, |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i)
    (hSres : (∑ i, ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set A : ℕ := 2 ^ k * (k + 2) ^ 3 with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨Q, hQp, hQN, hQsum, hQcop⟩ :=
    exists_coprime_modulus_ge (k + 1) v ((A + 1) * (∑ w, (v w).natAbs))
  have hQ0 : 0 < Q := hQp.pos
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
    riesz_mass_real (k + 1) v hSF Q hQ0 hQsum
  have hσnn : ∀ i, (0 : ℝ) ≤ ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
    fun i => Finset.sum_nonneg fun c _ => Finset.prod_nonneg fun j' _ => by positivity
  have hA3 : (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) ≤ δ ^ 3 * Q := by
    have hAval : ((A : ℝ) + 1) = (2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1 := by
      rw [hA]; push_cast; ring
    have hδ3 : ((k : ℝ) + 2) ^ 3 * δ ^ 3 = 1 := by rw [hδdef]; field_simp
    rw [div_le_iff₀ (by rw [hAval]; positivity), hAval]
    have hexp : δ ^ 3 * (Q : ℝ) * ((2 ^ k : ℝ) * ((k : ℝ) + 2) ^ 3 + 1)
        = (2 ^ k : ℝ) * Q * (((k : ℝ) + 2) ^ 3 * δ ^ 3) + δ ^ 3 * Q := by ring
    rw [hexp, hδ3, mul_one]
    nlinarith [pow_pos hδ0 3, hQR]
  set W : Fin (k + 1) → ℝ := fun i =>
    (2 * δ * Q + 2) * (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
      + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) with hW
  have hWbound : ∀ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
      (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
      ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
      ≤ W i := by
    intro i
    have hvpos := hpos i
    have hvnA : (v i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hvpos)
    have hcop := hQcop i hvnA
    have htoNat : (v i).toNat = (v i).natAbs := by
      have h1 : ((v i).toNat : ℤ) = ((v i).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg hvpos.le, Int.natAbs_of_nonneg hvpos.le]
      exact_mod_cast h1
    have hcop2 : Nat.Coprime ((v i).toNat % Q) Q := by
      rw [htoNat]
      show Nat.gcd ((v i).natAbs % Q) Q = 1
      rw [← Nat.gcd_rec Q (v i).natAbs, Nat.gcd_comm]
      exact hcop
    obtain ⟨b, hab⟩ := exists_nat_inverse _ Q hQ0 hcop2
    have hwtnn : ∀ c : Fin k → ℤ, (0 : ℝ) ≤ ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2) :=
      fun c => Finset.prod_nonneg fun j' _ => by positivity
    have hsum_wt : ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
        (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ (2 ^ k : ℝ) := by
      calc ∑ c ∈ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0,
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          ≤ ∑ c ∈ Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ)),
            (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun c _ _ => hwtnn c)
        _ = ∏ _j' : Fin k, ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
              (if a' = 0 then (1 : ℝ) else 1 / 2) := by
            rw [Finset.prod_univ_sum]
        _ = (2 ^ k : ℝ) := by
            have hthree : ∑ a' ∈ ({-1, 0, 1} : Finset ℤ),
                (if a' = 0 then (1 : ℝ) else 1 / 2) = 2 := by
              rw [show ({-1, 0, 1} : Finset ℤ) = insert (-1 : ℤ) (insert (0 : ℤ) {1}) from rfl,
                Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              norm_num
            rw [Finset.prod_congr rfl fun _ _ => hthree, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    have hcard' : (((Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
        ≤ 2 * δ * Q + 2 := by
      rw [badset_filter_eq Q hQ0 (v i) hvpos δ]
      exact badset_card_bound Q hQ0 ((v i).toNat % Q) b hab δ hδ0.le hδ2
    have hF0 : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ Res i, (∑ j', c j' * v (i.succAbove j')) ≠ 0 := by
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      intro hF
      have h1 : (1 : ℤ) ≤ ((A : ℕ) : ℤ) := by exact_mod_cast hA0
      exact hResClass i c hcmem' hc0 hcR 0 (by rw [abs_zero]; omega) (by rw [hF, zero_mul])
    have hsplit := badset_weight_split' v Q hQ0 hQsum i hvpos b hab δ hδ2 (Res i)
      (hResSub i) hF0
    have hperc : ∀ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
        \ Res i,
        4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
            * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖
          ≤ (Q : ℝ) / ((A : ℝ) + 1) := by
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_erase] at hc
      obtain ⟨⟨hc0, hcmem⟩, hcR⟩ := hc
      have hcmem' : ∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcmem) j'
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      have hnid := afree_nid_lower'' v i A Q hQ0 hQN b hab hvpos c hcmem' hc0
        (fun ρ hρ => hResClass i c hcmem' hc0 hcR ρ hρ)
      exact afree_perc_bound Q hQ0 ((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) A hnid
    calc ∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))
        ≤ (((Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ)).card : ℝ)
            * (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          + ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
              \ Res i,
              (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                    * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖) := hsplit
      _ ≤ (2 * δ * Q + 2)
            * (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
          + (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul hcard' (le_refl _) ?_ (by positivity)
            have := hσnn i; linarith
          · calc ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ Res i, (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))
                    * (4 / ‖1 - Complex.exp (2 * ↑π * Complex.I
                        * ↑((∑ j', c j' * v (i.succAbove j')) * (b : ℤ)) / ↑Q)‖)
                ≤ ∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ Res i, (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) * ((Q : ℝ) / ((A : ℝ) + 1)) :=
                  Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hperc c hc) (hwtnn c)
              _ = (∑ c ∈ ((Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0)
                  \ Res i, (∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2))) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  rw [Finset.sum_mul]
              _ ≤ (2 ^ k : ℝ) * ((Q : ℝ) / ((A : ℝ) + 1)) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                    Finset.sdiff_subset (fun c _ _ => hwtnn c)) hsum_wt
              _ = (2 ^ k : ℝ) * Q / ((A : ℝ) + 1) := by ring
      _ = W i := by rw [hW]
  refine riesz_union_weights v Q hQ0 δ hδ0 hδ2 (Q : ℝ) hmass W hWbound ?_
  -- union arithmetic: total weight ≤ 1 keeps the surcharge inside one runner
  have hUB : ∑ i, W i ≤ (2 * δ * Q + 2) * ((k : ℝ) + 2) + ((k : ℝ) + 1) * (δ ^ 3 * Q) := by
    have hstep : ∀ i, W i ≤ (2 * δ * Q + 2)
        * (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) + δ ^ 3 * Q := by
      intro i; simp only [hW]; linarith [hA3]
    calc ∑ i, W i
        ≤ ∑ i, ((2 * δ * Q + 2)
            * (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) + δ ^ 3 * Q) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (2 * δ * Q + 2) * (∑ i, (1 + ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)))
          + ((k : ℝ) + 1) * (δ ^ 3 * Q) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ = (2 * δ * Q + 2) * (((k : ℝ) + 1)
            + (∑ i, ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)))
          + ((k : ℝ) + 1) * (δ ^ 3 * Q) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          push_cast; ring
      _ ≤ (2 * δ * Q + 2) * ((k : ℝ) + 2) + ((k : ℝ) + 1) * (δ ^ 3 * Q) := by
          have h2 : (0 : ℝ) ≤ 2 * δ * Q + 2 := by positivity
          nlinarith [hSres, h2]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hδ2'' : ((k : ℝ) + 2) ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp
  have hδ49 : δ ^ 2 ≤ 1 / 49 := by
    have h2 : 49 * δ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * δ ^ 2 := by
      nlinarith [hkR, pow_pos hδ0 2]
    rw [hδ2''] at h2; linarith
  have hδ7 : δ ≤ 1 / 7 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ4 : δ ^ 4 ≤ 1 / 2401 := by nlinarith [hδ49, pow_pos hδ0 2, sq_nonneg (δ ^ 2)]
  have hID1 : ((k : ℝ) + 2) * δ ^ 3 = δ ^ 2 := by
    have h : ((k : ℝ) + 2) * δ ^ 3 = δ ^ 2 * (δ * ((k : ℝ) + 2)) := by ring
    rw [h, hδval, mul_one]
  have hID2 : ((k : ℝ) + 2) * δ ^ 2 = δ := by
    have h : ((k : ℝ) + 2) * δ ^ 2 = δ * (δ * ((k : ℝ) + 2)) := by ring
    rw [h, hδval, mul_one]
  have hID3 : ((k : ℝ) + 1) * δ ^ 5 ≤ δ ^ 4 := by
    have hle : ((k : ℝ) + 1) * δ ^ 5 ≤ ((k : ℝ) + 2) * δ ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_pos hδ0 5).le
    have heq : ((k : ℝ) + 2) * δ ^ 5 = δ ^ 4 := by
      have h : ((k : ℝ) + 2) * δ ^ 5 = δ ^ 4 * (δ * ((k : ℝ) + 2)) := by ring
      rw [h, hδval, mul_one]
    linarith [hle, heq]
  have hQ340 : (340 : ℝ) ≤ (Q : ℝ) := by
    have hA1 : 3456 ≤ A := by
      rw [hA]
      have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 3456 = 2 ^ 4 * 6 ^ 3 := by norm_num
        _ ≤ 2 ^ k * (k + 2) ^ 3 := Nat.mul_le_mul h1 h2
    have hsum1 : k + 1 ≤ ∑ w, (v w).natAbs := by
      calc k + 1 = ∑ _w : Fin (k + 1), 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        _ ≤ ∑ w, (v w).natAbs := by
            refine Finset.sum_le_sum fun w _ => ?_
            have h1 : (v w).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt (hpos w))
            omega
    have hQbig : 340 ≤ Q := by
      have h3 : (A + 1) * (∑ w, (v w).natAbs) ≥ 3457 * 6 := by
        have h4 : 6 ≤ ∑ w, (v w).natAbs := by omega
        exact Nat.mul_le_mul (by omega) h4
      omega
    exact_mod_cast hQbig
  have hUBpos : (0 : ℝ) < (2 * δ * Q + 2) * ((k : ℝ) + 2) + ((k : ℝ) + 1) * (δ ^ 3 * Q) := by
    positivity
  calc (∑ i, W i) * (1 - Real.cos (2 * π * δ))
      ≤ ((2 * δ * Q + 2) * ((k : ℝ) + 2) + ((k : ℝ) + 1) * (δ ^ 3 * Q))
          * (1 - Real.cos (2 * π * δ)) :=
        mul_le_mul_of_nonneg_right hUB hcosnn
    _ < ((2 * δ * Q + 2) * ((k : ℝ) + 2) + ((k : ℝ) + 1) * (δ ^ 3 * Q)) * (2 * (π * δ) ^ 2) :=
        mul_lt_mul_of_pos_left hu hUBpos
    _ = (Q : ℝ) * (4 * π ^ 2 * (((k : ℝ) + 2) * δ ^ 3))
        + 4 * π ^ 2 * (((k : ℝ) + 2) * δ ^ 2)
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 5)) := by ring
    _ = (Q : ℝ) * (4 * π ^ 2 * δ ^ 2) + 4 * π ^ 2 * δ
        + (Q : ℝ) * (2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 5)) := by rw [hID1, hID2]
    _ < (Q : ℝ) := by
        have hb1 : 4 * π ^ 2 * δ ^ 2 ≤ 4 * 9.9225 * (1 / 49) := by
          nlinarith [hδ49, hπ2, Real.pi_pos, pow_pos hδ0 2]
        have hb3 : 2 * π ^ 2 * (((k : ℝ) + 1) * δ ^ 5) ≤ 2 * 9.9225 * (1 / 2401) := by
          nlinarith [hID3, hδ4, hπ2, Real.pi_pos, pow_pos hδ0 4, pow_pos hδ0 5,
            mul_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1) (pow_pos hδ0 5)]
        have hbC : 4 * π ^ 2 * δ ≤ 4 * 9.9225 * (1 / 7) := by
          nlinarith [hδ7, hπ2, Real.pi_pos, hδ0]
        have hm1 := mul_le_mul_of_nonneg_left hb1 hQR.le
        have hm3 := mul_le_mul_of_nonneg_left hb3 hQR.le
        nlinarith [hm1, hm3, hbC, hQ340, hQR]


/-- **Bounded resonance** at level `A(k) = 2^k(k+2)³`: there is a per-runner
resonant set carrying every bounded torsion relation, of total weight at most
one.  A single torsion relation gives total weight `≤ 1`; so does any family
whose torsion relations, jointly, are sparse. -/
def BoundedResonance {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∃ Res : Fin (k + 1) → Finset (Fin k → ℤ),
    (∀ i, Res i ⊆ (Fintype.piFinset (fun _ : Fin k => ({-1, 0, 1} : Finset ℤ))).erase 0) ∧
    (∀ i : Fin (k + 1), ∀ c : Fin k → ℤ,
        (∀ j', c j' = -1 ∨ c j' = 0 ∨ c j' = 1) → c ≠ 0 → c ∉ Res i →
        ∀ ρ : ℤ, |ρ| ≤ ((2 ^ k * (k + 2) ^ 3 : ℕ) : ℤ) →
        (∑ j', c j' * v (i.succAbove j')) ≠ ρ * v i) ∧
    (∑ i, ∑ c ∈ Res i, ∏ j', (if c j' = 0 then (1 : ℝ) else 1 / 2)) ≤ 1

/-- **The bounded-resonance floor**: the multi-torsion engine, packaged. -/
theorem riesz_clears_floor_boundedResonance {k : ℕ} (hk : 5 ≤ k) (v : Fin (k + 1) → ℤ)
    (hpos : ∀ i, 0 < v i) (hSF : StrongFree v) (hBR : BoundedResonance v) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  obtain ⟨Res, hSub, hClass, hSres⟩ := hBR
  exact riesz_clears_floor_torsion_multi hk v hpos hSF Res hSub hClass hSres

/-- **The dense-torsion residual**: the free side after the multi-torsion engine.
Only two shards remain — four runners, and `5`–`8` runners whose torsion is so
dense that no bounded-weight resonant set captures it. -/
def DenseTorsionResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ATorsionFree v → ¬ SingleTorsionData v →
    (k = 4 ∨ ¬ BoundedResonance v) → 1 / ((k : ℝ) + 2) ≤ ML v

/-- The multi-torsion engine collapses the deep-torsion residual to the dense
shard: every `k ≥ 5` family with bounded resonance already meets its floor. -/
theorem deepTorsionResidual_of_dense (h : DenseTorsionResidual) : DeepTorsionResidual := by
  intro k hk4 hk7 v hv hSF hAF hnSingle
  by_cases hk5 : 5 ≤ k
  · by_cases hBR : BoundedResonance v
    · exact riesz_clears_floor_boundedResonance hk5 v hv hSF hBR
    · exact h k hk4 hk7 v hv hSF hAF hnSingle (Or.inr hBR)
  · exact h k hk4 hk7 v hv hSF hAF hnSingle (Or.inl (by omega))

/-- **Separation from the four-runner window and the dense-torsion residual.**
The free side of the all-`N` program after the A-free, single-torsion, and
multi-torsion floor theorems: only `m = 4` and the dense torsion shard remain. -/
theorem separationSF_of_four_and_dense (h1 : WindowFour) (h2 : DenseTorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_four_and_deep h1 (deepTorsionResidual_of_dense h2)


/-! ### The degree-two mass: the squared Riesz product -/

/-- **Two-dissociativity**: no nonzero integer combination with coefficients in
`[-2,2]` vanishes.  This is exactly what the *squared* Riesz product needs — it
is strong freeness reinforced against one collision step. -/
def TwoDissoc {m : ℕ} (v : Fin m → ℤ) : Prop :=
  ∀ d : Fin m → ℤ, (∀ i, -2 ≤ d i ∧ d i ≤ 2) → (∑ i, d i * v i) = 0 → d = 0

set_option maxHeartbeats 1000000 in
/-- **The squared-mass identity.**  For a two-dissociated family the degree-two
Riesz product `R(j)^2` has total grid mass `Q·(3/2)^m`.  `R^2` is the degree-one
mass of the *doubled* family `append v v`, whose only `{-1,0,1}`-relations are the
`m` disjoint duplicate pairs (this is precisely two-dissociativity); each pair
contributes `1 + 2·(1/4) = 3/2`. -/
theorem riesz_mass_sq (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : 2 * (∑ i, (v i).natAbs) < Q) (hdiss : TwoDissoc v) :
    ∑ j ∈ Finset.range Q,
        (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 2
      = (Q : ℝ) * (3 / 2) ^ m := by
  classical
  set w : Fin (m + m) → ℤ := Fin.append v v with hw
  have hwcast : ∀ i : Fin m, w (Fin.castAdd m i) = v i := fun i => by rw [hw, Fin.append_left]
  have hwnat : ∀ i : Fin m, w (Fin.natAdd m i) = v i := fun i => by rw [hw, Fin.append_right]
  have hwQ : (∑ l, (w l).natAbs) < Q := by
    have : (∑ l, (w l).natAbs) = 2 * (∑ i, (v i).natAbs) := by
      rw [Fin.sum_univ_add]
      simp only [hwcast, hwnat]; ring
    rw [this]; exact hQ
  set Rel : Fin m → Fin (m + m) → ℤ :=
    fun t l => if l = Fin.castAdd m t then 1 else if l = Fin.natAdd m t then -1 else 0 with hRel
  have hcastnat : ∀ t t' : Fin m, Fin.castAdd m t ≠ Fin.natAdd m t' := by
    intro t t' h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this; omega
  have hcastinj : ∀ i t : Fin m, Fin.castAdd m i = Fin.castAdd m t → i = t := by
    intro i t h; have := congrArg Fin.val h
    simp only [Fin.coe_castAdd] at this; exact Fin.ext this
  have hnatinj : ∀ i t : Fin m, Fin.natAdd m i = Fin.natAdd m t → i = t := by
    intro i t h; have := congrArg Fin.val h
    simp only [Fin.coe_natAdd] at this; exact Fin.ext (by omega)
  have hReliff : ∀ t l, Rel t l ≠ 0 → l = Fin.castAdd m t ∨ l = Fin.natAdd m t := by
    intro t l h; simp only [hRel] at h; split_ifs at h with h1 h2
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd rfl h
  have hmem : ∀ t l, Rel t l = -1 ∨ Rel t l = 0 ∨ Rel t l = 1 := by
    intro t l; simp only [hRel]; split_ifs <;> tauto
  have hRelcast : ∀ t i : Fin m, Rel t (Fin.castAdd m i) = (if i = t then (1:ℤ) else 0) := by
    intro t i; simp only [hRel]
    by_cases h : i = t
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun he => h (hcastinj i t he)), if_neg (hcastnat i t), if_neg h]
  have hRelnat : ∀ t i : Fin m, Rel t (Fin.natAdd m i) = (if i = t then (-1:ℤ) else 0) := by
    intro t i; simp only [hRel]
    by_cases h : i = t
    · rw [if_neg (fun he => hcastnat t i he.symm), if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun he => hcastnat t i he.symm), if_neg (fun he => h (hnatinj i t he)),
        if_neg h]
  have hrel : ∀ t, (∑ l, Rel t l * w l) = 0 := by
    intro t
    rw [Fin.sum_univ_add]
    simp only [hRelcast, hRelnat, hwcast, hwnat]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : i = t <;> simp [h]
  have hne : ∀ t, ∃ l, Rel t l ≠ 0 := fun t =>
    ⟨Fin.castAdd m t, by rw [hRelcast]; simp⟩
  have hdisj : ∀ t t', t ≠ t' → ∀ l, Rel t l = 0 ∨ Rel t' l = 0 := by
    intro t t' htt' l
    by_contra hcon; push_neg at hcon
    rcases hReliff t l hcon.1 with h | h <;> rcases hReliff t' l hcon.2 with h' | h'
    · exact htt' (hcastinj t t' (h.symm.trans h'))
    · exact hcastnat t t' (h.symm.trans h')
    · exact hcastnat t' t (h'.symm.trans h)
    · exact htt' (hnatinj t t' (h.symm.trans h'))
  have hchar : ∀ c : Fin (m + m) → ℤ, (∀ l, c l = -1 ∨ c l = 0 ∨ c l = 1) →
      (∑ l, c l * w l) = 0 → ∃ α : Fin m → ℤ, (∀ t, α t = -1 ∨ α t = 0 ∨ α t = 1) ∧
        c = fun l => ∑ t, α t * Rel t l := by
    intro c hcm hcv
    have hsum : (∑ l, c l * w l) = ∑ i, (c (Fin.castAdd m i) + c (Fin.natAdd m i)) * v i := by
      rw [Fin.sum_univ_add]
      simp only [hwcast, hwnat, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum] at hcv
    have hd : (fun i => c (Fin.castAdd m i) + c (Fin.natAdd m i)) = 0 := by
      apply hdiss
      · intro i
        rcases hcm (Fin.castAdd m i) with h1 | h1 | h1 <;>
          rcases hcm (Fin.natAdd m i) with h2 | h2 | h2 <;> rw [h1, h2] <;> omega
      · exact hcv
    have hc2 : ∀ i, c (Fin.natAdd m i) = - c (Fin.castAdd m i) := by
      intro i; have := congrFun hd i; simp only [Pi.zero_apply] at this; omega
    refine ⟨fun t => c (Fin.castAdd m t), fun t => hcm (Fin.castAdd m t), ?_⟩
    funext l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · simp only [hRelcast, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ i (fun t => c (Fin.castAdd m t))]
      simp
    · simp only [hRelnat, mul_ite, mul_neg, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ i (fun t => -c (Fin.castAdd m t)),
        if_pos (Finset.mem_univ i)]
      exact hc2 i
  -- convert R^2 into the doubled-family degree-one product, then evaluate
  have hregroup : ∀ j : ℕ,
      (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 2
      = ∏ l : Fin (m + m), (1 - Real.cos (2 * π * (w l : ℝ) * (j : ℝ) / (Q : ℝ))) := by
    intro j
    rw [Fin.prod_univ_add]
    simp only [hwcast, hwnat]
    rw [pow_two]
  rw [Finset.sum_congr rfl (fun j _ => hregroup j),
    riesz_mass_disjoint_real (m + m) m w Q hQ0 hwQ Rel hmem hrel hne hdisj hchar]
  -- evaluate the relation product to (3/2)^m
  have hfac : ∀ t : Fin m,
      (1 + 2 * ∏ l : Fin (m + m), (if Rel t l = 0 then (1:ℝ) else -1 / 2)) = 3 / 2 := by
    intro t
    have hp : (∏ l : Fin (m + m), (if Rel t l = 0 then (1:ℝ) else -1 / 2)) = 1 / 4 := by
      rw [Fin.prod_univ_add]
      have hc : (∏ i : Fin m, (if Rel t (Fin.castAdd m i) = 0 then (1:ℝ) else -1 / 2)) = -1 / 2 := by
        rw [Finset.prod_congr rfl (fun i _ =>
          show (if Rel t (Fin.castAdd m i) = 0 then (1:ℝ) else -1 / 2)
              = (if i = t then (-1/2 : ℝ) else 1) by
            rw [hRelcast]; by_cases h : i = t <;> simp [h])]
        rw [Finset.prod_ite_eq' Finset.univ t (fun _ => (-1/2 : ℝ))]; simp
      have hn : (∏ i : Fin m, (if Rel t (Fin.natAdd m i) = 0 then (1:ℝ) else -1 / 2)) = -1 / 2 := by
        rw [Finset.prod_congr rfl (fun i _ =>
          show (if Rel t (Fin.natAdd m i) = 0 then (1:ℝ) else -1 / 2)
              = (if i = t then (-1/2 : ℝ) else 1) by
            rw [hRelnat]; by_cases h : i = t <;> simp [h])]
        rw [Finset.prod_ite_eq' Finset.univ t (fun _ => (-1/2 : ℝ))]; simp
      rw [hc, hn]; norm_num
    rw [hp]; norm_num
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]


/-! ### The general character-sum mass (any family) -/

/-- **The general Riesz mass.**  On the prime-free grid `Q > ∑|v|`, the degree-one
Riesz product sums to `Q` times the weight of its *vanishing* `{-1,0,1}`-combinations:
`∑_j ∏_i (1-cos 2πv_i j/Q) = Q·∑_{c : ∑c_i v_i = 0} ∏_i wt(c_i)`.  Character
orthogonality on `Z/Q`; the size bound `|∑c_i v_i| ≤ ∑|v_i| < Q` turns `Q ∣ F(c)`
into `F(c) = 0`.  Both `riesz_mass_real` (empty relation set) and the disjoint and
squared masses are special evaluations of this. -/
theorem riesz_mass_general (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q))
      = (Q : ℂ) * ∑ c ∈ (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2) := by
  classical
  rw [riesz_mass_expand_pub m v Q hQ0]
  have habs : ∀ c ∈ Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ)),
      (Q : ℤ) ∣ (∑ i, c i * v i) → (∑ i, c i * v i) = 0 := by
    intro c hc hdvd
    have hb : (∑ i, c i * v i).natAbs ≤ ∑ i, (v i).natAbs := by
      calc (∑ i, c i * v i).natAbs ≤ ∑ i, (c i * v i).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ i, (v i).natAbs := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Int.natAbs_mul]
            have hci : (c i).natAbs ≤ 1 := by
              have := (Fintype.mem_piFinset.mp hc) i
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h | h <;> simp [h]
            calc (c i).natAbs * (v i).natAbs ≤ 1 * (v i).natAbs := Nat.mul_le_mul_right _ hci
              _ = (v i).natAbs := one_mul _
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_le_of_lt hb hQ
  rw [Finset.sum_filter]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hz : (∑ i, c i * v i) = 0
  · rw [if_pos (by rw [hz]; exact dvd_zero _), if_pos hz]; ring
  · rw [if_neg hz]
    by_cases hdvd : (Q : ℤ) ∣ (∑ i, c i * v i)
    · exact absurd (habs c hc hdvd) hz
    · rw [if_neg hdvd]; ring

/-- Real form of the general mass. -/
theorem riesz_mass_general_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * ∑ c ∈ (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, (if c i = 0 then (1 : ℝ) else -1 / 2) := by
  classical
  have h := riesz_mass_general m v Q hQ0 hQ
  have hcs : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2; push_cast; ring
  have hrs : (((Q : ℝ) * ∑ c ∈ (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, (if c i = 0 then (1 : ℝ) else -1 / 2) : ℝ) : ℂ)
      = (Q : ℂ) * ∑ c ∈ (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, (if c i = 0 then (1 : ℂ) else -1 / 2) := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    refine congrArg _ (Finset.sum_congr rfl (fun c _ => ?_))
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs <;> push_cast <;> ring
  exact Complex.ofReal_injective (hcs.trans (h.trans hrs.symm))


/-! ### The degree-three crude union (no equidistribution) -/

set_option maxHeartbeats 800000 in
/-- **The crude degree-three union.**  For the cube weight `R^3`, if the full and
subfamily cube masses are `M`, `Msub` and `(k+1)·(1-cos 2πδ)^3·Msub < M`, then a
`δ`-lonely grid point exists, so `ML ≥ δ`.  The bad-set weight is bounded
*crudely* — extended to the whole grid — so this needs no Fourier/dichotomy
control, only the mass identities. -/
theorem riesz_crude_union_cube {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M Msub : ℝ)
    (hM : ∑ j ∈ Finset.range Q,
        (∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 = M)
    (hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
        (∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
        = Msub)
    (hcond : ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3 * Msub < M) :
    δ ≤ ML v := by
  set R3 : ℕ → ℝ := fun j : ℕ =>
    (∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 with hR3def
  have hR3nn : ∀ j, 0 ≤ R3 j := fun j => by
    rw [hR3def]
    exact pow_nonneg (Finset.prod_nonneg fun i _ => by
      have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith) 3
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  -- per-runner crude bound
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
        ≤ (1 - Real.cos (2 * π * δ)) ^ 3 * Msub := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    set S3 : ℕ → ℝ := fun j : ℕ =>
      (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 with hS3def
    have hS3nn : ∀ j, 0 ≤ S3 j := fun j => by
      rw [hS3def]
      exact pow_nonneg (Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith) 3
    have hR3split : ∀ j : ℕ, R3 j
        = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 3 * S3 j := fun j => by
      simp only [hR3def, hS3def]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i, mul_pow]
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
        = ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 3 * S3 j :=
          Finset.sum_congr rfl (fun j _ => hR3split j)
      _ ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * δ)) ^ 3 * S3 j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          refine mul_le_mul_of_nonneg_right ?_ (hS3nn j)
          have hle : (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              ≤ 1 - Real.cos (2 * π * δ) := by
            rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
                = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
            have hcosle : Real.cos (2 * π * δ)
                ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
              Real.cos_le_cos_of_nonneg_of_le_pi
                (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
                (by nlinarith [Real.pi_pos, hδ2])
                (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
            linarith
          have hnn : 0 ≤ 1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
            have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
          exact pow_le_pow_left₀ hnn hle 3
      _ = (1 - Real.cos (2 * π * δ)) ^ 3 * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), S3 j :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - Real.cos (2 * π * δ)) ^ 3 * Msub := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hcosδ 3)
          rw [← hMsub i]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hS3nn j)
  -- covering ⟹ mass contradiction unless a lonely point exists
  have hgood : ∃ j ∈ Finset.range Q, ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hcover : ∑ j ∈ Finset.range Q, R3 j
        ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j := by
      have hrw : (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
          = ∑ j ∈ Finset.range Q, ∑ i : Fin (k + 1),
              (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
        simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      rw [hrw]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨i, hi⟩ := hcon j hj
      calc R3 j = (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
              rw [if_pos hi]
        _ ≤ ∑ i' : Fin (k + 1),
              (if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
            refine Finset.single_le_sum
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hR3nn j
            · exact le_refl 0
    have hchain : M ≤ ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3 * Msub := by
      rw [← hM]
      calc ∑ j ∈ Finset.range Q, R3 j
          ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j := hcover
        _ ≤ ∑ _i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) ^ 3 * Msub :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3 * Msub := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    linarith [hchain, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

#print axioms riesz_crude_union_cube

/-! ### The degree-three mass: the cubed Riesz product, directly -/

/-- **Three-dissociativity**: no nonzero `[-3,3]`-coefficient combination vanishes. -/
def ThreeDissoc {m : ℕ} (v : Fin m → ℤ) : Prop :=
  ∀ d : Fin m → ℤ, (∀ i, -3 ≤ d i ∧ d i ≤ 3) → (∑ i, d i * v i) = 0 → d = 0

/-- The seven-term weight of the cubed Riesz factor:
`(1−cos θ)³ = 5/2 − (15/8)(e(θ)+e(−θ)) + (3/4)(e(2θ)+e(−2θ)) − (1/8)(e(3θ)+e(−3θ))`. -/
noncomputable def cubeWt (a : ℤ) : ℂ :=
  if a = 0 then 5 / 2 else if a = 1 ∨ a = -1 then -15 / 8
  else if a = 2 ∨ a = -2 then 3 / 4 else -1 / 8

/-- The seven-term exponential expansion of a cubed Riesz factor. -/
private lemma cube_factor_pub (z : ℂ) :
    (1 - Complex.cos z) ^ 3
      = ∑ a ∈ ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ),
          cubeWt a * Complex.exp ((a : ℂ) * z * Complex.I) := by
  have hset : ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)
      = insert (-3 : ℤ) (insert (-2 : ℤ) (insert (-1 : ℤ) (insert (0 : ℤ)
          (insert (1 : ℤ) (insert (2 : ℤ) {3}))))) := rfl
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show cubeWt (-3) = -1/8 from by norm_num [cubeWt],
      show cubeWt (-2) = 3/4 from by norm_num [cubeWt],
      show cubeWt (-1) = -15/8 from by norm_num [cubeWt],
      show cubeWt 0 = 5/2 from by norm_num [cubeWt],
      show cubeWt 1 = -15/8 from by norm_num [cubeWt],
      show cubeWt 2 = 3/4 from by norm_num [cubeWt],
      show cubeWt 3 = -1/8 from by norm_num [cubeWt]]
  rw [show ((-3 : ℤ) : ℂ) * z * Complex.I = (3 : ℕ) * ((-z) * Complex.I) by push_cast; ring,
      show ((-2 : ℤ) : ℂ) * z * Complex.I = (2 : ℕ) * ((-z) * Complex.I) by push_cast; ring,
      show ((-1 : ℤ) : ℂ) * z * Complex.I = (-z) * Complex.I by push_cast; ring,
      show ((0 : ℤ) : ℂ) * z * Complex.I = 0 by push_cast; ring,
      show ((1 : ℤ) : ℂ) * z * Complex.I = z * Complex.I by push_cast; ring,
      show ((2 : ℤ) : ℂ) * z * Complex.I = (2 : ℕ) * (z * Complex.I) by push_cast; ring,
      show ((3 : ℤ) : ℂ) * z * Complex.I = (3 : ℕ) * (z * Complex.I) by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul,
      Complex.exp_zero, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
  linear_combination (3 / 4 : ℂ) * (2 - Complex.cos z) * Complex.sin_sq_add_cos_sq z
    + (3 / 4 : ℂ) * Complex.sin z ^ 2 * (Complex.cos z - 2) * Complex.I_sq

/-- **Public cubed-mass expansion**, indexed by `[-3,3]`-combinations. -/
theorem riesz_mass_cube_expand (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3
      = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)),
          (∏ i, cubeWt (c i))
            * (if (Q : ℤ) ∣ (∑ i, c i * v i) then (Q : ℂ) else 0) := by
  have step1 : ∀ j ∈ Finset.range Q,
      (∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3)
        = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)),
            (∏ i, cubeWt (c i))
              * Complex.exp (2 * ↑π * Complex.I * ↑(∑ i, c i * v i) * ↑j / ↑Q) := by
    intro j _
    rw [Finset.prod_congr rfl
      (fun i _ => cube_factor_pub (2 * ↑π * ↑(v i) * ↑j / ↑Q)), Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum, exp_geom_sum Q hQ0 (∑ i, c i * v i)]

set_option maxHeartbeats 1000000 in
/-- **The cubed-mass identity.**  For a three-dissociated family the degree-three
Riesz product has grid mass `Q·(5/2)^m`: on the grid `Q > 3∑|v|` every nonzero
`[-3,3]`-combination has `0 < |∑c_i v_i| < Q`, so only `c = 0` survives, with
weight `cubeWt(0)^m = (5/2)^m`. -/
theorem riesz_mass_cube (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : 3 * (∑ i, (v i).natAbs) < Q) (hdiss : ThreeDissoc v) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3
      = (Q : ℂ) * (5 / 2) ^ m := by
  classical
  rw [riesz_mass_cube_expand m v Q hQ0]
  have hmem0 : (0 : Fin m → ℤ) ∈ Fintype.piFinset
      (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
    rw [Fintype.mem_piFinset]
    intro i
    simp
  rw [Finset.sum_eq_single_of_mem (0 : Fin m → ℤ) hmem0 ?_]
  · have hF0 : (∑ i, (0 : Fin m → ℤ) i * v i) = 0 :=
      Finset.sum_eq_zero fun i _ => zero_mul _
    rw [hF0, if_pos (dvd_zero _)]
    have hwt : (∏ i : Fin m, cubeWt ((0 : Fin m → ℤ) i)) = (5 / 2 : ℂ) ^ m := by
      have h1 : ∀ i : Fin m, cubeWt ((0 : Fin m → ℤ) i) = 5 / 2 := fun i => by
        norm_num [cubeWt]
      rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [hwt, mul_comm]
  · intro c hc hc0
    have hcb : ∀ i, -3 ≤ c i ∧ c i ≤ 3 := by
      intro i
      have := (Fintype.mem_piFinset.mp hc) i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h | h | h | h <;> omega
    have hF : (∑ i, c i * v i) ≠ 0 := fun h => hc0 (hdiss c hcb h)
    have habs : (∑ i, c i * v i).natAbs < Q := by
      have hb : (∑ i, c i * v i).natAbs ≤ 3 * ∑ i, (v i).natAbs := by
        calc (∑ i, c i * v i).natAbs ≤ ∑ i, (c i * v i).natAbs := Int.natAbs_sum_le _ _
          _ ≤ ∑ i, 3 * (v i).natAbs := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [Int.natAbs_mul]
              have hci : (c i).natAbs ≤ 3 := by
                have := hcb i; omega
              exact Nat.mul_le_mul_right _ hci
          _ = 3 * ∑ i, (v i).natAbs := by rw [Finset.mul_sum]
      omega
    have hdvd : ¬ (Q : ℤ) ∣ (∑ i, c i * v i) := by
      intro hd
      apply hF
      refine Int.eq_zero_of_abs_lt_dvd hd ?_
      rw [Int.abs_eq_natAbs]
      exact_mod_cast habs
    rw [if_neg hdvd, mul_zero]

/-- Real form of the cubed mass, with the cube outside the product (as the
union engine consumes it). -/
theorem riesz_mass_cube_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : 3 * (∑ i, (v i).natAbs) < Q) (hdiss : ThreeDissoc v) :
    ∑ j ∈ Finset.range Q,
        (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (5 / 2) ^ m := by
  classical
  have h := riesz_mass_cube m v Q hQ0 hQ hdiss
  have hcs : ((∑ j ∈ Finset.range Q,
        (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q,
          ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3 := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_pow, Complex.ofReal_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hrs : (((Q : ℝ) * (5 / 2) ^ m : ℝ) : ℂ) = (Q : ℂ) * (5 / 2) ^ m := by
    push_cast
    ring
  exact Complex.ofReal_injective (hcs.trans (h.trans hrs.symm))

/-- Restriction preserves three-dissociativity. -/
theorem threeDissoc_succAbove {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ThreeDissoc v)
    (i : Fin (k + 1)) : ThreeDissoc (fun j => v (i.succAbove j)) := by
  intro c hc hsum
  let d : Fin (k + 1) → ℤ := i.insertNth 0 c
  have hd_same : d i = 0 := by simp only [d, Fin.insertNth_apply_same]
  have hd_succ : ∀ j', d (i.succAbove j') = c j' := fun j' => by
    simp only [d, Fin.insertNth_apply_succAbove]
  have hmem : ∀ w, -3 ≤ d w ∧ d w ≤ 3 := by
    intro w
    refine Fin.succAboveCases i ?_ (fun j' => ?_) w
    · rw [hd_same]; omega
    · rw [hd_succ]; exact hc j'
  have hsum' : (∑ w, d w * v w) = 0 := by
    rw [Fin.sum_univ_succAbove _ i, hd_same, zero_mul, zero_add]
    simp only [hd_succ]; exact hsum
  have hz := hv d hmem hsum'
  funext j'
  have hzz := congrFun hz (i.succAbove j')
  rw [hd_succ] at hzz
  simpa using hzz

set_option maxHeartbeats 1000000 in
/-- **The four-runner floor for three-dissociated families** — the wall theorem.
The cubed mass is `Q·(5/2)^4`, the subfamily cubed masses are `Q·(5/2)^3`, and
the crude union condition reads `4·(1−cos 2π/5)³ < 5/2`, i.e. `1.32 < 2.5`,
using `cos(2π/5) = (√5−1)/4`. -/
theorem riesz_clears_floor_threediss_four (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i)
    (hdiss : ThreeDissoc v) : 1 / 5 ≤ ML v := by
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hM := riesz_mass_cube_real 4 v Q hQ0 hQ hdiss
  have hMsub : ∀ i : Fin 4, ∑ j ∈ Finset.range Q,
      (∏ j' : Fin 3,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (5 / 2) ^ 3 := by
    intro i
    refine riesz_mass_cube_real 3 (fun j' => v (i.succAbove j')) Q hQ0 ?_
      (threeDissoc_succAbove v hdiss i)
    have hle : (∑ j' : Fin 3, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
      rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
      exact Nat.le_add_left _ _
    show 3 * (∑ j' : Fin 3, (v (i.succAbove j')).natAbs) < Q
    omega
  refine riesz_crude_union_cube (k := 3) v Q hQ0 (1 / 5) (by norm_num) (by norm_num)
    ((Q : ℝ) * (5 / 2) ^ 4) ((Q : ℝ) * (5 / 2) ^ 3) hM hMsub ?_
  -- the numeric condition: 4·(1−cos(2π/5))³·(5/2)³ < (5/2)⁴
  have hcos : Real.cos (2 * π * (1 / 5)) = (Real.sqrt 5 - 1) / 4 := by
    have h5 := Real.cos_pi_div_five
    have hdbl : Real.cos (2 * (π / 5)) = 2 * Real.cos (π / 5) ^ 2 - 1 :=
      Real.cos_two_mul _
    rw [show 2 * π * (1 / 5 : ℝ) = 2 * (π / 5) by ring, hdbl, h5]
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  rw [hcos]
  have hs5lo : (2.2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hs5hi : Real.sqrt 5 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hu07 : (1 : ℝ) - (Real.sqrt 5 - 1) / 4 < 0.7 := by nlinarith [hs5lo]
  have hu0 : (0 : ℝ) ≤ 1 - (Real.sqrt 5 - 1) / 4 := by nlinarith [hs5hi]
  have hu3 : ((1 : ℝ) - (Real.sqrt 5 - 1) / 4) ^ 3 < 0.343 := by
    calc ((1 : ℝ) - (Real.sqrt 5 - 1) / 4) ^ 3 < (0.7 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hu07 hu0 (by norm_num)
      _ = 0.343 := by norm_num
  nlinarith [hu3, hQR, hu0]

/-- **The four-runner deep residual**: strongly free positive `4`-families
carrying a `[-3,3]`-coefficient relation.  Everything else at four runners is
now machine-checked. -/
def FourDeepResidual : Prop :=
  ∀ v : Fin 4 → ℤ, (∀ i, 0 < v i) → StrongFree v → ¬ ThreeDissoc v →
    1 / (5 : ℝ) ≤ ML v

/-- The degree-three floor collapses the four-runner window to its deep residual. -/
theorem windowFour_of_deep (h : FourDeepResidual) : WindowFour := by
  intro v hv hSF
  by_cases hd : ThreeDissoc v
  · exact riesz_clears_floor_threediss_four v hv hd
  · exact h v hv hSF hd

/-- **Separation from the four-runner deep residual and the dense-torsion
residual**: the free side of the all-`N` program after the degree-three floor. -/
theorem separationSF_of_deepFour_and_dense (h1 : FourDeepResidual)
    (h2 : DenseTorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_four_and_dense (windowFour_of_deep h1) h2


/-! ### The four-runner single-relation floor -/

/-- Real form of the cubed weight. -/
noncomputable def cubeWtR (a : ℤ) : ℝ :=
  if a = 0 then 5 / 2 else if a = 1 ∨ a = -1 then -15 / 8
  else if a = 2 ∨ a = -2 then 3 / 4 else -1 / 8

theorem cubeWt_eq_ofReal (a : ℤ) : cubeWt a = ((cubeWtR a : ℝ) : ℂ) := by
  unfold cubeWt cubeWtR
  split_ifs <;> norm_num

/-- The integer octuple weight `8·cubeWt`, on absolute values. -/
def w8 (n : ℕ) : ℤ :=
  if n = 0 then 20 else if n = 1 then -15 else if n = 2 then 6 else -1

theorem cubeWtR_w8 (a : ℤ) : cubeWtR a = (w8 a.natAbs : ℝ) / 8 := by
  unfold cubeWtR w8
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos (by omega : a.natAbs = 0)]; norm_num
  · rw [if_neg h0, if_neg (by omega : ¬ a.natAbs = 0)]
    by_cases h1 : a = 1 ∨ a = -1
    · rw [if_pos h1, if_pos (by omega : a.natAbs = 1)]; norm_num
    · rw [if_neg h1, if_neg (by omega : ¬ a.natAbs = 1)]
      by_cases h2 : a = 2 ∨ a = -2
      · rw [if_pos h2, if_pos (by omega : a.natAbs = 2)]; norm_num
      · rw [if_neg h2, if_neg (by omega : ¬ a.natAbs = 2)]; norm_num

theorem cubeWtR_neg (a : ℤ) : cubeWtR (-a) = cubeWtR a := by
  rw [cubeWtR_w8, cubeWtR_w8, Int.natAbs_neg]

theorem cubeWtR_zero : cubeWtR 0 = 5 / 2 := by norm_num [cubeWtR]

/-- **The general cubed mass**: for any family on the grid `Q > 3∑|v|`, the cubed
Riesz product's mass is `Q` times the `cubeWt`-weight of its vanishing
`[-3,3]`-combinations. -/
theorem riesz_mass_cube_general (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : 3 * (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3
      = (Q : ℂ) * ∑ c ∈ (Fintype.piFinset
          (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, cubeWt (c i) := by
  classical
  rw [riesz_mass_cube_expand m v Q hQ0]
  have habs : ∀ c ∈ Fintype.piFinset (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)),
      (Q : ℤ) ∣ (∑ i, c i * v i) → (∑ i, c i * v i) = 0 := by
    intro c hc hdvd
    have hcb : ∀ i, -3 ≤ c i ∧ c i ≤ 3 := by
      intro i
      have := (Fintype.mem_piFinset.mp hc) i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h | h | h | h <;> omega
    have hb : (∑ i, c i * v i).natAbs ≤ 3 * ∑ i, (v i).natAbs := by
      calc (∑ i, c i * v i).natAbs ≤ ∑ i, (c i * v i).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ i, 3 * (v i).natAbs := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Int.natAbs_mul]
            have hci : (c i).natAbs ≤ 3 := by have := hcb i; omega
            exact Nat.mul_le_mul_right _ hci
        _ = 3 * ∑ i, (v i).natAbs := by rw [Finset.mul_sum]
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_le_of_lt hb hQ
  rw [Finset.sum_filter]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hz : (∑ i, c i * v i) = 0
  · rw [if_pos (by rw [hz]; exact dvd_zero _), if_pos hz]
    ring
  · rw [if_neg hz]
    by_cases hdvd : (Q : ℤ) ∣ (∑ i, c i * v i)
    · exact absurd (habs c hc hdvd) hz
    · rw [if_neg hdvd]
      ring

/-- Real form of the general cubed mass. -/
theorem riesz_mass_cube_general_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : 3 * (∑ i, (v i).natAbs) < Q) :
    ∑ j ∈ Finset.range Q,
        (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ∑ c ∈ (Fintype.piFinset
          (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, cubeWtR (c i) := by
  classical
  have h := riesz_mass_cube_general m v Q hQ0 hQ
  have hcs : ((∑ j ∈ Finset.range Q,
        (∏ i : Fin m, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q,
          ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) ^ 3 := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_pow, Complex.ofReal_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hrs : (((Q : ℝ) * ∑ c ∈ (Fintype.piFinset
          (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, cubeWtR (c i) : ℝ) : ℂ)
      = (Q : ℂ) * ∑ c ∈ (Fintype.piFinset
          (fun _ : Fin m => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ i, c i * v i) = 0),
          ∏ i, cubeWt (c i) := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    refine congrArg _ (Finset.sum_congr rfl (fun c _ => ?_))
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun i _ => (cubeWt_eq_ofReal (c i)).symm)
  exact Complex.ofReal_injective (hcs.trans (h.trans hrs.symm))

set_option maxHeartbeats 800000 in
/-- **The crude degree-three union with per-runner subfamily masses.** -/
theorem riesz_crude_union_cube' {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℝ) (Msub : Fin (k + 1) → ℝ)
    (hM : ∑ j ∈ Finset.range Q,
        (∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 = M)
    (hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
        (∏ j' : Fin k, (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
        = Msub i)
    (hcond : (1 - Real.cos (2 * π * δ)) ^ 3 * (∑ i, Msub i) < M) :
    δ ≤ ML v := by
  set R3 : ℕ → ℝ := fun j : ℕ =>
    (∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 with hR3def
  have hR3nn : ∀ j, 0 ≤ R3 j := fun j => by
    rw [hR3def]
    exact pow_nonneg (Finset.prod_nonneg fun i _ => by
      have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith) 3
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
        ≤ (1 - Real.cos (2 * π * δ)) ^ 3 * Msub i := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    set S3 : ℕ → ℝ := fun j : ℕ =>
      (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3 with hS3def
    have hS3nn : ∀ j, 0 ≤ S3 j := fun j => by
      rw [hS3def]
      exact pow_nonneg (Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith) 3
    have hR3split : ∀ j : ℕ, R3 j
        = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 3 * S3 j := fun j => by
      simp only [hR3def, hS3def]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i, mul_pow]
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
        = ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 3 * S3 j :=
          Finset.sum_congr rfl (fun j _ => hR3split j)
      _ ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 - Real.cos (2 * π * δ)) ^ 3 * S3 j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          refine mul_le_mul_of_nonneg_right ?_ (hS3nn j)
          have hle : (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              ≤ 1 - Real.cos (2 * π * δ) := by
            rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
                = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
            have hcosle : Real.cos (2 * π * δ)
                ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
              Real.cos_le_cos_of_nonneg_of_le_pi
                (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
                (by nlinarith [Real.pi_pos, hδ2])
                (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
            linarith
          have hnn : 0 ≤ 1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
            have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
          exact pow_le_pow_left₀ hnn hle 3
      _ = (1 - Real.cos (2 * π * δ)) ^ 3 * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), S3 j :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - Real.cos (2 * π * δ)) ^ 3 * Msub i := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hcosδ 3)
          rw [← hMsub i]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hS3nn j)
  have hgood : ∃ j ∈ Finset.range Q, ∀ i, δ ≤ nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hcover : ∑ j ∈ Finset.range Q, R3 j
        ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j := by
      have hrw : (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j)
          = ∑ j ∈ Finset.range Q, ∑ i : Fin (k + 1),
              (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
        simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      rw [hrw]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨i, hi⟩ := hcon j hj
      calc R3 j = (if nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
              rw [if_pos hi]
        _ ≤ ∑ i' : Fin (k + 1),
              (if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R3 j else 0) := by
            refine Finset.single_le_sum
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ
                then R3 j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hR3nn j
            · exact le_refl 0
    have hchain : M ≤ (1 - Real.cos (2 * π * δ)) ^ 3 * (∑ i, Msub i) := by
      rw [← hM]
      calc ∑ j ∈ Finset.range Q, R3 j
          ≤ ∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R3 j := hcover
        _ ≤ ∑ i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) ^ 3 * Msub i :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = (1 - Real.cos (2 * π * δ)) ^ 3 * (∑ i, Msub i) := by
            rw [← Finset.mul_sum]
    linarith [hchain, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The 240-case integer core of the single-relation four-runner floor. -/
theorem four_single_decide :
    ∀ b : Fin 4 → Fin 4, (∃ i, 2 ≤ (b i : ℕ)) →
      (0 < 160000 + 2 * ∏ i, w8 (b i : ℕ)) ∧
      (2744 * (32000 + ∑ i, (if b i = 0
          then 2 * ∏ j' : Fin 3, w8 ((b (i.succAbove j')) : ℕ) else 0))
        < 1000 * (160000 + 2 * ∏ i, w8 (b i : ℕ))) := by
  decide

set_option maxHeartbeats 3000000 in
/-- **The single-relation four-runner floor.**  A positive 4-family whose only
vanishing `[-3,3]`-combinations are `0, ±d` — with `d` carrying a coefficient of
size at least two — meets the floor `1/5`.  The cubed mass is
`Q((5/2)⁴ + 2∏cubeWt(dᵢ))`, the subfamily masses carry the restricted
correction exactly when `dᵢ = 0`, and the union condition reduces to a
240-case integer check on the absolute-value profile of `d`. -/
theorem riesz_clears_floor_four_single (v : Fin 4 → ℤ)
    (d : Fin 4 → ℤ) (hd3 : ∀ i, -3 ≤ d i ∧ d i ≤ 3) (hd0 : d ≠ 0)
    (hdrel : (∑ i, d i * v i) = 0) (hd2 : ∃ i, 2 ≤ (d i).natAbs)
    (hsingle : ∀ c : Fin 4 → ℤ, (∀ i, -3 ≤ c i ∧ c i ≤ 3) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c = d ∨ c = -d) :
    1 / 5 ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the full-family filter and mass
  have hd_memb : ∀ i, d i ∈ ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by
    intro i
    have := hd3 i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hnd_ne0 : (-d) ≠ (0 : Fin 4 → ℤ) := fun h => hd0 (neg_eq_zero.mp h)
  have hd_ne_nd : d ≠ -d := by
    intro h
    apply hd0
    funext i
    have := congrFun h i
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]
    omega
  have hfilter : (Fintype.piFinset
      (fun _ : Fin 4 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ i, c i * v i) = 0) = {0, d, -d} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ i, -3 ≤ c i ∧ c i ≤ 3 := by
        intro i
        have := (Fintype.mem_piFinset.mp hcm) i
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h | h | h | h | h <;> omega
      exact hsingle c hcb hcv
    · rintro (rfl | rfl | rfl)
      · refine ⟨?_, Finset.sum_eq_zero fun i _ => by simp⟩
        rw [Fintype.mem_piFinset]
        intro i
        simp
      · refine ⟨?_, hdrel⟩
        rw [Fintype.mem_piFinset]
        intro i
        exact hd_memb i
      · refine ⟨?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          intro i
          have := hd3 i
          simp only [Pi.neg_apply, Finset.mem_insert, Finset.mem_singleton]
          omega
        · have hneg : (∑ i, (-d) i * v i) = -(∑ i, d i * v i) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun i _ => by simp
          rw [hneg, hdrel, neg_zero]
  have hzero_wt : (∏ i : Fin 4, cubeWtR ((0 : Fin 4 → ℤ) i)) = (5 / 2 : ℝ) ^ 4 := by
    have h1 : ∀ i : Fin 4, cubeWtR ((0 : Fin 4 → ℤ) i) = 5 / 2 := fun i => by
      norm_num [cubeWtR]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hneg_wt : (∏ i : Fin 4, cubeWtR ((-d) i)) = ∏ i : Fin 4, cubeWtR (d i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, cubeWtR_neg]
  have hsum3 : (∑ c ∈ ({0, d, -d} : Finset (Fin 4 → ℤ)), ∏ i, cubeWtR (c i))
      = (5 / 2 : ℝ) ^ 4 + 2 * ∏ i, cubeWtR (d i) := by
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hd0 h.symm, fun h => hnd_ne0 h.symm⟩),
      Finset.sum_insert (by simpa using hd_ne_nd), Finset.sum_singleton,
      hzero_wt, hneg_wt]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ i : Fin 4, (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5 / 2 : ℝ) ^ 4 + 2 * ∏ i, cubeWtR (d i)) := by
    have h := riesz_mass_cube_general_real 4 v Q hQ0 hQ
    rw [hfilter, hsum3] at h
    exact h
  -- subfamily filters and masses
  have hsubQ : ∀ i : Fin 4, 3 * (∑ j' : Fin 3, (v (i.succAbove j')).natAbs) < Q := by
    intro i
    have hle : (∑ j' : Fin 3, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
      rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
      exact Nat.le_add_left _ _
    omega
  have hfsub_ne : ∀ i : Fin 4, d i ≠ 0 →
      (Fintype.piFinset (fun _ : Fin 3 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
        (fun c => (∑ j', c j' * v (i.succAbove j')) = 0) = {0} := by
    intro i hdi
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcm) j'
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h | h | h | h | h <;> omega
      set e : Fin 4 → ℤ := i.insertNth 0 c with he
      have he_same : e i = 0 := by simp only [he, Fin.insertNth_apply_same]
      have he_succ : ∀ j', e (i.succAbove j') = c j' := fun j' => by
        simp only [he, Fin.insertNth_apply_succAbove]
      have heb : ∀ w, -3 ≤ e w ∧ e w ≤ 3 := by
        intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [he_same]; omega
        · rw [he_succ]; exact hcb j'
      have hev : (∑ w, e w * v w) = 0 := by
        rw [Fin.sum_univ_succAbove (fun w => e w * v w) i, he_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [he_succ]]
        exact hcv
      rcases hsingle e heb hev with h | h | h
      · funext j'
        have := congrFun h (i.succAbove j')
        rw [he_succ] at this
        simpa using this
      · exfalso
        have := congrFun h i
        rw [he_same] at this
        exact hdi this.symm
      · exfalso
        have := congrFun h i
        rw [he_same] at this
        simp only [Pi.neg_apply] at this
        omega
    · rintro rfl
      refine ⟨?_, Finset.sum_eq_zero fun j' _ => by simp⟩
      rw [Fintype.mem_piFinset]
      intro j'
      simp
  have hfsub_eq : ∀ i : Fin 4, d i = 0 →
      (Fintype.piFinset (fun _ : Fin 3 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
        (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
      = {0, fun j' => d (i.succAbove j'), fun j' => -d (i.succAbove j')} := by
    intro i hdi
    have hdsub_ne : (fun j' => d (i.succAbove j')) ≠ (0 : Fin 3 → ℤ) := by
      intro h
      apply hd0
      funext w
      refine Fin.succAboveCases i ?_ (fun j' => ?_) w
      · exact hdi
      · have := congrFun h j'
        simpa using this
    have hvansub : (∑ j', d (i.succAbove j') * v (i.succAbove j')) = 0 := by
      have h := hdrel
      rw [Fin.sum_univ_succAbove (fun w => d w * v w) i, hdi, zero_mul, zero_add] at h
      exact h
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
        intro j'
        have := (Fintype.mem_piFinset.mp hcm) j'
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h | h | h | h | h <;> omega
      set e : Fin 4 → ℤ := i.insertNth 0 c with he
      have he_same : e i = 0 := by simp only [he, Fin.insertNth_apply_same]
      have he_succ : ∀ j', e (i.succAbove j') = c j' := fun j' => by
        simp only [he, Fin.insertNth_apply_succAbove]
      have heb : ∀ w, -3 ≤ e w ∧ e w ≤ 3 := by
        intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [he_same]; omega
        · rw [he_succ]; exact hcb j'
      have hev : (∑ w, e w * v w) = 0 := by
        rw [Fin.sum_univ_succAbove (fun w => e w * v w) i, he_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [he_succ]]
        exact hcv
      rcases hsingle e heb hev with h | h | h
      · left
        funext j'
        have := congrFun h (i.succAbove j')
        rw [he_succ] at this
        simpa using this
      · right; left
        funext j'
        have := congrFun h (i.succAbove j')
        rw [he_succ] at this
        exact this
      · right; right
        funext j'
        have := congrFun h (i.succAbove j')
        rw [he_succ] at this
        simpa using this
    · rintro (rfl | rfl | rfl)
      · refine ⟨?_, Finset.sum_eq_zero fun j' _ => by simp⟩
        rw [Fintype.mem_piFinset]
        intro j'
        simp
      · refine ⟨?_, hvansub⟩
        rw [Fintype.mem_piFinset]
        intro j'
        exact hd_memb _
      · refine ⟨?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          intro j'
          have := hd3 (i.succAbove j')
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · rw [show (∑ j', -d (i.succAbove j') * v (i.succAbove j'))
              = -(∑ j', d (i.succAbove j') * v (i.succAbove j')) from by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j' _ => by ring]
          rw [hvansub, neg_zero]
  -- subfamily masses
  have hMsub : ∀ i : Fin 4, ∑ j ∈ Finset.range Q,
      (∏ j' : Fin 3,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5 / 2 : ℝ) ^ 3
          + (if d i = 0 then 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) else 0)) := by
    intro i
    have h := riesz_mass_cube_general_real 3 (fun j' => v (i.succAbove j')) Q hQ0 (hsubQ i)
    have hzero3 : (∏ j' : Fin 3, cubeWtR ((0 : Fin 3 → ℤ) j')) = (5 / 2 : ℝ) ^ 3 := by
      have h1 : ∀ j' : Fin 3, cubeWtR ((0 : Fin 3 → ℤ) j') = 5 / 2 := fun j' => by
        norm_num [cubeWtR]
      rw [Finset.prod_congr rfl (fun j' _ => h1 j'), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    by_cases hdi : d i = 0
    · rw [hfsub_eq i hdi] at h
      have hdsub_ne : (fun j' => d (i.succAbove j')) ≠ (0 : Fin 3 → ℤ) := by
        intro hcon
        apply hd0
        funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hdi
        · have := congrFun hcon j'
          simpa using this
      have hndsub_ne : (fun j' => -d (i.succAbove j')) ≠ (0 : Fin 3 → ℤ) := by
        intro hcon
        apply hdsub_ne
        funext j'
        have := congrFun hcon j'
        simp only [Pi.zero_apply] at this ⊢
        omega
      have hd_nd : (fun j' => d (i.succAbove j')) ≠ (fun j' => -d (i.succAbove j')) := by
        intro hcon
        apply hdsub_ne
        funext j'
        have := congrFun hcon j'
        simp only [Pi.zero_apply]
        omega
      have hsum3' : (∑ c ∈ ({0, fun j' => d (i.succAbove j'),
            fun j' => -d (i.succAbove j')} : Finset (Fin 3 → ℤ)), ∏ j', cubeWtR (c j'))
          = (5 / 2 : ℝ) ^ 3 + 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun hcon => hdsub_ne hcon.symm, fun hcon => hndsub_ne hcon.symm⟩),
          Finset.sum_insert (by simpa using hd_nd), Finset.sum_singleton, hzero3]
        have hnegp : (∏ j' : Fin 3, cubeWtR (-d (i.succAbove j')))
            = ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) := by
          exact Finset.prod_congr rfl fun j' _ => cubeWtR_neg _
        rw [hnegp]
        ring
      rw [hsum3'] at h
      rw [if_pos hdi]
      exact h
    · rw [hfsub_ne i hdi, Finset.sum_singleton, hzero3] at h
      rw [if_neg hdi]
      rw [show ((5 : ℝ) / 2) ^ 3 + 0 = ((5 : ℝ) / 2) ^ 3 by ring]
      exact h
  -- assemble via the per-runner crude union
  refine riesz_crude_union_cube' (k := 3) v Q hQ0 (1 / 5) (by norm_num) (by norm_num)
    ((Q : ℝ) * ((5 / 2 : ℝ) ^ 4 + 2 * ∏ i, cubeWtR (d i)))
    (fun i => (Q : ℝ) * ((5 / 2 : ℝ) ^ 3
      + (if d i = 0 then 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) else 0)))
    hM hMsub ?_
  -- the numeric condition via the integer decide
  set b : Fin 4 → Fin 4 := fun i => ⟨(d i).natAbs, by have := hd3 i; omega⟩ with hb
  have hbnat : ∀ i, (b i : ℕ) = (d i).natAbs := fun i => by simp [hb]
  have hdec := four_single_decide b ⟨hd2.choose, by
    have := hd2.choose_spec
    simpa [hb] using this⟩
  -- bridge the real weights to the integer profile
  have hp4 : (∏ i, cubeWtR (d i)) = ((∏ i, w8 (b i : ℕ) : ℤ) : ℝ) / 4096 := by
    rw [Finset.prod_congr rfl (fun i _ => cubeWtR_w8 (d i))]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [hbnat]
    push_cast
    norm_num
  have hp3 : ∀ i : Fin 4, (∏ j' : Fin 3, cubeWtR (d (i.succAbove j')))
      = ((∏ j' : Fin 3, w8 (b (i.succAbove j') : ℕ) : ℤ) : ℝ) / 512 := by
    intro i
    rw [Finset.prod_congr rfl (fun j' _ => cubeWtR_w8 (d (i.succAbove j')))]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [hbnat]
    push_cast
    norm_num
  -- per-runner bridge of the correction term to the integer profile
  have hei : ∀ i : Fin 4,
      (if d i = 0 then 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) else 0)
      = (((if b i = 0 then 2 * ∏ j' : Fin 3, w8 (b (i.succAbove j') : ℕ) else 0) : ℤ) : ℝ)
          / 512 := by
    intro i
    by_cases hdi : d i = 0
    · rw [if_pos hdi, if_pos (Fin.ext (by simp [hb, hdi]))]
      rw [hp3 i]
      push_cast
      ring
    · rw [if_neg hdi, if_neg (fun hcon => hdi (Int.natAbs_eq_zero.mp
        (by simpa [hb] using congrArg Fin.val hcon)))]
      norm_num
  -- the integer quantities
  set AZ : ℤ := 160000 + 2 * ∏ i, w8 (b i : ℕ) with hAZ
  set BZ : ℤ := 32000 + ∑ i : Fin 4, (if b i = 0
      then 2 * ∏ j' : Fin 3, w8 (b (i.succAbove j') : ℕ) else 0) with hBZ
  obtain ⟨hAZpos, hZlt⟩ := hdec
  -- the real bridges
  have hA : ((5 / 2 : ℝ) ^ 4 + 2 * ∏ i, cubeWtR (d i)) = ((AZ : ℤ) : ℝ) / 4096 := by
    rw [hp4, hAZ]
    push_cast
    ring
  have hsum4 : (∑ i : Fin 4, ((Q : ℝ) * ((5 / 2 : ℝ) ^ 3
      + (if d i = 0 then 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) else 0))))
      = (Q : ℝ) * (((BZ : ℤ) : ℝ) / 512) := by
    rw [← Finset.mul_sum]
    congr 1
    have hper : ∀ i : Fin 4, (5 / 2 : ℝ) ^ 3
        + (if d i = 0 then 2 * ∏ j' : Fin 3, cubeWtR (d (i.succAbove j')) else 0)
        = (((8000 + (if b i = 0 then 2 * ∏ j' : Fin 3, w8 (b (i.succAbove j') : ℕ)
            else 0)) : ℤ) : ℝ) / 512 := by
      intro i
      rw [hei i]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun i _ => hper i), ← Finset.sum_div, ← Int.cast_sum]
    have hZsum : (∑ i : Fin 4, ((8000 : ℤ) + (if b i = 0
        then 2 * ∏ j' : Fin 3, w8 (b (i.succAbove j') : ℕ) else 0))) = BZ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hBZ, nsmul_eq_mul]
      norm_num
    rw [hZsum]
  -- the golden-cosine bounds
  have hcos : Real.cos (2 * π * (1 / 5)) = (Real.sqrt 5 - 1) / 4 := by
    have h5 := Real.cos_pi_div_five
    have hdbl : Real.cos (2 * (π / 5)) = 2 * Real.cos (π / 5) ^ 2 - 1 :=
      Real.cos_two_mul _
    rw [show 2 * π * (1 / 5 : ℝ) = 2 * (π / 5) by ring, hdbl, h5]
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  have hs5lo : (2.2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hs5hi : Real.sqrt 5 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hu_pos : 0 < 1 - Real.cos (2 * π * (1 / 5)) := by
    rw [hcos]
    nlinarith [hs5hi]
  have hu07 : 1 - Real.cos (2 * π * (1 / 5)) < 0.7 := by
    rw [hcos]
    nlinarith [hs5lo]
  have hu3 : (1 - Real.cos (2 * π * (1 / 5))) ^ 3 < 343 / 1000 := by
    calc (1 - Real.cos (2 * π * (1 / 5))) ^ 3 < (0.7 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hu07 hu_pos.le (by norm_num)
      _ = 343 / 1000 := by norm_num
  -- close
  rw [hsum4, hA]
  by_cases hB0 : 0 ≤ BZ
  · have hXBnn : (0 : ℝ) ≤ ((BZ : ℤ) : ℝ) / 512 :=
      div_nonneg (by exact_mod_cast hB0) (by norm_num)
    have h1 : (1 - Real.cos (2 * π * (1 / 5))) ^ 3 * (((BZ : ℤ) : ℝ) / 512)
        ≤ (343 / 1000) * (((BZ : ℤ) : ℝ) / 512) :=
      mul_le_mul_of_nonneg_right hu3.le hXBnn
    have hcast : (2744 : ℝ) * ((BZ : ℤ) : ℝ) < 1000 * ((AZ : ℤ) : ℝ) := by
      exact_mod_cast hZlt
    have h2 : (343 / 1000 : ℝ) * (((BZ : ℤ) : ℝ) / 512) < ((AZ : ℤ) : ℝ) / 4096 := by
      linarith
    have hcore : (1 - Real.cos (2 * π * (1 / 5))) ^ 3 * (((BZ : ℤ) : ℝ) / 512)
        < ((AZ : ℤ) : ℝ) / 4096 := lt_of_le_of_lt h1 h2
    nlinarith [mul_lt_mul_of_pos_left hcore hQR]
  · push_neg at hB0
    have hXBneg : ((BZ : ℤ) : ℝ) / 512 < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hB0) (by norm_num)
    have hXApos : (0 : ℝ) < ((AZ : ℤ) : ℝ) / 4096 :=
      div_pos (by exact_mod_cast hAZpos) (by norm_num)
    have hcore : (1 - Real.cos (2 * π * (1 / 5))) ^ 3 * (((BZ : ℤ) : ℝ) / 512)
        < ((AZ : ℤ) : ℝ) / 4096 :=
      lt_trans (mul_neg_of_pos_of_neg (pow_pos hu_pos 3) hXBneg) hXApos
    nlinarith [mul_lt_mul_of_pos_left hcore hQR]

/-- **The four-runner multi-relation residual**: strongly free positive
`4`-families with a `[-3,3]`-relation but NO single dominating one — at least
two essentially independent bounded relations. -/
def FourMultiResidual : Prop :=
  ∀ v : Fin 4 → ℤ, (∀ i, 0 < v i) → StrongFree v → ¬ ThreeDissoc v →
    (¬ ∃ d : Fin 4 → ℤ, (∀ i, -3 ≤ d i ∧ d i ≤ 3) ∧ d ≠ 0 ∧ (∑ i, d i * v i) = 0 ∧
        (∀ c : Fin 4 → ℤ, (∀ i, -3 ≤ c i ∧ c i ≤ 3) → (∑ i, c i * v i) = 0 →
          c = 0 ∨ c = d ∨ c = -d)) →
    1 / (5 : ℝ) ≤ ML v

/-- The single-relation floor collapses the four-runner deep residual to its
multi-relation core. -/
theorem fourDeep_of_multi (h : FourMultiResidual) : FourDeepResidual := by
  intro v hv hSF hnd
  by_cases hex : ∃ d : Fin 4 → ℤ, (∀ i, -3 ≤ d i ∧ d i ≤ 3) ∧ d ≠ 0 ∧
      (∑ i, d i * v i) = 0 ∧
      (∀ c : Fin 4 → ℤ, (∀ i, -3 ≤ c i ∧ c i ≤ 3) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c = d ∨ c = -d)
  · obtain ⟨d, hd3, hd0, hdrel, hsingle⟩ := hex
    have hd2 : ∃ i, 2 ≤ (d i).natAbs := by
      by_contra hno
      push_neg at hno
      have hmem : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1 := by
        intro i
        have := hno i
        omega
      have hz := hSF d hmem hdrel
      exact hd0 (funext fun i => hz i)
    exact riesz_clears_floor_four_single v d hd3 hd0 hdrel hd2 hsingle
  · exact h v hv hSF hnd hex

/-- **Separation from the four-runner multi-relation residual and the
dense-torsion residual**: the free side after the single-relation floor. -/
theorem separationSF_of_multiFour_and_dense (h1 : FourMultiResidual)
    (h2 : DenseTorsionResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_deepFour_and_dense (fourDeep_of_multi h1) h2

#print axioms four_single_decide
#print axioms riesz_clears_floor_four_single
#print axioms separationSF_of_multiFour_and_dense



set_option maxHeartbeats 1000000 in
/-- **The uniform three-dissociated floor**: for EVERY size `m = k+1 ≥ 4`, a
three-dissociated positive family meets its floor `1/(k+2)`.  The crude cube
union needs `(k+1)·(1−cos 2πδ)³ < 5/2`, and the quadratic bound
`1−cos x < x²/2` gives `(k+1)·8π⁶/(k+2)⁶ ≤ 8π⁶/(k+2)⁵ ≤ 8π⁶/3125 < 5/2`. -/
theorem riesz_clears_floor_threediss {k : ℕ} (hk : 3 ≤ k) (v : Fin (k + 1) → ℤ)
    (hdiss : ThreeDissoc v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ5 : δ ≤ 1 / 5 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hM := riesz_mass_cube_real (k + 1) v Q hQ0 hQ hdiss
  have hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (5 / 2) ^ k := by
    intro i
    refine riesz_mass_cube_real k (fun j' => v (i.succAbove j')) Q hQ0 ?_
      (threeDissoc_succAbove v hdiss i)
    have hle : (∑ j' : Fin k, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
      rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
      exact Nat.le_add_left _ _
    show 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q
    omega
  refine riesz_crude_union_cube (k := k) v Q hQ0 δ hδ0 hδ2
    ((Q : ℝ) * (5 / 2) ^ (k + 1)) ((Q : ℝ) * (5 / 2) ^ k) hM hMsub ?_
  -- (k+1)·u³ < 5/2 via the quadratic cosine bound
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  have hδ6k : ((k : ℝ) + 1) * δ ^ 6 ≤ δ ^ 5 := by
    have h1 : ((k : ℝ) + 1) * δ ^ 6 ≤ ((k : ℝ) + 2) * δ ^ 6 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : ((k : ℝ) + 2) * δ ^ 6 = δ ^ 5 := by
      have h3 : ((k : ℝ) + 2) * δ ^ 6 = δ ^ 5 * (δ * ((k : ℝ) + 2)) := by ring
      rw [h3, hδval, mul_one]
    linarith
  have hδ55 : δ ^ 5 ≤ 1 / 3125 := by
    calc δ ^ 5 ≤ (1 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ hδ0.le hδ5 5
      _ = 1 / 3125 := by norm_num
  have hcore : ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3 < 5 / 2 := by
    have h1 : ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3
        < ((k : ℝ) + 1) * (2 * (π * δ) ^ 2) ^ 3 := by
      refine mul_lt_mul_of_pos_left hu3 (by linarith)
    have h2 : ((k : ℝ) + 1) * (2 * (π * δ) ^ 2) ^ 3 = 8 * π ^ 6 * (((k : ℝ) + 1) * δ ^ 6) := by
      ring
    have h3 : 8 * π ^ 6 * (((k : ℝ) + 1) * δ ^ 6) ≤ 8 * π ^ 6 * δ ^ 5 :=
      mul_le_mul_of_nonneg_left hδ6k (by positivity)
    have h4 : 8 * π ^ 6 * δ ^ 5 ≤ 8 * π ^ 6 * (1 / 3125) :=
      mul_le_mul_of_nonneg_left hδ55 (by positivity)
    have h5 : 8 * π ^ 6 * (1 / 3125 : ℝ) < 5 / 2 := by nlinarith [hπ6, Real.pi_pos]
    calc ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3
        < ((k : ℝ) + 1) * (2 * (π * δ) ^ 2) ^ 3 := h1
      _ = 8 * π ^ 6 * (((k : ℝ) + 1) * δ ^ 6) := h2
      _ ≤ 8 * π ^ 6 * δ ^ 5 := h3
      _ ≤ 8 * π ^ 6 * (1 / 3125) := h4
      _ < 5 / 2 := h5
  have hpow : (0 : ℝ) < (Q : ℝ) * (5 / 2) ^ k := by positivity
  calc ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) ^ 3 * ((Q : ℝ) * (5 / 2) ^ k)
      < (5 / 2) * ((Q : ℝ) * (5 / 2) ^ k) := by
        exact mul_lt_mul_of_pos_right hcore hpow
    _ = (Q : ℝ) * (5 / 2) ^ (k + 1) := by ring

/-- **The window relation residual**: strongly free positive families of
`5`–`8` runners carrying a `[-3,3]`-coefficient relation.  Everything
three-dissociated in the window is now machine-checked. -/
def WindowRelationResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ThreeDissoc v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- The uniform three-dissociated floor collapses the dense-torsion residual to
the bounded-relation shard. -/
theorem denseTorsion_of_relation (h : WindowRelationResidual) : DenseTorsionResidual := by
  intro k hk4 hk7 v hv hSF _ _ _
  by_cases hd : ThreeDissoc v
  · exact riesz_clears_floor_threediss (by omega) v hd
  · exact h k hk4 hk7 v hv hSF hd

/-- **Separation from the two bounded-relation residuals**: after this session,
the free side of the all-`N` program is exactly (a) four-runner families with
two independent `[-3,3]`-relations, and (b) `5`–`8`-runner families with a
`[-3,3]`-relation. -/
theorem separationSF_of_multiFour_and_relation (h1 : FourMultiResidual)
    (h2 : WindowRelationResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_multiFour_and_dense h1 (denseTorsion_of_relation h2)

#print axioms riesz_clears_floor_threediss
#print axioms separationSF_of_multiFour_and_relation



set_option maxHeartbeats 3000000 in
/-- **The SumStep wall falls: the five-runner support-three single-relation
floor.**  A positive family of five runners with one `±1`-relation of support
three — whose only vanishing `[-3,3]`-combinations are the multiples
`0, ±r, ±2r, ±3r` — meets the floor `1/6`.  The degree-one mass here is exactly
`3Q/4` with vanishing union margin (the wall); the cube mass is
`Q·(105/32)·(5/2)²` and the crude cube union passes at `u = 1/2` exactly:
`4275/256 < 2625/128`. -/
theorem bridge_cube_single_four (v : Fin 5 → ℤ) (r : Fin 5 → ℤ)
    (hr : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hsupp : (Finset.univ.filter (fun w => r w ≠ 0)).card = 3)
    (hcube : ∀ c : Fin 5 → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = (fun w => 2 * r w) ∨ c = (fun w => -(2 * r w))
          ∨ c = (fun w => 3 * r w) ∨ c = (fun w => -(3 * r w))) :
    1 / 6 ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- support facts
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [show (Finset.univ.filter (fun w => r w ≠ 0)) = ∅ from by
      simp [Finset.filter_eq_empty_iff, h0]] at hsupp
    simp at hsupp
  -- the weight products over multiples of r
  have hwt_eval : ∀ (a : ℝ) (lam : ℤ), (∀ w, cubeWtR (lam * r w) = if r w = 0 then 5/2 else a) →
      (∏ w : Fin 5, cubeWtR (lam * r w)) = a ^ 3 * (5/2 : ℝ) ^ 2 := by
    intro a lam hval
    rw [Finset.prod_congr rfl (fun w _ => hval w)]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hcard2 : (Finset.univ.filter (fun w => r w = 0)).card = 2 := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin 5))) (p := fun w => r w = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have hswap : (Finset.univ.filter (fun w => ¬ r w = 0)).card = 3 := hsupp
      omega
    rw [hcard2, hsupp]
    ring
  have hP1 : (∏ w : Fin 5, cubeWtR (1 * r w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ 2 := by
    refine hwt_eval _ 1 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP2 : (∏ w : Fin 5, cubeWtR (2 * r w)) = (3/4 : ℝ) ^ 3 * (5/2) ^ 2 := by
    refine hwt_eval _ 2 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP3 : (∏ w : Fin 5, cubeWtR (3 * r w)) = (-1/8 : ℝ) ^ 3 * (5/2) ^ 2 := by
    refine hwt_eval _ 3 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  -- multiples are pairwise distinct and bounded
  obtain ⟨w₀, hw₀⟩ : ∃ w, r w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr_ne (funext h)
  have hrb : ∀ (lam : ℤ), (1 ≤ lam) → (lam ≤ 3) → ∀ w, -3 ≤ lam * r w ∧ lam * r w ≤ 3 := by
    intro lam h1 h3 w
    rcases hr w with h | h | h <;> rw [h] <;> constructor <;> nlinarith
  have hne_mult : ∀ (a b : ℤ), a ≠ b → (fun w => a * r w) ≠ (fun w => b * r w) := by
    intro a b hab hcon
    have := congrFun hcon w₀
    simp only at this
    rcases hr w₀ with h | h | h
    · rw [h] at this; omega
    · exact hw₀ h
    · rw [h] at this; omega
  -- the full-family filter is the seven multiples
  have hfilter : (Fintype.piFinset
      (fun _ : Fin 5 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0)
      = {0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
         fun w => 3 * r w, fun w => -(3 * r w)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      rcases hcube c hcb hcv with h|h|h|h|h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right; left
        exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · right; right; right; right; left
        rw [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · right; right; right; right; right; right
        rw [h]
    · intro hmem
      have hbox : ∀ (d : Fin 5 → ℤ), (∀ w, -3 ≤ d w ∧ d w ≤ 3) →
          d ∈ Fintype.piFinset (fun _ : Fin 5 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
        intro d hd
        rw [Fintype.mem_piFinset]
        intro w
        have := hd w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hvan : ∀ (lam : ℤ), (∑ w, (lam * r w) * v w) = 0 := by
        intro lam
        have h1 : (∑ w, (lam * r w) * v w) = lam * ∑ w, r w * v w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hrel, mul_zero]
      rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · refine ⟨hbox _ (fun w => by rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        exact hrel
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        have h1 : (∑ w, (-r) w * v w) = -(∑ w, r w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
      · exact ⟨hbox _ (hrb 2 (by norm_num) (by norm_num)), hvan 2⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 2 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(2 * r w)) * v w) = -(∑ w, (2 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 2, neg_zero]
      · exact ⟨hbox _ (hrb 3 (by norm_num) (by norm_num)), hvan 3⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 3 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(3 * r w)) * v w) = -(∑ w, (3 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 3, neg_zero]
  -- pairwise distinctness of the seven multiples (via the support witness)
  have hρ : r w₀ = -1 ∨ r w₀ = 1 := by
    rcases hr w₀ with h | h | h
    · exact Or.inl h
    · exact absurd h hw₀
    · exact Or.inr h
  have hval_ne : ∀ (f g : Fin 5 → ℤ), f w₀ ≠ g w₀ → f ≠ g :=
    fun f g h hc => h (congrFun hc w₀)
  -- the seven-element sum
  have hsum7 : (∑ c ∈ ({0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
        fun w => 3 * r w, fun w => -(3 * r w)} : Finset (Fin 5 → ℤ)),
        ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ 5 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ 2)
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ 2) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ 2) := by
    have e0 : (∏ w : Fin 5, cubeWtR ((0 : Fin 5 → ℤ) w)) = (5/2 : ℝ) ^ 5 := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin 5 → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 : (∏ w : Fin 5, cubeWtR (r w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ 2 := by
      have := hP1
      simp only [one_mul] at this
      exact this
    have e1n : (∏ w : Fin 5, cubeWtR ((-r) w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ 2 := by
      rw [Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])]
      exact e1
    have e2 : (∏ w : Fin 5, cubeWtR ((fun w => 2 * r w) w)) = (3/4 : ℝ) ^ 3 * (5/2) ^ 2 := hP2
    have e2n : (∏ w : Fin 5, cubeWtR ((fun w => -(2 * r w)) w))
        = (3/4 : ℝ) ^ 3 * (5/2) ^ 2 := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP2
    have e3 : (∏ w : Fin 5, cubeWtR ((fun w => 3 * r w) w)) = (-1/8 : ℝ) ^ 3 * (5/2) ^ 2 := hP3
    have e3n : (∏ w : Fin 5, cubeWtR ((fun w => -(3 * r w)) w))
        = (-1/8 : ℝ) ^ 3 * (5/2) ^ 2 := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP3
    -- distinctness facts at w₀
    have d01 : (0 : Fin 5 → ℤ) ≠ r := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d02 : (0 : Fin 5 → ℤ) ≠ -r := hval_ne _ _ (by
      simp only [Pi.zero_apply, Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d03 : (0 : Fin 5 → ℤ) ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d04 : (0 : Fin 5 → ℤ) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d05 : (0 : Fin 5 → ℤ) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d06 : (0 : Fin 5 → ℤ) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d12 : r ≠ -r := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d13 : r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d14 : r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d15 : r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d16 : r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d23 : -r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d24 : -r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d25 : -r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d26 : -r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d34 : (fun w => 2 * r w) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d35 : (fun w => 2 * r w) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d36 : (fun w => 2 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d45 : (fun w => -(2 * r w)) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d46 : (fun w => -(2 * r w)) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d56 : (fun w => 3 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d01, d02, d03, d04, d05, d06⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14, d15, d16⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24, d25, d26⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d34, d35, d36⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d45, d46⟩),
      Finset.sum_insert (by simpa using d56), Finset.sum_singleton,
      e0, e1, e1n, e2, e2n, e3, e3n]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ w : Fin 5, (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ 5 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ 2)
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ 2) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ 2)) := by
    have h := riesz_mass_cube_general_real 5 v Q hQ0 hQ
    rw [hfilter, hsum7] at h
    exact h
  -- subfamily filters: {0} when the dropped runner carries the relation,
  -- the seven restricted multiples otherwise
  have hcard0 : (Finset.univ.filter (fun w : Fin 5 => r w = 0)).card = 2 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 5))) (p := fun w => r w = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have hswap : (Finset.univ.filter (fun w : Fin 5 => ¬ r w = 0)).card = 3 := hsupp
    omega
  have hMsub : ∀ i : Fin 5, ∑ j ∈ Finset.range Q,
      (∏ j' : Fin 4,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (if r i = 0
          then (5/2 : ℝ) ^ 4 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2))
            + 2 * ((3/4 : ℝ) ^ 3 * (5/2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2))
          else (5/2 : ℝ) ^ 4) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin 4, (v (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j' : Fin 4, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        exact Nat.le_add_left _ _
      omega
    have h := riesz_mass_cube_general_real 4 (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    -- lift a sub-combination to the full family
    have hlift : ∀ c : Fin 4 → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        ((i.insertNth 0 c : Fin 5 → ℤ) = 0 ∨ (i.insertNth 0 c : Fin 5 → ℤ) = r
          ∨ (i.insertNth 0 c : Fin 5 → ℤ) = -r
          ∨ (i.insertNth 0 c : Fin 5 → ℤ) = (fun w => 2 * r w)
          ∨ (i.insertNth 0 c : Fin 5 → ℤ) = (fun w => -(2 * r w))
          ∨ (i.insertNth 0 c : Fin 5 → ℤ) = (fun w => 3 * r w)
          ∨ (i.insertNth 0 c : Fin 5 → ℤ) = (fun w => -(3 * r w))) := by
      intro c hcb hcv
      refine hcube (i.insertNth 0 c) ?_ ?_
      · intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [Fin.insertNth_apply_same]; omega
        · rw [Fin.insertNth_apply_succAbove]; exact hcb j'
      · rw [Fin.sum_univ_succAbove (fun w => (i.insertNth 0 c : Fin 5 → ℤ) w * v w) i,
          Fin.insertNth_apply_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [Fin.insertNth_apply_succAbove]]
        exact hcv
    by_cases hri : r i = 0
    · -- the relation survives: seven restricted multiples
      rw [if_pos hri]
      have hw₀i : w₀ ≠ i := fun h => hw₀ (h ▸ hri)
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hρ' : r (i.succAbove j₀) = -1 ∨ r (i.succAbove j₀) = 1 := by rw [hj₀]; exact hρ
      have hsupp' : (Finset.univ.filter (fun j' : Fin 4 => r (i.succAbove j') ≠ 0)).card = 3 := by
        have hbij : (Finset.univ.filter (fun j' : Fin 4 => r (i.succAbove j') ≠ 0)).card
            = (Finset.univ.filter (fun w : Fin 5 => r w ≠ 0)).card := by
          refine Finset.card_bij (fun j' _ => i.succAbove j') ?_ ?_ ?_
          · intro j' hj'
            rw [Finset.mem_filter] at hj' ⊢
            exact ⟨Finset.mem_univ _, hj'.2⟩
          · intro a ha b hb hab
            exact Fin.succAbove_right_injective hab
          · intro w hw
            rw [Finset.mem_filter] at hw
            have hwi : w ≠ i := fun h => hw.2 (h ▸ hri)
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hwi
            exact ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj']; exact hw.2⟩, hj'⟩
        rw [hbij, hsupp]
      have hwt_eval' : ∀ (a : ℝ) (lam : ℤ),
          (∀ j', cubeWtR (lam * r (i.succAbove j')) = if r (i.succAbove j') = 0 then 5/2 else a) →
          (∏ j' : Fin 4, cubeWtR (lam * r (i.succAbove j'))) = a ^ 3 * (5/2 : ℝ) := by
        intro a lam hval
        rw [Finset.prod_congr rfl (fun j' _ => hval j')]
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have hz : (Finset.univ.filter (fun j' : Fin 4 => r (i.succAbove j') = 0)).card = 1 := by
          have := Finset.filter_card_add_filter_neg_card_eq_card
            (s := (Finset.univ : Finset (Fin 4))) (p := fun j' => r (i.succAbove j') = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at this
          have hswap : (Finset.univ.filter
              (fun j' : Fin 4 => ¬ r (i.succAbove j') = 0)).card = 3 := hsupp'
          omega
        rw [hz, hsupp']
        ring
      have hQ1 : (∏ j' : Fin 4, cubeWtR (1 * r (i.succAbove j')))
          = (-15/8 : ℝ) ^ 3 * (5/2) := by
        refine hwt_eval' _ 1 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ2 : (∏ j' : Fin 4, cubeWtR (2 * r (i.succAbove j')))
          = (3/4 : ℝ) ^ 3 * (5/2) := by
        refine hwt_eval' _ 2 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ3 : (∏ j' : Fin 4, cubeWtR (3 * r (i.succAbove j')))
          = (-1/8 : ℝ) ^ 3 * (5/2) := by
        refine hwt_eval' _ 3 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      -- the restricted filter
      set rr : Fin 4 → ℤ := fun j' => r (i.succAbove j') with hrr
      have hfsub : (Fintype.piFinset
          (fun _ : Fin 4 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
             fun j' => 3 * rr j', fun j' => -(3 * rr j')} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hres : ∀ (f : Fin 5 → ℤ), (i.insertNth 0 c : Fin 5 → ℤ) = f → f i = 0 →
              c = fun j' => f (i.succAbove j') := by
            intro f hf _
            funext j'
            have := congrFun hf (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            exact this
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · left
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · right; left
            rw [hres r h hri]
          · right; right; left
            have : c = fun j' => (-r) (i.succAbove j') := hres (-r) h (by simp [hri])
            rw [this]
            funext j'
            simp [hrr]
          · right; right; right; left
            have : c = fun j' => 2 * r (i.succAbove j') :=
              hres (fun w => 2 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; left
            have : c = fun j' => -(2 * r (i.succAbove j')) :=
              hres (fun w => -(2 * r w)) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; left
            have : c = fun j' => 3 * r (i.succAbove j') :=
              hres (fun w => 3 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; right
            have : c = fun j' => -(3 * r (i.succAbove j')) :=
              hres (fun w => -(3 * r w)) h (by simp [hri])
            rw [this]
        · intro hmem
          have hbox4 : ∀ (d : Fin 4 → ℤ), (∀ j', -3 ≤ d j' ∧ d j' ≤ 3) →
              d ∈ Fintype.piFinset (fun _ : Fin 4 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
            intro d hd
            rw [Fintype.mem_piFinset]
            intro j'
            have := hd j'
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
          have hvansub : ∀ (lam : ℤ), (∑ j', (lam * rr j') * v (i.succAbove j')) = 0 := by
            intro lam
            have h1 : (∑ j', (lam * rr j') * v (i.succAbove j'))
                = lam * ∑ j', rr j' * v (i.succAbove j') := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            have h2 : (∑ j', rr j' * v (i.succAbove j')) = 0 := by
              have := hrel
              rw [Fin.sum_univ_succAbove (fun w => r w * v w) i, hri, zero_mul, zero_add] at this
              exact this
            rw [h1, h2, mul_zero]
          have hrrb : ∀ (lam : ℤ), 1 ≤ lam → lam ≤ 3 → ∀ j', -3 ≤ lam * rr j' ∧ lam * rr j' ≤ 3 := by
            intro lam h1 h3 j'
            rcases hr (i.succAbove j') with h | h | h <;>
              simp only [hrr, h] <;> constructor <;> nlinarith
          rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact ⟨hbox4 _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · refine ⟨hbox4 _ (fun j' => by
              rcases hr (i.succAbove j') with h|h|h <;> simp only [hrr, h] <;> omega), ?_⟩
            have := hvansub 1
            simpa using this
          · refine ⟨hbox4 _ (fun j' => by
              simp only [Pi.neg_apply, hrr]
              rcases hr (i.succAbove j') with h|h|h <;> rw [h] <;> omega), ?_⟩
            have h1 : (∑ j', (-rr) j' * v (i.succAbove j'))
                = -(∑ j', (1 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by simp only [Pi.neg_apply]; ring)
            rw [h1, hvansub 1, neg_zero]
          · exact ⟨hbox4 _ (hrrb 2 (by norm_num) (by norm_num)), hvansub 2⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 2 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(2 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (2 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 2, neg_zero]
          · exact ⟨hbox4 _ (hrrb 3 (by norm_num) (by norm_num)), hvansub 3⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 3 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(3 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (3 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 3, neg_zero]
      -- evaluate the restricted seven-element sum
      have hρ4 : rr j₀ = -1 ∨ rr j₀ = 1 := by simp only [hrr, hj₀]; exact hρ
      have hval_ne4 : ∀ (f g : Fin 4 → ℤ), f j₀ ≠ g j₀ → f ≠ g :=
        fun f g hne hc => hne (congrFun hc j₀)
      have e0' : (∏ j' : Fin 4, cubeWtR ((0 : Fin 4 → ℤ) j')) = (5/2 : ℝ) ^ 4 := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin 4 → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have e1' : (∏ j' : Fin 4, cubeWtR (rr j')) = (-15/8 : ℝ) ^ 3 * (5/2) := by
        have := hQ1
        simp only [one_mul, hrr] at this ⊢
        exact this
      have e1n' : (∏ j' : Fin 4, cubeWtR ((-rr) j')) = (-15/8 : ℝ) ^ 3 * (5/2) := by
        rw [Finset.prod_congr rfl (fun j' _ => by rw [Pi.neg_apply, cubeWtR_neg])]
        exact e1'
      have e2' : (∏ j' : Fin 4, cubeWtR ((fun j' => 2 * rr j') j'))
          = (3/4 : ℝ) ^ 3 * (5/2) := by
        simp only [hrr]
        exact hQ2
      have e2n' : (∏ j' : Fin 4, cubeWtR ((fun j' => -(2 * rr j')) j'))
          = (3/4 : ℝ) ^ 3 * (5/2) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ2
      have e3' : (∏ j' : Fin 4, cubeWtR ((fun j' => 3 * rr j') j'))
          = (-1/8 : ℝ) ^ 3 * (5/2) := by
        simp only [hrr]
        exact hQ3
      have e3n' : (∏ j' : Fin 4, cubeWtR ((fun j' => -(3 * rr j')) j'))
          = (-1/8 : ℝ) ^ 3 * (5/2) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ3
      have hsum7' : (∑ c ∈ ({0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
            fun j' => 3 * rr j', fun j' => -(3 * rr j')} : Finset (Fin 4 → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ 4 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2))
            + 2 * ((3/4 : ℝ) ^ 3 * (5/2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2)) := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.zero_apply, Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            refine hval_ne4 _ _ ?_
            rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_singleton, e0', e1', e1n', e2', e2n', e3', e3n']
        ring
      rw [hfsub, hsum7'] at h
      exact h
    · -- the dropped runner carries the relation: only the trivial combination
      rw [if_neg hri]
      have hfsub0 : (Fintype.piFinset
          (fun _ : Fin 4 => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hz : ∀ (f : Fin 5 → ℤ), (i.insertNth 0 c : Fin 5 → ℤ) = f → f i ≠ 0 → False := by
            intro f hf hfi
            have := congrFun hf i
            rw [Fin.insertNth_apply_same] at this
            exact hfi this.symm
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · exact (hz r h hri).elim
          · exact (hz (-r) h (by simp [hri])).elim
          · exact (hz _ h (by simpa using mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by simpa using mul_ne_zero three_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero three_ne_zero hri)).elim
        · rintro rfl
          refine ⟨?_, Finset.sum_eq_zero (fun j' _ => by simp)⟩
          rw [Fintype.mem_piFinset]
          intro j'
          simp
      rw [hfsub0, Finset.sum_singleton] at h
      have hzero4 : (∏ j' : Fin 4, cubeWtR ((0 : Fin 4 → ℤ) j')) = (5/2 : ℝ) ^ 4 := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin 4 → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hzero4] at h
      exact h
  -- assemble via the per-runner crude union at δ = 1/6, u = 1/2 exactly
  refine riesz_crude_union_cube' (k := 4) v Q hQ0 (1 / 6) (by norm_num) (by norm_num)
    ((Q : ℝ) * ((5/2 : ℝ) ^ 5 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ 2)
      + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ 2) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ 2)))
    (fun i => (Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ 4 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2))
      else (5/2 : ℝ) ^ 4)) hM hMsub ?_
  have hcos3 : Real.cos (2 * π * (1 / 6)) = 1 / 2 := by
    rw [show 2 * π * (1 / 6 : ℝ) = π / 3 by ring]
    exact Real.cos_pi_div_three
  rw [hcos3]
  have hsum5 : (∑ i : Fin 5, ((Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ 4 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2))
      else (5/2 : ℝ) ^ 4)))
      = (Q : ℝ) * (2 * ((5/2 : ℝ) ^ 4 + 2 * ((-15/8 : ℝ) ^ 3 * (5/2))
          + 2 * ((3/4 : ℝ) ^ 3 * (5/2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2)))
        + 3 * (5/2 : ℝ) ^ 4) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard0, hsupp]
    push_cast
    ring
  rw [hsum5]
  have hQpos := hQR
  nlinarith [hQpos]


#print axioms bridge_cube_single_four


#print axioms riesz_mass_cube_real
#print axioms riesz_clears_floor_threediss_four
#print axioms separationSF_of_deepFour_and_dense


#print axioms riesz_mass_general
#print axioms riesz_mass_general_real

#print axioms riesz_mass_sq

-- axiom audit
#print axioms riesz_mass_expand_pub
#print axioms riesz_mass_disjoint
#print axioms riesz_mass_disjoint_real
#print axioms disjoint_subfamily_passive
#print axioms disjoint_subfamily_active
#print axioms bridge_disjoint_triples
#print axioms norm_one_sub_exp
#print axioms sum_range_mul_mod
#print axioms riesz_badset_expand_pub
#print axioms badset_reindex
#print axioms interval_exp_bound
#print axioms badset_fourier_bound
#print axioms not_dvd_mul_inv
#print axioms riesz_union_weights
#print axioms badset_weight_fourier
#print axioms badset_card_bound
#print axioms exists_coprime_modulus_ge
#print axioms exists_nat_inverse
#print axioms badset_filter_eq
#print axioms norm_one_sub_exp_nid
#print axioms afree_nid_lower
#print axioms riesz_clears_floor_afree
#print axioms badset_weight_split
#print axioms riesz_clears_floor_torsion_single
#print axioms separationSF_of_four_and_torsion
#print axioms separationSF_of_four_and_deep
#print axioms bridge_single_relation_fourier
#print axioms riesz_clears_floor_torsion_multi
#print axioms bridge_single_relation_fourier_wide
#print axioms separationSF_of_four_and_dense

set_option maxHeartbeats 3000000 in
/-- **The generic SumStep cell: the support-three single-relation floor for
every `k ≥ 5`.**  A positive family of `k+1` runners with one `±1`-relation of
support three — whose only vanishing `[-3,3]`-combinations are the multiples
`0, ±r, ±2r, ±3r` — meets the floor `1/(k+2)`.  The degree-one mass is exactly
`3Q/4` with vanishing union margin (the wall); the cube mass is
`Q·(105/32)·(5/2)^(k-2)` and the crude cube union closes via the quadratic
cosine bound: `u³·((k-2)(105/32) + 375/8) < 8π⁶δ⁶·(47/5)(k+2) = (376/5)π⁶δ⁵ ≤
75.2·961.51/16807 < 525/64` at `δ = 1/(k+2) ≤ 1/7`.  Together with the banked
`bridge_cube_single_four` (`k = 4`, exact at `u = 1/2`), the SumStep cells
`k = 5, 6` — and all larger `k` — are closed in one stroke. -/
theorem bridge_cube_single_supp3 {k : ℕ} (hk : 5 ≤ k)
    (v : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hr : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hsupp : (Finset.univ.filter (fun w => r w ≠ 0)).card = 3)
    (hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = (fun w => 2 * r w) ∨ c = (fun w => -(2 * r w))
          ∨ c = (fun w => 3 * r w) ∨ c = (fun w => -(3 * r w))) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- support facts
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [show (Finset.univ.filter (fun w => r w ≠ 0)) = ∅ from by
      simp [Finset.filter_eq_empty_iff, h0]] at hsupp
    simp at hsupp
  -- the weight products over multiples of r
  have hwt_eval : ∀ (a : ℝ) (lam : ℤ), (∀ w, cubeWtR (lam * r w) = if r w = 0 then 5/2 else a) →
      (∏ w : Fin (k + 1), cubeWtR (lam * r w)) = a ^ 3 * (5/2 : ℝ) ^ (k - 2) := by
    intro a lam hval
    rw [Finset.prod_congr rfl (fun w _ => hval w)]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hcard2 : (Finset.univ.filter (fun w => r w = 0)).card = k - 2 := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun w => r w = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have hswap : (Finset.univ.filter (fun w => ¬ r w = 0)).card = 3 := hsupp
      omega
    rw [hcard2, hsupp]
    ring
  have hP1 : (∏ w : Fin (k + 1), cubeWtR (1 * r w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
    refine hwt_eval _ 1 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP2 : (∏ w : Fin (k + 1), cubeWtR (2 * r w)) = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
    refine hwt_eval _ 2 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP3 : (∏ w : Fin (k + 1), cubeWtR (3 * r w)) = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
    refine hwt_eval _ 3 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  -- multiples are pairwise distinct and bounded
  obtain ⟨w₀, hw₀⟩ : ∃ w, r w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr_ne (funext h)
  have hrb : ∀ (lam : ℤ), (1 ≤ lam) → (lam ≤ 3) → ∀ w, -3 ≤ lam * r w ∧ lam * r w ≤ 3 := by
    intro lam h1 h3 w
    rcases hr w with h | h | h <;> rw [h] <;> constructor <;> nlinarith
  have hne_mult : ∀ (a b : ℤ), a ≠ b → (fun w => a * r w) ≠ (fun w => b * r w) := by
    intro a b hab hcon
    have := congrFun hcon w₀
    simp only at this
    rcases hr w₀ with h | h | h
    · rw [h] at this; omega
    · exact hw₀ h
    · rw [h] at this; omega
  -- the full-family filter is the seven multiples
  have hfilter : (Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0)
      = {0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
         fun w => 3 * r w, fun w => -(3 * r w)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      rcases hcube c hcb hcv with h|h|h|h|h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right; left
        exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · right; right; right; right; left
        rw [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · right; right; right; right; right; right
        rw [h]
    · intro hmem
      have hbox : ∀ (d : Fin (k + 1) → ℤ), (∀ w, -3 ≤ d w ∧ d w ≤ 3) →
          d ∈ Fintype.piFinset (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
        intro d hd
        rw [Fintype.mem_piFinset]
        intro w
        have := hd w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hvan : ∀ (lam : ℤ), (∑ w, (lam * r w) * v w) = 0 := by
        intro lam
        have h1 : (∑ w, (lam * r w) * v w) = lam * ∑ w, r w * v w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hrel, mul_zero]
      rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · refine ⟨hbox _ (fun w => by rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        exact hrel
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        have h1 : (∑ w, (-r) w * v w) = -(∑ w, r w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
      · exact ⟨hbox _ (hrb 2 (by norm_num) (by norm_num)), hvan 2⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 2 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(2 * r w)) * v w) = -(∑ w, (2 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 2, neg_zero]
      · exact ⟨hbox _ (hrb 3 (by norm_num) (by norm_num)), hvan 3⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 3 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(3 * r w)) * v w) = -(∑ w, (3 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 3, neg_zero]
  -- pairwise distinctness of the seven multiples (via the support witness)
  have hρ : r w₀ = -1 ∨ r w₀ = 1 := by
    rcases hr w₀ with h | h | h
    · exact Or.inl h
    · exact absurd h hw₀
    · exact Or.inr h
  have hval_ne : ∀ (f g : Fin (k + 1) → ℤ), f w₀ ≠ g w₀ → f ≠ g :=
    fun f g h hc => h (congrFun hc w₀)
  -- the seven-element sum
  have hsum7 : (∑ c ∈ ({0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
        fun w => 3 * r w, fun w => -(3 * r w)} : Finset (Fin (k + 1) → ℤ)),
        ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2)) := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 : (∏ w : Fin (k + 1), cubeWtR (r w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
      have := hP1
      simp only [one_mul] at this
      exact this
    have e1n : (∏ w : Fin (k + 1), cubeWtR ((-r) w)) = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
      rw [Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])]
      exact e1
    have e2 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 2 * r w) w)) = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2) := hP2
    have e2n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(2 * r w)) w))
        = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP2
    have e3 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 3 * r w) w)) = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := hP3
    have e3n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(3 * r w)) w))
        = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP3
    -- distinctness facts at w₀
    have d01 : (0 : Fin (k + 1) → ℤ) ≠ r := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d02 : (0 : Fin (k + 1) → ℤ) ≠ -r := hval_ne _ _ (by
      simp only [Pi.zero_apply, Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d03 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d04 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d05 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d06 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d12 : r ≠ -r := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d13 : r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d14 : r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d15 : r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d16 : r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d23 : -r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d24 : -r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d25 : -r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d26 : -r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d34 : (fun w => 2 * r w) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d35 : (fun w => 2 * r w) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d36 : (fun w => 2 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d45 : (fun w => -(2 * r w)) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d46 : (fun w => -(2 * r w)) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d56 : (fun w => 3 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d01, d02, d03, d04, d05, d06⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14, d15, d16⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24, d25, d26⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d34, d35, d36⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d45, d46⟩),
      Finset.sum_insert (by simpa using d56), Finset.sum_singleton,
      e0, e1, e1n, e2, e2n, e3, e3n]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))) := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum7] at h
    exact h
  -- subfamily filters: {0} when the dropped runner carries the relation,
  -- the seven restricted multiples otherwise
  have hcard0 : (Finset.univ.filter (fun w : Fin (k + 1) => r w = 0)).card = k - 2 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun w => r w = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have hswap : (Finset.univ.filter (fun w : Fin (k + 1) => ¬ r w = 0)).card = 3 := hsupp
    omega
  have hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (if r i = 0
          then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
            + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
          else (5/2 : ℝ) ^ k) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j' : Fin k, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        exact Nat.le_add_left _ _
      omega
    have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    -- lift a sub-combination to the full family
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        ((i.insertNth 0 c : Fin (k + 1) → ℤ) = 0 ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => 2 * r w)
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => -(2 * r w))
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => 3 * r w)
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => -(3 * r w))) := by
      intro c hcb hcv
      refine hcube (i.insertNth 0 c) ?_ ?_
      · intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [Fin.insertNth_apply_same]; omega
        · rw [Fin.insertNth_apply_succAbove]; exact hcb j'
      · rw [Fin.sum_univ_succAbove (fun w => (i.insertNth 0 c : Fin (k + 1) → ℤ) w * v w) i,
          Fin.insertNth_apply_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [Fin.insertNth_apply_succAbove]]
        exact hcv
    by_cases hri : r i = 0
    · -- the relation survives: seven restricted multiples
      rw [if_pos hri]
      have hw₀i : w₀ ≠ i := fun h => hw₀ (h ▸ hri)
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hρ' : r (i.succAbove j₀) = -1 ∨ r (i.succAbove j₀) = 1 := by rw [hj₀]; exact hρ
      have hsupp' : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') ≠ 0)).card = 3 := by
        have hbij : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') ≠ 0)).card
            = (Finset.univ.filter (fun w : Fin (k + 1) => r w ≠ 0)).card := by
          refine Finset.card_bij (fun j' _ => i.succAbove j') ?_ ?_ ?_
          · intro j' hj'
            rw [Finset.mem_filter] at hj' ⊢
            exact ⟨Finset.mem_univ _, hj'.2⟩
          · intro a ha b hb hab
            exact Fin.succAbove_right_injective hab
          · intro w hw
            rw [Finset.mem_filter] at hw
            have hwi : w ≠ i := fun h => hw.2 (h ▸ hri)
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hwi
            exact ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj']; exact hw.2⟩, hj'⟩
        rw [hbij, hsupp]
      have hwt_eval' : ∀ (a : ℝ) (lam : ℤ),
          (∀ j', cubeWtR (lam * r (i.succAbove j')) = if r (i.succAbove j') = 0 then 5/2 else a) →
          (∏ j' : Fin k, cubeWtR (lam * r (i.succAbove j'))) = a ^ 3 * (5/2 : ℝ) ^ (k - 3) := by
        intro a lam hval
        rw [Finset.prod_congr rfl (fun j' _ => hval j')]
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have hz : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') = 0)).card = k - 3 := by
          have := Finset.filter_card_add_filter_neg_card_eq_card
            (s := (Finset.univ : Finset (Fin k))) (p := fun j' => r (i.succAbove j') = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at this
          have hswap : (Finset.univ.filter
              (fun j' : Fin k => ¬ r (i.succAbove j') = 0)).card = 3 := hsupp'
          omega
        rw [hz, hsupp']
        ring
      have hQ1 : (∏ j' : Fin k, cubeWtR (1 * r (i.succAbove j')))
          = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        refine hwt_eval' _ 1 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ2 : (∏ j' : Fin k, cubeWtR (2 * r (i.succAbove j')))
          = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        refine hwt_eval' _ 2 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ3 : (∏ j' : Fin k, cubeWtR (3 * r (i.succAbove j')))
          = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        refine hwt_eval' _ 3 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      -- the restricted filter
      set rr : Fin k → ℤ := fun j' => r (i.succAbove j') with hrr
      have hfsub : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
             fun j' => 3 * rr j', fun j' => -(3 * rr j')} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hres : ∀ (f : Fin (k + 1) → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = f → f i = 0 →
              c = fun j' => f (i.succAbove j') := by
            intro f hf _
            funext j'
            have := congrFun hf (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            exact this
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · left
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · right; left
            rw [hres r h hri]
          · right; right; left
            have : c = fun j' => (-r) (i.succAbove j') := hres (-r) h (by simp [hri])
            rw [this]
            funext j'
            simp [hrr]
          · right; right; right; left
            have : c = fun j' => 2 * r (i.succAbove j') :=
              hres (fun w => 2 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; left
            have : c = fun j' => -(2 * r (i.succAbove j')) :=
              hres (fun w => -(2 * r w)) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; left
            have : c = fun j' => 3 * r (i.succAbove j') :=
              hres (fun w => 3 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; right
            have : c = fun j' => -(3 * r (i.succAbove j')) :=
              hres (fun w => -(3 * r w)) h (by simp [hri])
            rw [this]
        · intro hmem
          have hbox4 : ∀ (d : Fin k → ℤ), (∀ j', -3 ≤ d j' ∧ d j' ≤ 3) →
              d ∈ Fintype.piFinset (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
            intro d hd
            rw [Fintype.mem_piFinset]
            intro j'
            have := hd j'
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
          have hvansub : ∀ (lam : ℤ), (∑ j', (lam * rr j') * v (i.succAbove j')) = 0 := by
            intro lam
            have h1 : (∑ j', (lam * rr j') * v (i.succAbove j'))
                = lam * ∑ j', rr j' * v (i.succAbove j') := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            have h2 : (∑ j', rr j' * v (i.succAbove j')) = 0 := by
              have := hrel
              rw [Fin.sum_univ_succAbove (fun w => r w * v w) i, hri, zero_mul, zero_add] at this
              exact this
            rw [h1, h2, mul_zero]
          have hrrb : ∀ (lam : ℤ), 1 ≤ lam → lam ≤ 3 → ∀ j', -3 ≤ lam * rr j' ∧ lam * rr j' ≤ 3 := by
            intro lam h1 h3 j'
            rcases hr (i.succAbove j') with h | h | h <;>
              simp only [hrr, h] <;> constructor <;> nlinarith
          rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact ⟨hbox4 _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · refine ⟨hbox4 _ (fun j' => by
              rcases hr (i.succAbove j') with h|h|h <;> simp only [hrr, h] <;> omega), ?_⟩
            have := hvansub 1
            simpa using this
          · refine ⟨hbox4 _ (fun j' => by
              simp only [Pi.neg_apply, hrr]
              rcases hr (i.succAbove j') with h|h|h <;> rw [h] <;> omega), ?_⟩
            have h1 : (∑ j', (-rr) j' * v (i.succAbove j'))
                = -(∑ j', (1 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by simp only [Pi.neg_apply]; ring)
            rw [h1, hvansub 1, neg_zero]
          · exact ⟨hbox4 _ (hrrb 2 (by norm_num) (by norm_num)), hvansub 2⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 2 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(2 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (2 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 2, neg_zero]
          · exact ⟨hbox4 _ (hrrb 3 (by norm_num) (by norm_num)), hvansub 3⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 3 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(3 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (3 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 3, neg_zero]
      -- evaluate the restricted seven-element sum
      have hρ4 : rr j₀ = -1 ∨ rr j₀ = 1 := by simp only [hrr, hj₀]; exact hρ
      have hval_ne4 : ∀ (f g : Fin k → ℤ), f j₀ ≠ g j₀ → f ≠ g :=
        fun f g hne hc => hne (congrFun hc j₀)
      have e0' : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have e1' : (∏ j' : Fin k, cubeWtR (rr j')) = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        have := hQ1
        simp only [one_mul, hrr] at this ⊢
        exact this
      have e1n' : (∏ j' : Fin k, cubeWtR ((-rr) j')) = (-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        rw [Finset.prod_congr rfl (fun j' _ => by rw [Pi.neg_apply, cubeWtR_neg])]
        exact e1'
      have e2' : (∏ j' : Fin k, cubeWtR ((fun j' => 2 * rr j') j'))
          = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        simp only [hrr]
        exact hQ2
      have e2n' : (∏ j' : Fin k, cubeWtR ((fun j' => -(2 * rr j')) j'))
          = (3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ2
      have e3' : (∏ j' : Fin k, cubeWtR ((fun j' => 3 * rr j') j'))
          = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        simp only [hrr]
        exact hQ3
      have e3n' : (∏ j' : Fin k, cubeWtR ((fun j' => -(3 * rr j')) j'))
          = (-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ3
      have hsum7' : (∑ c ∈ ({0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
            fun j' => 3 * rr j', fun j' => -(3 * rr j')} : Finset (Fin k → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
            + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3)) := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.zero_apply, Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            refine hval_ne4 _ _ ?_
            rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_singleton, e0', e1', e1n', e2', e2n', e3', e3n']
        ring
      rw [hfsub, hsum7'] at h
      exact h
    · -- the dropped runner carries the relation: only the trivial combination
      rw [if_neg hri]
      have hfsub0 : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hz : ∀ (f : Fin (k + 1) → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = f → f i ≠ 0 → False := by
            intro f hf hfi
            have := congrFun hf i
            rw [Fin.insertNth_apply_same] at this
            exact hfi this.symm
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · exact (hz r h hri).elim
          · exact (hz (-r) h (by simp [hri])).elim
          · exact (hz _ h (by simpa using mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by simpa using mul_ne_zero three_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero three_ne_zero hri)).elim
        · rintro rfl
          refine ⟨?_, Finset.sum_eq_zero (fun j' _ => by simp)⟩
          rw [Fintype.mem_piFinset]
          intro j'
          simp
      rw [hfsub0, Finset.sum_singleton] at h
      have hzero4 : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hzero4] at h
      exact h
  -- assemble via the per-runner crude union at δ = 1/6, u = 1/2 exactly
  have hkR : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))
      + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))))
    (fun i => (Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
      else (5/2 : ℝ) ^ k)) hM hMsub ?_
  -- the union arithmetic: quadratic cosine bound, uniform in k ≥ 5
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ7 : δ ≤ 1 / 7 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  -- power factorizations off the common (5/2)^(k-3)
  have hfk : (5/2 : ℝ) ^ k = (5/2 : ℝ) ^ (k - 3) * (5/2 : ℝ) ^ 3 := by
    rw [← pow_add]; congr 1; omega
  have hfk1 : (5/2 : ℝ) ^ (k + 1) = (5/2 : ℝ) ^ (k - 3) * (5/2 : ℝ) ^ 4 := by
    rw [← pow_add]; congr 1; omega
  have hfk2 : (5/2 : ℝ) ^ (k - 2) = (5/2 : ℝ) ^ (k - 3) * (5/2 : ℝ) := by
    rw [← pow_succ]; congr 1; omega
  have hY0 : (0 : ℝ) < (5/2 : ℝ) ^ (k - 3) := by positivity
  -- collapse the masses onto the common factor
  have hA : (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
      + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
      = (105/32 : ℝ) * (5/2 : ℝ) ^ (k - 3) := by
    rw [hfk]; ring
  have hMval : (5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))
      + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 2)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 2))
      = (525/64 : ℝ) * (5/2 : ℝ) ^ (k - 3) := by
    rw [hfk1, hfk2]; ring
  -- the runner sum: k - 2 zero-runners carry the correction, 3 do not
  have hsum5 : (∑ i : Fin (k + 1), ((Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
        + 2 * ((3/4 : ℝ) ^ 3 * (5/2) ^ (k - 3)) + 2 * ((-1/8 : ℝ) ^ 3 * (5/2) ^ (k - 3))
      else (5/2 : ℝ) ^ k)))
      = (Q : ℝ) * (((k : ℝ) - 2) * ((105/32 : ℝ) * (5/2 : ℝ) ^ (k - 3))
          + 3 * ((5/2 : ℝ) ^ (k - 3) * (5/2 : ℝ) ^ 3)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard0, hsupp,
      nsmul_eq_mul, nsmul_eq_mul, hA, hfk]
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    push_cast
    ring
  rw [hsum5, hMval]
  -- the core inequality, then multiply back
  have hbr0 : (0 : ℝ) < ((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ) := by nlinarith [hkR]
  have hstep1 : ((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ) ≤ (47/5) * ((k : ℝ) + 2) := by
    nlinarith [hkR]
  have hstep2 : δ ^ 6 * ((k : ℝ) + 2) = δ ^ 5 := by
    have h1 : δ ^ 6 * ((k : ℝ) + 2) = δ ^ 5 * (δ * ((k : ℝ) + 2)) := by ring
    rw [h1, hδval, mul_one]
  have hstep3 : δ ^ 5 ≤ 1 / 16807 := by
    calc δ ^ 5 ≤ (1/7 : ℝ) ^ 5 := pow_le_pow_left₀ hδ0.le hδ7 5
      _ = 1 / 16807 := by norm_num
  have hcore : (1 - Real.cos (2 * π * δ)) ^ 3
      * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ)) < 525/64 := by
    have h1 : (1 - Real.cos (2 * π * δ)) ^ 3
        * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ))
        < (2 * (π * δ) ^ 2) ^ 3 * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ)) :=
      mul_lt_mul_of_pos_right hu3 hbr0
    have h2 : (2 * (π * δ) ^ 2) ^ 3 * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ))
        ≤ (2 * (π * δ) ^ 2) ^ 3 * ((47/5) * ((k : ℝ) + 2)) := by
      refine mul_le_mul_of_nonneg_left hstep1 (by positivity)
    have h3 : (2 * (π * δ) ^ 2) ^ 3 * ((47/5) * ((k : ℝ) + 2))
        = (8 * (47/5)) * π ^ 6 * (δ ^ 6 * ((k : ℝ) + 2)) := by ring
    have h4 : (8 * (47/5) : ℝ) * π ^ 6 * (δ ^ 6 * ((k : ℝ) + 2))
        = (8 * (47/5)) * π ^ 6 * δ ^ 5 := by rw [hstep2]
    have h5 : (8 * (47/5) : ℝ) * π ^ 6 * δ ^ 5 ≤ (8 * (47/5)) * π ^ 6 * (1 / 16807) := by
      refine mul_le_mul_of_nonneg_left hstep3 (by positivity)
    have h6 : (8 * (47/5) : ℝ) * π ^ 6 * (1 / 16807) < 525/64 := by
      nlinarith [hπ6, Real.pi_pos, pow_pos Real.pi_pos 6]
    calc (1 - Real.cos (2 * π * δ)) ^ 3
        * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ))
        < (2 * (π * δ) ^ 2) ^ 3 * (((k : ℝ) - 2) * (105/32 : ℝ) + 3 * (125/8 : ℝ)) := h1
      _ ≤ (2 * (π * δ) ^ 2) ^ 3 * ((47/5) * ((k : ℝ) + 2)) := h2
      _ = (8 * (47/5)) * π ^ 6 * (δ ^ 6 * ((k : ℝ) + 2)) := h3
      _ = (8 * (47/5)) * π ^ 6 * δ ^ 5 := h4
      _ ≤ (8 * (47/5)) * π ^ 6 * (1 / 16807) := h5
      _ < 525/64 := h6
  have hQY : (0 : ℝ) < (Q : ℝ) * (5/2 : ℝ) ^ (k - 3) := mul_pos hQR hY0
  nlinarith [mul_lt_mul_of_pos_right hcore hQY, hY0, hQR, hcosnn,
    pow_nonneg hcosnn 3]

#print axioms bridge_cube_single_supp3

set_option maxHeartbeats 3000000 in
/-- **The window single-relation floor, uniform in `k ≥ 4`.**  A positive family
of `k+1` runners carrying one `[-3,3]`-relation `d` with a deep entry
(`|d_w| ≥ 2`, the strongly-free signature) — whose only vanishing
`[-3,3]`-combinations are `0, ±d` — meets the floor `1/(k+2)`.  The deep entry
caps the relation's weight product at `(3/4)(15/8)(5/2)^{k-1}`, so the cube mass
is at least `(55/16)(5/2)^{k-1}·Q` while each subfamily carries at most
`(29/8)(5/2)^{k-1}·Q`; the crude cube union closes by the quadratic cosine
bound, `464·π⁶·(k+1) < 55·(k+2)⁶` for every `k ≥ 4`.  This discharges the
single-relation half of `WindowRelationResidual` — for the whole window
`5 ≤ m ≤ 8` at once, and every larger `m` besides. -/
theorem riesz_clears_floor_window_single {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (hpos : ∀ i, 0 < v i)
    (d : Fin (k + 1) → ℤ)
    (hd3 : ∀ w, -3 ≤ d w ∧ d w ≤ 3)
    (hdeep : ∃ w, d w ≤ -2 ∨ 2 ≤ d w)
    (hrel : (∑ w, d w * v w) = 0)
    (hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = d ∨ c = -d) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the deep entry and a second support point
  obtain ⟨i₀, hi₀⟩ := hdeep
  have hd_i₀ : d i₀ ≠ 0 := by omega
  have hsecond : ∃ j₀, j₀ ≠ i₀ ∧ d j₀ ≠ 0 := by
    by_contra h
    push_neg at h
    have hsum : (∑ w, d w * v w) = d i₀ * v i₀ :=
      Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)
        (fun b _ hb => by rw [h b hb, zero_mul])
    rw [hrel] at hsum
    exact (mul_ne_zero hd_i₀ (ne_of_gt (hpos i₀))) hsum.symm
  obtain ⟨j₀, hj₀ne, hj₀nz⟩ := hsecond
  -- weight magnitudes
  have habs_le : ∀ a : ℤ, |cubeWtR a| ≤ 5/2 := by
    intro a; unfold cubeWtR
    split_ifs <;> rw [abs_le] <;> constructor <;> norm_num
  have habs_ne : ∀ a : ℤ, a ≠ 0 → |cubeWtR a| ≤ 15/8 := by
    intro a ha; unfold cubeWtR
    rw [if_neg ha]
    split_ifs <;> rw [abs_le] <;> constructor <;> norm_num
  have habs_deep : ∀ a : ℤ, (a ≤ -2 ∨ 2 ≤ a) → |cubeWtR a| ≤ 3/4 := by
    intro a ha; unfold cubeWtR
    rw [if_neg (by omega), if_neg (by omega)]
    split_ifs <;> rw [abs_le] <;> constructor <;> norm_num
  -- the relation's weight product is capped by the deep entry
  have hWabs : |∏ w, cubeWtR (d w)| ≤ (45/32 : ℝ) * (5/2) ^ (k - 1) := by
    rw [Finset.abs_prod]
    have hmem_j₀ : j₀ ∈ Finset.univ.erase i₀ :=
      Finset.mem_erase.mpr ⟨hj₀ne, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase _ _ hmem_j₀]
    have hcard : ((Finset.univ.erase i₀).erase j₀).card = k - 1 := by
      rw [Finset.card_erase_of_mem hmem_j₀, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      omega
    have hrest : (∏ w ∈ (Finset.univ.erase i₀).erase j₀, |cubeWtR (d w)|)
        ≤ (5/2 : ℝ) ^ (k - 1) := by
      calc (∏ w ∈ (Finset.univ.erase i₀).erase j₀, |cubeWtR (d w)|)
          ≤ ∏ _w ∈ (Finset.univ.erase i₀).erase j₀, (5/2 : ℝ) :=
            Finset.prod_le_prod (fun w _ => abs_nonneg _) (fun w _ => habs_le (d w))
        _ = (5/2 : ℝ) ^ (k - 1) := by rw [Finset.prod_const, hcard]
    have hrest_nn : (0:ℝ) ≤ ∏ w ∈ (Finset.univ.erase i₀).erase j₀, |cubeWtR (d w)| :=
      Finset.prod_nonneg (fun w _ => abs_nonneg _)
    calc |cubeWtR (d i₀)| * (|cubeWtR (d j₀)|
          * ∏ w ∈ (Finset.univ.erase i₀).erase j₀, |cubeWtR (d w)|)
        ≤ (3/4 : ℝ) * ((15/8) * (5/2) ^ (k - 1)) := by
          refine mul_le_mul (habs_deep _ hi₀) ?_
            (mul_nonneg (abs_nonneg _) hrest_nn) (by norm_num)
          exact mul_le_mul (habs_ne _ hj₀nz) hrest hrest_nn (by norm_num)
      _ = (45/32 : ℝ) * (5/2) ^ (k - 1) := by ring
  -- the full-family filter is exactly {0, d, -d}
  have hfilter : (Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0) = {0, d, -d} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      exact hcube c hcb hcv
    · intro hmem
      have hbox : ∀ (e : Fin (k + 1) → ℤ), (∀ w, -3 ≤ e w ∧ e w ≤ 3) →
          e ∈ Fintype.piFinset (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
        intro e he
        rw [Fintype.mem_piFinset]
        intro w
        have := he w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rcases hmem with rfl|rfl|rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · exact ⟨hbox _ hd3, hrel⟩
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          have := hd3 w
          omega), ?_⟩
        have h1 : (∑ w, (-d) w * v w) = -(∑ w, d w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
  -- distinctness at the deep entry
  have hd_ne0 : (0 : Fin (k + 1) → ℤ) ≠ d := fun h => by
    have := congrFun h i₀
    simp only [Pi.zero_apply] at this
    omega
  have hd_ne0' : (0 : Fin (k + 1) → ℤ) ≠ -d := fun h => by
    have := congrFun h i₀
    simp only [Pi.zero_apply, Pi.neg_apply] at this
    omega
  have hd_nened : d ≠ -d := fun h => by
    have := congrFun h i₀
    simp only [Pi.neg_apply] at this
    omega
  -- the three-element mass
  have hsum3 : (∑ c ∈ ({0, d, -d} : Finset (Fin (k + 1) → ℤ)), ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ (k + 1) + 2 * ∏ w, cubeWtR (d w) := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have edn : (∏ w : Fin (k + 1), cubeWtR ((-d) w)) = ∏ w, cubeWtR (d w) :=
      Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hd_ne0, hd_ne0'⟩),
      Finset.sum_insert (by simpa using hd_nened), Finset.sum_singleton, e0, edn]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ∏ w, cubeWtR (d w)) := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum3] at h
    exact h
  -- subfamily masses: {0, ±d|sub} when the dropped runner misses the relation,
  -- {0} when it carries it
  have hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0)) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j' : Fin k, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        exact Nat.le_add_left _ _
      omega
    have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        ((i.insertNth 0 c : Fin (k + 1) → ℤ) = 0 ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = d
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -d) := by
      intro c hcb hcv
      refine hcube (i.insertNth 0 c) ?_ ?_
      · intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [Fin.insertNth_apply_same]; omega
        · rw [Fin.insertNth_apply_succAbove]; exact hcb j'
      · rw [Fin.sum_univ_succAbove (fun w => (i.insertNth 0 c : Fin (k + 1) → ℤ) w * v w) i,
          Fin.insertNth_apply_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [Fin.insertNth_apply_succAbove]]
        exact hcv
    have e0k : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
      rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
        ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hbox4 : ∀ (e : Fin k → ℤ), (∀ j', -3 ≤ e j' ∧ e j' ≤ 3) →
        e ∈ Fintype.piFinset (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
      intro e he
      rw [Fintype.mem_piFinset]
      intro j'
      have := he j'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    by_cases hdi : d i = 0
    · rw [if_pos hdi]
      have hi₀i : i₀ ≠ i := fun hcon => hd_i₀ (hcon ▸ hdi)
      obtain ⟨j₁, hj₁⟩ := Fin.exists_succAbove_eq hi₀i
      have hvansub : (∑ j', d (i.succAbove j') * v (i.succAbove j')) = 0 := by
        have hh := hrel
        rw [Fin.sum_univ_succAbove (fun w => d w * v w) i, hdi, zero_mul, zero_add] at hh
        exact hh
      have hfsub : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, fun j' => d (i.succAbove j'), fun j' => -(d (i.succAbove j'))} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h'|h'|h'|h'|h'|h'|h' <;> omega
          have hres : ∀ (f : Fin (k + 1) → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = f →
              c = fun j' => f (i.succAbove j') := by
            intro f hf
            funext j'
            have := congrFun hf (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            exact this
          rcases hlift c hcb hcv with h'|h'|h'
          · left
            funext j'
            have := congrFun h' (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · right; left
            rw [hres d h']
          · right; right
            have hcc : c = fun j' => (-d) (i.succAbove j') := hres (-d) h'
            rw [hcc]
            funext j'
            simp
        · intro hmem
          rcases hmem with rfl|rfl|rfl
          · exact ⟨hbox4 _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · exact ⟨hbox4 _ (fun j' => hd3 (i.succAbove j')), by simpa using hvansub⟩
          · refine ⟨hbox4 _ (fun j' => by
              show -3 ≤ -(d (i.succAbove j')) ∧ -(d (i.succAbove j')) ≤ 3
              have := hd3 (i.succAbove j')
              omega), ?_⟩
            have h1 : (∑ j', (fun j' => -(d (i.succAbove j'))) j' * v (i.succAbove j'))
                = -(∑ j', d (i.succAbove j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub, neg_zero]
      have hne1 : (0 : Fin k → ℤ) ≠ (fun j' => d (i.succAbove j')) := fun h' => by
        have := congrFun h' j₁
        simp only [Pi.zero_apply, hj₁] at this
        omega
      have hne2 : (0 : Fin k → ℤ) ≠ (fun j' => -(d (i.succAbove j'))) := fun h' => by
        have := congrFun h' j₁
        simp only [Pi.zero_apply, hj₁] at this
        omega
      have hne3 : (fun j' => d (i.succAbove j')) ≠ (fun j' => -(d (i.succAbove j'))) := fun h' => by
        have := congrFun h' j₁
        simp only [hj₁] at this
        omega
      have en : (∏ j' : Fin k, cubeWtR ((fun j' => -(d (i.succAbove j'))) j'))
          = ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) :=
        Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])
      have hsub3 : (∑ c ∈ ({0, fun j' => d (i.succAbove j'),
            fun j' => -(d (i.succAbove j'))} : Finset (Fin k → ℤ)), ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hne1, hne2⟩),
          Finset.sum_insert (by simpa using hne3), Finset.sum_singleton, e0k, en]
        ring
      rw [hfsub, hsub3] at h
      exact h
    · rw [if_neg hdi, add_zero]
      have hfsub : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h'|h'|h'|h'|h'|h'|h' <;> omega
          rcases hlift c hcb hcv with h'|h'|h'
          · funext j'
            have := congrFun h' (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · exfalso
            have := congrFun h' i
            rw [Fin.insertNth_apply_same] at this
            exact hdi this.symm
          · exfalso
            have := congrFun h' i
            rw [Fin.insertNth_apply_same] at this
            simp only [Pi.neg_apply] at this
            omega
        · rintro rfl
          exact ⟨hbox4 _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
      rw [hfsub, Finset.sum_singleton, e0k] at h
      exact h
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ∏ w, cubeWtR (d w)))
    (fun i => (Q : ℝ) * ((5/2 : ℝ) ^ k
      + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0)))
    hM hMsub ?_
  -- the union arithmetic: quadratic cosine bound, uniform in k ≥ 4
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  -- the uniform key inequality: 29·π⁶·(k+1) < (55/16)·(k+2)⁶
  have hδ61 : δ ^ 6 * ((k : ℝ) + 2) ^ 6 = 1 := by
    rw [← mul_pow, hδval, one_pow]
  have hkey : 29 * π ^ 6 * ((k : ℝ) + 1) < (55/16) * ((k : ℝ) + 2) ^ 6 := by
    have h64 : (1296 : ℝ) ≤ ((k : ℝ) + 2) ^ 4 := by
      calc (1296 : ℝ) = 6 ^ 4 := by norm_num
        _ ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h6b : 1296 * ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 6 := by
      have hsplit : ((k : ℝ) + 2) ^ 6 = ((k : ℝ) + 2) ^ 4 * ((k : ℝ) + 2) ^ 2 := by ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right h64 (by positivity)
    have hπk : π ^ 6 * ((k : ℝ) + 1) < 961.51 * ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hπ6 (by linarith)
    nlinarith [hπk, h6b, hkR,
      mul_le_mul_of_nonneg_left hkR (by linarith : (0 : ℝ) ≤ (k : ℝ))]
  have hbr0 : (0 : ℝ) < ((k : ℝ) + 1) * (29/8) := by positivity
  have hcore : (1 - Real.cos (2 * π * δ)) ^ 3 * (((k : ℝ) + 1) * (29/8)) < 55/16 := by
    calc (1 - Real.cos (2 * π * δ)) ^ 3 * (((k : ℝ) + 1) * (29/8))
        < (2 * (π * δ) ^ 2) ^ 3 * (((k : ℝ) + 1) * (29/8)) :=
          mul_lt_mul_of_pos_right hu3 hbr0
      _ = (29 * π ^ 6 * ((k : ℝ) + 1)) * δ ^ 6 := by ring
      _ < ((55/16) * ((k : ℝ) + 2) ^ 6) * δ ^ 6 :=
          mul_lt_mul_of_pos_right hkey (pow_pos hδ0 6)
      _ = (55/16) * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by ring
      _ = 55/16 := by rw [hδ61, mul_one]
  -- power splits off the common (5/2)^(k-1) and (5/2)^(k-2)
  have hp1 : (5/2 : ℝ) ^ k = (5/2 : ℝ) ^ (k - 1) * (5/2) := by
    rw [← pow_succ]
    congr 1
    omega
  have hp2 : (5/2 : ℝ) ^ (k - 1) = (5/2 : ℝ) ^ (k - 2) * (5/2) := by
    rw [← pow_succ]
    congr 1
    omega
  -- subfamily weight products inherit the cap
  have hWsub : ∀ i : Fin (k + 1), d i = 0 →
      |∏ j' : Fin k, cubeWtR (d (i.succAbove j'))| ≤ (45/32 : ℝ) * (5/2) ^ (k - 2) := by
    intro i hdi
    have hfac : (∏ w : Fin (k + 1), cubeWtR (d w))
        = cubeWtR (d i) * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) :=
      Fin.prod_univ_succAbove (fun w => cubeWtR (d w)) i
    rw [hdi, cubeWtR_zero] at hfac
    have h52 : |(∏ w : Fin (k + 1), cubeWtR (d w))|
        = (5/2 : ℝ) * |∏ j' : Fin k, cubeWtR (d (i.succAbove j'))| := by
      rw [hfac, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < (5/2 : ℝ))]
    have h := hWabs
    rw [h52, hp2] at h
    linarith
  have hMsub_le : ∀ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0))
      ≤ (Q : ℝ) * ((29/8 : ℝ) * (5/2) ^ (k - 1)) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
    by_cases hdi : d i = 0
    · rw [if_pos hdi]
      have h1 := (abs_le.mp (hWsub i hdi)).2
      rw [hp1, hp2]
      linarith
    · rw [if_neg hdi, add_zero, hp1]
      have hY : (0:ℝ) ≤ (5/2 : ℝ) ^ (k - 1) := by positivity
      linarith
  have hsumMsub : (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0)))
      ≤ ((k : ℝ) + 1) * ((Q : ℝ) * ((29/8 : ℝ) * (5/2) ^ (k - 1))) := by
    calc (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
          + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0)))
        ≤ ∑ _i : Fin (k + 1), (Q : ℝ) * ((29/8 : ℝ) * (5/2) ^ (k - 1)) :=
          Finset.sum_le_sum (fun i _ => hMsub_le i)
      _ = ((k : ℝ) + 1) * ((Q : ℝ) * ((29/8 : ℝ) * (5/2) ^ (k - 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hMlow : (Q : ℝ) * ((55/16 : ℝ) * (5/2 : ℝ) ^ (k - 1))
      ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ∏ w, cubeWtR (d w)) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
    have hW := (abs_le.mp hWabs).1
    have hp : (5/2 : ℝ) ^ (k + 1) = (5/2 : ℝ) ^ (k - 1) * (25/4) := by
      have h1 : (5/2 : ℝ) ^ (k + 1) = (5/2 : ℝ) ^ ((k - 1) + 2) := by
        congr 1
        omega
      rw [h1, pow_add]
      norm_num
    rw [hp]
    linarith
  calc (1 - Real.cos (2 * π * δ)) ^ 3 * (∑ i : Fin (k + 1), (Q : ℝ) * ((5/2 : ℝ) ^ k
        + (if d i = 0 then 2 * ∏ j' : Fin k, cubeWtR (d (i.succAbove j')) else 0)))
      ≤ (1 - Real.cos (2 * π * δ)) ^ 3
        * (((k : ℝ) + 1) * ((Q : ℝ) * ((29/8 : ℝ) * (5/2) ^ (k - 1)))) :=
        mul_le_mul_of_nonneg_left hsumMsub (pow_nonneg hcosnn 3)
    _ = ((1 - Real.cos (2 * π * δ)) ^ 3 * (((k : ℝ) + 1) * (29/8)))
        * ((Q : ℝ) * (5/2 : ℝ) ^ (k - 1)) := by ring
    _ < (55/16) * ((Q : ℝ) * (5/2 : ℝ) ^ (k - 1)) :=
        mul_lt_mul_of_pos_right hcore (by positivity)
    _ = (Q : ℝ) * ((55/16 : ℝ) * (5/2 : ℝ) ^ (k - 1)) := by ring
    _ ≤ (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ∏ w, cubeWtR (d w)) := hMlow

#print axioms riesz_clears_floor_window_single

/-- **The multi-relation window residual**: strongly free positive families of
`5`–`8` runners whose `[-3,3]`-vanishing set is richer than a single relation
pair `{0, ±d}`.  After `riesz_clears_floor_window_single`, this is all that
remains of the window relation residual. -/
def WindowMultiRelationResidual : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → ¬ ThreeDissoc v →
    ¬ (∃ d : Fin (k + 1) → ℤ, (∀ w, -3 ≤ d w ∧ d w ≤ 3) ∧ (∑ w, d w * v w) = 0 ∧
        (∃ w, d w ≤ -2 ∨ 2 ≤ d w) ∧
        ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          c = 0 ∨ c = d ∨ c = -d) →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- The single-relation floor collapses the window relation residual to the
multi-relation shard. -/
theorem windowRelation_of_multi (h : WindowMultiRelationResidual) :
    WindowRelationResidual := by
  intro k hk4 hk7 v hpos hSF hnTD
  by_cases hsingle : ∃ d : Fin (k + 1) → ℤ, (∀ w, -3 ≤ d w ∧ d w ≤ 3) ∧
      (∑ w, d w * v w) = 0 ∧ (∃ w, d w ≤ -2 ∨ 2 ≤ d w) ∧
      ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = d ∨ c = -d
  · obtain ⟨d, hd3, hrel, hdeep, hcube⟩ := hsingle
    exact riesz_clears_floor_window_single hk4 v hpos d hd3 hdeep hrel hcube
  · exact h k hk4 hk7 v hpos hSF hnTD hsingle

/-- **Separation from the two multi-relation residuals**: the free side of the
all-`N` program is now exactly (a) four-runner families with two independent
`[-3,3]`-relations and (b) `5`–`8`-runner families whose `[-3,3]`-vanishing
set is richer than one relation pair. -/
theorem separationSF_of_multiFour_and_windowMulti (h1 : FourMultiResidual)
    (h2 : WindowMultiRelationResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_multiFour_and_relation h1 (windowRelation_of_multi h2)

#print axioms windowRelation_of_multi
#print axioms separationSF_of_multiFour_and_windowMulti


/-- **The vanishing trichotomy**: every integer family is three-dissociated, or
its `[-3,3]`-vanishing set lies on a single integer line `ℤ·d`, or it carries
two vanishing combinations not on one line.  This is the machine-checked router
of the assembly: the first case meets the floor by
`riesz_clears_floor_threediss`, the second feeds the single-relation floors
(`riesz_clears_floor_window_single` when `d` has a deep entry, the cube-single
bridge theorems when `d` is `±1`-valued), and the third is exactly the
multi-relation residual class. -/
theorem vanishing_trichotomy {m : ℕ} (v : Fin m → ℤ) :
    ThreeDissoc v
    ∨ (∃ d : Fin m → ℤ, (∀ w, -3 ≤ d w ∧ d w ≤ 3) ∧ (∑ w, d w * v w) = 0 ∧ d ≠ 0 ∧
        ∀ c : Fin m → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
          ∃ lam : ℤ, c = fun w => lam * d w)
    ∨ (∃ d e : Fin m → ℤ, ((∀ w, -3 ≤ d w ∧ d w ≤ 3) ∧ (∑ w, d w * v w) = 0 ∧ d ≠ 0)
        ∧ (∀ w, -3 ≤ e w ∧ e w ≤ 3) ∧ (∑ w, e w * v w) = 0 ∧ e ≠ 0
        ∧ ∀ lam : ℤ, e ≠ fun w => lam * d w) := by
  classical
  by_cases hTD : ThreeDissoc v
  · exact Or.inl hTD
  · unfold ThreeDissoc at hTD
    push_neg at hTD
    obtain ⟨d, hd3', hdrel, hd0⟩ := hTD
    have hd3 : ∀ w, -3 ≤ d w ∧ d w ≤ 3 := hd3'
    by_cases hline : ∀ c : Fin m → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        ∃ lam : ℤ, c = fun w => lam * d w
    · exact Or.inr (Or.inl ⟨d, hd3, hdrel, hd0, hline⟩)
    · push_neg at hline
      obtain ⟨e, he3, herel, heline⟩ := hline
      have he0 : e ≠ 0 := by
        intro h0
        exact heline 0 (by
          funext w
          rw [h0]
          simp)
      exact Or.inr (Or.inr ⟨d, e, ⟨hd3, hdrel, hd0⟩, he3, herel, he0, heline⟩)

#print axioms vanishing_trichotomy

set_option maxHeartbeats 3000000 in
/-- **The support-generic cube-single bridge floor.**  A positive family of
`k+1` runners with one `±1`-relation of support `s ≥ 4` — whose only vanishing
`[-3,3]`-combinations are the seven multiples `0, ±r, ±2r, ±3r` — meets the
floor `1/(k+2)`, for every `k ≥ 4` at once.  The relation-mass factor
`C_s = (5/2)^s + 2(-15/8)^s + 2(3/4)^s + 2(-1/8)^s` obeys the uniform bound
`C_s ≥ (7/20)(5/2)^s` (from `2(3/4)^s + 2(1/20)^s ≤ 13/20`, no parity split),
so the union closes by `u³(k+1) < 7/8`, i.e. `64π⁶(k+1) < 7(k+2)⁶` — corner
margin `1.06×` at `k = 4`.  With the banked support-`3` theorems this closes
every single-line bridge cell exposed by `vanishing_trichotomy`. -/
theorem bridge_cube_single_general {k s : ℕ} (hk : 4 ≤ k) (hs : 4 ≤ s) (hsk : s ≤ k)
    (v : Fin (k + 1) → ℤ) (r : Fin (k + 1) → ℤ)
    (hr : ∀ w, r w = -1 ∨ r w = 0 ∨ r w = 1)
    (hrel : (∑ w, r w * v w) = 0)
    (hsupp : (Finset.univ.filter (fun w => r w ≠ 0)).card = s)
    (hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        c = 0 ∨ c = r ∨ c = -r ∨ c = (fun w => 2 * r w) ∨ c = (fun w => -(2 * r w))
          ∨ c = (fun w => 3 * r w) ∨ c = (fun w => -(3 * r w))) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set Q : ℕ := 3 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQ : 3 * (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- support facts
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [show (Finset.univ.filter (fun w => r w ≠ 0)) = ∅ from by
      simp [Finset.filter_eq_empty_iff, h0]] at hsupp
    simp only [Finset.card_empty] at hsupp
    omega
  -- the weight products over multiples of r
  have hwt_eval : ∀ (a : ℝ) (lam : ℤ), (∀ w, cubeWtR (lam * r w) = if r w = 0 then 5/2 else a) →
      (∏ w : Fin (k + 1), cubeWtR (lam * r w)) = a ^ s * (5/2 : ℝ) ^ (k + 1 - s) := by
    intro a lam hval
    rw [Finset.prod_congr rfl (fun w _ => hval w)]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hcard2 : (Finset.univ.filter (fun w => r w = 0)).card = k + 1 - s := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun w => r w = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have hswap : (Finset.univ.filter (fun w => ¬ r w = 0)).card = s := hsupp
      omega
    rw [hcard2, hsupp]
    ring
  have hP1 : (∏ w : Fin (k + 1), cubeWtR (1 * r w)) = (-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
    refine hwt_eval _ 1 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP2 : (∏ w : Fin (k + 1), cubeWtR (2 * r w)) = (3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
    refine hwt_eval _ 2 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  have hP3 : (∏ w : Fin (k + 1), cubeWtR (3 * r w)) = (-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
    refine hwt_eval _ 3 (fun w => ?_)
    rcases hr w with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
  -- multiples are pairwise distinct and bounded
  obtain ⟨w₀, hw₀⟩ : ∃ w, r w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr_ne (funext h)
  have hrb : ∀ (lam : ℤ), (1 ≤ lam) → (lam ≤ 3) → ∀ w, -3 ≤ lam * r w ∧ lam * r w ≤ 3 := by
    intro lam h1 h3 w
    rcases hr w with h | h | h <;> rw [h] <;> constructor <;> nlinarith
  have hne_mult : ∀ (a b : ℤ), a ≠ b → (fun w => a * r w) ≠ (fun w => b * r w) := by
    intro a b hab hcon
    have := congrFun hcon w₀
    simp only at this
    rcases hr w₀ with h | h | h
    · rw [h] at this; omega
    · exact hw₀ h
    · rw [h] at this; omega
  -- the full-family filter is the seven multiples
  have hfilter : (Fintype.piFinset
      (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
      (fun c => (∑ w, c w * v w) = 0)
      = {0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
         fun w => 3 * r w, fun w => -(3 * r w)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcm, hcv⟩
      have hcb : ∀ w, -3 ≤ c w ∧ c w ≤ 3 := by
        intro w
        have := (Fintype.mem_piFinset.mp hcm) w
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h|h|h|h|h|h|h <;> omega
      rcases hcube c hcb hcv with h|h|h|h|h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · right; right; left
        exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · right; right; right; right; left
        rw [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · right; right; right; right; right; right
        rw [h]
    · intro hmem
      have hbox : ∀ (d : Fin (k + 1) → ℤ), (∀ w, -3 ≤ d w ∧ d w ≤ 3) →
          d ∈ Fintype.piFinset (fun _ : Fin (k + 1) => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
        intro d hd
        rw [Fintype.mem_piFinset]
        intro w
        have := hd w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hvan : ∀ (lam : ℤ), (∑ w, (lam * r w) * v w) = 0 := by
        intro lam
        have h1 : (∑ w, (lam * r w) * v w) = lam * ∑ w, r w * v w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hrel, mul_zero]
      rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨hbox _ (fun w => by simp), Finset.sum_eq_zero (fun w _ => by simp)⟩
      · refine ⟨hbox _ (fun w => by rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        exact hrel
      · refine ⟨hbox _ (fun w => by
          simp only [Pi.neg_apply]
          rcases hr w with h|h|h <;> rw [h] <;> omega), ?_⟩
        have h1 : (∑ w, (-r) w * v w) = -(∑ w, r w * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by simp)
        rw [h1, hrel, neg_zero]
      · exact ⟨hbox _ (hrb 2 (by norm_num) (by norm_num)), hvan 2⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 2 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(2 * r w)) * v w) = -(∑ w, (2 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 2, neg_zero]
      · exact ⟨hbox _ (hrb 3 (by norm_num) (by norm_num)), hvan 3⟩
      · refine ⟨hbox _ (fun w => by
          have := hrb 3 (by norm_num) (by norm_num) w
          constructor <;> omega), ?_⟩
        have h1 : (∑ w, (-(3 * r w)) * v w) = -(∑ w, (3 * r w) * v w) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [h1, hvan 3, neg_zero]
  -- pairwise distinctness of the seven multiples (via the support witness)
  have hρ : r w₀ = -1 ∨ r w₀ = 1 := by
    rcases hr w₀ with h | h | h
    · exact Or.inl h
    · exact absurd h hw₀
    · exact Or.inr h
  have hval_ne : ∀ (f g : Fin (k + 1) → ℤ), f w₀ ≠ g w₀ → f ≠ g :=
    fun f g h hc => h (congrFun hc w₀)
  -- the seven-element sum
  have hsum7 : (∑ c ∈ ({0, r, -r, fun w => 2 * r w, fun w => -(2 * r w),
        fun w => 3 * r w, fun w => -(3 * r w)} : Finset (Fin (k + 1) → ℤ)),
        ∏ w, cubeWtR (c w))
      = (5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))
        + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s)) := by
    have e0 : (∏ w : Fin (k + 1), cubeWtR ((0 : Fin (k + 1) → ℤ) w)) = (5/2 : ℝ) ^ (k + 1) := by
      rw [Finset.prod_congr rfl (fun w _ => by norm_num [cubeWtR] :
        ∀ w ∈ Finset.univ, cubeWtR ((0 : Fin (k + 1) → ℤ) w) = 5/2)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 : (∏ w : Fin (k + 1), cubeWtR (r w)) = (-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
      have := hP1
      simp only [one_mul] at this
      exact this
    have e1n : (∏ w : Fin (k + 1), cubeWtR ((-r) w)) = (-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
      rw [Finset.prod_congr rfl (fun w _ => by rw [Pi.neg_apply, cubeWtR_neg])]
      exact e1
    have e2 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 2 * r w) w)) = (3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := hP2
    have e2n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(2 * r w)) w))
        = (3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP2
    have e3 : (∏ w : Fin (k + 1), cubeWtR ((fun w => 3 * r w) w)) = (-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := hP3
    have e3n : (∏ w : Fin (k + 1), cubeWtR ((fun w => -(3 * r w)) w))
        = (-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s) := by
      rw [Finset.prod_congr rfl (fun w _ => by simp only; rw [cubeWtR_neg])]
      exact hP3
    -- distinctness facts at w₀
    have d01 : (0 : Fin (k + 1) → ℤ) ≠ r := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d02 : (0 : Fin (k + 1) → ℤ) ≠ -r := hval_ne _ _ (by
      simp only [Pi.zero_apply, Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d03 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d04 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d05 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d06 : (0 : Fin (k + 1) → ℤ) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.zero_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d12 : r ≠ -r := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d13 : r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d14 : r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d15 : r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d16 : r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d23 : -r ≠ (fun w => 2 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d24 : -r ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d25 : -r ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d26 : -r ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      simp only [Pi.neg_apply]; rcases hρ with h | h <;> rw [h] <;> omega)
    have d34 : (fun w => 2 * r w) ≠ (fun w => -(2 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d35 : (fun w => 2 * r w) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d36 : (fun w => 2 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d45 : (fun w => -(2 * r w)) ≠ (fun w => 3 * r w) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d46 : (fun w => -(2 * r w)) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    have d56 : (fun w => 3 * r w) ≠ (fun w => -(3 * r w)) := hval_ne _ _ (by
      rcases hρ with h | h <;> rw [h] <;> omega)
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d01, d02, d03, d04, d05, d06⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14, d15, d16⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24, d25, d26⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d34, d35, d36⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d45, d46⟩),
      Finset.sum_insert (by simpa using d56), Finset.sum_singleton,
      e0, e1, e1n, e2, e2n, e3, e3n]
    ring
  have hM : ∑ j ∈ Finset.range Q,
      (∏ w : Fin (k + 1), (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))
        + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))) := by
    have h := riesz_mass_cube_general_real (k + 1) v Q hQ0 hQ
    rw [hfilter, hsum7] at h
    exact h
  -- subfamily filters: {0} when the dropped runner carries the relation,
  -- the seven restricted multiples otherwise
  have hcard0 : (Finset.univ.filter (fun w : Fin (k + 1) => r w = 0)).card = k + 1 - s := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun w => r w = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have hswap : (Finset.univ.filter (fun w : Fin (k + 1) => ¬ r w = 0)).card = s := hsupp
    omega
  have hMsub : ∀ i : Fin (k + 1), ∑ j ∈ Finset.range Q,
      (∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ)))) ^ 3
      = (Q : ℝ) * (if r i = 0
          then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k - s))
            + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k - s))
          else (5/2 : ℝ) ^ k) := by
    intro i
    have hsubQ : 3 * (∑ j' : Fin k, (v (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j' : Fin k, (v (i.succAbove j')).natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]
        exact Nat.le_add_left _ _
      omega
    have h := riesz_mass_cube_general_real k (fun j' => v (i.succAbove j')) Q hQ0 hsubQ
    -- lift a sub-combination to the full family
    have hlift : ∀ c : Fin k → ℤ, (∀ j', -3 ≤ c j' ∧ c j' ≤ 3) →
        (∑ j', c j' * v (i.succAbove j')) = 0 →
        ((i.insertNth 0 c : Fin (k + 1) → ℤ) = 0 ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = -r
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => 2 * r w)
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => -(2 * r w))
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => 3 * r w)
          ∨ (i.insertNth 0 c : Fin (k + 1) → ℤ) = (fun w => -(3 * r w))) := by
      intro c hcb hcv
      refine hcube (i.insertNth 0 c) ?_ ?_
      · intro w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · rw [Fin.insertNth_apply_same]; omega
        · rw [Fin.insertNth_apply_succAbove]; exact hcb j'
      · rw [Fin.sum_univ_succAbove (fun w => (i.insertNth 0 c : Fin (k + 1) → ℤ) w * v w) i,
          Fin.insertNth_apply_same, zero_mul, zero_add]
        rw [Finset.sum_congr rfl fun j' _ => by rw [Fin.insertNth_apply_succAbove]]
        exact hcv
    by_cases hri : r i = 0
    · -- the relation survives: seven restricted multiples
      rw [if_pos hri]
      have hw₀i : w₀ ≠ i := fun h => hw₀ (h ▸ hri)
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hw₀i
      have hρ' : r (i.succAbove j₀) = -1 ∨ r (i.succAbove j₀) = 1 := by rw [hj₀]; exact hρ
      have hsupp' : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') ≠ 0)).card = s := by
        have hbij : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') ≠ 0)).card
            = (Finset.univ.filter (fun w : Fin (k + 1) => r w ≠ 0)).card := by
          refine Finset.card_bij (fun j' _ => i.succAbove j') ?_ ?_ ?_
          · intro j' hj'
            rw [Finset.mem_filter] at hj' ⊢
            exact ⟨Finset.mem_univ _, hj'.2⟩
          · intro a ha b hb hab
            exact Fin.succAbove_right_injective hab
          · intro w hw
            rw [Finset.mem_filter] at hw
            have hwi : w ≠ i := fun h => hw.2 (h ▸ hri)
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hwi
            exact ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj']; exact hw.2⟩, hj'⟩
        rw [hbij, hsupp]
      have hwt_eval' : ∀ (a : ℝ) (lam : ℤ),
          (∀ j', cubeWtR (lam * r (i.succAbove j')) = if r (i.succAbove j') = 0 then 5/2 else a) →
          (∏ j' : Fin k, cubeWtR (lam * r (i.succAbove j'))) = a ^ s * (5/2 : ℝ) ^ (k - s) := by
        intro a lam hval
        rw [Finset.prod_congr rfl (fun j' _ => hval j')]
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have hz : (Finset.univ.filter (fun j' : Fin k => r (i.succAbove j') = 0)).card = k - s := by
          have := Finset.filter_card_add_filter_neg_card_eq_card
            (s := (Finset.univ : Finset (Fin k))) (p := fun j' => r (i.succAbove j') = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at this
          have hswap : (Finset.univ.filter
              (fun j' : Fin k => ¬ r (i.succAbove j') = 0)).card = s := hsupp'
          omega
        rw [hz, hsupp']
        ring
      have hQ1 : (∏ j' : Fin k, cubeWtR (1 * r (i.succAbove j')))
          = (-15/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        refine hwt_eval' _ 1 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ2 : (∏ j' : Fin k, cubeWtR (2 * r (i.succAbove j')))
          = (3/4 : ℝ) ^ s * (5/2) ^ (k - s) := by
        refine hwt_eval' _ 2 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      have hQ3 : (∏ j' : Fin k, cubeWtR (3 * r (i.succAbove j')))
          = (-1/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        refine hwt_eval' _ 3 (fun j' => ?_)
        rcases hr (i.succAbove j') with h | h | h <;> rw [h] <;> norm_num [cubeWtR]
      -- the restricted filter
      set rr : Fin k → ℤ := fun j' => r (i.succAbove j') with hrr
      have hfsub : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0)
          = {0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
             fun j' => 3 * rr j', fun j' => -(3 * rr j')} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hres : ∀ (f : Fin (k + 1) → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = f → f i = 0 →
              c = fun j' => f (i.succAbove j') := by
            intro f hf _
            funext j'
            have := congrFun hf (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            exact this
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · left
            funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · right; left
            rw [hres r h hri]
          · right; right; left
            have : c = fun j' => (-r) (i.succAbove j') := hres (-r) h (by simp [hri])
            rw [this]
            funext j'
            simp [hrr]
          · right; right; right; left
            have : c = fun j' => 2 * r (i.succAbove j') :=
              hres (fun w => 2 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; left
            have : c = fun j' => -(2 * r (i.succAbove j')) :=
              hres (fun w => -(2 * r w)) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; left
            have : c = fun j' => 3 * r (i.succAbove j') :=
              hres (fun w => 3 * r w) h (by simp [hri])
            rw [this]
          · right; right; right; right; right; right
            have : c = fun j' => -(3 * r (i.succAbove j')) :=
              hres (fun w => -(3 * r w)) h (by simp [hri])
            rw [this]
        · intro hmem
          have hbox4 : ∀ (d : Fin k → ℤ), (∀ j', -3 ≤ d j' ∧ d j' ≤ 3) →
              d ∈ Fintype.piFinset (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)) := by
            intro d hd
            rw [Fintype.mem_piFinset]
            intro j'
            have := hd j'
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
          have hvansub : ∀ (lam : ℤ), (∑ j', (lam * rr j') * v (i.succAbove j')) = 0 := by
            intro lam
            have h1 : (∑ j', (lam * rr j') * v (i.succAbove j'))
                = lam * ∑ j', rr j' * v (i.succAbove j') := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            have h2 : (∑ j', rr j' * v (i.succAbove j')) = 0 := by
              have := hrel
              rw [Fin.sum_univ_succAbove (fun w => r w * v w) i, hri, zero_mul, zero_add] at this
              exact this
            rw [h1, h2, mul_zero]
          have hrrb : ∀ (lam : ℤ), 1 ≤ lam → lam ≤ 3 → ∀ j', -3 ≤ lam * rr j' ∧ lam * rr j' ≤ 3 := by
            intro lam h1 h3 j'
            rcases hr (i.succAbove j') with h | h | h <;>
              simp only [hrr, h] <;> constructor <;> nlinarith
          rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact ⟨hbox4 _ (fun j' => by simp), Finset.sum_eq_zero (fun j' _ => by simp)⟩
          · refine ⟨hbox4 _ (fun j' => by
              rcases hr (i.succAbove j') with h|h|h <;> simp only [hrr, h] <;> omega), ?_⟩
            have := hvansub 1
            simpa using this
          · refine ⟨hbox4 _ (fun j' => by
              simp only [Pi.neg_apply, hrr]
              rcases hr (i.succAbove j') with h|h|h <;> rw [h] <;> omega), ?_⟩
            have h1 : (∑ j', (-rr) j' * v (i.succAbove j'))
                = -(∑ j', (1 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by simp only [Pi.neg_apply]; ring)
            rw [h1, hvansub 1, neg_zero]
          · exact ⟨hbox4 _ (hrrb 2 (by norm_num) (by norm_num)), hvansub 2⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 2 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(2 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (2 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 2, neg_zero]
          · exact ⟨hbox4 _ (hrrb 3 (by norm_num) (by norm_num)), hvansub 3⟩
          · refine ⟨hbox4 _ (fun j' => by
              have := hrrb 3 (by norm_num) (by norm_num) j'
              constructor <;> omega), ?_⟩
            have h1 : (∑ j', (-(3 * rr j')) * v (i.succAbove j'))
                = -(∑ j', (3 * rr j') * v (i.succAbove j')) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun j' _ => by ring)
            rw [h1, hvansub 3, neg_zero]
      -- evaluate the restricted seven-element sum
      have hρ4 : rr j₀ = -1 ∨ rr j₀ = 1 := by simp only [hrr, hj₀]; exact hρ
      have hval_ne4 : ∀ (f g : Fin k → ℤ), f j₀ ≠ g j₀ → f ≠ g :=
        fun f g hne hc => hne (congrFun hc j₀)
      have e0' : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have e1' : (∏ j' : Fin k, cubeWtR (rr j')) = (-15/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        have := hQ1
        simp only [one_mul, hrr] at this ⊢
        exact this
      have e1n' : (∏ j' : Fin k, cubeWtR ((-rr) j')) = (-15/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        rw [Finset.prod_congr rfl (fun j' _ => by rw [Pi.neg_apply, cubeWtR_neg])]
        exact e1'
      have e2' : (∏ j' : Fin k, cubeWtR ((fun j' => 2 * rr j') j'))
          = (3/4 : ℝ) ^ s * (5/2) ^ (k - s) := by
        simp only [hrr]
        exact hQ2
      have e2n' : (∏ j' : Fin k, cubeWtR ((fun j' => -(2 * rr j')) j'))
          = (3/4 : ℝ) ^ s * (5/2) ^ (k - s) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ2
      have e3' : (∏ j' : Fin k, cubeWtR ((fun j' => 3 * rr j') j'))
          = (-1/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        simp only [hrr]
        exact hQ3
      have e3n' : (∏ j' : Fin k, cubeWtR ((fun j' => -(3 * rr j')) j'))
          = (-1/8 : ℝ) ^ s * (5/2) ^ (k - s) := by
        rw [Finset.prod_congr rfl (fun j' _ => by simp only; rw [cubeWtR_neg])]
        simp only [hrr]
        exact hQ3
      have hsum7' : (∑ c ∈ ({0, rr, -rr, fun j' => 2 * rr j', fun j' => -(2 * rr j'),
            fun j' => 3 * rr j', fun j' => -(3 * rr j')} : Finset (Fin k → ℤ)),
            ∏ j', cubeWtR (c j'))
          = (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k - s))
            + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k - s)) := by
        rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.zero_apply, Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_,
              hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              (try simp only [Pi.neg_apply]) <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨hval_ne4 _ _ ?_, hval_ne4 _ _ ?_⟩ <;>
              rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            refine hval_ne4 _ _ ?_
            rcases hρ4 with h | h <;> rw [h] <;> omega),
          Finset.sum_singleton, e0', e1', e1n', e2', e2n', e3', e3n']
        ring
      rw [hfsub, hsum7'] at h
      exact h
    · -- the dropped runner carries the relation: only the trivial combination
      rw [if_neg hri]
      have hfsub0 : (Fintype.piFinset
          (fun _ : Fin k => ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ))).filter
          (fun c => (∑ j', c j' * v (i.succAbove j')) = 0) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hcm, hcv⟩
          have hcb : ∀ j', -3 ≤ c j' ∧ c j' ≤ 3 := by
            intro j'
            have := (Fintype.mem_piFinset.mp hcm) j'
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h|h|h|h|h|h|h <;> omega
          have hz : ∀ (f : Fin (k + 1) → ℤ), (i.insertNth 0 c : Fin (k + 1) → ℤ) = f → f i ≠ 0 → False := by
            intro f hf hfi
            have := congrFun hf i
            rw [Fin.insertNth_apply_same] at this
            exact hfi this.symm
          rcases hlift c hcb hcv with h|h|h|h|h|h|h
          · funext j'
            have := congrFun h (i.succAbove j')
            rw [Fin.insertNth_apply_succAbove] at this
            simpa using this
          · exact (hz r h hri).elim
          · exact (hz (-r) h (by simp [hri])).elim
          · exact (hz _ h (by simpa using mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero two_ne_zero hri)).elim
          · exact (hz _ h (by simpa using mul_ne_zero three_ne_zero hri)).elim
          · exact (hz _ h (by
              simp only [neg_ne_zero]
              exact mul_ne_zero three_ne_zero hri)).elim
        · rintro rfl
          refine ⟨?_, Finset.sum_eq_zero (fun j' _ => by simp)⟩
          rw [Fintype.mem_piFinset]
          intro j'
          simp
      rw [hfsub0, Finset.sum_singleton] at h
      have hzero4 : (∏ j' : Fin k, cubeWtR ((0 : Fin k → ℤ) j')) = (5/2 : ℝ) ^ k := by
        rw [Finset.prod_congr rfl (fun j' _ => by norm_num [cubeWtR] :
          ∀ j' ∈ Finset.univ, cubeWtR ((0 : Fin k → ℤ) j') = 5/2)]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hzero4] at h
      exact h
  -- assemble via the per-runner crude union at δ = 1/6, u = 1/2 exactly
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine riesz_crude_union_cube' (k := k) v Q hQ0 (1 / ((k : ℝ) + 2))
    (by positivity) (by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      linarith)
    ((Q : ℝ) * ((5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))
      + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))))
    (fun i => (Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k - s))
        + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k - s))
      else (5/2 : ℝ) ^ k)) hM hMsub ?_
  -- the union arithmetic: quadratic cosine bound, uniform in k ≥ 5
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hsin' : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hπδltpi : π * δ < π := by nlinarith [Real.pi_pos, hδ2]
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * δ) < 2 * (π * δ) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin', hsinpos]
    linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hu3 : (1 - Real.cos (2 * π * δ)) ^ 3 < (2 * (π * δ) ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hu hcosnn (by norm_num)
  have hπ2 : π ^ 2 < 9.87 := by
    have hm := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
    nlinarith [hm]
  have hπ6 : π ^ 6 < 961.51 := by
    have h1 : π ^ 6 = (π ^ 2) ^ 3 := by ring
    rw [h1]
    calc (π ^ 2) ^ 3 < (9.87 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hπ2 (sq_nonneg π) (by norm_num)
      _ < 961.51 := by norm_num
  -- power factorizations off the common (5/2)^(k-3)
  -- power splits off the common (5/2)^(k-s)
  have hfk : (5/2 : ℝ) ^ k = (5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) ^ s := by
    rw [← pow_add]; congr 1; omega
  have hfk1 : (5/2 : ℝ) ^ (k + 1) = (5/2 : ℝ) ^ (k - s) * ((5/2 : ℝ) ^ s * (5/2)) := by
    rw [show (5/2 : ℝ) ^ (k - s) * ((5/2 : ℝ) ^ s * (5/2)) = (5/2 : ℝ) ^ ((k - s) + s) * (5/2)
      from by rw [pow_add]; ring]
    rw [show (k - s) + s = k from by omega, ← pow_succ]
  have hfk2 : (5/2 : ℝ) ^ (k + 1 - s) = (5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) := by
    rw [← pow_succ]; congr 1; omega
  have hY0 : (0 : ℝ) < (5/2 : ℝ) ^ (k - s) := by positivity
  -- the relation-mass factor: uniform lower bound (7/20)(5/2)^s, no parity split
  have hT : (15/8 : ℝ) ^ s = (3/4 : ℝ) ^ s * (5/2 : ℝ) ^ s := by
    rw [← mul_pow]; norm_num
  have hV : (1/8 : ℝ) ^ s = (1/20 : ℝ) ^ s * (5/2 : ℝ) ^ s := by
    rw [← mul_pow]; norm_num
  have h34 : (3/4 : ℝ) ^ s ≤ (3/4 : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have h120 : (1/20 : ℝ) ^ s ≤ (1/20 : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hTneg : -((15/8 : ℝ) ^ s) ≤ (-15/8 : ℝ) ^ s := by
    have h := neg_abs_le ((-15/8 : ℝ) ^ s)
    rw [abs_pow, show |(-15/8 : ℝ)| = 15/8 from by
      rw [abs_of_neg (by norm_num : (-15/8 : ℝ) < 0)]; norm_num] at h
    exact h
  have hVneg : -((1/8 : ℝ) ^ s) ≤ (-1/8 : ℝ) ^ s := by
    have h := neg_abs_le ((-1/8 : ℝ) ^ s)
    rw [abs_pow, show |(-1/8 : ℝ)| = 1/8 from by
      rw [abs_of_neg (by norm_num : (-1/8 : ℝ) < 0)]; norm_num] at h
    exact h
  have hUpos : (0 : ℝ) ≤ (3/4 : ℝ) ^ s := by positivity
  have hXpos : (0 : ℝ) < (5/2 : ℝ) ^ s := by positivity
  have h1320 : (15/8 : ℝ) ^ s + (1/8 : ℝ) ^ s ≤ (13/40) * (5/2 : ℝ) ^ s := by
    rw [hT, hV]
    have hpa := mul_le_mul_of_nonneg_right h34 (le_of_lt hXpos)
    have hpb := mul_le_mul_of_nonneg_right h120 (le_of_lt hXpos)
    nlinarith [hpa, hpb]
  have hClow : (7/20 : ℝ) * (5/2 : ℝ) ^ s ≤ ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) := by
    linarith [hTneg, hVneg, hUpos, h1320]
  have hCpos : (0 : ℝ) < ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) := by
    nlinarith [hClow, hXpos]
  have hsX : (s : ℝ) * (5/2 : ℝ) ^ s ≤ (20/7 : ℝ) * (s : ℝ) * ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    nlinarith [mul_le_mul_of_nonneg_left hClow hs0]
  -- the runner sum: k+1-s zero-runners carry the correction, s do not
  have hA : (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k - s))
      + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k - s))
      = ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s) := by
    rw [hfk]; ring
  have hMval : (5/2 : ℝ) ^ (k + 1) + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))
      + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k + 1 - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k + 1 - s))
      = ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * ((5/2 : ℝ) ^ (k - s) * (5/2)) := by
    rw [hfk1, hfk2]; ring
  have hsum5 : (∑ i : Fin (k + 1), ((Q : ℝ) * (if r i = 0
      then (5/2 : ℝ) ^ k + 2 * ((-15/8 : ℝ) ^ s * (5/2) ^ (k - s))
        + 2 * ((3/4 : ℝ) ^ s * (5/2) ^ (k - s)) + 2 * ((-1/8 : ℝ) ^ s * (5/2) ^ (k - s))
      else (5/2 : ℝ) ^ k)))
      = (Q : ℝ) * (((k : ℝ) + 1 - (s : ℝ)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))
          + (s : ℝ) * ((5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) ^ s)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard0, hsupp,
      nsmul_eq_mul, nsmul_eq_mul, hA, hfk]
    rw [Nat.cast_sub (by omega : s ≤ k + 1)]
    push_cast
    ring
  rw [hsum5, hMval]
  -- the uniform close: u³(k+1) < 7/8
  have hδ61 : δ ^ 6 * ((k : ℝ) + 2) ^ 6 = 1 := by
    rw [← mul_pow, hδval, one_pow]
  have hkey : 64 * π ^ 6 * ((k : ℝ) + 1) < 7 * ((k : ℝ) + 2) ^ 6 := by
    have h64 : (1296 : ℝ) ≤ ((k : ℝ) + 2) ^ 4 := by
      calc (1296 : ℝ) = 6 ^ 4 := by norm_num
        _ ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h6b : 1296 * ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 6 := by
      have hsplit : ((k : ℝ) + 2) ^ 6 = ((k : ℝ) + 2) ^ 4 * ((k : ℝ) + 2) ^ 2 := by ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right h64 (by positivity)
    have hπk : π ^ 6 * ((k : ℝ) + 1) < 961.51 * ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hπ6 (by linarith)
    nlinarith [hπk, h6b, hkR,
      mul_le_mul_of_nonneg_left hkR (by linarith : (0 : ℝ) ≤ (k : ℝ))]
  have hcore : (1 - Real.cos (2 * π * δ)) ^ 3 * ((20/7) * ((k : ℝ) + 1)) < 5/2 := by
    have hbr0 : (0 : ℝ) < (20/7 : ℝ) * ((k : ℝ) + 1) := by positivity
    calc (1 - Real.cos (2 * π * δ)) ^ 3 * ((20/7) * ((k : ℝ) + 1))
        < (2 * (π * δ) ^ 2) ^ 3 * ((20/7) * ((k : ℝ) + 1)) :=
          mul_lt_mul_of_pos_right hu3 hbr0
      _ = ((160/7) * π ^ 6 * ((k : ℝ) + 1)) * δ ^ 6 := by ring
      _ < ((5/2) * ((k : ℝ) + 2) ^ 6) * δ ^ 6 := by
          refine mul_lt_mul_of_pos_right ?_ (pow_pos hδ0 6)
          nlinarith [hkey]
      _ = (5/2) * (δ ^ 6 * ((k : ℝ) + 2) ^ 6) := by ring
      _ = 5/2 := by rw [hδ61, mul_one]
  have hABle : ((k : ℝ) + 1 - (s : ℝ)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))
      + (s : ℝ) * ((5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) ^ s)
      ≤ ((20/7) * ((k : ℝ) + 1)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s)) := by
    have hsle : (s : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : s ≤ k + 1)
    have h2 : ((k : ℝ) + 1 - (s : ℝ)) * ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) + (s : ℝ) * (5/2 : ℝ) ^ s
        ≤ (20/7) * ((k : ℝ) + 1) * ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) := by
      have hprod : (0 : ℝ) ≤ ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * ((k : ℝ) + 1 - (s : ℝ)) :=
        mul_nonneg (le_of_lt hCpos) (by linarith)
      nlinarith [hsX, hprod]
    calc ((k : ℝ) + 1 - (s : ℝ)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))
        + (s : ℝ) * ((5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) ^ s)
        = (((k : ℝ) + 1 - (s : ℝ)) * ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) + (s : ℝ) * (5/2 : ℝ) ^ s)
            * (5/2 : ℝ) ^ (k - s) := by ring
      _ ≤ ((20/7) * ((k : ℝ) + 1) * ((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s)) * (5/2 : ℝ) ^ (k - s) :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hY0)
      _ = ((20/7) * ((k : ℝ) + 1)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s)) := by ring
  calc (1 - Real.cos (2 * π * δ)) ^ 3
      * ((Q : ℝ) * (((k : ℝ) + 1 - (s : ℝ)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))
          + (s : ℝ) * ((5/2 : ℝ) ^ (k - s) * (5/2 : ℝ) ^ s)))
      ≤ (1 - Real.cos (2 * π * δ)) ^ 3
        * ((Q : ℝ) * (((20/7) * ((k : ℝ) + 1)) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hcosnn 3)
        exact mul_le_mul_of_nonneg_left hABle (le_of_lt hQR)
    _ = ((1 - Real.cos (2 * π * δ)) ^ 3 * ((20/7) * ((k : ℝ) + 1)))
        * ((Q : ℝ) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))) := by ring
    _ < (5/2) * ((Q : ℝ) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * (5/2 : ℝ) ^ (k - s))) :=
        mul_lt_mul_of_pos_right hcore (mul_pos hQR (mul_pos hCpos hY0))
    _ = (Q : ℝ) * (((5/2 : ℝ) ^ s + 2 * (-15/8 : ℝ) ^ s + 2 * (3/4 : ℝ) ^ s + 2 * (-1/8 : ℝ) ^ s) * ((5/2 : ℝ) ^ (k - s) * (5/2))) := by ring

#print axioms bridge_cube_single_general

set_option maxHeartbeats 1600000 in
/-- **The ±1-valued single-line bridge dispatcher.**  A positive family of
`k+1` runners (`k ≥ 4`) carrying a `±1`-valued combination `d ≠ 0`, whose only
vanishing `[-3,3]`-combinations lie on the line `ℤ·d`, meets the floor
`1/(k+2)` — provided the support `s` of `d` satisfies `3 ≤ s ≤ k`.  This is the
assembly glue: it converts the `vanishing_trichotomy` single-line output into
the seven-multiple hypothesis and dispatches to the exact cube-single floor
(`bridge_cube_single_four` at `k = 4`, `bridge_cube_single_supp3` for support
three at `k ≥ 5`, `bridge_cube_single_general` for support `≥ 4`).  The
remaining `±1`-valued single-line cases are the support-two collision
(`v_i = v_j`) and the full-support relation `s = k+1`. -/
theorem bridge_cube_single_pm1 {k : ℕ} (hk : 4 ≤ k)
    (v : Fin (k + 1) → ℤ) (d : Fin (k + 1) → ℤ)
    (hd1 : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1)
    (hrel : (∑ w, d w * v w) = 0)
    (hs3 : 3 ≤ (Finset.univ.filter (fun w => d w ≠ 0)).card)
    (hsk : (Finset.univ.filter (fun w => d w ≠ 0)).card ≤ k)
    (hline : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
        ∃ lam : ℤ, c = fun w => lam * d w) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  -- a support witness
  obtain ⟨w₀, hw₀⟩ : ∃ w, d w ≠ 0 := by
    by_contra h
    push_neg at h
    have hempty : (Finset.univ.filter (fun w => d w ≠ 0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _
      simp only [not_not]
      exact h w
    rw [hempty, Finset.card_empty] at hs3
    omega
  have hρ : d w₀ = -1 ∨ d w₀ = 1 := by
    rcases hd1 w₀ with h | h | h
    · exact Or.inl h
    · exact absurd h hw₀
    · exact Or.inr h
  -- the seven-multiple hypothesis, from the single-line property
  have hcube : ∀ c : Fin (k + 1) → ℤ, (∀ w, -3 ≤ c w ∧ c w ≤ 3) → (∑ w, c w * v w) = 0 →
      c = 0 ∨ c = d ∨ c = -d ∨ c = (fun w => 2 * d w) ∨ c = (fun w => -(2 * d w))
        ∨ c = (fun w => 3 * d w) ∨ c = (fun w => -(3 * d w)) := by
    intro c hcb hcv
    obtain ⟨lam, hc⟩ := hline c hcb hcv
    have hbound : -3 ≤ lam ∧ lam ≤ 3 := by
      have hcw := congrFun hc w₀
      simp only at hcw
      have hb := hcb w₀
      rcases hρ with h | h <;> rw [h] at hcw <;> omega
    obtain ⟨hlo, hhi⟩ := hbound
    have hlam : lam = 0 ∨ lam = 1 ∨ lam = -1 ∨ lam = 2 ∨ lam = -2 ∨ lam = 3 ∨ lam = -3 := by omega
    rcases hlam with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring)
    · exact Or.inr (Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring))
    · exact Or.inr (Or.inr (Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by funext w; rw [congrFun hc w]; try simp only [Pi.neg_apply, Pi.zero_apply, neg_mul, one_mul, zero_mul]; try ring))))))
  set s := (Finset.univ.filter (fun w => d w ≠ 0)).card with hsdef
  have hr : ∀ w, d w = -1 ∨ d w = 0 ∨ d w = 1 := hd1
  rcases eq_or_lt_of_le hs3 with hs3eq | hs4
  · -- support exactly three
    rcases eq_or_lt_of_le hk with hk4 | hk5
    · -- k = 4
      subst hk4
      have h := bridge_cube_single_four v d hr hrel (by rw [← hsdef]; omega) hcube
      rw [show ((4 : ℕ) : ℝ) + 2 = 6 from by norm_num]
      exact h
    · -- k ≥ 5
      exact bridge_cube_single_supp3 (by omega) v d hr hrel (by rw [← hsdef]; omega) hcube
  · -- support ≥ 4
    exact bridge_cube_single_general hk (by omega) hsk v d hr hrel rfl hcube

#print axioms bridge_cube_single_pm1

end LRSpectrumFull
