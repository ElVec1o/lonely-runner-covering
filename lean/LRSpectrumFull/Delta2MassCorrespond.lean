/-
# The mass correspondence: rational web masses = real grid masses / Q

Closes the two named hypotheses of `floor_of_rieszSharpFiresQ_of_masses` by identifying the
computable rational `webMassQ` with the real grid mass, via `riesz_mass_web_real`.

The bridge is the ternary encoding: `webSections v` (sections `σ : Fin m → Fin 3` with
`∑ sgn3(σ i)·vᵢ = 0`, `σ ≠ 0`) maps bijectively to the integer web
`W = image (fun σ i => sgn3 (σ i))`, and `sgn3` is `reps` of `Delta2RieszMass`.  The per-section
weight matches: `∏ᵢ (cᵢ = 0 ? 1 : −½) = (−½)^{#supp}`.
-/
import LRSpectrumFull.Delta2WebAbsorb
import LRSpectrumFull.Delta2BridgeDisjunction
import LRSpectrumFull.Delta2GrandReduction

namespace LRSpectrumFull

open Real

/-- `sgn3` is injective on `Fin 3`. -/
theorem sgn3_injective : Function.Injective sgn3 := by
  decide

theorem sgn3_eq_zero_iff (t : Fin 3) : sgn3 t = 0 ↔ t = 0 := by
  fin_cases t <;> simp [sgn3]

theorem sgn3_mem (t : Fin 3) : sgn3 t = -1 ∨ sgn3 t = 0 ∨ sgn3 t = 1 := by
  fin_cases t <;> simp [sgn3]

/-- The integer web of `v`: the image of the ternary sections under `sgn3`. -/
def intWeb {m : ℕ} (v : Fin m → ℤ) : Finset (Fin m → ℤ) :=
  (webSections v).image (fun σ i => sgn3 (σ i))

theorem sgn3_comp_injective {m : ℕ} : Function.Injective (fun (σ : Fin m → Fin 3) i => sgn3 (σ i)) := by
  intro σ σ' h
  funext i
  exact sgn3_injective (congrFun h i)

/-- Membership in `intWeb`: integer webs are exactly the `sgn3`-images of nonzero vanishing
sections. -/
theorem mem_intWeb {m : ℕ} (v : Fin m → ℤ) (c : Fin m → ℤ) :
    c ∈ intWeb v ↔ (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧ (∑ i, c i * v i) = 0 ∧ c ≠ 0 := by
  classical
  constructor
  · intro hc
    simp only [intWeb, Finset.mem_image, webSections, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc
    obtain ⟨σ, ⟨hrel, hne⟩, hcσ⟩ := hc
    subst hcσ
    refine ⟨fun i => sgn3_mem (σ i), hrel, ?_⟩
    intro h0
    apply hne
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply] at this
    exact (sgn3_eq_zero_iff (σ i)).mp this
  · rintro ⟨hmem, hrel, hne⟩
    -- decode c to a ternary section
    refine Finset.mem_image.mpr ⟨fun i => if c i = 1 then 1 else if c i = -1 then 2 else 0, ?_, ?_⟩
    · simp only [webSections, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rw [← hrel]
        exact Finset.sum_congr rfl (fun i _ => by
          rcases hmem i with h | h | h <;> simp [sgn3, h])
      · intro h0
        apply hne
        funext i
        have := congrFun h0 i
        simp only [Pi.zero_apply] at this
        rcases hmem i with h | h | h
        · simp [h] at this
        · exact h
        · simp [h] at this
    · funext i
      rcases hmem i with h | h | h <;> simp [sgn3, h]

/-- The section weight, real-valued: `((−½)^{#supp σ} : ℚ→ℝ) = ∏ᵢ (sgn3(σ i)=0 ? 1 : −½)`. -/
theorem weight_section {m : ℕ} (σ : Fin m → Fin 3) :
    ((-1 / 2 : ℝ) ^ (Finset.univ.filter (fun i => σ i ≠ 0)).card)
      = ∏ i, (if sgn3 (σ i) = 0 then (1 : ℝ) else -1 / 2) := by
  have hset : (Finset.univ.filter (fun i => σ i ≠ 0))
      = (Finset.univ.filter (fun i => ¬ sgn3 (σ i) = 0)) := by
    apply Finset.filter_congr
    intro i _
    simp only [ne_eq, eq_iff_iff]
    rw [sgn3_eq_zero_iff]
  rw [hset, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => sgn3 (σ i) = 0)]
  rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos (Finset.mem_filter.mp hi).2] :
      ∀ i ∈ Finset.univ.filter (fun i => sgn3 (σ i) = 0), (if sgn3 (σ i) = 0 then (1:ℝ) else -1/2) = 1)]
  rw [Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_filter.mp hi).2] :
      ∀ i ∈ Finset.univ.filter (fun i => ¬ sgn3 (σ i) = 0), (if sgn3 (σ i) = 0 then (1:ℝ) else -1/2) = -1/2)]
  rw [Finset.prod_const, Finset.prod_const, one_pow, one_mul]

/-- **The full-family mass correspondence.**  `rieszMassSum v Q = Q · webMassQ v` at the
canonical modulus. -/
theorem rieszMassSum_eq_webMassQ_of {m : ℕ} (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQsum : (∑ i, (v i).natAbs) < Q) :
    rieszMassSum v Q = ((Q : ℕ) : ℝ) * (webMassQ v : ℝ) := by
  classical
  -- the four web hypotheses
  have hW0 : (0 : Fin m → ℤ) ∉ intWeb v := by
    rw [mem_intWeb]; rintro ⟨_, _, hne⟩; exact hne rfl
  have hWmem : ∀ c ∈ intWeb v, ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1 :=
    fun c hc => ((mem_intWeb v c).mp hc).1
  have hWrel : ∀ c ∈ intWeb v, (∑ i, c i * v i) = 0 :=
    fun c hc => ((mem_intWeb v c).mp hc).2.1
  have hWchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
      c = 0 ∨ c ∈ intWeb v := by
    intro c hmem hrel
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · exact Or.inr ((mem_intWeb v c).mpr ⟨hmem, hrel, hc0⟩)
  -- the real mass identity
  have hreal := riesz_mass_web_real m v Q hQ0 hQsum (intWeb v) hW0 hWmem hWrel hWchar
  rw [rieszMassSum, hreal]
  congr 1
  -- the mass value: rational webMassQ = real web sum
  rw [webMassQ, intWeb, Finset.sum_image (fun σ _ σ' _ h => sgn3_comp_injective h)]
  push_cast
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact (weight_section σ).symm

/-- The canonical-modulus corollary. -/
theorem rieszMassSum_eq_webMassQ {m : ℕ} (v : Fin m → ℤ) :
    rieszMassSum v (canonicalQ v) = ((canonicalQ v : ℕ) : ℝ) * (webMassQ v : ℝ) :=
  rieszMassSum_eq_webMassQ_of v (canonicalQ v) (Nat.succ_pos _) (Nat.lt_succ_self _)

/-- The subfamily web mass equals the full family relations restricted:
`webMassQ (v after p.succAbove) = webMassDelQ v p`, via `sigma ↦ sigma ∘ p.succAbove`. -/
theorem webMassQ_succAbove_eq_webMassDelQ {m : ℕ} (v : Fin (m + 1) → ℤ) (p : Fin (m + 1)) :
    webMassQ (fun j' : Fin m => v (p.succAbove j')) = webMassDelQ v p := by
  classical
  set u : Fin m → ℤ := fun j' => v (p.succAbove j') with hu
  rw [webMassQ, webMassDelQ]
  congr 1
  have hins_rel : ∀ τ : Fin m → Fin 3, (∑ j', sgn3 (τ j') * u j') = 0 →
      (∑ j, sgn3 (Fin.insertNth (α := fun _ => Fin 3) p (0 : Fin 3) τ j) * v j) = 0 := by
    intro τ hτ
    rw [Fin.sum_univ_succAbove _ p, Fin.insertNth_apply_same]
    have hterm : ∀ j', sgn3 (Fin.insertNth (α := fun _ => Fin 3) p (0 : Fin 3) τ (p.succAbove j')) * v (p.succAbove j')
        = sgn3 (τ j') * u j' := by
      intro j'; rw [Fin.insertNth_apply_succAbove]
    simp only [hterm]
    rw [hτ]; simp [sgn3]
  have hres_rel : ∀ σ : Fin (m + 1) → Fin 3, σ p = 0 → (∑ j, sgn3 (σ j) * v j) = 0 →
      (∑ j', sgn3 (σ (p.succAbove j')) * u j') = 0 := by
    intro σ hσp hσ
    have hh := hσ
    rw [Fin.sum_univ_succAbove _ p, hσp] at hh
    simpa [sgn3, hu] using hh
  have hcard : ∀ τ : Fin m → Fin 3,
      (Finset.univ.filter (fun j => Fin.insertNth (α := fun _ => Fin 3) p (0 : Fin 3) τ j ≠ 0)).card
        = (Finset.univ.filter (fun j' => τ j' ≠ 0)).card := by
    intro τ
    have hset : (Finset.univ.filter (fun j => Fin.insertNth (α := fun _ => Fin 3) p (0 : Fin 3) τ j ≠ 0))
        = (Finset.univ.filter (fun j' => τ j' ≠ 0)).image p.succAbove := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj
        by_cases hjp : j = p
        · exact absurd (by rw [hjp, Fin.insertNth_apply_same]) hj
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjp
          refine ⟨j', ?_, rfl⟩
          rwa [Fin.insertNth_apply_succAbove] at hj
      · rintro ⟨j', hj', rfl⟩
        rwa [Fin.insertNth_apply_succAbove]
    rw [hset, Finset.card_image_of_injective _ (Fin.succAbove_right_injective)]

  refine Finset.sum_bij' (fun τ _ => Fin.insertNth (α := fun _ => Fin 3) p (0 : Fin 3) τ)
    (fun σ _ => fun j' => σ (p.succAbove j')) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [webSections, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    obtain ⟨hrel, hne⟩ := hτ
    refine ⟨⟨hins_rel τ hrel, ?_⟩, Fin.insertNth_apply_same (α := fun _ => Fin 3) p (0 : Fin 3) τ⟩
    intro h0
    apply hne; funext j'
    have hc := congrFun h0 (p.succAbove j')
    rw [Fin.insertNth_apply_succAbove] at hc
    simpa using hc
  · intro σ hσ
    simp only [webSections, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨⟨hrel, hne⟩, hp0⟩ := hσ
    refine ⟨hres_rel σ hp0 hrel, ?_⟩
    intro h0
    apply hne; funext j
    rcases eq_or_ne j p with rfl | hjp
    · exact hp0
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjp
      simpa using congrFun h0 j'
  · intro τ _; funext j'; simp only [Fin.insertNth_apply_succAbove]
  · intro σ hσ
    simp only [webSections, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    funext j
    rcases eq_or_ne j p with rfl | hjp
    · simp only [Fin.insertNth_apply_same, hσ.2]
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjp
      simp only [Fin.insertNth_apply_succAbove]
  · intro τ _; rw [hcard τ]

end LRSpectrumFull
