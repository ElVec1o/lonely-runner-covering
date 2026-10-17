/-
# Absorption, the real web mass, and the sharp two-relation Bridge

Three pieces on top of `riesz_union_markov` and `riesz_mass_web`:

* `riesz_mass_web_real` — the general web mass identity over `ℝ`.
* `absorption` — the closed-form criterion: masses supplied as data, with a distinguished
  core `S` outside of which every subfamily mass equals the total mass (web-free pads).  If
  `9.9225·(B + (k+2−|S|)·M) ≤ (k+2)²·M`, the floor holds.  Any fixed relation core, however
  dense its web, is absorbed once the family is large enough.
* `bridge_two_relations_markov` — two disjoint support-`3` relations, `k ≥ 11` (down from
  `k ≥ 19`), via the Markov union; the escape parameter is `δ = 1/(k+2)` itself, and
  `∑(2Mᵢ − M) = (k+5)·M` exactly.
-/
import LRSpectrumFull.Delta2WebRieszSharp

namespace LRSpectrumFull

open Real

/-- Real form of `riesz_mass_web`. -/
theorem riesz_mass_web_real (m : ℕ) (v : Fin m → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : (∑ i, (v i).natAbs) < Q)
    (W : Finset (Fin m → ℤ)) (hW0 : (0 : Fin m → ℤ) ∉ W)
    (hWmem : ∀ c ∈ W, ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hWrel : ∀ c ∈ W, (∑ i, c i * v i) = 0)
    (hWchar : ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * v i) = 0 →
        c = 0 ∨ c ∈ W) :
    ∑ j ∈ Finset.range Q, ∏ i : Fin m,
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
      = (Q : ℝ) * (1 + ∑ c ∈ W, ∏ i, (if c i = 0 then (1 : ℝ) else -1 / 2)) := by
  have h := riesz_mass_web m v Q hQ0 hQ W hW0 hWmem hWrel hWchar
  have hcs : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range Q, ∏ i : Fin m, (1 - Complex.cos (2 * ↑π * ↑(v i) * ↑j / ↑Q)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
    congr 2
    push_cast
    ring
  have hite : ∀ (c : Fin m → ℤ) (i : Fin m),
      (((if c i = 0 then (1 : ℝ) else -1 / 2) : ℝ) : ℂ)
        = (if c i = 0 then (1 : ℂ) else -1 / 2) := by
    intro c i
    by_cases hci : c i = 0
    · simp [hci]
    · simp only [hci, if_false]
      norm_num
  have cast_eq : ((∑ j ∈ Finset.range Q, ∏ i : Fin m,
          (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) : ℝ) : ℂ)
      = (((Q : ℝ) * (1 + ∑ c ∈ W, ∏ i, (if c i = 0 then (1 : ℝ) else -1 / 2)) : ℝ) : ℂ) := by
    rw [hcs, h, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_sum, Complex.ofReal_natCast]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Complex.ofReal_prod]
    exact (Finset.prod_congr rfl (fun i _ => (hite c i))).symm
  exact_mod_cast cast_eq

set_option maxHeartbeats 1000000 in
/-- **Absorption.**  Masses as data, with a distinguished core `S`: outside `S` every
subfamily mass equals the total mass (deleting a web-free pad does not change the web), and
the core budget is `∑_{i∈S}(2Mᵢ − M) ≤ B`.  If

  `9.9225 · (B + (k+2−|S|)·M) ≤ (k+2)²·M`

then the Lonely-Runner floor holds.  Since the left side grows linearly in `k` and the right
side quadratically, **every fixed core is absorbed for all sufficiently many pads**. -/
theorem absorption {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (M : ℝ) (hM0 : 0 < M)
    (hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = M)
    (Mi : Fin (k + 1) → ℝ)
    (hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i)
    (S : Finset (Fin (k + 1))) (B : ℝ) (hB0 : 0 ≤ B)
    (hpads : ∀ i ∉ S, Mi i = M)
    (hcoreB : (∑ i ∈ S, (2 * Mi i - M)) ≤ B)
    (hthr : 9.9225 * (B + (((k : ℝ) + 2) - S.card) * M) ≤ ((k : ℝ) + 2) ^ 2 * M) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- the pad bound: `∑ᵢ (2Mᵢ − M) ≤ X := B + (k+1−|S|)·M`
  have hScard : (S.card : ℝ) ≤ (k : ℝ) + 1 := by
    have h := Finset.card_le_univ S
    have h2 : (Fintype.card (Fin (k + 1)) : ℝ) = (k : ℝ) + 1 := by
      rw [Fintype.card_fin]; push_cast; ring
    calc (S.card : ℝ) ≤ (Fintype.card (Fin (k + 1)) : ℝ) := by exact_mod_cast h
      _ = (k : ℝ) + 1 := h2
  set X : ℝ := B + (((k : ℝ) + 1) - S.card) * M with hXdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0 : ℝ) ≤ (((k : ℝ) + 1) - S.card) * M :=
      mul_nonneg (by linarith [hScard]) hM0.le
    linarith
  have hSig : (∑ i, (2 * Mi i - M)) ≤ X := by
    have hsplit : (∑ i ∈ S, (2 * Mi i - M)) + (∑ i ∈ Sᶜ, (2 * Mi i - M))
        = ∑ i, (2 * Mi i - M) := Finset.sum_add_sum_compl S _
    have hcompl : (∑ i ∈ Sᶜ, (2 * Mi i - M)) = ((Sᶜ.card : ℝ)) * M := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_compl] at hi
        rw [hpads i hi]
        ring : ∀ i ∈ Sᶜ, (2 * Mi i - M) = M)]
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcc : (Sᶜ.card : ℝ) = ((k : ℝ) + 1) - S.card := by
      have h := Finset.card_compl S
      rw [h, Fintype.card_fin]
      have hle : S.card ≤ k + 1 := by
        have := Finset.card_le_univ S
        simpa [Finset.card_univ, Fintype.card_fin] using this
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [← hsplit, hcompl, hcc, hXdef]
    linarith [hcoreB]
  -- trigonometric frame at `δ = 1/(k+2)`
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hπδltpi : π * δ < π := by
    rw [hδdef]
    have h1 : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one hk2]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc π * (1 / ((k : ℝ) + 2)) < π * 1 := mul_lt_mul_of_pos_left h1 Real.pi_pos
      _ = π := mul_one π
  have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
  have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * δ)
    rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
  have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have h1pc : 2 - 2 * (π * δ) ^ 2 ≤ 1 + Real.cos (2 * π * δ) := by
    rw [show (1 : ℝ) + Real.cos (2 * π * δ) = 2 - (1 - Real.cos (2 * π * δ)) by ring, h1mc]
    nlinarith [hsq]
  -- the threshold delivers `(X+M)·(πδ)² < M`
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hδsq2 : (π * δ) ^ 2 * ((k : ℝ) + 2) ^ 2 = π ^ 2 := by
    rw [hδdef]
    field_simp
  have hXM0 : 0 < X + M := by linarith [hXnn, hM0]
  have hkey0 : (X + M) * π ^ 2 < ((k : ℝ) + 2) ^ 2 * M := by
    have hlt : (X + M) * π ^ 2 < (X + M) * 9.9225 :=
      mul_lt_mul_of_pos_left hπ2 hXM0
    have hXM_eq : X + M = B + (((k : ℝ) + 2) - S.card) * M := by
      rw [hXdef]; ring
    nlinarith [hlt, hthr, hXM_eq]
  have hXM : (X + M) * (π * δ) ^ 2 < M := by
    refine lt_of_mul_lt_mul_right ?_ (sq_nonneg ((k : ℝ) + 2))
    calc (X + M) * (π * δ) ^ 2 * ((k : ℝ) + 2) ^ 2
        = (X + M) * ((π * δ) ^ 2 * ((k : ℝ) + 2) ^ 2) := by ring
      _ = (X + M) * π ^ 2 := by rw [hδsq2]
      _ < ((k : ℝ) + 2) ^ 2 * M := hkey0
      _ = M * ((k : ℝ) + 2) ^ 2 := by ring
  -- assemble the sharp condition and conclude
  have hcond : (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
      < M * (1 + Real.cos (2 * π * δ)) := by
    calc (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
        ≤ X * (1 - Real.cos (2 * π * δ)) := mul_le_mul_of_nonneg_right hSig hcosnn
      _ = X * (2 * Real.sin (π * δ) ^ 2) := by rw [h1mc]
      _ ≤ X * (2 * (π * δ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hXnn
          nlinarith [hsq]
      _ < M * (2 - 2 * (π * δ) ^ 2) := by nlinarith [hXM]
      _ ≤ M * (1 + Real.cos (2 * π * δ)) := mul_le_mul_of_nonneg_left h1pc hM0.le
  exact riesz_union_markov v Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass hcond

set_option maxHeartbeats 1000000 in
/-- **The Bridge, two-relation slice, sharp threshold.**  Two disjoint support-`3` relations,
`k ≥ 11` (down from `k ≥ 19`), via the Markov union.  The mass is `M = 9Q/16` and
`∑(2Mᵢ − M) = (k+5)·M` exactly, so the condition is `(k+5)(1−c) < 1+c` at `δ = 1/(k+2)` —
which needs `π²(k+6) ≤ (k+2)²`, true from `k = 11` (`9.9225·17 = 168.68 ≤ 169`). -/
theorem bridge_two_relations_markov {k : ℕ} (hk : 11 ≤ k) (u : Fin (k + 1) → ℤ)
    (r s : Fin (k + 1) → ℤ) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1)
    (hsmem : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hrel_r : (∑ i, r i * u i) = 0) (hrel_s : (∑ i, s i * u i) = 0)
    (hdisj : ∀ i, r i = 0 ∨ s i = 0)
    (hchar2 : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        ∃ α β : ℤ, (α = -1 ∨ α = 0 ∨ α = 1) ∧ (β = -1 ∨ β = 0 ∨ β = 1) ∧
          c = fun i => α * r i + β * s i)
    (hsupp_r : (Finset.univ.filter (fun i => r i ≠ 0)).card = 3)
    (hsupp_s : (Finset.univ.filter (fun i => s i ≠ 0)).card = 3) :
    1 / ((k : ℝ) + 2) ≤ ML u := by
  set Q : ℕ := (∑ i, (u i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (u i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hPr : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) = -1 / 8 := by
    have hthis : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => r i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]; apply Finset.prod_congr rfl
      intro i _; by_cases h : r i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp_r]; norm_num
  have hPs : (∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2)) = -1 / 8 := by
    have hthis : (∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => s i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]; apply Finset.prod_congr rfl
      intro i _; by_cases h : s i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp_s]; norm_num
  set M : ℝ := (Q : ℝ) * ((1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
                        * (1 + 2 * ∏ i, (if s i = 0 then (1 : ℝ) else -1 / 2))) with hMdef
  have hMval : M = (Q : ℝ) * 9 / 16 := by rw [hMdef, hPr, hPs]; ring
  have hM0 : 0 < M := by rw [hMval]; positivity
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_two_relations_real (k + 1) u Q hQ0 hQsum r s hr0 hs0 hrmem hsmem hrel_r hrel_s
      hdisj hchar2
  set Mi : Fin (k + 1) → ℝ := fun i => if r i = 0 ∧ s i = 0 then M else (Q : ℝ) * 3 / 4 with hMidef
  have hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (u (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i := by
    intro i
    have hv'sum : (∑ j', (u (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (u (i.succAbove j')).natAbs) ≤ ∑ w, (u w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (u w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    simp only [hMidef]
    by_cases hboth : r i = 0 ∧ s i = 0
    · rw [if_pos hboth]
      obtain ⟨hri, hsi⟩ := hboth
      have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
        intro hcon; apply hr0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hri
        · exact congrFun hcon j'
      have hs'0 : (fun j' => s (i.succAbove j')) ≠ 0 := by
        intro hcon; apply hs0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hsi
        · exact congrFun hcon j'
      have hrelr' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
        rw [hri, zero_mul, zero_add] at h; rw [← h]; exact hrel_r
      have hrels' : (∑ j', s (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => s w * u w) i
        rw [hsi, zero_mul, zero_add] at h; rw [← h]; exact hrel_s
      rw [riesz_mass_two_relations_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) (fun j' => s (i.succAbove j')) hr'0 hs'0
        (fun j' => hrmem _) (fun j' => hsmem _) hrelr' hrels' (fun j' => hdisj _)
        (subfamily2_two u r s hchar2 i)]
      have hPr_sub : (∏ j', (if r (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
          = ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) := by
        rw [Fin.prod_univ_succAbove (fun w => if r w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hri,
          one_mul]
      have hPs_sub : (∏ j', (if s (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
          = ∏ w, (if s w = 0 then (1 : ℝ) else -1 / 2) := by
        rw [Fin.prod_univ_succAbove (fun w => if s w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hsi,
          one_mul]
      rw [hMdef, hPr_sub, hPs_sub]
    · rw [if_neg hboth]
      by_cases hri : r i = 0
      · have hsi : s i ≠ 0 := fun h => hboth ⟨hri, h⟩
        have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
          intro hcon; apply hr0; funext w
          refine Fin.succAboveCases i ?_ (fun j' => ?_) w
          · exact hri
          · exact congrFun hcon j'
        have hrelr' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
          have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
          rw [hri, zero_mul, zero_add] at h; rw [← h]; exact hrel_r
        rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
          (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrelr'
          (subfamily2_single_s u r s hdisj hchar2 i hsi)]
        have hPr_sub : (∏ j', (if r (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
            = ∏ w, (if r w = 0 then (1 : ℝ) else -1 / 2) := by
          rw [Fin.prod_univ_succAbove (fun w => if r w = 0 then (1 : ℝ) else -1 / 2) i,
            if_pos hri, one_mul]
        rw [hPr_sub, hPr]; ring
      · have hsi : s i = 0 := (hdisj i).resolve_left hri
        have hs'0 : (fun j' => s (i.succAbove j')) ≠ 0 := by
          intro hcon; apply hs0; funext w
          refine Fin.succAboveCases i ?_ (fun j' => ?_) w
          · exact hsi
          · exact congrFun hcon j'
        have hrels' : (∑ j', s (i.succAbove j') * u (i.succAbove j')) = 0 := by
          have h := Fin.sum_univ_succAbove (fun w => s w * u w) i
          rw [hsi, zero_mul, zero_add] at h; rw [← h]; exact hrel_s
        rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
          (fun j' => s (i.succAbove j')) hs'0 (fun j' => hsmem _) hrels'
          (subfamily2_single_r u r s hdisj hchar2 i hri)]
        have hPs_sub : (∏ j', (if s (i.succAbove j') = 0 then (1 : ℝ) else -1 / 2))
            = ∏ w, (if s w = 0 then (1 : ℝ) else -1 / 2) := by
          rw [Fin.prod_univ_succAbove (fun w => if s w = 0 then (1 : ℝ) else -1 / 2) i,
            if_pos hsi, one_mul]
        rw [hPs_sub, hPs]; ring
  -- the support cards
  have hcard_np : (Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0))).card = 6 := by
    have heq : (Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0)))
        = (Finset.univ.filter (fun i => r i ≠ 0)) ∪ (Finset.univ.filter (fun i => s i ≠ 0)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_and_or]
    rw [heq, Finset.card_union_of_disjoint, hsupp_r, hsupp_s]
    rw [Finset.disjoint_left]
    intro i hir his
    rw [Finset.mem_filter] at hir his
    rcases hdisj i with h | h
    · exact hir.2 h
    · exact his.2 h
  have hcard_p : (Finset.univ.filter (fun i => r i = 0 ∧ s i = 0)).card = k - 5 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0 ∧ s i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  -- `∑ (2Mᵢ − M) = (k+5)·M` exactly
  have hSigEq : (∑ i, (2 * Mi i - M)) = ((k : ℝ) + 5) * M := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => r i = 0 ∧ s i = 0) (fun i => 2 * Mi i - M)
    have h1 : (∑ i ∈ Finset.univ.filter (fun i => r i = 0 ∧ s i = 0), (2 * Mi i - M))
        = ((k - 5 : ℕ) : ℝ) * M := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_filter] at hi
        simp only [hMidef, if_pos hi.2]
        ring : ∀ i ∈ Finset.univ.filter (fun i => r i = 0 ∧ s i = 0),
          (2 * Mi i - M) = M)]
      rw [Finset.sum_const, hcard_p, nsmul_eq_mul]
    have h2 : (∑ i ∈ Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0)), (2 * Mi i - M))
        = 6 * ((Q : ℝ) * 3 / 2 - M) := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_filter] at hi
        simp only [hMidef, if_neg hi.2]
        ring : ∀ i ∈ Finset.univ.filter (fun i => ¬ (r i = 0 ∧ s i = 0)),
          (2 * Mi i - M) = (Q : ℝ) * 3 / 2 - M)]
      rw [Finset.sum_const, hcard_np, nsmul_eq_mul]
      norm_num
    have hks5 : ((k - 5 : ℕ) : ℝ) = (k : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega : 5 ≤ k)]
      push_cast
      ring
    rw [← hsplit, h1, h2, hks5, hMval]
    ring
  -- the sharp key at `δ = 1/(k+2)`
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (11 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  have hkey : ((k : ℝ) + 5) * (1 - Real.cos (2 * π * δ)) < 1 + Real.cos (2 * π * δ) := by
    have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
    have hπδltpi : π * δ < π := by
      rw [hδdef]
      have h1 : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
        rw [div_lt_one hk2]; linarith
      calc π * (1 / ((k : ℝ) + 2)) < π * 1 := mul_lt_mul_of_pos_left h1 Real.pi_pos
        _ = π := mul_one π
    have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
    have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
      have hpy := Real.sin_sq_add_cos_sq (π * δ)
      rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
    have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hδsq : (π * δ) ^ 2 = π ^ 2 / ((k : ℝ) + 2) ^ 2 := by
      rw [hδdef, mul_pow, div_pow, one_pow]
      ring
    have hbudget : ((k : ℝ) + 6) * (π * δ) ^ 2 ≤ 1 := by
      rw [hδsq, ← mul_div_assoc,
        div_le_one (by positivity : (0:ℝ) < ((k : ℝ) + 2) ^ 2)]
      nlinarith [hkR, sq_nonneg ((k : ℝ) - 11),
        mul_lt_mul_of_pos_left hπ2 (show (0:ℝ) < (k : ℝ) + 6 by linarith)]
    have h1pc : 2 - 2 * (π * δ) ^ 2 ≤ 1 + Real.cos (2 * π * δ) := by
      rw [show (1 : ℝ) + Real.cos (2 * π * δ) = 2 - (1 - Real.cos (2 * π * δ)) by ring, h1mc]
      nlinarith [hsq]
    calc ((k : ℝ) + 5) * (1 - Real.cos (2 * π * δ))
        = ((k : ℝ) + 5) * (2 * Real.sin (π * δ) ^ 2) := by rw [h1mc]
      _ < ((k : ℝ) + 5) * (2 * (π * δ) ^ 2) := by
          apply mul_lt_mul_of_pos_left _ (by positivity); linarith [hsq]
      _ ≤ 2 - 2 * (π * δ) ^ 2 := by nlinarith [hbudget]
      _ ≤ 1 + Real.cos (2 * π * δ) := h1pc
  have hcond : (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
      < M * (1 + Real.cos (2 * π * δ)) := by
    rw [hSigEq]
    calc ((k : ℝ) + 5) * M * (1 - Real.cos (2 * π * δ))
        = M * (((k : ℝ) + 5) * (1 - Real.cos (2 * π * δ))) := by ring
      _ < M * (1 + Real.cos (2 * π * δ)) := mul_lt_mul_of_pos_left hkey hM0
  exact riesz_union_markov u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass hcond

end LRSpectrumFull
