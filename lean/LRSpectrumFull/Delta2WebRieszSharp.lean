/-
# The Markov-sharpened Riesz union, and the single-relation Bridge at `k ≥ 10`

`riesz_union_general` bounds the bad weight of runner `i` by `(1 − cos 2πδ)·Mᵢ` — the crude
cap by the full subfamily mass.  The subfamily weight is in fact almost *unbiased* against its
missing runner: the exact first moment is `∑_j cos θᵢ(j)·Pᵢ(j) = Mᵢ − M`, an identity, not an
estimate, because `P = (1 − cos θᵢ)·Pᵢ` pointwise.  Markov's inequality applied to the
nonnegative weight `1 + cos θᵢ` then caps the bad set's subfamily weight at `(2Mᵢ − M)/(1+c)`,
sharpening the union condition from `(∑Mᵢ)(1−c) < M` to

    `(∑ (2Mᵢ − M))·(1 − c) < M·(1 + c)`,   `c = cos 2πδ`.

`riesz_union_markov` proves this, division-free.  Consequence: `bridge_single_relation_any_sharp` —
every `(k+1)`-runner tuple, `k ≥ 10`, whose only vanishing `{−1,0,1}`-combinations are `{0, ±r}`
for a single relation of any support `s ≥ 2`, satisfies the Lonely-Runner floor `1/(k+2) ≤ ML`.
The budget reduces to the same `s·Q ≤ (s+1)·M` as the weak case, and the escape parameter is
`δ = 1/(k+2)` itself — no square root.  At `k = 10` (eleven moving runners, support `3`) the
certificate is exact algebra: `13·(2 − √3) < 2 + √3 ⟺ 576 < 588`.
-/
import LRSpectrumFull.Delta2RieszBound

namespace LRSpectrumFull

open Real

set_option maxHeartbeats 1000000 in
/-- **Markov-sharpened first-moment Riesz bound.**  Same data as `riesz_union_general`, with the
condition sharpened to `(∑ (2Mᵢ − M))·(1 − cos 2πδ) < M·(1 + cos 2πδ)`.  The gain is the exact
unbiasedness `∑_j cos θᵢ·Pᵢ = Mᵢ − M` (an identity), which Markov on the nonnegative weight
`1 + cos θᵢ` converts into the cap `∑_{bad_i} Pᵢ ≤ (2Mᵢ − M)/(1 + c)`. -/
theorem riesz_union_markov {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℝ)
    (hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = M)
    (Mi : Fin (k + 1) → ℝ)
    (hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i)
    (hcond : (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
        < M * (1 + Real.cos (2 * π * δ))) :
    δ ≤ ML v := by
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hcos1p : 0 ≤ 1 + Real.cos (2 * π * δ) := by
    have := Real.neg_one_le_cos (2 * π * δ); linarith
  -- the sharpened per-runner bound, division-free:
  -- (∑_{bad_i} R)·(1+c) ≤ (1−c)·(2Mᵢ − M)
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          * (1 + Real.cos (2 * π * δ))
        ≤ (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hsubnn : ∀ j : ℕ, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    -- rewrite the runner's cosine through the nearest-integer distance (ground instance)
    have hcs : ∀ j : ℕ, Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
        = Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
          = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring]
      exact cos_two_pi_nid _
    -- on the bad set the runner's cosine is at least `cos 2πδ`
    have hcosle : ∀ j ∈ (Finset.range Q).filter
        (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
        Real.cos (2 * π * δ)
          ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact Real.cos_le_cos_of_nonneg_of_le_pi
        (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
        (by nlinarith [Real.pi_pos, hδ2])
        (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
    -- (a) the bad weight is controlled by the bad subfamily weight
    have ha : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [hRsplit j]
      refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
      rw [hcs j]
      have := hcosle j hj
      linarith
    -- (b) Markov: the bad subfamily weight, times `1+c`, is at most `2Mᵢ − M`
    have hb : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ))
        ≤ 2 * Mi i - M := by
      have hb1 : (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ))
          ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        rw [hcs j]
        have h1c : (1 : ℝ) + Real.cos (2 * π * δ)
            ≤ 1 + Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := by
          linarith [hcosle j hj]
        nlinarith [mul_le_mul_of_nonneg_left h1c (hsubnn j)]
      have hb2 : (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          ≤ ∑ j ∈ Finset.range Q,
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => ?_)
        have h1 : -1 ≤ Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)) :=
          Real.neg_one_le_cos _
        exact mul_nonneg (by linarith [h1]) (hsubnn j)
      have hb3 : (∑ j ∈ Finset.range Q,
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          = 2 * Mi i - M := by
        have hterm : ∀ j : ℕ,
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))
            = 2 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
              - R j := fun j => by
          rw [hRsplit j]; ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
          ← Finset.mul_sum, hsubmass i, hmass]
      calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ))
          ≤ ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := hb1
        _ ≤ ∑ j ∈ Finset.range Q,
            (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
              * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := hb2
        _ = 2 * Mi i - M := hb3
    -- combine (a) and (b)
    calc (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          * (1 + Real.cos (2 * π * δ))
        ≤ ((1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right ha hcos1p
      _ = (1 - Real.cos (2 * π * δ)) * ((∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ))) := by ring
      _ ≤ (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) :=
          mul_le_mul_of_nonneg_left hb hcosδ
  -- a good grid point exists
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
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ
                then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : M * (1 + Real.cos (2 * π * δ))
        ≤ (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ)) := by
      calc M * (1 + Real.cos (2 * π * δ))
          = (∑ j ∈ Finset.range Q, R j) * (1 + Real.cos (2 * π * δ)) := by rw [hmass]
        _ ≤ (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
              * (1 + Real.cos (2 * π * δ)) :=
            mul_le_mul_of_nonneg_right hcover hcos1p
        _ = ∑ i : Fin (k + 1), (∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
              * (1 + Real.cos (2 * π * δ)) := Finset.sum_mul _ _ _
        _ ≤ ∑ i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ)) := by
            rw [← Finset.mul_sum]; ring
    linarith [hfinal, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

set_option maxHeartbeats 1000000 in
/-- **The Bridge, single-relation slice, sharp threshold.**  Every `(k+1)`-runner tuple with
`k ≥ 10` whose only vanishing `{−1,0,1}`-combinations are `{0, ±r}` — one relation, any support
`s ≥ 2` — satisfies the Lonely-Runner floor `1/(k+2) ≤ ML u`.  Improves `k ≥ 18` of
`bridge_single_relation_any` via `riesz_union_markov`; the escape parameter is `δ = 1/(k+2)`
itself, and the sharp budget `∑(2Mᵢ − M) ≤ (k+3)·M` reduces to the same `s·Q ≤ (s+1)·M`. -/
theorem bridge_single_relation_any_sharp {k s : ℕ} (hk : 10 ≤ k) (hs : 2 ≤ s)
    (u : Fin (k + 1) → ℤ)
    (r : Fin (k + 1) → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * u i) = 0)
    (hchar : ∀ c : Fin (k + 1) → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (hsupp : (Finset.univ.filter (fun i => r i ≠ 0)).card = s) :
    1 / ((k : ℝ) + 2) ≤ ML u := by
  set Q : ℕ := (∑ i, (u i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (u i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hP : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) = (-1 / 2 : ℝ) ^ s := by
    have hthis : (∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2))
        = ∏ _i ∈ Finset.univ.filter (fun i => r i ≠ 0), (-1 / 2 : ℝ) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _; by_cases h : r i = 0 <;> simp [h]
    rw [hthis, Finset.prod_const, hsupp]
  set M : ℝ := (Q : ℝ) * (1 + 2 * ∏ i, (if r i = 0 then (1 : ℝ) else -1 / 2)) with hMdef
  -- mass positivity and the budget, by parity
  have hMlow : (1 : ℝ) / 2 ≤ 1 + 2 * (-1 / 2 : ℝ) ^ s := by
    rcases Nat.even_or_odd s with he | ho
    · have hop : (-1 / 2 : ℝ) ^ s = (1 / 2 : ℝ) ^ s := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Even.neg_pow he _
      have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s := by positivity
      rw [hop]; linarith
    · have hs3 : 3 ≤ s := by obtain ⟨t, ht⟩ := ho; omega
      have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow ho _
      have habs : (1 / 2 : ℝ) ^ s ≤ (1 / 2 : ℝ) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hs3
      rw [hop]; nlinarith [habs]
  have hM0 : 0 < M := by
    rw [hMdef, hP]
    exact mul_pos hQR (by linarith [hMlow])
  have hnat : ∀ n, 3 ≤ n → 2 * (n + 1) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega
  have hsQM : (s : ℝ) * (Q : ℝ) ≤ ((s : ℝ) + 1) * M := by
    rcases Nat.even_or_odd s with heven | hodd
    · -- even support: the mass inflates, `M ≥ Q`
      have hop : (-1 / 2 : ℝ) ^ s = (1 / 2 : ℝ) ^ s := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Even.neg_pow heven _
      have hMQ : (Q : ℝ) ≤ M := by
        rw [hMdef, hP, hop]
        nlinarith [hQR, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) s]
      have hsR : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      nlinarith [hMQ, hM0, hsR]
    · -- odd support: `s ≥ 3` and the exponential lever `2(s+1) ≤ 2^s`
      have hs3 : 3 ≤ s := by obtain ⟨t, ht⟩ := hodd; omega
      rw [hMdef, hP]
      have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow hodd _
      have hpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      have hnatR : (2 : ℝ) * ((s : ℝ) + 1) ≤ (2 : ℝ) ^ s := by exact_mod_cast hnat s hs3
      have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by rw [div_pow, one_pow]
      have hfrac : ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s)) ≤ 1 := by
        rw [show ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s))
            = (2 * ((s : ℝ) + 1)) / (2 : ℝ) ^ s by ring, div_le_one hpos]
        exact hnatR
      rw [hop, hhalf]
      nlinarith [hfrac, hQR]
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_single_relation_real (k + 1) u Q hQ0 hQsum r hr0 hrmem hrel hchar
  set Mi : Fin (k + 1) → ℝ := fun i => if r i = 0 then M else (Q : ℝ) with hMidef
  have hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
      (1 - Real.cos (2 * π * (u (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i := by
    intro i
    have hv'sum : (∑ j', (u (i.succAbove j')).natAbs) < Q := by
      have hle : (∑ j', (u (i.succAbove j')).natAbs) ≤ ∑ w, (u w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (u w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    simp only [hMidef]
    by_cases hri : r i = 0
    · rw [if_pos hri]
      have hr'0 : (fun j' => r (i.succAbove j')) ≠ 0 := by
        intro hr'
        apply hr0; funext w
        refine Fin.succAboveCases i ?_ (fun j' => ?_) w
        · exact hri
        · exact congrFun hr' j'
      have hrel' : (∑ j', r (i.succAbove j') * u (i.succAbove j')) = 0 := by
        have h := Fin.sum_univ_succAbove (fun w => r w * u w) i
        rw [hri, zero_mul, zero_add] at h
        rw [← h]; exact hrel
      rw [riesz_mass_single_relation_real k (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrel'
        (subfamily_hchar u r hchar i hri)]
      rw [hMdef]
      congr 2
      rw [Fin.prod_univ_succAbove (fun w => (if r w = 0 then (1 : ℝ) else -1 / 2)) i, if_pos hri,
        one_mul]
    · rw [if_neg hri]
      exact riesz_mass_real k (fun j' => u (i.succAbove j'))
        (subfamily_strongFree u r hchar i hri) Q hQ0 hv'sum
  -- the sharp budget: `∑ (2Mᵢ − M) ≤ (k+3)·M`, reduced to `s·Q ≤ (s+1)·M`
  have hsumSharp : (∑ i, (2 * Mi i - M)) ≤ ((k : ℝ) + 3) * M := by
    have hcard2 : (Finset.univ.filter (fun i => r i = 0)).card = k + 1 - s := by
      have hc := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hss : (Finset.univ.filter (fun i => ¬ r i = 0)).card = s := hsupp
      omega
    have hsk1 : s ≤ k + 1 := by
      rw [← hsupp]
      calc (Finset.univ.filter (fun i => r i ≠ 0)).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k + 1 := by simp [Finset.card_univ]
    have hMiSum : (∑ i, Mi i) = ((k : ℝ) + 1 - (s : ℝ)) * M + (s : ℝ) * (Q : ℝ) := by
      simp only [hMidef]
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
      rw [hcard2, show (Finset.univ.filter (fun i => ¬ r i = 0)).card = s from hsupp]
      have hks : ((k + 1 - s : ℕ) : ℝ) = (k : ℝ) + 1 - (s : ℝ) := by
        rw [Nat.cast_sub hsk1]; push_cast; ring
      rw [hks]
    have hsum2 : (∑ i, (2 * Mi i - M)) = 2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [hsum2, hMiSum]
    nlinarith [hsQM]
  -- the escape parameter is the floor itself
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hkR : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hπδpos : 0 < π * δ := mul_pos Real.pi_pos hδ0
  -- the sharp key: `(k+3)(1 − cos 2πδ) < 1 + cos 2πδ` at `δ = 1/(k+2)`, `k ≥ 10`
  have hkey : ((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ)) < 1 + Real.cos (2 * π * δ) := by
    have hsin : Real.sin (π * δ) < π * δ := Real.sin_lt hπδpos
    have hπδltpi : π * δ < π := by
      rw [hδdef]
      have h1 : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      calc π * (1 / ((k : ℝ) + 2)) < π * 1 := by
            exact mul_lt_mul_of_pos_left h1 Real.pi_pos
        _ = π := mul_one π
    have hsinpos : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
    have h1mc : 1 - Real.cos (2 * π * δ) = 2 * Real.sin (π * δ) ^ 2 := by
      have hpy := Real.sin_sq_add_cos_sq (π * δ)
      rw [show 2 * π * δ = 2 * (π * δ) by ring, Real.cos_two_mul]; nlinarith [hpy]
    have hsq : Real.sin (π * δ) ^ 2 < (π * δ) ^ 2 := by nlinarith [hsin, hsinpos]
    -- `(πδ)² = π²/(k+2)²` and `π²(k+4) ≤ (k+2)²` for `k ≥ 10`
    have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hδsq : (π * δ) ^ 2 = π ^ 2 / ((k : ℝ) + 2) ^ 2 := by
      rw [hδdef, mul_pow, div_pow, one_pow]
      ring
    have hbudget : ((k : ℝ) + 4) * (π * δ) ^ 2 ≤ 1 := by
      rw [hδsq, ← mul_div_assoc,
        div_le_one (by positivity : (0:ℝ) < ((k : ℝ) + 2) ^ 2)]
      nlinarith [hπ2, hkR]
    have h1pc : 2 - 2 * (π * δ) ^ 2 ≤ 1 + Real.cos (2 * π * δ) := by
      rw [show (1 : ℝ) + Real.cos (2 * π * δ) = 2 - (1 - Real.cos (2 * π * δ)) by ring, h1mc]
      nlinarith [hsq]
    calc ((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ))
        = ((k : ℝ) + 3) * (2 * Real.sin (π * δ) ^ 2) := by rw [h1mc]
      _ < ((k : ℝ) + 3) * (2 * (π * δ) ^ 2) := by
          apply mul_lt_mul_of_pos_left _ (by positivity); linarith [hsq]
      _ ≤ 2 - 2 * (π * δ) ^ 2 := by nlinarith [hbudget]
      _ ≤ 1 + Real.cos (2 * π * δ) := h1pc
  have hcond : (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
      < M * (1 + Real.cos (2 * π * δ)) := by
    have hcosnn : 0 ≤ 1 - Real.cos (2 * π * δ) := by
      have := Real.cos_le_one (2 * π * δ); linarith
    calc (∑ i, (2 * Mi i - M)) * (1 - Real.cos (2 * π * δ))
        ≤ ((k : ℝ) + 3) * M * (1 - Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right hsumSharp hcosnn
      _ = M * (((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ))) := by ring
      _ < M * (1 + Real.cos (2 * π * δ)) := by
          exact mul_lt_mul_of_pos_left hkey hM0
  exact riesz_union_markov u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass hcond

end LRSpectrumFull
