/-
# Separation over the `StrongFree` spectrum: the corrected reduction

`separation_of_riesz` demanded the *sharp* constant `√2/3` uniformly.  The
first-moment Riesz bound (arXiv:2511.16636, Lemma 4.1) misses it by a fixed factor
`3/(2π) ≈ 0.477` — a permanent, not asymptotically-vanishing, shortfall.  But the
sharp constant was never the real target: Separation asks only for the floor
`1/(k+2)`, and the *proven* first-moment bound `riesz_clears_floor` already clears
that for every `k ≥ 17`.  The genuinely open content is therefore a **finite
window** — and after the bases, the `k = 1, 2` rungs, and the sharp first moment
below (which clears every `k ≥ 8`), only `3 ≤ k ≤ 7`: five sizes, all in the
classical literature.

The free class here is `StrongFree` — the exact class the Riesz bound handles —
rather than the strictly weaker `¬HasPM1RelationN` used by `ladder`.  The gap
between the two is real: `(1,2,3)` has no proper-support relation yet is not
`StrongFree` (`1+2−3 = 0` is full-support), so `riesz_clears_floor` cannot bound
it at any `k`.  Such configs belong to the strengthened bridge `RelationBridgeSF`.

The `UniversalQED` glue lives in `Delta2SeparationSummit` (its import closure is
heavier); this file is self-contained over the Riesz/loneliness core.
-/
import LRSpectrumFull.Delta2RieszBound
import LRSpectrumFull.LonelyRunner3
import LRSpectrumFull.TripleNormalize
import LRSpectrumFull.TwoRunnerBound

namespace LRSpectrumFull

open Real (pi)
local notation "π" => Real.pi

/-- The strongly-free spectrum at `k+1` runners — the exact class Riesz bounds. -/
def freeSpectrumSF (k : ℕ) : Set ℝ :=
  {x | ∃ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) ∧ StrongFree v ∧ ML v = x}

/-- Its infimum: the strongly-free threshold ladder. -/
noncomputable def ladderSF (k : ℕ) : ℝ := sInf (freeSpectrumSF k)

theorem freeSpectrumSF_bddBelow (k : ℕ) : BddBelow (freeSpectrumSF k) := by
  refine ⟨0, ?_⟩
  rintro x ⟨v, _, _, rfl⟩
  calc (0 : ℝ) ≤ gap v 0 := gap_nonneg v 0
    _ ≤ ML v := le_csSup (bddAbove_range_gap v) ⟨0, rfl⟩

/-- Every strongly-free family bounds its ladder from above. -/
theorem ladderSF_le {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hSF : StrongFree v) : ladderSF k ≤ ML v :=
  csInf_le (freeSpectrumSF_bddBelow k) ⟨v, hv, hSF, rfl⟩

/-- **The strengthened bridge.**  Any positive family that is *not* strongly free —
i.e. carries a `±1` relation of any support, full or proper — meets its Lonely-Runner
floor.  This absorbs the full-support-relation configs that the old
`HasPM1RelationN` partition stranded on the free side. -/
def RelationBridgeSF : Prop :=
  ∀ k : ℕ, ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
    1 / ((k : ℝ) + 2) ≤ ML v

/-- **Separation reduced to a finite strongly-free window.**  Given the trivial
single-runner base, nonemptiness, and the floor on strongly-free families for the
finitely many sizes `1 ≤ k ≤ 16`, the strongly-free ladder clears `1/(n+2)` at every
level — the tail `n ≥ 17` supplied *unconditionally* by the proven
`riesz_clears_floor`.  This is the honest state of Separation: the only open
analytic content is the finite window. -/
theorem separationSF_of_window
    (hbase : 1 / ((0 : ℝ) + 2) ≤ ladderSF 0)
    (hne : ∀ n, (freeSpectrumSF n).Nonempty)
    (hwin : ∀ k : ℕ, 1 ≤ k → k ≤ 16 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
        StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n := by
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simpa using hbase
  · apply le_csInf (hne n)
    rintro x ⟨v, hv, hSF, rfl⟩
    by_cases hle : n ≤ 16
    · exact hwin n h0 hle v hv hSF
    · exact riesz_clears_floor (by omega : 17 ≤ n) v hSF

/-! ### Instantiating the base, the witnesses, and the first window rungs

Everything below discharges hypotheses of `separationSF_of_window` from
in-project material: powers of two give nonemptiness at every size, the
single-runner base is exact (`ML = 1/2` at `t = 1/(2v)`), and the window
rungs `k = 1, 2` are the two- and three-runner Lonely Runner theorems
already banked (`D_two_le`, `lonely_runner_three`).  What remains open is
`StrongFreeWindow` (the rungs `3 ≤ k ≤ 16`). -/

/-- **Powers of two are strongly free**: a vanishing `{−1,0,1}`-combination of
`1, 2, 4, …` is identically zero — the mod-2 digit argument, by induction. -/
theorem strongFree_two_pow (k : ℕ) :
    StrongFree (fun i : Fin k => (2 : ℤ) ^ (i : ℕ)) := by
  induction k with
  | zero => intro c _ _ i; exact i.elim0
  | succ k ih =>
    intro c hc hsum
    set S : ℤ := ∑ i : Fin k, c i.succ * 2 ^ (i : ℕ) with hS
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ] at hsum
    have hrw : ∑ i : Fin k, c i.succ * ((2 : ℤ) ^ (i : ℕ) * 2) = 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw] at hsum
    have h0 : c 0 = 0 := by rcases hc 0 with h | h | h <;> omega
    have hS0 : ∑ i : Fin k, c i.succ * (2 : ℤ) ^ (i : ℕ) = 0 := by
      rw [← hS]; omega
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h0
    · exact ih (fun i => c i.succ) (fun i => hc i.succ) hS0 j

/-- The powers-of-two family witnesses the strongly-free spectrum at every
size. -/
theorem freeSpectrumSF_nonempty (n : ℕ) : (freeSpectrumSF n).Nonempty :=
  ⟨ML (fun i : Fin (n + 1) => (2 : ℤ) ^ (i : ℕ)),
    fun i : Fin (n + 1) => (2 : ℤ) ^ (i : ℕ), fun i => pow_pos (by norm_num) _,
    strongFree_two_pow (n + 1), rfl⟩

/-- **The single-runner base**: one positive runner reaches distance exactly
`1/2` at time `1/(2v)`, so the strongly-free ladder starts at `1/2`. -/
theorem ladderSF_base : 1 / ((0 : ℝ) + 2) ≤ ladderSF 0 := by
  apply le_csInf (freeSpectrumSF_nonempty 0)
  rintro x ⟨v, hv, _, rfl⟩
  have hv0 : (0 : ℝ) < (v 0 : ℝ) := by exact_mod_cast hv 0
  have hhalf : nearestIntDist ((1 : ℝ) / 2) = 1 / 2 := by
    have h := nearestIntDist_int_add_half 0
    rw [Int.cast_zero, zero_add] at h
    exact h
  have ht : (v 0 : ℝ) * (1 / (2 * (v 0 : ℝ))) = 1 / 2 := by
    rw [mul_one_div, div_eq_iff (by positivity : (2 : ℝ) * (v 0 : ℝ) ≠ 0)]
    ring
  have hgap : 1 / ((0 : ℝ) + 2) ≤ gap v (1 / (2 * (v 0 : ℝ))) := by
    apply le_gap
    intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    rw [ht, hhalf]
    norm_num
  exact le_trans hgap (le_csSup (bddAbove_range_gap v) ⟨_, rfl⟩)

/-- **The two-runner window rung** (`k = 1`): any two positive speeds meet the
`1/3` floor — `D_two_le`, no coprimality or attainment needed. -/
theorem window_rung_one (v : Fin 2 → ℤ) (hv : ∀ i, 0 < v i) :
    1 / 3 ≤ ML v := by
  have hD := D_two_le (v 0) (v 1) (ne_of_gt (hv 0)) (ne_of_gt (hv 1))
  have hveq : ![v 0, v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hveq] at hD
  unfold D at hD
  linarith

/-- **The open strongly-free window**: the Lonely-Runner floor for strongly
free families of `4`–`17` runners (`3 ≤ k ≤ 16`).  Every size outside this
window is machine-checked — `k = 0` is the base, `k = 1, 2` are the two- and
three-runner theorems, `k ≥ 17` is the Riesz tail. -/
def StrongFreeWindow : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ 16 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- **Separation from the open window alone.**  The base, the nonemptiness
witnesses, and the `k = 1, 2` rungs are discharged; the strongly-free ladder
clears the floor at every level given only the fourteen open window sizes. -/
theorem separationSF_of_strongFreeWindow (hwin : StrongFreeWindow) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n := by
  refine separationSF_of_window ladderSF_base freeSpectrumSF_nonempty ?_
  intro k hk1 hk16 v hv hSF
  by_cases h1 : k = 1
  · subst h1
    have h := window_rung_one v hv
    have hc : 1 / (((1 : ℕ) : ℝ) + 2) = 1 / 3 := by norm_num
    rw [hc]; exact h
  · by_cases h2 : k = 2
    · subst h2
      have h := lonely_runner_three v fun i => ne_of_gt (hv i)
      have hc : 1 / (((2 : ℕ) : ℝ) + 2) = 1 / 4 := by norm_num
      rw [hc]; exact h
    · exact hwin k (by omega) hk16 v hv hSF

/-! ### The sharp first moment: Markov on `1 + cos`

The first-moment budget bounded the bad set's *subfamily* weight by the full
subfamily mass `Q`.  But the subfamily weight is exactly *unbiased* against its
missing runner: `∑_j cos(2πv_i j/Q)·P_i(j) = M_i − M = 0` — both masses are `Q`
by dissociativity.  Markov's inequality on the nonnegative weight `1 + cos`
therefore caps the bad-set subfamily weight at `Q/(1 + cos 2πδ)`, replacing the
union condition `(k+1)(1−cos 2πδ) < 1` by `(k+1)(1−cos 2πδ) < 1 + cos 2πδ`,
i.e. `(k+2)(1−cos 2πδ) < 2` — an asymptotic constant `1/π` in place of
`1/(π√2)`.  With `1−cos x < x²/2` this clears the Lonely-Runner floor for every
`k + 2 > π²`, i.e. every `k ≥ 8` — nine of the fourteen open window rungs,
including the entire band `m = 14..17` that is open in the literature. -/

/-- **Sharp first-moment Riesz lower bound.**  For a dissociated `(k+1)`-family,
if `δ ≤ 1/2` and `(k+1)(1 − cos 2πδ) < 1 + cos 2πδ`, then `ML(v) ≥ δ`.  The
gain over `riesz_lower_bound` is the unbiasedness identity
`∑_j cos(2πv_i j/Q)·P_i(j) = 0`: the bad set, where `cos ≥ cos 2πδ`, can carry
at most a `1/(1 + cos 2πδ)` share of the subfamily weight. -/
theorem riesz_lower_bound_sharp {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : StrongFree v)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hcond : ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) < 1 + Real.cos (2 * π * δ)) :
    δ ≤ ML v := by
  set Q : ℕ := (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (v i).natAbs) < Q := Nat.lt_succ_self _
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hmass : ∑ j ∈ Finset.range Q, R j = (Q : ℝ) := riesz_mass_real (k + 1) v hv Q hQ0 hQsum
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hc1 : 0 < 1 + Real.cos (2 * π * δ) :=
    lt_of_le_of_lt (mul_nonneg (by positivity) hcosδ) hcond
  -- per-runner bound, sharpened: bad weight × (1+cos2πδ) ≤ (1−cos2πδ)·Q
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        * (1 + Real.cos (2 * π * δ))
        ≤ (1 - Real.cos (2 * π * δ)) * (Q : ℝ) := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hv'sum : (∑ j', (v' j').natAbs) < Q := by
      have hle : (∑ j', (v' j').natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    have hsubmass : ∑ j ∈ Finset.range Q,
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
      riesz_mass_real k v' (strongFree_succAbove v hv i) Q hQ0 hv'sum
    have hsubnn : ∀ j, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    -- the unbiasedness mass identity: ∑ (1 + cosᵢ)·Pᵢ = 2Mᵢ − M = Q
    have hplus : ∑ j ∈ Finset.range Q,
        (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
          * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        = (Q : ℝ) := by
      have hsplit : ∀ j : ℕ,
          (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
            * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          = 2 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - R j := by
        intro j; rw [hRsplit j]; ring
      calc (∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))))
          = ∑ j ∈ Finset.range Q,
              (2 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                - R j) := Finset.sum_congr rfl fun j _ => hsplit j
        _ = 2 * (∑ j ∈ Finset.range Q,
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - ∑ j ∈ Finset.range Q, R j := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = 2 * (Q : ℝ) - (Q : ℝ) := by rw [hsubmass, hmass]
        _ = (Q : ℝ) := by ring
    -- Markov: the bad set carries ≤ Q/(1+cos2πδ) of the subfamily weight
    have hfilter : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        * (1 + Real.cos (2 * π * δ)) ≤ (Q : ℝ) := by
      calc (∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ))
          = ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                * (1 + Real.cos (2 * π * δ)) := by rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_filter] at hj
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
            have hrw2 : Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
                = Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := by
              rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
                  = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
            have hcosle : Real.cos (2 * π * δ)
                ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
              Real.cos_le_cos_of_nonneg_of_le_pi
                (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
                (by nlinarith [Real.pi_pos, hδ2])
                (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
            rw [hrw2]; linarith
        _ ≤ ∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun j _ _ => mul_nonneg ?_ (hsubnn j))
            have := Real.neg_one_le_cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
            linarith
        _ = (Q : ℝ) := hplus
    -- the crude factor bound on the bad set, kept in filtered form
    have hbad : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
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
    -- chain: bad·(1+c) ≤ (1−c)·(∑fil P)·(1+c) ≤ (1−c)·Q
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          * (1 + Real.cos (2 * π * δ))
        ≤ ((1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right hbad hc1.le
      _ = (1 - Real.cos (2 * π * δ)) * ((∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ))) := by ring
      _ ≤ (1 - Real.cos (2 * π * δ)) * (Q : ℝ) :=
          mul_le_mul_of_nonneg_left hfilter hcosδ
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
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : (Q : ℝ) * (1 + Real.cos (2 * π * δ))
        ≤ ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (Q : ℝ)) := by
      calc (Q : ℝ) * (1 + Real.cos (2 * π * δ))
          = (∑ j ∈ Finset.range Q, R j) * (1 + Real.cos (2 * π * δ)) := by rw [hmass]
        _ ≤ (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ)) :=
            mul_le_mul_of_nonneg_right hcover hc1.le
        _ = ∑ i : Fin (k + 1), ((∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ))) := by rw [Finset.sum_mul]
        _ ≤ ∑ _i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * (Q : ℝ) :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (Q : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
    have hlt : ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (Q : ℝ))
        < (1 + Real.cos (2 * π * δ)) * (Q : ℝ) := by
      have := mul_lt_mul_of_pos_right hcond hQR
      nlinarith [this]
    nlinarith [hfinal, hlt]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

/-- **The floor for every dissociated family of at least nine velocities.**
`(k+2)(1 − cos(2π/(k+2))) < 2` as soon as `k + 2 > π²`, i.e. `k ≥ 8`, by
`1 − cos x < x²/2`.  Nine of the fourteen open window rungs close here,
including all of `m = 14..17`. -/
theorem riesz_clears_floor_sharp {k : ℕ} (hk : 8 ≤ k) (v : Fin (k + 1) → ℤ)
    (hv : StrongFree v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  have hkR : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ10 : δ ≤ 1 / 10 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by
    rw [hδdef]; field_simp
  refine riesz_lower_bound_sharp v hv δ hδ0 hδ2 ?_
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
  have hkey : ((k : ℝ) + 2) * (1 - Real.cos (2 * π * δ)) < 2 := by
    have h1 : ((k : ℝ) + 2) * (1 - Real.cos (2 * π * δ))
        < ((k : ℝ) + 2) * (2 * (π * δ) ^ 2) :=
      mul_lt_mul_of_pos_left hu (by linarith)
    have h2 : ((k : ℝ) + 2) * (2 * (π * δ) ^ 2)
        = 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 2)) := by ring
    rw [h2, hδval, mul_one] at h1
    have h3 : 2 * π ^ 2 * δ ≤ 2 * π ^ 2 * (1 / 10) := by
      refine mul_le_mul_of_nonneg_left hδ10 ?_
      positivity
    nlinarith [hπ2]
  have hcosu : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  nlinarith [hkey, hcosu]

/-- **The residual small window**: after the sharp bound, only `4`–`8` runners
remain open (`3 ≤ k ≤ 7`) — `m = 4..7` are refereed classical results in the
literature, `m = 8` is computer-verified. -/
def StrongFreeWindowSmall : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ 7 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- The sharp bound collapses the window: the fourteen open sizes reduce to five. -/
theorem strongFreeWindow_of_small (hwin : StrongFreeWindowSmall) : StrongFreeWindow := by
  intro k hk3 hk16 v hv hSF
  by_cases hk7 : k ≤ 7
  · exact hwin k hk3 hk7 v hv hSF
  · exact riesz_clears_floor_sharp (by omega) v hSF

/-- **Separation from the small window alone**: strongly-free families of `4`–`8`
runners are the only remaining obligation on the free side. -/
theorem separationSF_of_smallWindow (hwin : StrongFreeWindowSmall) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_strongFreeWindow (strongFreeWindow_of_small hwin)

/-! ### The degree-two weight: eight runners, modulo doubled relations

The degree-one weight `1 + cos` cannot clear eight runners (`1.87 > 1.77` even
with the exact cosine).  The degree-two weight `(1 + cos)²` can — its expansion
introduces the doubled frequency `2v_i`, whose twisted mass
`∑_j cos(2π(2v_i)j/Q)·P_i(j)` vanishes exactly when the *swapped family*
`v[i ↦ 2v_i]` is itself strongly free (`TwoFree`).  Then
`∑ (1+cos_i)²·P_i = 4M_i − 2M − M^{swap}/2 = 3Q/2`, and the union condition
becomes `3(k+1)(1 − cos 2πδ) < 2(1 + cos 2πδ)²`, which holds at the eight-runner
floor `δ = 1/9` since `π² < 9.9225`.  The `¬TwoFree` residual — families with a
`±2`-relation `2v_i = ∑ε_k v_k` — remains as a named obligation. -/

/-- Doubling-freeness: every swapped family `v[i ↦ 2v_i]` is strongly free,
i.e. no relation `±2v_i = ∑ε_k v_k` with `ε ∈ {−1,0,1}` holds. -/
def TwoFree {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ i : Fin (k + 1), StrongFree (fun w => if w = i then 2 * v i else v w)

/-- **Degree-two Riesz lower bound.**  For a strongly free, doubling-free
`(k+1)`-family, if `δ ≤ 1/2` and `3(k+1)(1 − cos 2πδ) < 2(1 + cos 2πδ)²`,
then `ML(v) ≥ δ`. -/
theorem riesz_lower_bound_sharp2 {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : StrongFree v)
    (hTF : TwoFree v) (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hcond : 3 * ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ))
      < 2 * (1 + Real.cos (2 * π * δ)) ^ 2) :
    δ ≤ ML v := by
  set Q : ℕ := 2 * (∑ i, (v i).natAbs) + 1 with hQdef
  have hQ0 : 0 < Q := Nat.succ_pos _
  have hQsum : (∑ i, (v i).natAbs) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hmass : ∑ j ∈ Finset.range Q, R j = (Q : ℝ) := riesz_mass_real (k + 1) v hv Q hQ0 hQsum
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hc0 : 0 ≤ 1 + Real.cos (2 * π * δ) := by
    have := Real.neg_one_le_cos (2 * π * δ); linarith
  have hcpos : 0 < 1 + Real.cos (2 * π * δ) := by
    rcases lt_or_eq_of_le hc0 with h | h
    · exact h
    · exfalso
      have hL : 0 ≤ 3 * ((k : ℝ) + 1) * (1 - Real.cos (2 * π * δ)) :=
        mul_nonneg (by positivity) hcosδ
      rw [← h] at hcond
      norm_num at hcond
      linarith
  -- per-runner: bad weight × (1+cos2πδ)² ≤ (1−cos2πδ)·(3/2)·Q
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        * (1 + Real.cos (2 * π * δ)) ^ 2
        ≤ (1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ)) := by
    intro i
    set v' : Fin k → ℤ := fun j' => v (i.succAbove j') with hv'def
    have hv'sum : (∑ j', (v' j').natAbs) < Q := by
      have hle : (∑ j', (v' j').natAbs) ≤ ∑ w, (v w).natAbs := by
        rw [Fin.sum_univ_succAbove (fun w => (v w).natAbs) i]; exact Nat.le_add_left _ _
      omega
    have hsubmass : ∑ j ∈ Finset.range Q,
        ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
      riesz_mass_real k v' (strongFree_succAbove v hv i) Q hQ0 hv'sum
    have hsubnn : ∀ j, 0 ≤ ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j =>
      Finset.prod_nonneg fun j' _ => by
        have := Real.cos_le_one (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
    have hRsplit : ∀ j : ℕ, R j = (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
        * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := fun j => by
      simp only [hRdef]
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (v w : ℝ) * (j : ℝ) / (Q : ℝ)))) i]
    -- the swapped family and its mass
    have hswapsum : (∑ w, ((fun w => if w = i then 2 * v i else v w) w).natAbs) < Q := by
      have hle : (∑ w, ((fun w => if w = i then 2 * v i else v w) w).natAbs)
          ≤ ∑ w, 2 * (v w).natAbs := by
        refine Finset.sum_le_sum fun w _ => ?_
        rcases eq_or_ne w i with rfl | hw
        · simp [Int.natAbs_mul]
        · simp only [if_neg hw]; omega
      have h2 : (∑ w, 2 * (v w).natAbs) = 2 * ∑ w, (v w).natAbs := by
        rw [Finset.mul_sum]
      omega
    have hswapmass : ∑ j ∈ Finset.range Q,
        ∏ w : Fin (k + 1),
          (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
            * (j : ℝ) / (Q : ℝ))) = (Q : ℝ) :=
      riesz_mass_real (k + 1) (fun w => if w = i then 2 * v i else v w) (hTF i) Q hQ0 hswapsum
    have hRswapsplit : ∀ j : ℕ,
        (∏ w : Fin (k + 1),
          (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
            * (j : ℝ) / (Q : ℝ))))
        = (1 - Real.cos (2 * π * (2 * (v i : ℝ)) * (j : ℝ) / (Q : ℝ)))
          * ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
      intro j
      rw [Fin.prod_univ_succAbove
        (fun w => (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
          * (j : ℝ) / (Q : ℝ)))) i]
      congr 1
      · rw [if_pos rfl]
        push_cast
        ring_nf
      · refine Finset.prod_congr rfl fun j' _ => ?_
        rw [if_neg (Fin.succAbove_ne i j')]
    -- the degree-two mass identity: ∑ (1+cosᵢ)²·Pᵢ = 3Q/2
    have hplus2 : ∑ j ∈ Finset.range Q,
        (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 2
          * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        = 3 / 2 * (Q : ℝ) := by
      have hsplit2 : ∀ j : ℕ,
          (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 2
            * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          = 4 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - 2 * R j
            - 1 / 2 * (∏ w : Fin (k + 1),
                (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
                  * (j : ℝ) / (Q : ℝ)))) := by
        intro j
        have hcos2 : Real.cos (2 * π * (2 * (v i : ℝ)) * (j : ℝ) / (Q : ℝ))
            = 2 * Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)) ^ 2 - 1 := by
          rw [show 2 * π * (2 * (v i : ℝ)) * (j : ℝ) / (Q : ℝ)
              = 2 * (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, Real.cos_two_mul]
        rw [hRsplit j, hRswapsplit j, hcos2]
        ring
      calc (∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 2
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))))
          = ∑ j ∈ Finset.range Q,
              (4 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                - 2 * R j
                - 1 / 2 * (∏ w : Fin (k + 1),
                    (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
                      * (j : ℝ) / (Q : ℝ))))) :=
            Finset.sum_congr rfl fun j _ => hsplit2 j
        _ = 4 * (∑ j ∈ Finset.range Q,
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - 2 * (∑ j ∈ Finset.range Q, R j)
            - 1 / 2 * (∑ j ∈ Finset.range Q, ∏ w : Fin (k + 1),
                (1 - Real.cos (2 * π * (((if w = i then 2 * v i else v w : ℤ)) : ℝ)
                  * (j : ℝ) / (Q : ℝ)))) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        _ = 4 * (Q : ℝ) - 2 * (Q : ℝ) - 1 / 2 * (Q : ℝ) := by
            rw [hsubmass, hmass, hswapmass]
        _ = 3 / 2 * (Q : ℝ) := by ring
    -- Markov at degree two
    have hfilter : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        * (1 + Real.cos (2 * π * δ)) ^ 2 ≤ 3 / 2 * (Q : ℝ) := by
      calc (∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ)) ^ 2
          = ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                * (1 + Real.cos (2 * π * δ)) ^ 2 := by rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 2
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_filter] at hj
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
            have hrw2 : Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
                = Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := by
              rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
                  = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
            have hcosle : Real.cos (2 * π * δ)
                ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
              Real.cos_le_cos_of_nonneg_of_le_pi
                (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
                (by nlinarith [Real.pi_pos, hδ2])
                (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
            rw [hrw2, pow_two, pow_two]
            refine mul_self_le_mul_self hc0 ?_
            linarith
        _ ≤ ∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) ^ 2
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun j _ _ => mul_nonneg (sq_nonneg _) (hsubnn j))
        _ = 3 / 2 * (Q : ℝ) := hplus2
    -- the crude factor bound on the bad set
    have hbad : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
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
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          * (1 + Real.cos (2 * π * δ)) ^ 2
        ≤ ((1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hbad (sq_nonneg _)
      _ = (1 - Real.cos (2 * π * δ)) * ((∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ)) ^ 2) := by ring
      _ ≤ (1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ)) :=
          mul_le_mul_of_nonneg_left hfilter hcosδ
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
              (f := fun i' => if nearestIntDist ((v i' : ℝ) * (j : ℝ) / (Q : ℝ)) < δ then R j else 0)
              (fun i' _ => ?_) (Finset.mem_univ i)
            dsimp only
            split_ifs
            · exact hRnn j
            · exact le_refl 0
    have hfinal : (Q : ℝ) * (1 + Real.cos (2 * π * δ)) ^ 2
        ≤ ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ))) := by
      calc (Q : ℝ) * (1 + Real.cos (2 * π * δ)) ^ 2
          = (∑ j ∈ Finset.range Q, R j) * (1 + Real.cos (2 * π * δ)) ^ 2 := by rw [hmass]
        _ ≤ (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hcover (sq_nonneg _)
        _ = ∑ i : Fin (k + 1), ((∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ)) ^ 2) := by rw [Finset.sum_mul]
        _ ≤ ∑ _i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ)) :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
    have hlt : ((k : ℝ) + 1) * ((1 - Real.cos (2 * π * δ)) * (3 / 2 * (Q : ℝ)))
        < (1 + Real.cos (2 * π * δ)) ^ 2 * (Q : ℝ) := by
      have := mul_lt_mul_of_pos_right hcond hQR
      nlinarith [this]
    nlinarith [hfinal, hlt]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

/-- **The eight-runner floor for doubling-free families.**  At `δ = 1/9` the
degree-two condition reads `24(1 − cos 2π/9) < 2(1 + cos 2π/9)²`, which follows
from `1 − cos x < x²/2` and `π² < 9.9225` (`5.881 < 6.160`). -/
theorem riesz_clears_floor_eight (v : Fin 8 → ℤ) (hv : StrongFree v)
    (hTF : TwoFree v) : 1 / 9 ≤ ML v := by
  refine riesz_lower_bound_sharp2 (k := 7) v hv hTF (1 / 9) (by norm_num) (by norm_num) ?_
  have h78 : ((7 : ℕ) : ℝ) + 1 = 8 := by norm_num
  rw [h78]
  have hπδpos : 0 < π * (1 / 9 : ℝ) := by positivity
  have hsin : Real.sin (π * (1 / 9 : ℝ)) < π * (1 / 9 : ℝ) := Real.sin_lt hπδpos
  have hπδltpi : π * (1 / 9 : ℝ) < π := by nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (π * (1 / 9 : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * (1 / 9 : ℝ)) = 2 * Real.sin (π * (1 / 9 : ℝ)) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * (1 / 9 : ℝ))
    rw [show 2 * π * (1 / 9 : ℝ) = 2 * (π * (1 / 9 : ℝ)) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * (1 / 9 : ℝ)) < 2 * (π * (1 / 9 : ℝ)) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * (1 / 9 : ℝ)) ^ 2 < (π * (1 / 9 : ℝ)) ^ 2 := by
      nlinarith [hsin, hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hub : 1 - Real.cos (2 * π * (1 / 9 : ℝ)) < 0.245 := by nlinarith [hu, hπ2]
  have hcb : (1.755 : ℝ) < 1 + Real.cos (2 * π * (1 / 9 : ℝ)) := by linarith
  nlinarith [hub, hcb]

/-- **The residual tiny window**: strongly free families of `4`–`7` runners. -/
def StrongFreeWindowTiny : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ 6 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) →
    StrongFree v → 1 / ((k : ℝ) + 2) ≤ ML v

/-- **The doubled-relation residual at eight runners**: strongly free families
of `8` runners carrying a `±2`-relation `2v_i = ∑ε_k v_k`. -/
def EightDoubledResidual : Prop :=
  ∀ v : Fin 8 → ℤ, (∀ i, 0 < v i) → StrongFree v → ¬ TwoFree v →
    1 / ((7 : ℝ) + 2) ≤ ML v

/-- The degree-two bound splits the eight-runner rung: the small window follows
from the tiny window plus the doubled residual. -/
theorem smallWindow_of_tiny_and_residual (h1 : StrongFreeWindowTiny)
    (h2 : EightDoubledResidual) : StrongFreeWindowSmall := by
  intro k hk3 hk7 v hv hSF
  by_cases hk6 : k ≤ 6
  · exact h1 k hk3 hk6 v hv hSF
  · have hk7' : k = 7 := by omega
    subst hk7'
    by_cases hTF : TwoFree v
    · have h := riesz_clears_floor_eight v hSF hTF
      have hc : 1 / (((7 : ℕ) : ℝ) + 2) = 1 / 9 := by norm_num
      rw [hc]; exact h
    · have h := h2 v hv hSF hTF
      have hc : 1 / (((7 : ℕ) : ℝ) + 2) = 1 / ((7 : ℝ) + 2) := by norm_num
      rw [hc]; exact h

/-- **Separation from the tiny window and the doubled residual**: the free-side
obligation is `4`–`7` runners in full, plus only the `±2`-relation-carrying
families at `8` runners. -/
theorem separationSF_of_tiny_and_residual (h1 : StrongFreeWindowTiny)
    (h2 : EightDoubledResidual) :
    ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ ladderSF n :=
  separationSF_of_smallWindow (smallWindow_of_tiny_and_residual h1 h2)

/-! ### The Markov engine with arbitrary masses: sharpening the Bridge

The unbiasedness identity `∑_j (1 + cos θᵢ)·Pᵢ(j) = 2Mᵢ − M` is pure pointwise
algebra plus the two mass values — it needs no dissociativity.  So the Markov
step applies verbatim to *relation-carrying* families with their masses
supplied as data, improving the generalized union engine's condition from
`(∑Mᵢ)(1 − cos 2πδ) < M` to `(2∑Mᵢ − (k+1)M)(1 − cos 2πδ) < (1 + cos 2πδ)·M`.
For the single-relation Bridge (`∑Mᵢ ≤ (k+2)M`) this reads
`(k+3)(1 − cos 2πδ) < 1 + cos 2πδ`, i.e. `(k+4)(1 − cos 2πδ) < 2`, which clears
the floor `δ = 1/(k+2)` for every `k ≥ 10` — down from `k ≥ 18`. -/

/-- **Sharp generalized union engine.**  `riesz_union_general` with the Markov
budget: per-runner bad weight `× (1 + cos 2πδ)` is at most
`(1 − cos 2πδ)(2Mᵢ − M)`. -/
theorem riesz_union_general_sharp {k : ℕ} (v : Fin (k + 1) → ℤ) (Q : ℕ) (hQ0 : 0 < Q)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℝ)
    (hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin (k + 1),
        (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) = M)
    (Mi : Fin (k + 1) → ℝ)
    (hsubmass : ∀ i, ∑ j ∈ Finset.range Q, ∏ j' : Fin k,
        (1 - Real.cos (2 * π * (v (i.succAbove j') : ℝ) * (j : ℝ) / (Q : ℝ))) = Mi i)
    (hcond : (2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M) * (1 - Real.cos (2 * π * δ))
      < (1 + Real.cos (2 * π * δ)) * M) :
    δ ≤ ML v := by
  set R : ℕ → ℝ := fun j : ℕ =>
    ∏ i : Fin (k + 1), (1 - Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))) with hRdef
  have hRnn : ∀ j, 0 ≤ R j := fun j => Finset.prod_nonneg fun i _ => by
    have := Real.cos_le_one (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)); linarith
  have hcosδ : 0 ≤ 1 - Real.cos (2 * π * δ) := by
    have := Real.cos_le_one (2 * π * δ); linarith
  have hc0 : 0 ≤ 1 + Real.cos (2 * π * δ) := by
    have := Real.neg_one_le_cos (2 * π * δ); linarith
  -- per-runner Markov bound
  have hrunner : ∀ i : Fin (k + 1),
      (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        * (1 + Real.cos (2 * π * δ))
        ≤ (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) := by
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
    -- the unbiasedness identity with data masses: ∑ (1+cosᵢ)·Pᵢ = 2Mᵢ − M
    have hplus : ∑ j ∈ Finset.range Q,
        (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
          * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        = 2 * Mi i - M := by
      have hsplit : ∀ j : ℕ,
          (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
            * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          = 2 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - R j := by
        intro j; rw [hRsplit j]; ring
      calc (∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))))
          = ∑ j ∈ Finset.range Q,
              (2 * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                - R j) := Finset.sum_congr rfl fun j _ => hsplit j
        _ = 2 * (∑ j ∈ Finset.range Q,
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            - ∑ j ∈ Finset.range Q, R j := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = 2 * Mi i - M := by rw [hsubmass i, hmass]
    have hfilter : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
          ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
        * (1 + Real.cos (2 * π * δ)) ≤ 2 * Mi i - M := by
      calc (∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
            * (1 + Real.cos (2 * π * δ))
          = ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
                * (1 + Real.cos (2 * π * δ)) := by rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_filter] at hj
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (hsubnn j)
            have hrw2 : Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
                = Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) := by
              rw [show 2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)
                  = 2 * π * ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) by ring, cos_two_pi_nid]
            have hcosle : Real.cos (2 * π * δ)
                ≤ Real.cos (2 * π * nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ))) :=
              Real.cos_le_cos_of_nonneg_of_le_pi
                (mul_nonneg (by positivity) (nearestIntDist_nonneg _))
                (by nlinarith [Real.pi_pos, hδ2])
                (mul_le_mul_of_nonneg_left hj.2.le (by positivity))
            rw [hrw2]; linarith
        _ ≤ ∑ j ∈ Finset.range Q,
              (1 + Real.cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ)))
                * (∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ)))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun j _ _ => mul_nonneg ?_ (hsubnn j))
            have := Real.neg_one_le_cos (2 * π * (v i : ℝ) * (j : ℝ) / (Q : ℝ))
            linarith
        _ = 2 * Mi i - M := hplus
    have hbad : (∑ j ∈ (Finset.range Q).filter
          (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
        ≤ (1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))) := by
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
    calc (∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
          * (1 + Real.cos (2 * π * δ))
        ≤ ((1 - Real.cos (2 * π * δ)) * ∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ)) :=
          mul_le_mul_of_nonneg_right hbad hc0
      _ = (1 - Real.cos (2 * π * δ)) * ((∑ j ∈ (Finset.range Q).filter
            (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ),
            ∏ j' : Fin k, (1 - Real.cos (2 * π * (v' j' : ℝ) * (j : ℝ) / (Q : ℝ))))
          * (1 + Real.cos (2 * π * δ))) := by ring
      _ ≤ (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) :=
          mul_le_mul_of_nonneg_left hfilter hcosδ
  -- escape
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
    have hfinal : M * (1 + Real.cos (2 * π * δ))
        ≤ (1 - Real.cos (2 * π * δ)) * (2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M) := by
      calc M * (1 + Real.cos (2 * π * δ))
          = (∑ j ∈ Finset.range Q, R j) * (1 + Real.cos (2 * π * δ)) := by rw [hmass]
        _ ≤ (∑ i : Fin (k + 1), ∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ)) :=
            mul_le_mul_of_nonneg_right hcover hc0
        _ = ∑ i : Fin (k + 1), ((∑ j ∈ (Finset.range Q).filter
              (fun j : ℕ => nearestIntDist ((v i : ℝ) * (j : ℝ) / (Q : ℝ)) < δ), R j)
            * (1 + Real.cos (2 * π * δ))) := by rw [Finset.sum_mul]
        _ ≤ ∑ i : Fin (k + 1), (1 - Real.cos (2 * π * δ)) * (2 * Mi i - M) :=
            Finset.sum_le_sum (fun i _ => hrunner i)
        _ = (1 - Real.cos (2 * π * δ)) * (2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin]
            push_cast; ring
    nlinarith [hfinal, hcond]
  obtain ⟨j, _, hgj⟩ := hgood
  refine (le_gap v ((j : ℝ) / (Q : ℝ)) δ (fun i => ?_)).trans
    (le_csSup (bddAbove_range_gap v) ⟨(j : ℝ) / (Q : ℝ), rfl⟩)
  rw [show (v i : ℝ) * ((j : ℝ) / (Q : ℝ)) = (v i : ℝ) * (j : ℝ) / (Q : ℝ) by ring]
  exact hgj i

set_option maxHeartbeats 1000000 in
/-- **The sharp single-relation Bridge** (any odd support): the Markov budget
drops the threshold of `bridge_single_relation` from `k ≥ 18` to `k ≥ 10`.
With `∑Mᵢ ≤ (k+2)M`, the sharp condition reads `(k+4)(1 − cos 2πδ) < 2` at
`δ = 1/(k+2)`, which holds for `k + 2 ≥ 12` since `π² < 9.9225`. -/
theorem bridge_single_relation_sharp {k s : ℕ} (hk : 10 ≤ k) (hs : 3 ≤ s) (hodd : Odd s)
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
  have hpowbnd : (-1 / 4 : ℝ) ≤ 2 * (-1 / 2 : ℝ) ^ s := by
    have habs : |(-1 / 2 : ℝ) ^ s| ≤ (1 / 2) ^ 3 := by
      rw [abs_pow, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    have h8 : ((1 : ℝ) / 2) ^ 3 = 1 / 8 := by norm_num
    rw [h8] at habs
    have := (abs_le.mp habs).1
    linarith
  have hM0 : 0 < M := by
    rw [hMdef, hP]
    have h34 : (3 : ℝ) / 4 ≤ 1 + 2 * (-1 / 2 : ℝ) ^ s := by linarith [hpowbnd]
    nlinarith [hQR, h34]
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
  have hnat : ∀ n, 3 ≤ n → 2 * (n + 1) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega
  have hsQM : (s : ℝ) * (Q : ℝ) ≤ ((s : ℝ) + 1) * M := by
    rw [hMdef, hP]
    have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow hodd _
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have hnatR : (2 : ℝ) * ((s : ℝ) + 1) ≤ (2 : ℝ) ^ s := by exact_mod_cast hnat s hs
    have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by rw [div_pow, one_pow]
    have hfrac : ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s)) ≤ 1 := by
      rw [show ((s : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ s)) = (2 * ((s : ℝ) + 1)) / (2 : ℝ) ^ s by ring,
        div_le_one hpos]
      exact hnatR
    rw [hop, hhalf]
    nlinarith [hfrac, hQR]
  have hsumMi : (∑ i, Mi i) ≤ ((k : ℝ) + 2) * M := by
    have hcard2 : (Finset.univ.filter (fun i => r i = 0)).card = k + 1 - s := by
      have hc := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun i => r i = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hss : (Finset.univ.filter (fun i => ¬ r i = 0)).card = s := hsupp
      omega
    simp only [hMidef]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [hcard2, show (Finset.univ.filter (fun i => ¬ r i = 0)).card = s from hsupp]
    have hsk1 : s ≤ k + 1 := by
      rw [← hsupp]
      calc (Finset.univ.filter (fun i => r i ≠ 0)).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k + 1 := by simp [Finset.card_univ]
    have hks : ((k + 1 - s : ℕ) : ℝ) = (k : ℝ) + 1 - (s : ℝ) := by
      rw [Nat.cast_sub hsk1]; push_cast; ring
    rw [hks]
    nlinarith [hsQM, hM0]
  -- the sharp union call at the floor δ = 1/(k+2)
  have hkR : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ12 : δ ≤ 1 / 12 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  refine riesz_union_general_sharp u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass ?_
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
  -- (k+4)(1 − cos 2πδ) < 2
  have hkey : ((k : ℝ) + 4) * (1 - Real.cos (2 * π * δ)) < 2 := by
    have h1 : ((k : ℝ) + 4) * (1 - Real.cos (2 * π * δ))
        < ((k : ℝ) + 4) * (2 * (π * δ) ^ 2) :=
      mul_lt_mul_of_pos_left hu (by linarith)
    have hδk4 : δ * ((k : ℝ) + 4) ≤ 7 / 6 := by
      have hexp : δ * ((k : ℝ) + 4) = δ * ((k : ℝ) + 2) + 2 * δ := by ring
      rw [hexp, hδval]; linarith
    have h2 : ((k : ℝ) + 4) * (2 * (π * δ) ^ 2) = 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 4)) := by
      ring
    rw [h2] at h1
    have h3 : 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 4)) ≤ 2 * π ^ 2 * δ * (7 / 6) :=
      mul_le_mul_of_nonneg_left hδk4 (by positivity)
    have h5 : 2 * π ^ 2 * δ ≤ 2 * π ^ 2 * (1 / 12) :=
      mul_le_mul_of_nonneg_left hδ12 (by positivity)
    have h4 : 2 * π ^ 2 * δ * (7 / 6) ≤ 2 * π ^ 2 * (1 / 12) * (7 / 6) :=
      mul_le_mul_of_nonneg_right h5 (by norm_num)
    nlinarith [h1, h3, h4, hπ2]
  -- assemble the sharp condition
  have hA : 2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M ≤ ((k : ℝ) + 3) * M := by
    nlinarith [hsumMi, hM0]
  have hstep : ((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ)) < 1 + Real.cos (2 * π * δ) := by
    linarith [hkey]
  have hAc : (2 * (∑ i, Mi i) - ((k : ℝ) + 1) * M) * (1 - Real.cos (2 * π * δ))
      ≤ (((k : ℝ) + 3) * M) * (1 - Real.cos (2 * π * δ)) :=
    mul_le_mul_of_nonneg_right hA hcosδ
  have hMlt : M * (((k : ℝ) + 3) * (1 - Real.cos (2 * π * δ)))
      < M * (1 + Real.cos (2 * π * δ)) :=
    mul_lt_mul_of_pos_left hstep hM0
  nlinarith [hAc, hMlt]

-- axiom audit
#print axioms separationSF_of_window
#print axioms strongFree_two_pow
#print axioms freeSpectrumSF_nonempty
#print axioms ladderSF_base
#print axioms window_rung_one
#print axioms separationSF_of_strongFreeWindow
#print axioms riesz_lower_bound_sharp
#print axioms riesz_clears_floor_sharp
#print axioms separationSF_of_smallWindow
#print axioms riesz_lower_bound_sharp2
#print axioms riesz_clears_floor_eight
#print axioms separationSF_of_tiny_and_residual
#print axioms riesz_union_general_sharp
#print axioms bridge_single_relation_sharp

set_option maxHeartbeats 1000000 in
/-- **The sharp two-relation Bridge**: the Markov budget drops the threshold of
`bridge_two_relations` from `k ≥ 19` to `k ≥ 11`.  With `∑Mᵢ = (k+3)M` exactly,
the sharp condition reads `(k+6)(1 − cos 2πδ) < 2` at `δ = 1/(k+2)`, which holds
for `k + 2 ≥ 13` since `34π²/169 < 2` from `π² < 9.9225`. -/
theorem bridge_two_relations_sharp {k : ℕ} (hk : 11 ≤ k) (u : Fin (k + 1) → ℤ)
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
          rw [Fin.prod_univ_succAbove (fun w => if r w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hri,
            one_mul]
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
          rw [Fin.prod_univ_succAbove (fun w => if s w = 0 then (1 : ℝ) else -1 / 2) i, if_pos hsi,
            one_mul]
        rw [hPs_sub, hPs]; ring
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
  have hsumMi : (∑ i, Mi i) = ((k : ℝ) + 3) * M := by
    simp only [hMidef]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard_p, hcard_np]
    have hk5 : ((k - 5 : ℕ) : ℝ) = (k : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hk5, hMval]; push_cast; ring
  -- the sharp union call at the floor δ = 1/(k+2)
  have hkR : (11 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδ13 : δ ≤ 1 / 13 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδval : δ * ((k : ℝ) + 2) = 1 := by rw [hδdef]; field_simp
  refine riesz_union_general_sharp u Q hQ0 δ hδ0 hδ2 M hmass Mi hsubmass ?_
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
  have hkey : ((k : ℝ) + 6) * (1 - Real.cos (2 * π * δ)) < 2 := by
    have h1 : ((k : ℝ) + 6) * (1 - Real.cos (2 * π * δ))
        < ((k : ℝ) + 6) * (2 * (π * δ) ^ 2) :=
      mul_lt_mul_of_pos_left hu (by linarith)
    have hδk6 : δ * ((k : ℝ) + 6) ≤ 17 / 13 := by
      have hexp : δ * ((k : ℝ) + 6) = δ * ((k : ℝ) + 2) + 4 * δ := by ring
      rw [hexp, hδval]; linarith
    have h2 : ((k : ℝ) + 6) * (2 * (π * δ) ^ 2) = 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 6)) := by
      ring
    rw [h2] at h1
    have h3 : 2 * π ^ 2 * δ * (δ * ((k : ℝ) + 6)) ≤ 2 * π ^ 2 * δ * (17 / 13) :=
      mul_le_mul_of_nonneg_left hδk6 (by positivity)
    have h5 : 2 * π ^ 2 * δ ≤ 2 * π ^ 2 * (1 / 13) :=
      mul_le_mul_of_nonneg_left hδ13 (by positivity)
    have h4 : 2 * π ^ 2 * δ * (17 / 13) ≤ 2 * π ^ 2 * (1 / 13) * (17 / 13) :=
      mul_le_mul_of_nonneg_right h5 (by norm_num)
    nlinarith [h1, h3, h4, hπ2]
  rw [hsumMi]
  have hexp2 : 2 * (((k : ℝ) + 3) * M) - ((k : ℝ) + 1) * M = ((k : ℝ) + 5) * M := by ring
  rw [hexp2]
  have hstep : ((k : ℝ) + 5) * (1 - Real.cos (2 * π * δ)) < 1 + Real.cos (2 * π * δ) := by
    linarith [hkey]
  have hMlt : M * (((k : ℝ) + 5) * (1 - Real.cos (2 * π * δ)))
      < M * (1 + Real.cos (2 * π * δ)) :=
    mul_lt_mul_of_pos_left hstep hM0
  nlinarith [hMlt]

set_option maxHeartbeats 1000000 in
/-- **The ten-runner single-relation Bridge for support `≥ 5`.**  At `k = 9`
the sharp budget with the *exact* sum `∑Mᵢ = (10−s)M + sQ` clears the floor
for every odd support `s ≥ 5`: the budget factor is `(10−2s)μ + 2s =
10 + (2s−10)·2^{1−s} ≤ 161/16` (the lever `32(2s−10) ≤ 2^s`), the mass factor
is `μ ≥ 15/16`, and `161(1 − cos 2π/11) < 15(1 + cos 2π/11)` follows from
`1 − cos x < x²/2` and `π² < 9.9225` (`1.651 < 1.721`).  Support `3` at ten
runners genuinely fails the degree-one budget even with the exact cosine. -/
theorem bridge_single_relation_nine {s : ℕ} (hs : 5 ≤ s) (hodd : Odd s)
    (u : Fin 10 → ℤ)
    (r : Fin 10 → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * u i) = 0)
    (hchar : ∀ c : Fin 10 → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (hsupp : (Finset.univ.filter (fun i => r i ≠ 0)).card = s) :
    1 / 11 ≤ ML u := by
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
  have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow hodd _
  have hpow5 : (1 / 2 : ℝ) ^ s ≤ 1 / 32 := by
    have h : ((1 : ℝ) / 2) ^ s ≤ (1 / 2) ^ 5 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    norm_num at h
    linarith
  have hpownn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s := by positivity
  have hM15 : (15 / 16 : ℝ) * (Q : ℝ) ≤ M := by
    rw [hMdef, hP, hop]
    nlinarith [hpow5, hQR]
  have hM0 : 0 < M := by
    have : (0 : ℝ) < (15 / 16 : ℝ) * (Q : ℝ) := by positivity
    linarith [hM15]
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin 10,
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_single_relation_real 10 u Q hQ0 hQsum r hr0 hrmem hrel hchar
  set Mi : Fin 10 → ℝ := fun i => if r i = 0 then M else (Q : ℝ) with hMidef
  have hsubmass : ∀ i : Fin 10, ∑ j ∈ Finset.range Q, ∏ j' : Fin 9,
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
      rw [riesz_mass_single_relation_real 9 (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrel'
        (subfamily_hchar u r hchar i hri)]
      rw [hMdef]
      congr 2
      rw [Fin.prod_univ_succAbove (fun w => (if r w = 0 then (1 : ℝ) else -1 / 2)) i, if_pos hri,
        one_mul]
    · rw [if_neg hri]
      exact riesz_mass_real 9 (fun j' => u (i.succAbove j'))
        (subfamily_strongFree u r hchar i hri) Q hQ0 hv'sum
  have hsk1 : s ≤ 10 := by
    rw [← hsupp]
    calc (Finset.univ.filter (fun i => r i ≠ 0)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = 10 := by simp [Finset.card_univ]
  have hcard2 : (Finset.univ.filter (fun i : Fin 10 => r i = 0)).card = 10 - s := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 10))) (p := fun i => r i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hss : (Finset.univ.filter (fun i : Fin 10 => ¬ r i = 0)).card = s := hsupp
    omega
  have hsumMi : (∑ i, Mi i) = ((10 : ℝ) - (s : ℝ)) * M + (s : ℝ) * (Q : ℝ) := by
    simp only [hMidef]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard2, show (Finset.univ.filter (fun i : Fin 10 => ¬ r i = 0)).card = s from hsupp]
    have hks : ((10 - s : ℕ) : ℝ) = (10 : ℝ) - (s : ℝ) := by
      rw [Nat.cast_sub hsk1]; push_cast; ring
    rw [hks]
  -- the budget lever: 32(2s−10) ≤ 2^s for s ≥ 5
  have hnat32 : ∀ n, 5 ≤ n → 32 * (2 * n - 10) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rcases Nat.eq_or_lt_of_le hm with rfl | hm6
      · norm_num
      · have h64 : 64 ≤ 2 ^ m := by
          calc (64 : ℕ) = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
        omega
  have h2s10 : (10 : ℕ) ≤ 2 * s := by omega
  have hfrac : (2 * (s : ℝ) - 10) * (2 * (1 / 2 : ℝ) ^ s) ≤ 1 / 16 := by
    have hcast : (32 : ℝ) * (2 * (s : ℝ) - 10) ≤ 2 ^ s := by
      have h := hnat32 s hs
      have : ((32 * (2 * s - 10) : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub h2s10] at this
      linarith
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by rw [div_pow, one_pow]
    rw [hhalf, show (2 * (s : ℝ) - 10) * (2 * (1 / (2 : ℝ) ^ s))
        = (2 * (2 * (s : ℝ) - 10)) / (2 : ℝ) ^ s by ring, div_le_iff₀ hpos]
    nlinarith [hcast]
  -- the budget bound: 2∑Mᵢ − 10M ≤ (161/16)·Q
  have hbudget : 2 * (∑ i, Mi i) - 10 * M ≤ (161 / 16 : ℝ) * (Q : ℝ) := by
    rw [hsumMi]
    have hexp : 2 * (((10 : ℝ) - (s : ℝ)) * M + (s : ℝ) * (Q : ℝ)) - 10 * M
        = ((10 : ℝ) - 2 * (s : ℝ)) * M + 2 * (s : ℝ) * (Q : ℝ) := by ring
    rw [hexp, hMdef, hP, hop]
    have hgoal : ((10 : ℝ) - 2 * (s : ℝ)) * ((Q : ℝ) * (1 + 2 * -(1 / 2 : ℝ) ^ s))
        + 2 * (s : ℝ) * (Q : ℝ)
        = (Q : ℝ) * (10 + (2 * (s : ℝ) - 10) * (2 * (1 / 2 : ℝ) ^ s)) := by ring
    rw [hgoal]
    nlinarith [hfrac, hQR]
  refine riesz_union_general_sharp (k := 9) u Q hQ0 (1 / 11) (by norm_num) (by norm_num) M
    hmass Mi hsubmass ?_
  have h91 : ((9 : ℕ) : ℝ) + 1 = 10 := by norm_num
  rw [h91]
  -- cosine bounds at δ = 1/11
  have hπδpos : 0 < π * (1 / 11 : ℝ) := by positivity
  have hsin : Real.sin (π * (1 / 11 : ℝ)) < π * (1 / 11 : ℝ) := Real.sin_lt hπδpos
  have hπδltpi : π * (1 / 11 : ℝ) < π := by nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (π * (1 / 11 : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hπδpos hπδltpi
  have h1mc : 1 - Real.cos (2 * π * (1 / 11 : ℝ)) = 2 * Real.sin (π * (1 / 11 : ℝ)) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq (π * (1 / 11 : ℝ))
    rw [show 2 * π * (1 / 11 : ℝ) = 2 * (π * (1 / 11 : ℝ)) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hu : 1 - Real.cos (2 * π * (1 / 11 : ℝ)) < 2 * (π * (1 / 11 : ℝ)) ^ 2 := by
    rw [h1mc]
    have hsq : Real.sin (π * (1 / 11 : ℝ)) ^ 2 < (π * (1 / 11 : ℝ)) ^ 2 := by
      nlinarith [hsin, hsinpos]
    linarith
  have hπ2 : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hub : 1 - Real.cos (2 * π * (1 / 11 : ℝ)) < 19.845 / 121 := by nlinarith [hu, hπ2]
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * (1 / 11 : ℝ)) := by
    have := Real.cos_le_one (2 * π * (1 / 11 : ℝ)); linarith
  -- assemble: (2∑Mᵢ − 10M)(1−c) ≤ (161/16)Q(1−c) < (161/16)(19.845/121)Q
  --           < (2 − 19.845/121)(15/16)Q ≤ (1+c)M
  have hstep1 : (2 * (∑ i, Mi i) - 10 * M) * (1 - Real.cos (2 * π * (1 / 11 : ℝ)))
      ≤ ((161 / 16 : ℝ) * (Q : ℝ)) * (1 - Real.cos (2 * π * (1 / 11 : ℝ))) :=
    mul_le_mul_of_nonneg_right hbudget hcosnn
  have hstep2 : ((161 / 16 : ℝ) * (Q : ℝ)) * (1 - Real.cos (2 * π * (1 / 11 : ℝ)))
      < ((161 / 16 : ℝ) * (Q : ℝ)) * (19.845 / 121) :=
    mul_lt_mul_of_pos_left hub (by positivity)
  have hcb : (2 : ℝ) - 19.845 / 121 < 1 + Real.cos (2 * π * (1 / 11 : ℝ)) := by linarith
  have hstep3 : ((2 : ℝ) - 19.845 / 121) * ((15 / 16 : ℝ) * (Q : ℝ))
      ≤ (1 + Real.cos (2 * π * (1 / 11 : ℝ))) * M := by
    have h := mul_le_mul hcb.le hM15 (by positivity)
      (by linarith [hcosnn, Real.cos_le_one (2 * π * (1 / 11 : ℝ)),
        Real.neg_one_le_cos (2 * π * (1 / 11 : ℝ))] : (0 : ℝ) ≤ 1 + Real.cos (2 * π * (1 / 11 : ℝ)))
    linarith [h]
  nlinarith [hstep1, hstep2, hstep3, hQR]

set_option maxHeartbeats 1000000 in
/-- **The nine-runner single-relation Bridge for support `≥ 7`, by the golden
cosine.**  At `k = 8` the floor is `δ = 1/10` and `cos(2π/10) = cos(π/5) =
(1+√5)/4` *exactly*, so no Taylor loss: the exact-sum budget factor is
`9 + (2s−9)·2^{1−s} ≤ 581/64` (lever `128(2s−9) ≤ 5·2^s`, equality at `s = 7`),
the mass factor is `μ ≥ 63/64`, and `581(1 − cos) < 63(1 + cos)` reduces to
`√5 > 357/161`, i.e. `5 > 127449/25921`. -/
theorem bridge_single_relation_eight {s : ℕ} (hs : 7 ≤ s) (hodd : Odd s)
    (u : Fin 9 → ℤ)
    (r : Fin 9 → ℤ) (hr0 : r ≠ 0)
    (hrmem : ∀ i, r i = -1 ∨ r i = 0 ∨ r i = 1) (hrel : (∑ i, r i * u i) = 0)
    (hchar : ∀ c : Fin 9 → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∑ i, c i * u i) = 0 →
        c = 0 ∨ c = r ∨ c = -r)
    (hsupp : (Finset.univ.filter (fun i => r i ≠ 0)).card = s) :
    1 / 10 ≤ ML u := by
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
  have hop : (-1 / 2 : ℝ) ^ s = -(1 / 2 : ℝ) ^ s := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact Odd.neg_pow hodd _
  have hpow7 : (1 / 2 : ℝ) ^ s ≤ 1 / 128 := by
    have h : ((1 : ℝ) / 2) ^ s ≤ (1 / 2) ^ 7 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    norm_num at h
    linarith
  have hM63 : (63 / 64 : ℝ) * (Q : ℝ) ≤ M := by
    rw [hMdef, hP, hop]
    nlinarith [hpow7, hQR]
  have hM0 : 0 < M := by
    have : (0 : ℝ) < (63 / 64 : ℝ) * (Q : ℝ) := by positivity
    linarith [hM63]
  have hmass : ∑ j ∈ Finset.range Q, ∏ i : Fin 9,
      (1 - Real.cos (2 * π * (u i : ℝ) * (j : ℝ) / (Q : ℝ))) = M :=
    riesz_mass_single_relation_real 9 u Q hQ0 hQsum r hr0 hrmem hrel hchar
  set Mi : Fin 9 → ℝ := fun i => if r i = 0 then M else (Q : ℝ) with hMidef
  have hsubmass : ∀ i : Fin 9, ∑ j ∈ Finset.range Q, ∏ j' : Fin 8,
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
      rw [riesz_mass_single_relation_real 8 (fun j' => u (i.succAbove j')) Q hQ0 hv'sum
        (fun j' => r (i.succAbove j')) hr'0 (fun j' => hrmem _) hrel'
        (subfamily_hchar u r hchar i hri)]
      rw [hMdef]
      congr 2
      rw [Fin.prod_univ_succAbove (fun w => (if r w = 0 then (1 : ℝ) else -1 / 2)) i, if_pos hri,
        one_mul]
    · rw [if_neg hri]
      exact riesz_mass_real 8 (fun j' => u (i.succAbove j'))
        (subfamily_strongFree u r hchar i hri) Q hQ0 hv'sum
  have hsk1 : s ≤ 9 := by
    rw [← hsupp]
    calc (Finset.univ.filter (fun i => r i ≠ 0)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = 9 := by simp [Finset.card_univ]
  have hcard2 : (Finset.univ.filter (fun i : Fin 9 => r i = 0)).card = 9 - s := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 9))) (p := fun i => r i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hss : (Finset.univ.filter (fun i : Fin 9 => ¬ r i = 0)).card = s := hsupp
    omega
  have hsumMi : (∑ i, Mi i) = ((9 : ℝ) - (s : ℝ)) * M + (s : ℝ) * (Q : ℝ) := by
    simp only [hMidef]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard2, show (Finset.univ.filter (fun i : Fin 9 => ¬ r i = 0)).card = s from hsupp]
    have hks : ((9 - s : ℕ) : ℝ) = (9 : ℝ) - (s : ℝ) := by
      rw [Nat.cast_sub hsk1]; push_cast; ring
    rw [hks]
  -- the budget lever: 128(2s−9) ≤ 5·2^s for s ≥ 7 (equality at s = 7)
  have hnat128 : ∀ n, 7 ≤ n → 128 * (2 * n - 9) ≤ 5 * 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have h128 : 128 ≤ 2 ^ m := by
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega
  have h2s9 : (9 : ℕ) ≤ 2 * s := by omega
  have hfrac : (2 * (s : ℝ) - 9) * (2 * (1 / 2 : ℝ) ^ s) ≤ 5 / 64 := by
    have hcast : (128 : ℝ) * (2 * (s : ℝ) - 9) ≤ 5 * 2 ^ s := by
      have h := hnat128 s hs
      have : ((128 * (2 * s - 9) : ℕ) : ℝ) ≤ ((5 * 2 ^ s : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub h2s9] at this
      linarith
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by rw [div_pow, one_pow]
    rw [hhalf, show (2 * (s : ℝ) - 9) * (2 * (1 / (2 : ℝ) ^ s))
        = (2 * (2 * (s : ℝ) - 9)) / (2 : ℝ) ^ s by ring, div_le_iff₀ hpos]
    nlinarith [hcast]
  have hbudget : 2 * (∑ i, Mi i) - 9 * M ≤ (581 / 64 : ℝ) * (Q : ℝ) := by
    rw [hsumMi]
    have hexp : 2 * (((9 : ℝ) - (s : ℝ)) * M + (s : ℝ) * (Q : ℝ)) - 9 * M
        = ((9 : ℝ) - 2 * (s : ℝ)) * M + 2 * (s : ℝ) * (Q : ℝ) := by ring
    rw [hexp, hMdef, hP, hop]
    have hgoal : ((9 : ℝ) - 2 * (s : ℝ)) * ((Q : ℝ) * (1 + 2 * -(1 / 2 : ℝ) ^ s))
        + 2 * (s : ℝ) * (Q : ℝ)
        = (Q : ℝ) * (9 + (2 * (s : ℝ) - 9) * (2 * (1 / 2 : ℝ) ^ s)) := by ring
    rw [hgoal]
    nlinarith [hfrac, hQR]
  refine riesz_union_general_sharp (k := 8) u Q hQ0 (1 / 10) (by norm_num) (by norm_num) M
    hmass Mi hsubmass ?_
  have h81 : ((8 : ℕ) : ℝ) + 1 = 9 := by norm_num
  rw [h81]
  -- the golden cosine: cos(2π/10) = cos(π/5) = (1+√5)/4, exactly
  have hc5 : Real.cos (2 * π * (1 / 10 : ℝ)) = (1 + Real.sqrt 5) / 4 := by
    rw [show 2 * π * (1 / 10 : ℝ) = π / 5 by ring]
    exact Real.cos_pi_div_five
  have hsqrt5 : (357 / 161 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hcb : (259 / 322 : ℝ) < Real.cos (2 * π * (1 / 10 : ℝ)) := by
    rw [hc5]; linarith
  have hcosnn : 0 ≤ 1 - Real.cos (2 * π * (1 / 10 : ℝ)) := by
    have := Real.cos_le_one (2 * π * (1 / 10 : ℝ)); linarith
  have h1c0 : (0 : ℝ) ≤ 1 + Real.cos (2 * π * (1 / 10 : ℝ)) := by
    have := Real.neg_one_le_cos (2 * π * (1 / 10 : ℝ)); linarith
  calc (2 * (∑ i, Mi i) - 9 * M) * (1 - Real.cos (2 * π * (1 / 10 : ℝ)))
      ≤ ((581 / 64 : ℝ) * (Q : ℝ)) * (1 - Real.cos (2 * π * (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hbudget hcosnn
    _ < ((63 / 64 : ℝ) * (Q : ℝ)) * (1 + Real.cos (2 * π * (1 / 10 : ℝ))) := by
        nlinarith [hcb, hQR]
    _ ≤ M * (1 + Real.cos (2 * π * (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hM63 h1c0
    _ = (1 + Real.cos (2 * π * (1 / 10 : ℝ))) * M := by ring

-- axiom audit
#print axioms bridge_two_relations_sharp
#print axioms bridge_single_relation_nine
#print axioms bridge_single_relation_eight

end LRSpectrumFull
