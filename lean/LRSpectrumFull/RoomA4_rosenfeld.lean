/-
# ROOM A4, field seat (finite-checking lens): an inductive, Lemma-5-reduced form of crux A4

`BridgeDisjunctionQPrim` (A4) asks for the Riesz-or-witness disjunction on every primitive
non-StrongFree family with `k+1 ≥ 12` speeds, with no hypothesis about smaller families.

The finite-checking literature (Rosenfeld arXiv:2509.14111 and its continuations) always argues by
induction on the number of speeds: LRC for `k` speeds is assumed when treating `k+1` speeds.  This
module makes that induction available to A4 and spends it once, on Rosenfeld's Lemma 5 (whose core
is `lemma5_core`, already verified in `Lemma5.lean`):

* `BridgeDisjunctionQPrimInd` : A4 weakened in two ways:
  (1) the floor for every smaller number of speeds is a hypothesis;
  (2) the family is additionally assumed *leave-one-out primitive*: deleting any one speed leaves a
      family of gcd `1`.
* `bridgeDisjunctionQPrimInd_of_QPrim` : the old crux implies the new one (so the new one is weaker).
* `universalFloor_of_four_atoms_ind` : the four-atom theorem with A4 replaced by the weaker atom.

Proof of the leave-one-out step: if deleting `l` leaves gcd `g ≥ 2`, the induction hypothesis
gives a time `t` with gap `> 1/(k+2)` for the other `k` speeds (their floor is `1/(k+1)`), `v l` is
coprime to `g` because the whole family is primitive, and `lemma5_core` upgrades `t` to a time
with gap `≥ min(1/(k+2), 1/4) = 1/(k+2)` for all speeds (`k ≥ 2`).
-/

import LRSpectrumFull.Delta2Connect
import LRSpectrumFull.Lemma5

namespace LRSpectrumFull.RoomA4Rosenfeld

open LRSpectrumFull

/-- **Crux A4, inductive and leave-one-out-primitive form.** -/
def BridgeDisjunctionQPrimInd : Prop :=
  ∀ k : ℕ, 11 ≤ k →
    (∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u) →
    ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 →
    (∀ l : Fin (k + 1), Finset.univ.gcd (fun j : Fin k => v (l.succAbove j)) = 1) →
    ¬ StrongFree v →
    rieszSharpFiresQ v ∨
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- The new atom is implied by the old one (it is weaker). -/
theorem bridgeDisjunctionQPrimInd_of_QPrim (h : BridgeDisjunctionQPrim) :
    BridgeDisjunctionQPrimInd := by
  intro k hk _ v hv hprim _ hSF
  exact h k hk v hv hprim hSF

/-- **Rosenfeld's Lemma 5 in project conventions (VERIFIED here, from `lemma5_core`).**
`k+2` runners, `k+1` speeds, `k ≥ 2`.  If the floor holds for `k` speeds, the family is primitive,
and deleting speed `l` leaves a family with gcd `≠ 1`, then the floor holds. -/
theorem floor_of_leaveOneOut_imprimitive (k₀ : ℕ) (hk : 1 ≤ k₀)
    (ih : ∀ u : Fin (k₀ + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k₀ : ℝ) + 2) ≤ ML u)
    (v : Fin (k₀ + 1 + 1) → ℤ) (hv : ∀ i, 0 < v i) (hprim : Finset.univ.gcd v = 1)
    (l : Fin (k₀ + 1 + 1))
    (hl : Finset.univ.gcd (fun j : Fin (k₀ + 1) => v (l.succAbove j)) ≠ 1) :
    1 / (((k₀ + 1 : ℕ) : ℝ) + 2) ≤ ML v := by
  set u : Fin (k₀ + 1) → ℤ := fun j => v (l.succAbove j) with hu
  set g : ℤ := Finset.univ.gcd u with hg
  -- g ≥ 2
  have hnorm : normalize g = g := by rw [hg]; exact Finset.normalize_gcd
  have hgnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self hnorm
  have hg0 : g ≠ 0 := by
    rw [hg, Ne, Finset.gcd_eq_zero_iff]; push Not
    exact ⟨0, Finset.mem_univ 0, (hv _).ne'⟩
  have hg2 : 2 ≤ g := by
    have : g ≠ 1 := hl
    omega
  set q : ℕ := g.toNat with hq
  have hqg : (q : ℤ) = g := Int.toNat_of_nonneg hgnn
  have hq2 : 2 ≤ q := by omega
  -- divisibility of the others
  have hdvd : ∀ i, i ≠ l → (q : ℤ) ∣ v i := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [hqg, hg]
    exact Finset.gcd_dvd (f := u) (Finset.mem_univ j)
  -- coprimality of the distinguished speed
  have hcop : Nat.Coprime (v l).toNat q := by
    set d := Nat.gcd (v l).toNat q with hd
    have hdl : (d : ℤ) ∣ v l := by
      have h1 : d ∣ (v l).toNat := Nat.gcd_dvd_left _ _
      have h2 : ((v l).toNat : ℤ) = v l := Int.toNat_of_nonneg (hv l).le
      rw [← h2]; exact_mod_cast h1
    have hdq : (d : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_right _ _
    have hdall : (d : ℤ) ∣ Finset.univ.gcd v := by
      refine Finset.dvd_gcd (fun i _ => ?_)
      by_cases hi : i = l
      · rw [hi]; exact hdl
      · exact dvd_trans hdq (hdvd i hi)
    rw [hprim] at hdall
    have : d = 1 := by
      have h3 := Int.eq_one_of_dvd_one (by positivity) hdall
      exact_mod_cast h3
    exact this
  -- a good time for the others, from the induction hypothesis
  have hML := ih u (fun j => hv _)
  have hlt : 1 / (((k₀ + 1 : ℕ) : ℝ) + 2) < ML u := by
    refine lt_of_lt_of_le ?_ hML
    push_cast
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (gap u)) hlt
  have hfar : ∀ i, i ≠ l → 1 / (((k₀ + 1 : ℕ) : ℝ) + 2) ≤ nearestIntDist ((v i : ℝ) * t) := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    exact le_trans hy.le (gap_le u t j)
  have hcore := lemma5_core v l q hq2 hdvd hcop (hv l) t _ hfar
  have hmin : min (1 / (((k₀ + 1 : ℕ) : ℝ) + 2)) (1 / 4) = 1 / (((k₀ + 1 : ℕ) : ℝ) + 2) := by
    apply min_eq_left
    have h4 : (4 : ℝ) ≤ ((k₀ + 1 : ℕ) : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
      push_cast; linarith
    exact one_div_le_one_div_of_le (by norm_num) h4
  rw [hmin] at hcore
  exact hcore

/-- One inductive step on primitive non-StrongFree families with `k ≥ 11`. -/
theorem floor_step (hdisj : BridgeDisjunctionQPrimInd) (k : ℕ) (hk : 11 ≤ k)
    (ih : ∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (hprim : Finset.univ.gcd v = 1)
    (hSF : ¬ StrongFree v) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  by_cases hall : ∀ l : Fin (k₀ + 1 + 1),
      Finset.univ.gcd (fun j : Fin (k₀ + 1) => v (l.succAbove j)) = 1
  · rcases hdisj (k₀ + 1) hk ih v hv hprim hall hSF with h | ⟨p, q, hq, hwit⟩
    · exact floor_of_rieszSharpFiresQ v h
    · exact cube_floor_of_witness v hv p q hq hwit
  · push Not at hall
    obtain ⟨l, hl⟩ := hall
    have := floor_of_leaveOneOut_imprimitive k₀ (by omega) (ih k₀ (by omega)) v hv hprim l hl
    exact_mod_cast this

/-- **Four-atom theorem with the weaker, inductive crux (VERIFIED).** -/
theorem universalFloor_of_four_atoms_ind
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQPrimInd) : UniversalFloor := by
  have hsep := separationSF_of_tiny_and_residual h1 (eightDoubledResidual_of_witness h2)
  have key : ∀ n : ℕ, ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → 1 / ((n : ℝ) + 2) ≤ ML v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hSF : StrongFree v
      · exact le_trans (hsep n) (ladderSF_le v hv hSF)
      · by_cases hk : n ≤ 10
        · exact hwinB n hk v hv hSF
        · refine floor_of_primitive_floor_pred (fun u => ¬ StrongFree u) ?_ ?_ v hv hSF
          · intro g hg w hgw hsfw
            exact hgw ((strongFree_smul g hg.ne' w).mpr hsfw)
          · intro u hu hprim hsfu
            exact floor_step hdisj n (by omega) ih u hu hprim hsfu
  intro n _ v hv
  exact key n v hv

/-! ### Rosenfeld's Lemma 4 inside the witness branch

If some `j` with `2 ≤ j ≤ k+2` divides no speed, the time `1/j` is a residue witness: every
`v_i mod j` lies in `[1, j-1]`, so `(k+2) * min(r, j-r) ≥ k+2 ≥ j`.  Hence the crux can further
assume that every `j ∈ [2, k+2]` divides some speed. -/

/-- **Lemma 4 as a witness (VERIFIED).** -/
theorem witness_of_missing_divisor {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (j : ℕ) (hj2 : 2 ≤ j) (hjk : j ≤ k + 2) (hnd : ∀ i, ¬ ((j : ℤ) ∣ v i)) :
    ∀ i, j ≤ (k + 2) * min ((v i).toNat * 1 % j) (j - (v i).toNat * 1 % j) := by
  intro i
  have hvi : ((v i).toNat : ℤ) = v i := Int.toNat_of_nonneg (hv i).le
  have hr0 : (v i).toNat % j ≠ 0 := by
    intro h0
    apply hnd i
    rw [← hvi]
    exact_mod_cast Nat.dvd_of_mod_eq_zero h0
  have hrlt : (v i).toNat % j < j := Nat.mod_lt _ (by omega)
  rw [Nat.mul_one]
  have hmin : 1 ≤ min ((v i).toNat % j) (j - (v i).toNat % j) := by
    apply le_min <;> omega
  calc j ≤ k + 2 := hjk
    _ = (k + 2) * 1 := by ring
    _ ≤ (k + 2) * min ((v i).toNat % j) (j - (v i).toNat % j) := Nat.mul_le_mul_left _ hmin

/-- **Crux A4, inductive, leave-one-out primitive, and divisor-complete.** -/
def BridgeDisjunctionQPrimInd2 : Prop :=
  ∀ k : ℕ, 11 ≤ k →
    (∀ k' : ℕ, k' < k → ∀ u : Fin (k' + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((k' : ℝ) + 2) ≤ ML u) →
    ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 →
    (∀ l : Fin (k + 1), Finset.univ.gcd (fun j : Fin k => v (l.succAbove j)) = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ k + 2 → ∃ i, (j : ℤ) ∣ v i) →
    ¬ StrongFree v →
    rieszSharpFiresQ v ∨
    ∃ p q : ℕ, 0 < q ∧
      ∀ i, q ≤ (k + 2) * min ((v i).toNat * p % q) (q - (v i).toNat * p % q)

/-- The divisor-complete atom implies the inductive atom (so it is the weaker of the two). -/
theorem ind_of_ind2 (h : BridgeDisjunctionQPrimInd2) : BridgeDisjunctionQPrimInd := by
  intro k hk ih v hv hprim hl1o hSF
  by_cases hdiv : ∀ j : ℕ, 2 ≤ j → j ≤ k + 2 → ∃ i, (j : ℤ) ∣ v i
  · exact h k hk ih v hv hprim hl1o hdiv hSF
  · push Not at hdiv
    obtain ⟨j, hj2, hjk, hnd⟩ := hdiv
    exact Or.inr ⟨1, j, by omega, witness_of_missing_divisor v hv j hj2 hjk hnd⟩

/-- **Four-atom theorem with the divisor-complete inductive crux (VERIFIED).** -/
theorem universalFloor_of_four_atoms_ind2
    (h1 : StrongFreeWindowTiny) (h2 : DissociatedOctetWitness)
    (hwinB : ∀ k : ℕ, k ≤ 10 → ∀ v : Fin (k + 1) → ℤ, (∀ i, 0 < v i) → ¬ StrongFree v →
        1 / ((k : ℝ) + 2) ≤ ML v)
    (hdisj : BridgeDisjunctionQPrimInd2) : UniversalFloor :=
  universalFloor_of_four_atoms_ind h1 h2 hwinB (ind_of_ind2 hdisj)

end LRSpectrumFull.RoomA4Rosenfeld
