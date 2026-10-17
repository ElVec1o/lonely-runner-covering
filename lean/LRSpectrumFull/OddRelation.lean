/-
# The constructive core of the odd-relation loneliness bound

The bound `no all-odd relation ⟹ ML(v) ≥ 1/4` has an elementary proof: the
"far indicator" measure is `2⁻ⁿ + Σ_S I_S` with `I_S = ∫ ∏_{i∈S} f(vᵢt)`, and
the substitution `t ↦ t + 1/(2·gcd_S)` gives `I_S = (−1)^{Σ(vᵢ/g_S)} I_S`, so
`I_S = 0` whenever `Σ(vᵢ/g_S)` is odd. The remaining input is purely
number-theoretic:

    for a coprime tuple `w`, an all-odd relation exists  ⟺  `Σ wᵢ` is even.

This file formalizes the substantive `⟸` direction **constructively**: given a
Bézout vector `c` (`Σ cᵢwᵢ = 1`, which exists exactly when `gcd = 1`) and
`Σ wᵢ` even, the vector `kᵢ = 1 − (Σ wⱼ)·cᵢ` is all-odd and satisfies
`Σ kᵢwᵢ = 0`. The easy `⟹` direction is `all_odd_relation_sum_even`. No `sorry`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace LRSpectrumFull

open Finset

variable {m : ℕ}

/-- **Constructive `⟸`.** If `w` admits a Bézout combination `∑ cᵢwᵢ = 1`
(equivalently `gcd wᵢ = 1`) and `∑ wᵢ` is even, then there is an **all-odd**
integer relation `∑ kᵢwᵢ = 0`. Witness: `kᵢ = 1 − (∑ wⱼ)·cᵢ`. -/
theorem exists_all_odd_relation (w c : Fin m → ℤ)
    (hbez : ∑ i, c i * w i = 1) (heven : Even (∑ i, w i)) :
    ∃ k : Fin m → ℤ, (∀ i, Odd (k i)) ∧ ∑ i, k i * w i = 0 := by
  obtain ⟨r, hr⟩ := heven
  refine ⟨fun i => 1 - (∑ j, w j) * c i, fun i => ⟨-(r * c i), ?_⟩, ?_⟩
  · rw [hr]; ring
  · have key : ∑ i, (1 - (∑ j, w j) * c i) * w i
        = (∑ i, w i) - (∑ j, w j) * (∑ i, c i * w i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key, hbez, mul_one, sub_self]

/-- **Easy `⟹`.** If an all-odd relation `∑ kᵢwᵢ = 0` exists, then `∑ wᵢ` is
even (reduce mod `2`: each `kᵢ ≡ 1`). -/
theorem all_odd_relation_sum_even (w k : Fin m → ℤ)
    (hodd : ∀ i, Odd (k i)) (hrel : ∑ i, k i * w i = 0) :
    Even (∑ i, w i) := by
  have h2 : (2 : ℤ) ∣ ∑ i, w i := by
    have : (∑ i, w i) - (∑ i, k i * w i) = ∑ i, (1 - k i) * w i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    have hdvd : (2 : ℤ) ∣ ∑ i, (1 - k i) * w i := by
      apply Finset.dvd_sum
      intro i _
      obtain ⟨s, hs⟩ := hodd i
      exact ⟨-(s * w i), by rw [hs]; ring⟩
    rw [hrel, sub_zero] at this
    rwa [this]
  obtain ⟨s, hs⟩ := h2
  exact ⟨s, by rw [hs]; ring⟩

/-- The biconditional, packaged: with a Bézout witness, an all-odd relation
exists iff `∑ wᵢ` is even. -/
theorem all_odd_relation_iff_sum_even (w c : Fin m → ℤ)
    (hbez : ∑ i, c i * w i = 1) :
    (∃ k : Fin m → ℤ, (∀ i, Odd (k i)) ∧ ∑ i, k i * w i = 0) ↔ Even (∑ i, w i) := by
  constructor
  · rintro ⟨k, hodd, hrel⟩; exact all_odd_relation_sum_even w k hodd hrel
  · intro h; exact exists_all_odd_relation w c hbez h

end LRSpectrumFull
