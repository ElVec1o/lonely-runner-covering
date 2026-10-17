/-
# Rosenfeld's Lemma 5, assembled

If the velocities `vᵢ` for `i ≠ l` are all divisible by `q ≥ 2`, and the distinguished velocity `v l`
is coprime to `q`, then a lonely time for the others can be improved into a lonely time for
everybody, at the cost of dropping the distinguished runner's guarantee to `1/4`.

The mechanism, from `EvenlySpaced.lean`: shifting the time by `j/q` is invisible to every velocity
divisible by `q` (`nid_shift_of_dvd`), while it moves the distinguished velocity to the residue
`j'` determined by `v l * j ≡ j' (mod q)` (`nid_shift_of_congr`).  Coprimality makes `j ↦ v l * j` a
bijection on residues, so `j` can be chosen to realise whichever `j'` `exists_far_point` says is far
from the integers.

For `k ≥ 3` the resulting `1/4` is at least `1/(k+1)`, which is what Lemma 5 needs.
-/

import LRSpectrumFull.EvenlySpaced
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull

/-- Coprimality lets any target residue be hit.  Bezout gives `1 = w*A + q*B`, so `A*j'` sends `w`
to `j'` modulo `q`; reducing it modulo `q` puts the multiplier in `[0, q)`. -/
theorem exists_mul_congr (w q j' : ℕ) (hq : 0 < q) (hcop : Nat.Coprime w q) :
    ∃ j : ℕ, j < q ∧ ∃ c : ℤ, (w : ℤ) * (j : ℤ) = (j' : ℤ) + (q : ℤ) * c := by
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hb : ((Nat.gcd w q : ℕ) : ℤ) = (w : ℤ) * Nat.gcdA w q + (q : ℤ) * Nat.gcdB w q :=
    Nat.gcd_eq_gcd_ab w q
  rw [Nat.Coprime.gcd_eq_one hcop] at hb
  set A : ℤ := Nat.gcdA w q with hA
  set B : ℤ := Nat.gcdB w q with hB
  set m : ℤ := (A * (j' : ℤ)) % (q : ℤ) with hm
  have hm0 : 0 ≤ m := Int.emod_nonneg _ (by omega)
  have hmq : m < (q : ℤ) := Int.emod_lt_of_pos _ hqz
  have hdec := Int.ediv_add_emod (A * (j' : ℤ)) (q : ℤ)
  have hb' : (1 : ℤ) = (w : ℤ) * A + (q : ℤ) * B := by exact_mod_cast hb
  refine ⟨m.toNat, by omega, -(B * (j' : ℤ) + (w : ℤ) * (A * (j' : ℤ) / (q : ℤ))), ?_⟩
  have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0
  rw [hcast, hm]
  linear_combination (w : ℤ) * hdec - (j' : ℤ) * hb'

/-- **Lemma 5's core (VERIFIED).**

`t` is lonely at level `c` for every runner but `l`; all those velocities are divisible by `q ≥ 2`;
and `v l` is coprime to `q`.  Then the whole configuration is lonely at level `min c (1/4)`. -/
theorem lemma5_core {k : ℕ} (v : Fin (k + 1) → ℤ) (l : Fin (k + 1)) (q : ℕ) (hq : 2 ≤ q)
    (hdvd : ∀ i, i ≠ l → (q : ℤ) ∣ v i)
    (hcop : Nat.Coprime (v l).toNat q) (hvl : 0 < v l)
    (t : ℝ) (c : ℝ) (hfar : ∀ i, i ≠ l → c ≤ nearestIntDist ((v i : ℝ) * t)) :
    min c (1 / 4) ≤ ML v := by
  have hq0 : 0 < q := by omega
  obtain ⟨j', hj'lt, hj'far⟩ := exists_far_point ((v l : ℝ) * t) q hq
  obtain ⟨j, hjlt, hcongr⟩ := exists_mul_congr (v l).toNat q j' hq0 hcop
  have hvlcast : ((v l).toNat : ℤ) = v l := Int.toNat_of_nonneg hvl.le
  set t' : ℝ := t + (j : ℝ) / (q : ℝ) with ht'
  have hgap : min c (1 / 4) ≤ gap v t' := by
    refine le_gap v t' _ (fun i => ?_)
    by_cases hi : i = l
    · subst hi
      have hc2 : ∃ c' : ℤ, (v i : ℤ) * (j : ℤ) = (j' : ℤ) + (q : ℤ) * c' := by
        obtain ⟨c', hc'⟩ := hcongr
        exact ⟨c', by rw [← hvlcast]; exact hc'⟩
      rw [ht', nid_shift_of_congr (v i) q hq0 j j' t hc2]
      exact le_trans (min_le_right _ _) hj'far
    · rw [ht', nid_shift_of_dvd (v i) q hq0 j (hdvd i hi) t]
      exact le_trans (min_le_left _ _) (hfar i hi)
  exact le_trans hgap (le_csSup (bddAbove_range_gap v) ⟨t', rfl⟩)

/-- **Reduction modulo the denominator is invisible (VERIFIED).**

The last mathematical ingredient of Rosenfeld's Lemma 6.  There a counterexample `w` is replaced by
its residues `v ≡ w (mod (k+1)p)`, the hypothesis produces a good time `t/((k+1)p)` for `v`, and this
lemma transports it back to `w`: the two positions differ by `t * ((w - v)/N)`, an integer. -/
theorem nid_congr_mod (w v : ℤ) (N : ℕ) (hN : 0 < N) (t : ℤ) (h : (N : ℤ) ∣ (w - v)) :
    nearestIntDist ((t : ℝ) * (w : ℝ) / (N : ℝ))
      = nearestIntDist ((t : ℝ) * (v : ℝ) / (N : ℝ)) := by
  obtain ⟨c, hc⟩ := h
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcR : (w : ℝ) - (v : ℝ) = (N : ℝ) * (c : ℝ) := by exact_mod_cast hc
  have hexp : (t : ℝ) * (w : ℝ) / (N : ℝ)
      = (t : ℝ) * (v : ℝ) / (N : ℝ) + ((t * c : ℤ) : ℝ) := by
    field_simp
    push_cast
    linear_combination (t : ℝ) * hcR
  rw [hexp, nid_add_int]

end LRSpectrumFull
