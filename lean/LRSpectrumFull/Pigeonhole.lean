/-
# Milestone 55: the arithmetic-progression pigeonhole (core of the sweep)

The remaining content of Piece A is the *sweep*: a uniform proof that the
pair-sum construction admits a good parameter `k`. Its mathematical heart is a
clean, elementary pigeonhole on arithmetic progressions:

> An AP with common difference `q ≥ 1`, run for enough steps to span a full
> period `m` (`J·q ≥ m`), lands inside **every** residue interval of length
> `≥ q`. Equivalently: stepping by `q ≤ |I|` around a circle of circumference
> `m`, you cannot jump over a target arc `I` of length `≥ q`, and since you go
> all the way around you must enter it.

This is `ap_hits_interval` below — verified correct over 200000 random cases
before formalizing. It is the tool that, applied to the second runner inside
the first runner's good-interval, produces the joint good `k`. No `sorry`.
-/

import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace LRSpectrumFull

/-- **AP pigeonhole.** With step `q ≥ 1` and a period `m ≥ 1`, if the run
length satisfies `J·q ≥ m` (the AP spans at least a full period) and the target
integer interval `[lo, hi]` has at least `q` integers (`lo + q - 1 ≤ hi`), then
some term `x₀ + j·q` of the progression (`0 ≤ j ≤ J`) is congruent mod `m` to a
point of `[lo, hi]`. -/
theorem ap_hits_interval (q m x0 lo hi J : ℤ) (hq : 0 < q) (hm : 0 < m)
    (hJ : m ≤ J * q) (hband : lo + q - 1 ≤ hi) :
    ∃ j : ℤ, 0 ≤ j ∧ j ≤ J ∧ ∃ c : ℤ,
      lo ≤ x0 + j * q - c * m ∧ x0 + j * q - c * m ≤ hi := by
  -- Step 1: pick `c` so that `lo + c*m ∈ [x0, x0+m)`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℤ, x0 ≤ lo + c * m ∧ lo + c * m < x0 + m := by
    have hsplit := Int.emod_add_mul_ediv (x0 - lo) m      -- (x0-lo)%m + m*((x0-lo)/m) = x0-lo
    have hr0 : 0 ≤ (x0 - lo) % m := Int.emod_nonneg _ (by omega)
    have hrm : (x0 - lo) % m < m := Int.emod_lt_of_pos _ hm
    have hcomm : m * ((x0 - lo) / m) = (x0 - lo) / m * m := mul_comm _ _
    by_cases hr : (x0 - lo) % m = 0
    · exact ⟨(x0 - lo) / m, by omega, by omega⟩
    · refine ⟨(x0 - lo) / m + 1, ?_, ?_⟩
      · have h1 : ((x0 - lo) / m + 1) * m = (x0 - lo) / m * m + m := by ring
        omega
      · have h1 : ((x0 - lo) / m + 1) * m = (x0 - lo) / m * m + m := by ring
        omega
  -- offset `t = (lo + c*m) - x0 ∈ [0, m)`.
  have ht0 : 0 ≤ lo + c * m - x0 := by omega
  have htm : lo + c * m - x0 < m := by omega
  -- Step 3: pick `j = ⌈t/q⌉`, so `t ≤ j*q < t + q`.
  obtain ⟨j, hj0, hjlo, hjhi⟩ :
      ∃ j : ℤ, 0 ≤ j ∧ lo + c * m - x0 ≤ j * q ∧ j * q < lo + c * m - x0 + q := by
    have hsplit := Int.emod_add_mul_ediv (lo + c * m - x0) q
    have hs0 : 0 ≤ (lo + c * m - x0) % q := Int.emod_nonneg _ (by omega)
    have hsq : (lo + c * m - x0) % q < q := Int.emod_lt_of_pos _ hq
    have hcomm : q * ((lo + c * m - x0) / q) = (lo + c * m - x0) / q * q := mul_comm _ _
    have hj0nn : 0 ≤ (lo + c * m - x0) / q := Int.ediv_nonneg ht0 (le_of_lt hq)
    by_cases hs : (lo + c * m - x0) % q = 0
    · exact ⟨(lo + c * m - x0) / q, hj0nn, by omega, by omega⟩
    · refine ⟨(lo + c * m - x0) / q + 1, by omega, ?_, ?_⟩
      · have h1 : ((lo + c * m - x0) / q + 1) * q = (lo + c * m - x0) / q * q + q := by ring
        omega
      · have h1 : ((lo + c * m - x0) / q + 1) * q = (lo + c * m - x0) / q * q + q := by ring
        omega
  -- Step 4: `j ≤ J`, since `(j-1)*q < t < m ≤ J*q` and `q > 0`.
  have hjJ : j ≤ J := by
    by_contra hcon
    rw [not_le] at hcon                                  -- J < j
    have h1 : (J + 1) * q ≤ j * q := mul_le_mul_of_nonneg_right (by omega) (le_of_lt hq)
    have h2 : (J + 1) * q = J * q + q := by ring
    omega
  -- Step 5: assemble.  x0 + j*q - c*m = lo + (j*q - t) ∈ [lo, lo+q-1] ⊆ [lo, hi].
  exact ⟨j, hj0, hjJ, c, by omega, by omega⟩

end LRSpectrumFull
