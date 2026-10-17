/-
# Cover-capacity certificate for m = 25

`2m+1 = 51 = 3 * 17` is composite, so the uniform prime argument does not apply and the
LP bound is not sufficient (the fractional matching number of the bad-velocity hypergraph is 24,
which is below `m = 25`, see (development file, not part of this archive)).  The certificate below was found by
`code/dense/src/pool/pool.rs` (column pool: unions of minimal bad sets of size at most 8, closed under
capacity-preserving extension), an LP dual restricted to zero-reduced-cost columns
(`code/dense/src/pool/dumpkept.py`), a MIP over those columns (`code/dense/src/pool/mipkept.py`), and
re-checked by the independent exact checker `code/dense/src/pool/emit.rs`.
-/
import LRSpectrumFull.Delta2CoverCapacity

namespace LRSpectrumFull

open Finset

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = 25** (`2m+1 = 51`, composite): every 25 distinct positive velocities
bounded by 50 meet the floor `1/26`.  Cover-capacity certificate: 12 parts, capacities
summing to 24 < 25, using 43 witness times. -/
theorem dense_floor_m25 (v : Fin 25 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 50) :
    1 / (26 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 24) (t := 12) (N := 43) v hv hinj
    (by simpa using hden) ![1,1,1,1,1,1,1,1,1,4,14,5,10,13,25,9,11,3,7,19,23,15,17,19,15,11,28,25,7,2,10,8,6,23,13,4,13,27,21,11,23,31,26] ![26,52,18,19,20,21,22,24,25,51,51,51,51,51,52,52,52,52,52,52,52,52,52,58,59,65,65,67,71,41,43,45,47,48,49,49,50,56,65,68,71,71,73] (by decide)
    ![{26},{1},{18,36},{19,38},{20,40},{21,42},{22,44},{24,48},{25,50},{13,38},{11,40},{10,41},{5,46},{4,47},{25,27},{23,29},{19,33},{17,35},{15,37},{11,41},{9,43},{7,45},{3,49},{3,6},{4,8},{6,12},{7,14},{8,16},{10,20},{20,21,41},{13,30,43},{17,28,45},{8,39,47},{23,25,48},{15,34,49},{12,37,49},{23,27,50},{2,27,29},{3,31,34},{6,31,37},{3,34,37},{16,32,39},{14,28,45}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{2,23,24,25,27,29,48,50},{1,26},{26},{3,6,12,15,31,34,37,49},{1,7,14,17,26,28,35,45},{1,22,26,44},{4,8,16,26,32,39,47},{1,9,13,19,30,33,38,43},{1,18,36},{1},{5,46},{10,11,20,21,26,40,41,42}] ![4,0,0,4,3,1,3,4,1,0,1,3]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

end LRSpectrumFull
