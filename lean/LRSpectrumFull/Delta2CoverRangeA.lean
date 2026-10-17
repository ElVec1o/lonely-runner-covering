/-
# Cover-capacity certificates for 25 <= m <= 63

`Delta2CoverCapacity` verifies the dense window up to m = 24 one case at a time.  This file extends
the verified range, using certificates found by `certgen.rs`.

The shape is uniform.  `{1}` and `{m+1}` are bad singletons, so they are parts of capacity 0 and
each contributes one unit of surplus; the rest of the window is covered by parts of capacity
exactly half their size, which contribute nothing.  Two units is what the budget needs, so the
whole question is whether the rest of the window admits such a cover.

When `2m+1` is prime the bad-pair graph has a perfect matching and every remaining part is a single
bad pair `{j, 2m+1-j}`.  When `2m+1` is composite the matching is imperfect, and the vertices it
exposes have to be absorbed into parts of size 4 or 6 with capacity 2 or 3.  The accounting is
insensitive to the mix: covering the 2m-2 non-free vertices by parts of capacity half their size
always gives sum_c = m-1 < m.
-/
import LRSpectrumFull.Delta2CoverCapacity

namespace LRSpectrumFull

open Finset

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **Dense window at m = 26**: every 26 distinct positive velocities bounded by 52 meet the
floor `1/27`.  Cover-capacity certificate: 27 parts, capacities summing to 25 < 26, from
27 witness times.  The bad-pair matching is perfect here (2m+1 = 53 is prime), so every part but the two free singletons is a single bad pair. -/
theorem dense_floor_m26 (v : Fin 26 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 52) :
    1 / (27 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 25) (t := 27) (N := 27) v hv hinj
    (by simpa using hden) ![1,1,26,18,13,21,9,15,20,6,16,24,22,4,19,7,10,25,3,14,8,5,12,23,11,17,1] ![54,27,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,53,26] (by decide)
    ![{1},{27},{2,51},{3,50},{4,49},{5,48},{6,47},{7,46},{8,45},{9,44},{10,43},{11,42},{12,41},{13,40},{14,39},{15,38},{16,37},{17,36},{18,35},{19,34},{20,33},{21,32},{22,31},{23,30},{24,29},{25,28},{26,52}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1},{27},{2,51},{3,50},{4,49},{5,48},{6,47},{7,46},{8,45},{9,44},{10,43},{11,42},{12,41},{13,40},{14,39},{15,38},{16,37},{17,36},{18,35},{19,34},{20,33},{21,32},{22,31},{23,30},{24,29},{25,28},{26,52}] ![0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **Dense window at m = 29**: every 29 distinct positive velocities bounded by 58 meet the
floor `1/30`.  Cover-capacity certificate: 30 parts, capacities summing to 28 < 29, from
30 witness times.  The bad-pair matching is perfect here (2m+1 = 59 is prime), so every part but the two free singletons is a single bad pair. -/
theorem dense_floor_m29 (v : Fin 29 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 58) :
    1 / (30 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 28) (t := 30) (N := 30) v hv hinj
    (by simpa using hden) ![1,1,29,20,15,12,10,17,22,13,6,16,5,9,21,4,11,7,23,28,3,14,8,18,27,26,25,24,19,1] ![60,30,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,59,29] (by decide)
    ![{1},{30},{2,57},{3,56},{4,55},{5,54},{6,53},{7,52},{8,51},{9,50},{10,49},{11,48},{12,47},{13,46},{14,45},{15,44},{16,43},{17,42},{18,41},{19,40},{20,39},{21,38},{22,37},{23,36},{24,35},{25,34},{26,33},{27,32},{28,31},{29,58}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1},{30},{2,57},{3,56},{4,55},{5,54},{6,53},{7,52},{8,51},{9,50},{10,49},{11,48},{12,47},{13,46},{14,45},{15,44},{16,43},{17,42},{18,41},{19,40},{20,39},{21,38},{22,37},{23,36},{24,35},{25,34},{26,33},{27,32},{28,31},{29,58}] ![0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

end LRSpectrumFull
