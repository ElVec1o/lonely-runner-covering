/-
# Cover-capacity certificates: beating the LP bound

`floor_of_frac_blocking` bounds the covering number of the bad-velocity hypergraph by its
*fractional* matching number.  For `2m+1 = 21, 33, 49` that bound is exactly `m` — tight, so LP
duality can never close those cases.  What remains is the integrality gap, and this file closes it.

Write `W` for the complement of the velocity set inside `[1, 2(k+1)]`; it has exactly `k+1`
elements.  A family with no witness makes `W` *independent*: `W` contains no bad-velocity set.
Independence is bounded part by part — if `U_1, …, U_t` cover `[1,2(k+1)]` and each `U_i` has the
property that any subset of more than `c_i` elements already contains a bad set, then

        k+1 = |W| ≤ ∑ |W ∩ U_i| ≤ ∑ c_i,

so `∑ c_i < k+1` is a contradiction.  The per-part capacities are Chvátal–Gomory cuts: a part of
six velocities with capacity three is invisible to the LP, which only ever sees `1/2` per vertex.

Certificates below were found by integer programming and re-verified in exact integer arithmetic.
-/
import LRSpectrumFull.Delta2FracBlocking

namespace LRSpectrumFull

open Finset

/-- **The cover-capacity certificate.**  `bad j` over-approximates the bad-velocity set of the
time `p j / q j`; the parts `U i` cover the window, and more than `c i` elements of `U i` always
contain some `bad j`.  If `∑ c i < k+1` the floor is unconditional. -/
theorem floor_of_cover_capacity {k t N : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 (2 * (k + 1)))
    (p q : Fin N → ℕ) (hq : ∀ j, 0 < q j) (bad : Fin N → Finset ℕ)
    (hbad : ∀ j, ∀ x, 1 ≤ x → x ≤ 2 * (k + 1) →
      goodAt k x (p j) (q j) = false → x ∈ bad j)
    (U : Fin t → Finset ℕ) (c : Fin t → ℕ)
    (hcover : Finset.Icc 1 (2 * (k + 1)) ⊆ Finset.univ.biUnion U)
    (hcap : ∀ i, ∀ T ∈ (U i).powerset, c i < T.card → ∃ j, bad j ⊆ T)
    (hsum : ∑ i, c i < k + 1) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  by_contra hcon
  push_neg at hcon
  set Vs : Finset ℕ := Finset.univ.image fun i => (v i).toNat with hVs
  -- every certificate time is defeated, so every `bad j` meets the velocity set
  have hmeet : ∀ j : Fin N, ∃ x ∈ bad j, x ∈ Vs := by
    intro j
    by_contra hno
    push_neg at hno
    refine absurd (cube_floor_of_witness v hv (p j) (q j) (hq j) (fun i => ?_)) (not_le.mpr hcon)
    by_contra hg
    have hmem : (v i).toNat ∈ Vs := by
      simp only [hVs, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩
    have h1 := (Finset.mem_Icc.mp (hden i)).1
    have h2 := (Finset.mem_Icc.mp (hden i)).2
    have hfalse : goodAt k (v i).toNat (p j) (q j) = false := by
      simpa [goodAt, decide_eq_false_iff_not] using hg
    exact hno _ (hbad j _ h1 h2 hfalse) hmem
  -- the complement `W` has exactly `k+1` elements
  set W : Finset ℕ := Finset.Icc 1 (2 * (k + 1)) \ Vs with hW
  have hVsub : Vs ⊆ Finset.Icc 1 (2 * (k + 1)) := by
    intro x hx
    simp only [hVs, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hden i
  have hVcard : Vs.card = k + 1 := by
    rw [hVs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hWcard : W.card = k + 1 := by
    rw [hW, Finset.card_sdiff, Finset.inter_eq_left.mpr hVsub, hVcard, Nat.card_Icc]
    omega
  -- each part contributes at most its capacity
  have hpart : ∀ i, (W ∩ U i).card ≤ c i := by
    intro i
    by_contra hgt
    push_neg at hgt
    obtain ⟨j, hj⟩ := hcap i (W ∩ U i) (Finset.mem_powerset.mpr Finset.inter_subset_right) hgt
    obtain ⟨x, hxb, hxV⟩ := hmeet j
    have : x ∈ W := (Finset.mem_inter.mp (hj hxb)).1
    exact (Finset.mem_sdiff.mp this).2 hxV
  -- and the parts cover `W`
  have hWcov : W ⊆ Finset.univ.biUnion fun i => W ∩ U i := by
    intro x hx
    have hxI : x ∈ Finset.Icc 1 (2 * (k + 1)) := (Finset.mem_sdiff.mp hx).1
    obtain ⟨i, _, hxU⟩ := Finset.mem_biUnion.mp (hcover hxI)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hxU⟩⟩
  have : (k + 1) ≤ ∑ i, c i := by
    calc (k + 1) = W.card := hWcard.symm
      _ ≤ (Finset.univ.biUnion fun i => W ∩ U i).card := Finset.card_le_card hWcov
      _ ≤ ∑ i, (W ∩ U i).card := Finset.card_biUnion_le
      _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ => hpart i
  omega


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **Dense window at m = 10** (`2m+1 = 21`, composite): every 10 distinct positive velocities
bounded by 20 meet the floor `1/11`.  Cover-capacity certificate: 5 parts,
capacities summing to 9 < 10, using 14 witness times.  The fractional
matching number here is exactly 10, so `floor_of_frac_blocking` cannot reach this case. -/
theorem dense_floor_m10 (v : Fin 10 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 20) :
    1 / (11 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 9) (t := 5) (N := 14) v hv hinj
    (by simpa using hden) ![1,1,1,5,12,15,1,7,9,5,1,1,7,5] ![22,11,8,21,25,32,7,22,28,31,9,10,18,22] (by decide) ![{1},{11},{8,16},{4,17},{2,4},{2,15,17},{7,14},{3,19},{3,6},{6,12,19},{9,18},{10,20},{5,13,18},{9,13}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1},{11},{2,4,8,15,16,17},{3,6,7,12,14,19},{5,9,10,13,18,20}] ![0,0,3,3,3] (by decide) (by decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **Dense window at m = 16** (`2m+1 = 33`, composite): every 16 distinct positive velocities
bounded by 32 meet the floor `1/17`.  Cover-capacity certificate: 7 parts,
capacities summing to 15 < 16, using 22 witness times.  The fractional
matching number here is exactly 16, so `floor_of_frac_blocking` cannot reach this case. -/
theorem dense_floor_m16 (v : Fin 16 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 32) :
    1 / (17 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 15) (t := 7) (N := 22) v hv hinj
    (by simpa using hden) ![1,1,7,16,8,18,10,13,5,5,15,1,13,13,1,1,14,1,4,15,6,11] ![34,17,33,33,31,37,33,40,49,29,43,15,33,34,11,12,33,16,33,34,49,50] (by decide) ![{1},{17},{14,19},{2,31},{4,27,31},{2,4},{10,23},{3,6},{10,20,29},{6,23,29},{3,20,23},{15,30},{5,28},{13,21},{11,22},{12,24},{7,26},{16,32},{8,25},{9,25},{8,16},{9,18,32}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1},{17},{2,4,14,19,27,31},{3,6,10,20,23,29},{5,13,15,21,28,30},{7,11,12,22,24,26},{8,9,16,18,25,32}] ![0,0,3,3,3,3,3] (by decide) (by decide) (by decide)
  norm_num at h
  exact h



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **Dense window at m = 24** (`2m+1 = 49 = 7^2`): every 24 distinct positive velocities bounded
by 48 meet the floor `1/25`.  Cover-capacity certificate: 10 parts, capacities summing to
23 < 24, using 33 witness times.  The fractional matching number is exactly 24, so
`floor_of_frac_blocking` cannot reach this case.  Overlapping parts are essential here: folding the
free singleton `1` into a part adds an element at no capacity cost. -/
theorem dense_floor_m24 (v : Fin 24 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 48) :
    1 / (25 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 23) (t := 10) (N := 33) v hv hinj
    (by simpa using hden) ![1,1,24,13,16,23,7,9,5,1,1,6,12,1,14,19,1,5,12,15,3,4,10,11,1,23,7,15,15,1,1,11,22] ![25,50,49,50,49,49,50,64,71,19,22,49,49,15,57,71,21,49,59,73,49,49,61,68,18,75,61,49,67,20,24,40,49] (by decide)
    ![{25},{1},{2,47},{23,27},{3,46},{17,32},{7,43},{7,14},{14,28,43},{19,38},{22,44},{8,41},{4,45},{15,30,45},{4,8},{15,30,41},{21,42},{10,39},{5,10},{5,34,39},{16,33},{12,37},{6,12},{6,31,37},{18,36},{13,26},{9,26,35},{13,36},{9,18},{20,40},{24,48},{11,29,40},{20,29}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1,25},{2,23,27,47},{1,3,17,32,46},{1,7,14,28,43},{19,22,25,38,44},{4,8,15,30,41,45},{5,10,21,34,39,42},{6,12,16,31,33,37},{9,13,18,26,35,36},{11,20,24,29,40,48}] ![0,2,2,2,2,3,3,3,3,3]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h



set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = 17** (`2m+1 = 35`, composite): every 17 distinct positive velocities
bounded by 34 meet the floor `1/18`.  Cover-capacity certificate: 6 parts, capacities
summing to 16 < 17, using 26 witness times. -/
theorem dense_floor_m17 (v : Fin 17 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 34) :
    1 / (18 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 16) (t := 6) (N := 26) v hv hinj
    (by simpa using hden) ![1,1,1,11,17,11,19,7,13,6,11,1,1,4,1,12,13,8,19,9,15,9,13,14,11,5] ![18,36,14,35,35,58,40,33,33,35,36,12,17,35,15,35,36,59,52,32,47,35,35,47,43,51] (by decide)
    ![{18},{1},{14,28},{16,19},{2,33},{5,16,21},{2,19,21},{14,19,33},{5,28,33},{6,29},{13,23},{12,24},{17,34},{9,26},{15,30},{3,32},{11,25},{7,15,22},{11,22,30},{7,25,32},{3,22,25},{4,31},{8,27},{10,20,27},{4,8},{10,20,31}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1,18},{2,5,14,16,18,19,21,28,33},{6,13,18,23,29},{9,12,17,24,26,34},{3,7,11,15,22,25,30,32},{1,4,8,10,18,20,27,31}] ![0,4,2,3,4,3]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = 19** (`2m+1 = 39`, composite): every 19 distinct positive velocities
bounded by 38 meet the floor `1/20`.  Cover-capacity certificate: 6 parts, capacities
summing to 18 < 19, using 27 witness times. -/
theorem dense_floor_m19 (v : Fin 19 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 38) :
    1 / (20 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 18) (t := 6) (N := 27) v hv hinj
    (by simpa using hden) ![1,1,1,21,1,9,13,9,14,17,3,5,4,1,4,10,11,1,10,17,13,12,1,1,1,16,5] ![40,13,18,44,14,40,40,53,39,53,37,31,37,15,39,49,53,16,39,40,35,47,20,17,19,39,56] (by decide)
    ![{1},{13,26},{18,36},{2,21,23},{14,28},{9,31},{3,37},{6,12},{14,25},{3,25,28},{12,25,37},{6,25,31,37},{9,28,37},{15,30},{10,29},{5,10},{5,24,29},{16,32},{4,35},{7,33},{8,27,35},{4,8},{20},{17,34},{19,38},{17,22},{11,22,34}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{1,2,13,18,21,23,26,36},{3,6,9,12,14,25,28,31,37},{5,10,15,24,29,30},{4,7,8,16,27,32,33,35},{1,20},{11,17,19,20,22,34,38}] ![4,4,3,4,0,3]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = 22** (`2m+1 = 45`, composite): every 22 distinct positive velocities
bounded by 44 meet the floor `1/23`.  Cover-capacity certificate: 7 parts, capacities
summing to 21 < 22, using 31 witness times. -/
theorem dense_floor_m22 (v : Fin 22 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 44) :
    1 / (23 : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := 21) (t := 7) (N := 31) v hv hinj
    (by simpa using hden) ![1,17,5,14,21,10,11,1,4,19,26,13,7,1,16,9,11,3,4,1,1,1,17,13,22,11,24,1,8,7,1] ![16,52,59,45,61,59,64,18,45,45,59,36,64,15,45,46,56,41,41,46,20,21,45,45,45,43,49,22,45,46,23] (by decide)
    ![{16,32},{3,6},{12,24,35},{16,29},{3,29,32},{6,12},{6,29,35},{18,36},{11,34},{19,26},{9,25,34},{11,25,36},{9,18},{15,30},{14,31},{5,41},{5,10},{14,27,41},{10,31,41},{1},{20,40},{21,42},{8,37},{7,38},{2,43},{4,39,43},{2,4},{22,44},{17,28},{13,33},{23}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{3,6,12,16,24,29,32,35},{9,11,18,19,25,26,34,36},{5,10,14,15,27,30,31,41},{1,8,20,21,37,40,42},{2,4,7,38,39,43},{1,13,17,22,28,33,44},{1,23}] ![4,4,4,3,3,3,0]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h


end LRSpectrumFull
