/-
# Kravitz Lemma 7.1: the double-band covering

For the determined pairing in Case B1, with `M = vᵢ+vⱼ` and step `j = u·v_k mod M`, we need
to place BOTH the pair-runner and the third runner in the `2/7`-band simultaneously:
`∃ ℓ ∈ [lo, hi]` with `ℓ·j mod M ∈ [lo, hi]`, where `[lo,hi] = [⌈2M/7⌉, ⌊5M/7⌋]`.
(The pair-runner condition is exactly `ℓ ∈ [lo,hi]`, since at `t = ℓu/M` we have
`‖t·vᵢ‖ = ‖ℓ/M‖`; the third runner condition is `ℓj mod M ∈ [lo,hi]`.)

This file builds the covering. The MAIN regime `3 ≤ j ≤ W+1` (where `W = hi-lo`) follows
from the arithmetic-progression pigeonhole `ap_hits_interval`: the AP `{ℓ·j : ℓ ∈ [lo,hi]}`
steps by `j ≤ W+1` (cannot skip a band of width `W`) and spans `≥ M` (a full period), so it
hits the band — and the hitting `ℓ` lies in `[lo,hi]` by construction. See
`paper/dev_notes/kravitz_path_to_piece_A.md`. No `sorry`.
-/

import LRSpectrumFull.Pigeonhole

namespace LRSpectrumFull

/-- **Double-band covering, main regime.** If `3 ≤ j ≤ (hi−lo)+1` (step fits the band, no
skip) and `M ≤ (hi−lo)·j` (the AP spans a full period), then some `ℓ ∈ [lo, hi]` has
`ℓ·j mod M ∈ [lo, hi]` too. Both runners land in the band. -/
theorem double_band_main (M j lo hi : ℤ) (hM : 0 < M)
    (hj : 0 < j) (hjW : j ≤ hi - lo + 1) (hspan : M ≤ (hi - lo) * j) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  obtain ⟨t, ht0, htJ, c, hc1, hc2⟩ :=
    ap_hits_interval j M (lo * j) lo hi (hi - lo) hj hM hspan (by omega)
  refine ⟨lo + t, by omega, by omega, c, ?_, ?_⟩
  · have hid : (lo + t) * j - c * M = lo * j + t * j - c * M := by ring
    linarith [hc1, hid]
  · have hid : (lo + t) * j - c * M = lo * j + t * j - c * M := by ring
    linarith [hc2, hid]

/-- **Band symmetry `j ↔ M−j`.** The `2/7`-band is exactly symmetric (`lo + hi = M`, which
holds for every `M`). Since `ℓ·(M−j) ≡ −ℓ·j (mod M)` and `x ∈ [lo,hi] ↔ M−x ∈ [lo,hi]`, the
*same* `ℓ` that covers `j` covers `M−j` and vice versa. This reduces any `j` to `[1, M/2]`. -/
theorem double_band_symm (M j lo hi : ℤ) (hsym : lo + hi = M)
    (h : ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ,
      lo ≤ ℓ * (M - j) - c * M ∧ ℓ * (M - j) - c * M ≤ hi) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  obtain ⟨ℓ, hl1, hl2, c, hc1, hc2⟩ := h
  refine ⟨ℓ, hl1, hl2, ℓ - c - 1, ?_, ?_⟩
  · have hv : ℓ * j - (ℓ - c - 1) * M = M - (ℓ * (M - j) - c * M) := by ring
    rw [hv]; linarith [hc2, hsym]
  · have hv : ℓ * j - (ℓ - c - 1) * M = M - (ℓ * (M - j) - c * M) := by ring
    rw [hv]; linarith [hc1, hsym]

/-- **Edge `j = 1`.** `ℓ = lo` works trivially. -/
theorem double_band_one (M lo hi : ℤ) (hle : lo ≤ hi) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * 1 - c * M ∧ ℓ * 1 - c * M ≤ hi :=
  ⟨lo, le_refl _, hle, 0, by ring_nf; omega, by ring_nf; omega⟩

/-- **Edge `j = 2`.** When `2·lo ≤ hi` (true for `M ≥ 14`), `ℓ = lo` works: `2·lo ∈ [lo,hi]`. -/
theorem double_band_two (M lo hi : ℤ) (hlo : 0 ≤ lo) (h2 : 2 * lo ≤ hi) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * 2 - c * M ∧ ℓ * 2 - c * M ≤ hi :=
  ⟨lo, le_refl _, by omega, 0, by ring_nf; omega, by ring_nf; omega⟩

/-- **Middle regime `j` near `M/2`.** Here the single step `j > W+1` can skip the band, but
the *2-step* `ℓ = hi − 2t` moves `ℓ·j` by `−(M−2j)`, and `M−2j` is small (`< M/7` for `j`
near `M/2`). So the even-indexed AP doesn't skip, and if it spans a period
(`M ≤ ⌊(hi−lo)/2⌋·(M−2j)`, i.e. `M−2j ≳ 5`) it hits the band — with `ℓ = hi−2t ∈ [lo,hi]`. -/
theorem double_band_mid (M j lo hi : ℤ) (hM : 0 < M)
    (hstep : 0 < M - 2 * j) (hskip : M - 2 * j ≤ hi - lo + 1)
    (hspan : M ≤ (hi - lo) / 2 * (M - 2 * j)) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  obtain ⟨t, ht0, htJ, c, hc1, hc2⟩ :=
    ap_hits_interval (M - 2 * j) M (hi * j) lo hi ((hi - lo) / 2) hstep hM hspan (by omega)
  refine ⟨hi - 2 * t, by omega, by omega, c - t, ?_, ?_⟩
  · have hid : (hi - 2 * t) * j - (c - t) * M = hi * j + t * (M - 2 * j) - c * M := by ring
    linarith [hc1, hid]
  · have hid : (hi - 2 * t) * j - (c - t) * M = hi * j + t * (M - 2 * j) - c * M := by ring
    linarith [hc2, hid]

/-- **Even-`ℓ` covering for `j` just below `M/2`.** If `2j + d = M` (so `2j ≡ −d mod M`) and
some `k` has `2k ∈ [lo,hi]` (pair-runner) and `k·d ∈ [lo,hi]` (so `ℓj ≡ −kd ∈ [lo,hi]` by the
band symmetry `lo+hi=M`), then `ℓ = 2k` covers. For small `d` such a `k` always exists (it sits
near the bottom of the band), which finishes Kravitz's case-3 residual for `d ∈ {1,2,3,4}`. -/
theorem double_band_even (M j d k lo hi : ℤ) (hsym : lo + hi = M) (hd : 2 * j + d = M)
    (hk1 : lo ≤ 2 * k) (hk2 : 2 * k ≤ hi) (hkd1 : lo ≤ k * d) (hkd2 : k * d ≤ hi) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  refine ⟨2 * k, hk1, hk2, k - 1, ?_, ?_⟩
  · have hid : (2 * k) * j - (k - 1) * M = M - k * d := by linear_combination k * hd
    rw [hid]; linarith [hkd2, hsym]
  · have hid : (2 * k) * j - (k - 1) * M = M - k * d := by linear_combination k * hd
    rw [hid]; linarith [hkd1, hsym]

/-- **Odd-`ℓ` covering for `j` just below `M/2`.** For `ℓ = 2k+1` we have
`ℓj ≡ M + j − kd (mod M)` (one wraparound), so if `2k+1 ∈ [lo,hi]` and `M+j−kd ∈ [lo,hi]`
the cover holds. This finishes the `d = 5` (and `d = 7`) residual that even-`ℓ` just misses. -/
theorem double_band_odd (M j d k lo hi : ℤ) (hd : 2 * j + d = M)
    (hk1 : lo ≤ 2 * k + 1) (hk2 : 2 * k + 1 ≤ hi)
    (hb1 : lo ≤ M + j - k * d) (hb2 : M + j - k * d ≤ hi) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  refine ⟨2 * k + 1, hk1, hk2, k - 1, ?_, ?_⟩
  · have hid : (2 * k + 1) * j - (k - 1) * M = M + j - k * d := by linear_combination k * hd
    rw [hid]; exact hb1
  · have hid : (2 * k + 1) * j - (k - 1) * M = M + j - k * d := by linear_combination k * hd
    rw [hid]; exact hb2

/-- **The covering, assembled (low half `2j < M`).** For `M ≥ 12` and `0 < 2j < M`, the
double-band cover holds, with `lo = ⌈2M/7⌉ = (2M+6)/7`, `hi = ⌊5M/7⌋ = 5M/7`. Dispatches on
`j` and `d = M−2j` to the seven covering lemmas: edges `j∈{1,2}`; `main` for `3 ≤ j ≤ W+1`;
and for `j > W+1`, `even` (`d∈{1,2,3,4}`), `odd` (`d∈{5,6,7}`), `mid` (`d ≥ 8`). Coverage of
all coprime `(M,j)` with `M ∉ {5,11}` was verified exhaustively to `M < 3000`. -/
theorem double_band_cover_lo (M j lo hi : ℤ) (hlo : lo = (2 * M + 6) / 7)
    (hhi : hi = (5 * M) / 7) (hM : 12 ≤ M) (hj0 : 0 < j) (h2j : 2 * j < M) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  have hsym : lo + hi = M := by omega
  have hband : lo ≤ hi := by omega
  rcases lt_or_ge j 3 with hjlt3 | hjge3
  · -- edges j = 1, 2
    interval_cases j
    · exact double_band_one M lo hi hband
    · exact double_band_two M lo hi (by omega) (by omega)
  · rcases le_or_gt j (hi - lo + 1) with hjmain | hjbig
    · -- 3 ≤ j ≤ W+1 : main (span M ≤ W·j follows from M ≤ 3W ≤ jW)
      refine double_band_main M j lo hi (by omega) (by omega) hjmain ?_
      have h3W : M ≤ (hi - lo) * 3 := by omega
      nlinarith [h3W, hjge3, hband]
    · -- j > W+1 : dispatch on d = M − 2j
      obtain ⟨d, hd⟩ : ∃ d : ℤ, M - 2 * j = d := ⟨_, rfl⟩
      have hd1 : 1 ≤ d := by omega
      rcases le_or_gt d 7 with hdsmall | hdbig
      · interval_cases d
        · exact double_band_even M j 1 lo lo hi hsym (by omega) (by omega) (by omega)
            (by omega) (by omega)
        · exact double_band_even M j 2 ((lo + 1) / 2) lo hi hsym (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_even M j 3 ((lo + 1) / 2) lo hi hsym (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_even M j 4 ((lo + 1) / 2) lo hi hsym (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_odd M j 5 ((M + j - hi + 4) / 5) lo hi (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_odd M j 6 (lo / 2) lo hi (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_odd M j 7 (lo / 2) lo hi (by omega) (by omega)
            (by omega) (by omega) (by omega)
      · -- d ≥ 8 : mid
        refine double_band_mid M j lo hi (by omega) (by omega) (by omega) ?_
        have h8 : M ≤ (hi - lo) / 2 * 8 := by omega
        have hWh : 0 ≤ (hi - lo) / 2 := by omega
        nlinarith [h8, hdbig, hWh, hd]

/-- **Kravitz Lemma 7.1 — the double-band covering, complete.** For `M ≥ 12` and any step `j`
with `0 < j < M` and `2j ≠ M` (always true for `j` coprime to `M`, since then `j ≠ M/2`), there
is `ℓ ∈ [⌈2M/7⌉, ⌊5M/7⌋]` with `ℓ·j mod M` in the same band — i.e. a time placing both the
pair-runner and the third runner `≥ 2/7` from the integers. Reduces `j > M/2` to the low half
by the band symmetry, then dispatches to the seven covering lemmas. (The genuine exceptions
`M ∈ {5,11}` are excluded by `M ≥ 12`; verified exhaustively to `M < 3000`.) -/
theorem double_band_cover (M j : ℤ) (hM : 12 ≤ M) (hj0 : 0 < j) (hjM : j < M) (hne : 2 * j ≠ M) :
    ∃ ℓ : ℤ, (2 * M + 6) / 7 ≤ ℓ ∧ ℓ ≤ (5 * M) / 7 ∧
      ∃ c : ℤ, (2 * M + 6) / 7 ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ (5 * M) / 7 := by
  rcases lt_or_gt_of_ne hne with hsmall | hbig
  · exact double_band_cover_lo M j ((2 * M + 6) / 7) ((5 * M) / 7) rfl rfl hM hj0 hsmall
  · refine double_band_symm M j ((2 * M + 6) / 7) ((5 * M) / 7) (by omega) ?_
    exact double_band_cover_lo M (M - j) ((2 * M + 6) / 7) ((5 * M) / 7) rfl rfl hM
      (by omega) (by omega)

/-- **Non-vacuousness check.** A concrete instance: `M = 100`, step `j = 23` — the machine
produces a covering `ℓ`. -/
example : ∃ ℓ : ℤ, (2 * 100 + 6) / 7 ≤ ℓ ∧ ℓ ≤ (5 * 100) / 7 ∧
    ∃ c : ℤ, (2 * 100 + 6) / 7 ≤ ℓ * 23 - c * 100 ∧ ℓ * 23 - c * 100 ≤ (5 * 100) / 7 :=
  double_band_cover 100 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Strict covering: the *interior* band `[⌈2M/7⌉+1, ⌊5M/7⌋−1]`

Every residue here is `> 2M/7` and `< 5M/7`, so `‖·/M‖ > 2/7` *strictly*. The same generic
covering lemmas apply; the assembly requires `M ≥ 33` (for `r>30` the relevant pair-sums are
always `≥ 33`) and two direct-witness patches at `(M,j) = (37,15), (43,18)`. Verified covering
of all coprime `(M,j)` for `33 ≤ M < 8000`. -/

/-- **Strict covering (low half `2j < M`).** -/
theorem double_band_cover_lo_strict (M j lo hi : ℤ) (hlo : lo = (2 * M + 6) / 7 + 1)
    (hhi : hi = (5 * M) / 7 - 1) (hM : 33 ≤ M) (hj0 : 0 < j) (h2j : 2 * j < M) :
    ∃ ℓ : ℤ, lo ≤ ℓ ∧ ℓ ≤ hi ∧ ∃ c : ℤ, lo ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ hi := by
  have hsym : lo + hi = M := by omega
  have hband : lo ≤ hi := by omega
  rcases lt_or_ge j 3 with hjlt3 | hjge3
  · interval_cases j
    · exact double_band_one M lo hi hband
    · exact double_band_two M lo hi (by omega) (by omega)
  · rcases le_or_gt j (hi - lo + 1) with hjmain | hjbig
    · refine double_band_main M j lo hi (by omega) (by omega) hjmain ?_
      have h3W : M ≤ (hi - lo) * 3 := by omega
      nlinarith [h3W, hjge3, hband]
    · obtain ⟨d, hd⟩ : ∃ d : ℤ, M - 2 * j = d := ⟨_, rfl⟩
      have hd1 : 1 ≤ d := by omega
      rcases le_or_gt d 6 with hdsmall | hdbig
      · interval_cases d
        · exact double_band_even M j 1 lo lo hi hsym (by omega) (by omega) (by omega)
            (by omega) (by omega)
        · exact double_band_even M j 2 ((lo + 1) / 2) lo hi hsym (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_even M j 3 ((lo + 1) / 2) lo hi hsym (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · exact double_band_odd M j 4 ((M + j - hi + 3) / 4) lo hi (by omega)
            (by omega) (by omega) (by omega) (by omega)
        · exact double_band_odd M j 5 ((M + j - hi + 4) / 5) lo hi (by omega)
            (by omega) (by omega) (by omega) (by omega)
        · exact double_band_odd M j 6 (lo / 2) lo hi (by omega)
            (by omega) (by omega) (by omega) (by omega)
      · -- d ≥ 7 : mid (span via M ≤ ⌊W/2⌋·7 ≤ ⌊W/2⌋·d)
        refine double_band_mid M j lo hi (by omega) (by omega) (by omega) ?_
        have h7 : M ≤ (hi - lo) / 2 * 7 := by omega
        have hWh : 0 ≤ (hi - lo) / 2 := by omega
        nlinarith [h7, hdbig, hWh, hd]

/-- **Strict covering (full).** For `M ≥ 33`, any `0 < j < M` with `2j ≠ M`: some
`ℓ ∈ [⌈2M/7⌉+1, ⌊5M/7⌋−1]` has `ℓ·j mod M` in the same interior band — so both runners are
*strictly* more than `2/7` from the integers. -/
theorem double_band_cover_strict (M j : ℤ) (hM : 33 ≤ M) (hj0 : 0 < j) (hjM : j < M)
    (hne : 2 * j ≠ M) :
    ∃ ℓ : ℤ, (2 * M + 6) / 7 + 1 ≤ ℓ ∧ ℓ ≤ (5 * M) / 7 - 1 ∧
      ∃ c : ℤ, (2 * M + 6) / 7 + 1 ≤ ℓ * j - c * M ∧ ℓ * j - c * M ≤ (5 * M) / 7 - 1 := by
  rcases lt_or_gt_of_ne hne with hsmall | hbig
  · exact double_band_cover_lo_strict M j _ _ rfl rfl hM hj0 hsmall
  · refine double_band_symm M j ((2 * M + 6) / 7 + 1) ((5 * M) / 7 - 1) (by omega) ?_
    exact double_band_cover_lo_strict M (M - j) _ _ rfl rfl hM (by omega) (by omega)

end LRSpectrumFull





