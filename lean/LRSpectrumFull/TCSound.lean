/-
# Time cover certificate: the checker `tcOK` and `tc_sound`

Certificate for four natural speeds `v0 v1 v2 v3`: a denominator `q > 0` and a list of numerators `times`
(the times `n / q`).  `tcBoxes` keeps the times at which runner 0 (phase 0 after a real time shift) is good,
`wv q v0 n ≤ 6 q`, and records the arc offsets of runners 1, 2, 3.  `tcOK` checks `coverB` on the grid of
`10 q` pieces per coordinate.

`tc_sound : tcOK v0 v1 v2 v3 q times = true → S4 ![v0, v1, v2, v3]`: for every real phase vector `φ` there is a
real `t` with `1/5 ≤ ‖v_i t + φ_i‖` for all `i` (non-strict: closed boxes).

Proof: shift time by `τ = -φ₀ / v₀` so that runner 0 has phase 0; the piece indices of `5 q φ'_i` (`i = 1,2,3`)
reduced mod `10 q` form a point of the grid; `cover_sound` gives a box (a time `n/q`) containing it in all three
coordinates; `coord_good` turns box membership into `1/5 ≤ tpDist`.
-/
import LRSpectrumFull.TCArc
import LRSpectrumFull.TCCover

namespace LRSpectrumFull
namespace TC

open D0

def tcBoxes (q v0 v1 v2 v3 : ℕ) (times : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (times.filter fun n => wv q v0 n ≤ 6 * q).map fun n => (wv q v1 n, wv q v2 n, wv q v3 n)

def tcOK (v0 v1 v2 v3 q : ℕ) (times : List ℕ) : Bool :=
  decide (0 < q ∧ 0 < v0) && coverB (10 * q) (6 * q) (tcBoxes q v0 v1 v2 v3 times)

/-- piece index of a real `x`, reduced mod `10 q` (as an integer) -/
noncomputable def pidx (q : ℕ) (φ : ℝ) : ℤ :=
  (⌊5 * (q : ℝ) * φ⌋ + ⌈5 * (q : ℝ) * φ⌉) % (10 * (q : ℤ))

theorem pidx_nat (q : ℕ) (hq : 0 < q) (φ : ℝ) :
    ((pidx q φ).toNat : ℤ) = pidx q φ ∧ (pidx q φ).toNat < 10 * q := by
  have hQ : (0 : ℤ) < 10 * (q : ℤ) := by positivity
  have h0 : 0 ≤ pidx q φ := Int.emod_nonneg _ hQ.ne'
  have h1 : pidx q φ < 10 * (q : ℤ) := Int.emod_lt_of_pos _ hQ
  refine ⟨Int.toNat_of_nonneg h0, ?_⟩
  omega

theorem tc_sound (v0 v1 v2 v3 q : ℕ) (times : List ℕ) (h : tcOK v0 v1 v2 v3 q times = true) :
    S4 ![v0, v1, v2, v3] := by
  unfold tcOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hv0⟩, hc⟩ := h
  intro φ
  have hv0R : (v0 : ℝ) ≠ 0 := by exact_mod_cast hv0.ne'
  set τ : ℝ := -φ 0 / v0 with hτ
  have hph0 : φ 0 + (v0 : ℝ) * τ = 0 := by rw [hτ]; field_simp; ring
  obtain ⟨e1, l1⟩ := pidx_nat q hq (φ 1 + (v1 : ℝ) * τ)
  obtain ⟨e2, l2⟩ := pidx_nat q hq (φ 2 + (v2 : ℝ) * τ)
  obtain ⟨e3, l3⟩ := pidx_nat q hq (φ 3 + (v3 : ℝ) * τ)
  obtain ⟨k, hk, c1, c2, c3⟩ := cover_sound hc l1 l2 l3
  have hmem : (tcBoxes q v0 v1 v2 v3 times)[k] ∈ tcBoxes q v0 v1 v2 v3 times := List.getElem_mem hk
  unfold tcBoxes at hmem
  obtain ⟨n, hn, hbox⟩ := List.mem_map.mp hmem
  have hn' := List.mem_filter.mp hn
  have hw0 : wv q v0 n ≤ 6 * q := by simpa using hn'.2
  have hb1 : ((tcBoxes q v0 v1 v2 v3 times)[k]).1 = wv q v1 n := by
    unfold tcBoxes at *; rw [← hbox]
  have hb2 : ((tcBoxes q v0 v1 v2 v3 times)[k]).2.1 = wv q v2 n := by
    unfold tcBoxes at *; rw [← hbox]
  have hb3 : ((tcBoxes q v0 v1 v2 v3 times)[k]).2.2 = wv q v3 n := by
    unfold tcBoxes at *; rw [← hbox]
  rw [hb1] at c1
  rw [hb2] at c2
  rw [hb3] at c3
  have G0 : 1 / 5 ≤ tpDist ((v0 : ℝ) * ((n : ℝ) / q + τ) + φ 0) := by
    have key := coord_good q v0 n hq (φ 0 + (v0 : ℝ) * τ) 0 (by rw [hph0]; simp)
      (by
        have : wv q v0 n < 10 * q := by
          unfold wv; exact Nat.mod_lt _ (by omega)
        rw [Nat.zero_add, Nat.mod_eq_of_lt this]; exact hw0)
    have e : (v0 : ℝ) * ((n : ℝ) / q + τ) + φ 0 = (v0 : ℝ) * ((n : ℝ) / q) + (φ 0 + (v0 : ℝ) * τ) := by
      ring
    rw [e]; exact key
  have G1 : 1 / 5 ≤ tpDist ((v1 : ℝ) * ((n : ℝ) / q + τ) + φ 1) := by
    have key := coord_good q v1 n hq (φ 1 + (v1 : ℝ) * τ) _ (by rw [e1]; rfl) c1
    have e : (v1 : ℝ) * ((n : ℝ) / q + τ) + φ 1 = (v1 : ℝ) * ((n : ℝ) / q) + (φ 1 + (v1 : ℝ) * τ) := by
      ring
    rw [e]; exact key
  have G2 : 1 / 5 ≤ tpDist ((v2 : ℝ) * ((n : ℝ) / q + τ) + φ 2) := by
    have key := coord_good q v2 n hq (φ 2 + (v2 : ℝ) * τ) _ (by rw [e2]; rfl) c2
    have e : (v2 : ℝ) * ((n : ℝ) / q + τ) + φ 2 = (v2 : ℝ) * ((n : ℝ) / q) + (φ 2 + (v2 : ℝ) * τ) := by
      ring
    rw [e]; exact key
  have G3 : 1 / 5 ≤ tpDist ((v3 : ℝ) * ((n : ℝ) / q + τ) + φ 3) := by
    have key := coord_good q v3 n hq (φ 3 + (v3 : ℝ) * τ) _ (by rw [e3]; rfl) c3
    have e : (v3 : ℝ) * ((n : ℝ) / q + τ) + φ 3 = (v3 : ℝ) * ((n : ℝ) / q) + (φ 3 + (v3 : ℝ) * τ) := by
      ring
    rw [e]; exact key
  refine ⟨(n : ℝ) / q + τ, fun i => ?_⟩
  unfold GoodR
  fin_cases i
  · simpa using G0
  · simpa using G1
  · simpa using G2
  · simpa using G3

end TC
end LRSpectrumFull
