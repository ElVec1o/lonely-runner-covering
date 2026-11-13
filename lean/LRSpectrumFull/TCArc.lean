/-
# Time cover: the one-coordinate lemma (closed arcs read off from the piece index `⌊x⌋ + ⌈x⌉`)

For a real `x`, the integer `⌊x⌋ + ⌈x⌉` records the "piece" of the grid `ℤ` containing `x`: `2j` if `x = j`,
`2j + 1` if `j < x < j + 1`.  `arc_of_floor_ceil`: if `⌊y⌋ + ⌈y⌉ = 2c + r` with `0 ≤ r ≤ 2L` then the CLOSED
interval condition `c ≤ y ≤ c + L` holds (the converse is not needed).

`coord_good`: time `t₀ = n/q` and a real phase `φ`; let `p` be the piece index of `5qφ` reduced mod `10q`.  If
`(p + w) mod 10q ≤ 6q` with `w = wv q v n = (10 v n + 8 q) mod 10q`, then `1/5 ≤ tpDist (v t₀ + φ)`.
(`[1/5, 4/5] + ℤ` is the good set; scaled by `5q` it is the closed arc `[q, 4q] + 5q ℤ`.)  All inequalities are
non-strict.
-/
import LRSpectrumFull.D0Bridge

namespace LRSpectrumFull
namespace TC

open D0

/-- arc offset of the time `n/q` for speed `v` (in units of the doubled grid, modulus `10 q`) -/
def wv (q v n : ℕ) : ℕ := (10 * v * n + 8 * q) % (10 * q)

theorem arc_of_floor_ceil (y : ℝ) (c r L : ℤ) (h : ⌊y⌋ + ⌈y⌉ = 2 * c + r) (h0 : 0 ≤ r)
    (h1 : r ≤ 2 * L) : (c : ℝ) ≤ y ∧ y ≤ (c : ℝ) + L := by
  have e1 := Int.floor_le y
  have e2 := Int.le_ceil y
  have e3 := Int.ceil_le_floor_add_one y
  have hf : c ≤ ⌊y⌋ := by omega
  have hc : ⌈y⌉ ≤ c + L := by omega
  constructor
  · calc (c : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hf
      _ ≤ y := e1
  · calc y ≤ (⌈y⌉ : ℝ) := e2
      _ ≤ ((c + L : ℤ) : ℝ) := by exact_mod_cast hc
      _ = (c : ℝ) + L := by push_cast; ring

theorem coord_good (q v n : ℕ) (hq : 0 < q) (φ : ℝ) (p : ℕ)
    (hp : (p : ℤ) = (⌊5 * (q : ℝ) * φ⌋ + ⌈5 * (q : ℝ) * φ⌉) % (10 * (q : ℤ)))
    (h : (p + wv q v n) % (10 * q) ≤ 6 * q) :
    1 / 5 ≤ tpDist ((v : ℝ) * ((n : ℝ) / q) + φ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : (0 : ℤ) < 10 * (q : ℤ) := by positivity
  have hw : ((wv q v n : ℕ) : ℤ) = (10 * (v : ℤ) * n + 8 * q) % (10 * (q : ℤ)) := by
    unfold wv; push_cast; rfl
  have hR : (((p + wv q v n) % (10 * q) : ℕ) : ℤ)
      = ((p : ℤ) + ((wv q v n : ℕ) : ℤ)) % (10 * (q : ℤ)) := by
    push_cast; rfl
  have e1 := Int.emod_add_mul_ediv (⌊5 * (q : ℝ) * φ⌋ + ⌈5 * (q : ℝ) * φ⌉) (10 * (q : ℤ))
  have e2 := Int.emod_add_mul_ediv (10 * (v : ℤ) * n + 8 * q) (10 * (q : ℤ))
  have e3 := Int.emod_add_mul_ediv ((p : ℤ) + ((wv q v n : ℕ) : ℤ)) (10 * (q : ℤ))
  rw [← hp] at e1
  rw [← hw] at e2
  rw [← hR] at e3
  set R : ℕ := (p + wv q v n) % (10 * q) with hRdef
  have hRle : (R : ℤ) ≤ 6 * q := by exact_mod_cast h
  have hR0 : (0 : ℤ) ≤ R := by positivity
  set m : ℤ := (⌊5 * (q : ℝ) * φ⌋ + ⌈5 * (q : ℝ) * φ⌉) / (10 * (q : ℤ))
      + (10 * (v : ℤ) * n + 8 * q) / (10 * (q : ℤ))
      + ((p : ℤ) + ((wv q v n : ℕ) : ℤ)) / (10 * (q : ℤ)) with hm
  have hsum : (⌊5 * (q : ℝ) * φ⌋ + ⌈5 * (q : ℝ) * φ⌉) + 10 * (v : ℤ) * n + 8 * q
      = 10 * q * m + R := by
    rw [hm]; linarith
  set y : ℝ := 5 * (q : ℝ) * φ + ((5 * (v : ℤ) * n : ℤ) : ℝ) with hy
  have hfl : ⌊y⌋ = ⌊5 * (q : ℝ) * φ⌋ + 5 * (v : ℤ) * n := Int.floor_add_intCast _ _
  have hce : ⌈y⌉ = ⌈5 * (q : ℝ) * φ⌉ + 5 * (v : ℤ) * n := Int.ceil_add_intCast _ _
  have harc := arc_of_floor_ceil y (5 * q * m - 4 * q) R (3 * q)
    (by rw [hfl, hce]; linarith) hR0 (by linarith)
  obtain ⟨hlo, hhi⟩ := harc
  push_cast at hlo hhi
  have hxy : 5 * (q : ℝ) * ((v : ℝ) * ((n : ℝ) / q) + φ) = y := by
    rw [hy]; push_cast; field_simp; ring
  apply tpDist_ge_of_frac _ (m - 1)
  · have h1 : (1 / 5 : ℝ) * (5 * q) ≤ (((v : ℝ) * ((n : ℝ) / q) + φ) - ((m - 1 : ℤ) : ℝ)) * (5 * q) := by
      push_cast
      nlinarith [hxy, hlo]
    exact le_of_mul_le_mul_right h1 (by positivity)
  · have h1 : (((v : ℝ) * ((n : ℝ) / q) + φ) - ((m - 1 : ℤ) : ℝ)) * (5 * q) ≤ (4 / 5 : ℝ) * (5 * q) := by
      push_cast
      nlinarith [hxy, hhi]
    exact le_of_mul_le_mul_right h1 (by positivity)

end TC
end LRSpectrumFull
