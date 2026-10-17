/-
# Evenly spaced points on the circle

The mathematical heart of Rosenfeld's Lemma 5 (arXiv:2509.14111).  There, `q = gcd(v₁,…,v_{k-1})`
and the times `(qa + jb)/(qb)` for `j = 0,…,q-1` leave the first `k-1` runners exactly where a
lonely time `a/b` put them, because each `vᵢ` is a multiple of `q` so the shift is by an integer,
while `v_k` sweeps `v_k·a/b + j/q`.  Crucially `gcd(v_k, q) = 1` comes for free, since
`gcd(q, v_k) = gcd(gcd(v₁,…,v_{k-1}), v_k) = gcd(v₁,…,v_k) = 1`, so those `q` points are evenly
spaced on the circle.

The lemma below is the resulting fact, stated independently of the runners: among `q ≥ 2` evenly
spaced points, one is at distance at least `1/4` from the integers.  For `k ≥ 3` that is at least
`1/(k+1)`, which is what Lemma 5 needs.

The proof avoids `nid_lipschitz`, and with it the whole `Delta2GlobalPartition` import: choosing
`n = round (q * (1/2 - x))` places `x + n/q` within `1/(2q) ≤ 1/4` of `1/2`, so that point lies in
`[1/4, 3/4] ⊆ [0,1)`, where the fractional part is the point itself and the distance is simply
`min (y, 1-y)`.  Reducing `n` modulo `q` shifts by an integer, which the distance does not see.

This routing is deliberate: `Delta2GlobalPartition` currently cannot be rebuilt on this machine,
because `Delta2Seam23C` is OOM-killed (exit 137) after about 51 minutes. 
-/

import Mathlib
import LRSpectrumFull.NearestInteger

namespace LRSpectrumFull

/-- `nearestIntDist` is unchanged by an integer shift. -/
theorem nid_add_int (x : ℝ) (n : ℤ) : nearestIntDist (x + n) = nearestIntDist x := by
  unfold nearestIntDist Int.fract
  rw [Int.floor_add_intCast]
  push_cast
  ring_nf

/-- A point within `1/4` of a half-integer is at distance at least `1/4` from the integers. -/
theorem nid_ge_quarter_of_near_half (y : ℝ) (h : |y - 1 / 2| ≤ 1 / 4) :
    1 / 4 ≤ nearestIntDist y := by
  rw [abs_le] at h
  have hy0 : (0 : ℝ) ≤ y := by linarith [h.1]
  have hy1 : y < 1 := by linarith [h.2]
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨hy0, hy1⟩]
  exact le_min (by linarith [h.1]) (by linarith [h.2])

/-- **Among `q ≥ 2` evenly spaced points, one is far from the integers (VERIFIED).**

Some `x + j/q` with `j < q` has `nearestIntDist ≥ 1/4`.  Choosing `n = round (q*(1/2 - x))` puts
`x + n/q` within `1/(2q) ≤ 1/4` of `1/2`, and reducing `n` modulo `q` shifts by an integer, which
`nearestIntDist` does not see. -/
theorem exists_far_point (x : ℝ) (q : ℕ) (hq : 2 ≤ q) :
    ∃ j : ℕ, j < q ∧ 1 / 4 ≤ nearestIntDist (x + (j : ℝ) / (q : ℝ)) := by
  have hqn : 0 < q := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqn
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set n : ℤ := round ((q : ℝ) * (1 / 2 - x)) with hn
  have hround : |((q : ℝ) * (1 / 2 - x)) - (n : ℝ)| ≤ 1 / 2 := by
    rw [hn]; exact abs_sub_round _
  have hnn : 0 ≤ n % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hqn.ne')
  have hlt : n % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hqn)
  refine ⟨(n % (q : ℤ)).toNat, by omega, ?_⟩
  have hcast : (((n % (q : ℤ)).toNat : ℕ) : ℝ) = ((n % (q : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hnn)
  have hmod : ((n % (q : ℤ) : ℤ) : ℝ) = (n : ℝ) - ((n / (q : ℤ) : ℤ) : ℝ) * (q : ℝ) := by
    have h := Int.emod_add_mul_ediv n (q : ℤ)
    have h2 : ((n % (q : ℤ) + (q : ℤ) * (n / (q : ℤ)) : ℤ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) h
    push_cast at h2 ⊢
    linarith
  have hshift : x + (((n % (q : ℤ)).toNat : ℕ) : ℝ) / (q : ℝ)
      = (x + (n : ℝ) / (q : ℝ)) + ((-(n / (q : ℤ)) : ℤ) : ℝ) := by
    rw [hcast, hmod]; push_cast; field_simp; ring
  rw [hshift]
  rw [show (x + (n : ℝ) / (q : ℝ)) + ((-(n / (q : ℤ)) : ℤ) : ℝ)
        = (x + (n : ℝ) / (q : ℝ)) + ((-(n / (q : ℤ)) : ℤ) : ℝ) from rfl]
  rw [nid_add_int]
  refine nid_ge_quarter_of_near_half _ ?_
  have hexp : (x + (n : ℝ) / (q : ℝ)) - 1 / 2
      = -(((q : ℝ) * (1 / 2 - x) - (n : ℝ)) / (q : ℝ)) := by field_simp; ring
  rw [hexp, abs_neg, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
  nlinarith [hround, hq0]

/-- **A shift by `j/q` is invisible to any velocity divisible by `q` (VERIFIED).**

This is the half of Rosenfeld's Lemma 5 that keeps the first `k-1` runners where they were.  The
times he uses are `(qa + jb)/(qb) = a/b + j/q`, and if `q ∣ w` then `w * (j/q)` is an integer, which
the distance to the integers does not see. -/
theorem nid_shift_of_dvd (w : ℤ) (q : ℕ) (hq : 0 < q) (j : ℕ) (hdvd : (q : ℤ) ∣ w) (t : ℝ) :
    nearestIntDist ((w : ℝ) * (t + (j : ℝ) / (q : ℝ))) = nearestIntDist ((w : ℝ) * t) := by
  obtain ⟨c, rfl⟩ := hdvd
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : ((((q : ℤ) * c : ℤ)) : ℝ) * (t + (j : ℝ) / (q : ℝ))
      = (((q : ℤ) * c : ℤ) : ℝ) * t + ((c * (j : ℤ) : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [hexp, nid_add_int]

/-- **The distinguished runner's shift (VERIFIED).**

If `w * j ≡ j' (mod q)` then shifting the time by `j/q` moves `w`'s position by `j'/q` up to an
integer, so the distance is the one computed at `j'/q`.  Together with `exists_far_point` this is the
other half of Lemma 5: `gcd(w, q) = 1` lets `j` be chosen to realise any target residue `j'`. -/
theorem nid_shift_of_congr (w : ℤ) (q : ℕ) (hq : 0 < q) (j j' : ℕ) (t : ℝ)
    (hcongr : ∃ c : ℤ, (w : ℤ) * (j : ℤ) = (j' : ℤ) + (q : ℤ) * c) :
    nearestIntDist ((w : ℝ) * (t + (j : ℝ) / (q : ℝ)))
      = nearestIntDist ((w : ℝ) * t + (j' : ℝ) / (q : ℝ)) := by
  obtain ⟨c, hc⟩ := hcongr
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcR : (w : ℝ) * (j : ℝ) = (j' : ℝ) + (q : ℝ) * (c : ℝ) := by exact_mod_cast hc
  have hexp : (w : ℝ) * (t + (j : ℝ) / (q : ℝ))
      = ((w : ℝ) * t + (j' : ℝ) / (q : ℝ)) + ((c : ℤ) : ℝ) := by
    field_simp
    nlinarith [hcR, hq0]
  rw [hexp, nid_add_int]

/-- **The sweep engine (VERIFIED).**

Over any interval of length `1/v` the velocity `v` traverses a full period, so somewhere in it `v`
sits exactly at a half-integer, the farthest possible from the integers.

This is the engine behind every "large ratio" argument: if the velocities already pinned down leave
a free interval of length at least `1/v`, then `v` can be satisfied inside it at no cost.  Any upper
bound on a minimal counterexample -- the ingredient Rosenfeld imports as Theorem 2 -- is built from
statements of this shape. -/
theorem exists_good_in_interval (v : ℕ) (hv : 0 < v) (x : ℝ) :
    ∃ t : ℝ, x ≤ t ∧ t ≤ x + 1 / (v : ℝ) ∧ nearestIntDist ((v : ℝ) * t) = 1 / 2 := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  set n : ℤ := ⌈(v : ℝ) * x - 1 / 2⌉ with hn
  have hge : (v : ℝ) * x - 1 / 2 ≤ (n : ℝ) := by rw [hn]; exact Int.le_ceil _
  have hlt : (n : ℝ) < (v : ℝ) * x - 1 / 2 + 1 := by
    rw [hn]; exact Int.ceil_lt_add_one _
  refine ⟨((n : ℝ) + 1 / 2) / (v : ℝ), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hv0]; linarith
  · rw [div_le_iff₀ hv0]; field_simp; linarith
  · have : (v : ℝ) * (((n : ℝ) + 1 / 2) / (v : ℝ)) = (n : ℝ) + 1 / 2 := by field_simp
    rw [this]
    have h2 : nearestIntDist (((n : ℤ) : ℝ) + 1 / 2) = 1 / 2 := by
      unfold nearestIntDist
      rw [show ((n : ℤ) : ℝ) + 1 / 2 = 1 / 2 + (n : ℤ) by ring, Int.fract_add_intCast]
      norm_num [Int.fract_eq_self.mpr (by norm_num : (0:ℝ) ≤ 1/2 ∧ (1:ℝ)/2 < 1)]
    exact h2

/-- **A velocity's good set contains explicit intervals (VERIFIED).**

For every integer `n`, the whole interval `[(n + 1/4)/v, (n + 3/4)/v]` -- of length `1/(2v)` -- keeps
`v` at distance at least `1/4` from the integers.  These intervals sit `1/v` apart, one per period.

Together with `exists_good_in_interval` this is the pair of facts every large-ratio argument runs
on: a velocity constrains time to a union of intervals of length `1/(2v)`, and any interval of
length `1/w` is enough to satisfy a further velocity `w`.  So once `w` is large enough that
`1/w ≤ 1/(2v)`, that is `w ≥ 2v`, the new velocity costs nothing. -/
theorem good_interval (v : ℕ) (hv : 0 < v) (n : ℤ) (t : ℝ)
    (h1 : ((n : ℝ) + 1 / 4) / (v : ℝ) ≤ t) (h2 : t ≤ ((n : ℝ) + 3 / 4) / (v : ℝ)) :
    1 / 4 ≤ nearestIntDist ((v : ℝ) * t) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hlo : (n : ℝ) + 1 / 4 ≤ (v : ℝ) * t := by
    rw [div_le_iff₀ hv0] at h1; linarith [h1]
  have hhi : (v : ℝ) * t ≤ (n : ℝ) + 3 / 4 := by
    rw [le_div_iff₀ hv0] at h2; linarith [h2]
  have hsplit : (v : ℝ) * t = ((v : ℝ) * t - (n : ℝ)) + ((n : ℤ) : ℝ) := by ring
  rw [hsplit, nid_add_int]
  refine nid_ge_quarter_of_near_half _ ?_
  rw [abs_le]
  constructor <;> linarith

/-- **Good intervals nest when the ratio is at least three (VERIFIED).**

If `w ≥ 3v` then some good interval of `w` sits entirely inside the given good interval of `v`.

The count: the admissible integers `m` form a range of length `w/(2v) - 1/2 ≥ 3/2 - 1/2 = 1`, and a
real interval of length at least one contains an integer.

This is the lacunary engine.  Because the conclusion has the same shape as the hypothesis -- a good
interval of the new velocity -- it CHAINS: for `a`, `b`, `c` with `b ≥ 3a` and `c ≥ 3b` one nests
twice and all three velocities are simultaneously at distance at least `1/4`.  Bounding a minimal
counterexample means showing that only bounded ratios can escape this, which is the shape of the
Theorem 2 that Rosenfeld imports. -/
theorem nested_good_interval (v w : ℕ) (hv : 0 < v) (hw : 3 * v ≤ w) (n : ℤ) :
    ∃ m : ℤ, ((n : ℝ) + 1 / 4) / (v : ℝ) ≤ ((m : ℝ) + 1 / 4) / (w : ℝ) ∧
             ((m : ℝ) + 3 / 4) / (w : ℝ) ≤ ((n : ℝ) + 3 / 4) / (v : ℝ) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hw0 : (0 : ℝ) < (w : ℝ) := by
    have : 0 < w := by omega
    exact_mod_cast this
  have hwv : 3 * (v : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  set lo : ℝ := (w : ℝ) * ((n : ℝ) + 1 / 4) / (v : ℝ) - 1 / 4 with hlo
  set hi : ℝ := (w : ℝ) * ((n : ℝ) + 3 / 4) / (v : ℝ) - 3 / 4 with hhi
  have hlen : lo + 1 ≤ hi := by
    rw [hlo, hhi]
    have hkey : (w : ℝ) * ((n : ℝ) + 3 / 4) / (v : ℝ) - (w : ℝ) * ((n : ℝ) + 1 / 4) / (v : ℝ)
        = (w : ℝ) / (2 * (v : ℝ)) := by field_simp; ring
    have h32 : (3 : ℝ) / 2 ≤ (w : ℝ) / (2 * (v : ℝ)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    linarith [hkey, h32]
  refine ⟨⌈lo⌉, ?_, ?_⟩
  · rw [div_le_div_iff₀ hv0 hw0]
    have hc : lo ≤ (⌈lo⌉ : ℝ) := Int.le_ceil _
    rw [hlo] at hc
    have : (w : ℝ) * ((n : ℝ) + 1 / 4) / (v : ℝ) ≤ (⌈lo⌉ : ℝ) + 1 / 4 := by linarith
    rw [div_le_iff₀ hv0] at this
    linarith
  · rw [div_le_div_iff₀ hw0 hv0]
    have hc : (⌈lo⌉ : ℝ) < lo + 1 := Int.ceil_lt_add_one _
    have hle : (⌈lo⌉ : ℝ) ≤ hi := by linarith
    rw [hhi] at hle
    have : (⌈lo⌉ : ℝ) + 3 / 4 ≤ (w : ℝ) * ((n : ℝ) + 3 / 4) / (v : ℝ) := by linarith
    rw [le_div_iff₀ hv0] at this
    linarith

end LRSpectrumFull
