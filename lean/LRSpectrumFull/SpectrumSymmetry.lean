/-
# Milestone 50: scaling symmetry of the spectrum (a covering-POV lemma)

Viewing `D` through the **covering** lens — `D(v) ≥ 3/14` iff the sets
`{‖vᵢ·t‖ ≤ 2/7}` cover the circle — makes one symmetry obvious that is easy
to miss in the runner picture: **common scaling of the speeds is a
reparametrization of the circle**, hence leaves `D` unchanged.

`D(m·v) = D(v)` for `m ≥ 1`: scaling all speeds by `m` just relabels the
parameter `t ↦ m·t`, a bijection of `ℝ`, so the supremum defining `ML` is
unchanged. This is the rigorous justification for restricting the whole
`S₁(3)` classification to **primitive** triples (`gcd = 1`) — which every
enumeration in this project does implicitly. No `sorry`.
-/

import LRSpectrumFull.DValue

namespace LRSpectrumFull

variable {k : ℕ}

/-- Scaling the speeds by `m` reparametrizes the gap: `gap (m·v) t = gap v (m·t)`. -/
theorem gap_scale (v : Fin (k + 1) → ℤ) (m : ℤ) (t : ℝ) :
    gap (fun i => m * v i) t = gap v ((m : ℝ) * t) := by
  unfold gap
  congr 1
  funext i
  congr 1
  push_cast
  ring

/-- The range of the scaled gap equals the range of the original gap (the
reparametrization `t ↦ m·t` is onto for `m ≠ 0`). -/
theorem range_gap_scale (v : Fin (k + 1) → ℤ) (m : ℤ) (hm : 0 < m) :
    Set.range (gap (fun i => m * v i)) = Set.range (gap v) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(m : ℝ) * t, (gap_scale v m t).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s / (m : ℝ), ?_⟩
    rw [gap_scale, mul_div_cancel₀ _ hmne]

/-- **Scaling invariance of maximum loneliness.** -/
theorem ML_scale (v : Fin (k + 1) → ℤ) (m : ℤ) (hm : 0 < m) :
    ML (fun i => m * v i) = ML v := by
  unfold ML
  rw [range_gap_scale v m hm]

/-- **Scaling invariance of the D-value.** `D(m·v) = D(v)` for `m ≥ 1` — the
covering problem only sees the speeds up to common scaling, so the
classification reduces to primitive triples. -/
theorem D_scale (v : Fin (k + 1) → ℤ) (m : ℤ) (hm : 0 < m) :
    D (fun i => m * v i) = D v := by
  unfold D
  rw [ML_scale v m hm]

end LRSpectrumFull
