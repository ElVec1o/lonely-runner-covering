/-
Room FCU, moderator round (2026-09-24).

* `ML_ge_of_escape` : the window-escape lemma in uniform form.  If for a base point `a/q`
  and a displacement `ε` every speed has an integer representative `r_i ≡ v_i a (mod q)`
  with `r_i/q + v_i ε ∈ [δ, 1 - δ]`, then `δ ≤ ML v` (witness `t = a/q + ε`).  Lemma P,
  the window lemma at levels `m+1 < q ≤ 2m+2` (ε = 0), the window certificate and the
  Theorem-F witness are all instances; the per-family content is the arithmetic check.
* `strictFloorD_false` : the proposition `RoomFCUErdos.StrictFloorD` (strict floor on every
  family in which the runner count divides a speed, WITHOUT a gcd hypothesis) is false:
  `4·(1,2,3)` has `ML = 1/4`.  So `universalFloor_of_strictD` holds vacuously; the intended
  strong form of (T) needs `gcd v = 1`.
-/
import Mathlib
import LRSpectrumFull.CoveringWitness
import LRSpectrumFull.NearestInteger
import LRSpectrumFull.LonelyRunner3
import LRSpectrumFull.RoomFCU_erdos

namespace LRSpectrumFull.RoomFCUModerator

open LRSpectrumFull

theorem ML_ge_of_escape {k : ℕ} (v : Fin (k + 1) → ℤ) (q a : ℤ) (hq : 0 < q) (ε δ : ℝ)
    (hδ : 0 < δ)
    (h : ∀ i, ∃ N r : ℤ, v i * a = q * N + r ∧
      δ ≤ (r : ℝ) / q + (v i : ℝ) * ε ∧ (r : ℝ) / q + (v i : ℝ) * ε ≤ 1 - δ) :
    δ ≤ ML v := by
  refine ML_ge_of_witness v ((a : ℝ) / q + ε) δ (fun i => ?_)
  obtain ⟨N, r, hvr, h0, h1⟩ := h i
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hva : (v i : ℝ) * (a : ℝ) = (q : ℝ) * (N : ℝ) + (r : ℝ) := by exact_mod_cast hvr
  have e : (v i : ℝ) * ((a : ℝ) / q + ε) = ((r : ℝ) / q + (v i : ℝ) * ε) + ((N : ℤ) : ℝ) := by
    have e1 : (v i : ℝ) * ((a : ℝ) / q + ε) = ((v i : ℝ) * (a : ℝ)) / q + (v i : ℝ) * ε := by
      ring
    rw [e1, hva]
    field_simp
    ring
  rw [e, nearestIntDist_add_int]
  exact nearestIntDist_ge (by linarith) (by linarith) h0 (by linarith)

theorem strictFloorD_false : ¬ RoomFCUErdos.StrictFloorD := by
  intro h
  have hpos : ∀ i, 0 < (fun i : Fin 3 => (4 : ℤ) * v123 i) i := by
    intro i; fin_cases i <;> simp [v123]
  have hdiv : ∃ i, (((2 + 2 : ℕ) : ℤ)) ∣ (fun i : Fin 3 => (4 : ℤ) * v123 i) i :=
    ⟨0, by simp [v123]⟩
  have hlt := h 2 le_rfl (fun i => (4 : ℤ) * v123 i) hpos hdiv
  rw [ML_scale v123 4 (by norm_num), lonely_runner_three_sharp] at hlt
  norm_num at hlt

end LRSpectrumFull.RoomFCUModerator
