/-
# The far-runner decoupling factorization

`vanMass_decouple` — if one velocity dominates, `3·∑_{w≠i} v_w < v_i`, then
runner `i` **decouples**: no bounded vanishing combination can use it
(`van_decouple_ci`), so the vanishing web is carried entirely by the other
`k` runners and the family mass factorizes,
`vanMass (k+1) v = (5/2)·vanMass k (v ∘ i.succAbove)`.

This is the tall regime of the four-direction residual.  Conceptually it is
the vanishing tail of the exact `w8`-autocorrelation identity
`S = 20·S_w − 30·R_w(v_w) + 12·R_w(2v_w) − 2·R_w(3v_w)`: the three
autocorrelations `R_w(ℓ v_w)` of the deleted-runner polynomial `∏_{u≠w}(1−x^{v_u})³`
vanish once their lag `ℓ v_w` exceeds its degree `3∑_{u≠w} v_u`, leaving the
bare `S = 20·S_w`.  The formalization below reaches the same identity by the
elementary route: every box vector `c` in the web has `c_i = 0`, so the web
is literally the `c_i = 0` slice, and `vanMass_sub_slice` finishes it.
-/
import LRSpectrumFull.Delta2CubeAllOdd

namespace LRSpectrumFull

open Finset

local notation "π" => Real.pi

/-- **The decoupling coordinate vanishing.**  If `3·∑_{w≠i} v_w < v_i` and all
velocities are positive, every `[-3,3]`-vanishing combination has `c_i = 0`:
no box coefficient on `i` can be cancelled by the others. -/
theorem van_decouple_ci {k : ℕ} (v : Fin (k + 1) → ℤ) (hpos : ∀ w, 0 < v w)
    (i : Fin (k + 1)) (hbig : 3 * (∑ w ∈ Finset.univ.erase i, v w) < v i) :
    ∀ c ∈ vanFilter (k + 1) v, c i = 0 := by
  intro c hc
  rw [mem_vanFilter] at hc
  obtain ⟨hbox, hvan⟩ := hc
  -- split off runner i
  have hsplit : c i * v i + ∑ w ∈ Finset.univ.erase i, c w * v w = 0 := by
    rw [Finset.add_sum_erase Finset.univ (fun w => c w * v w) (Finset.mem_univ i)]
    exact hvan
  have hci_eq : c i * v i = -(∑ w ∈ Finset.univ.erase i, c w * v w) := by linarith
  -- the rest is bounded by 3·∑ v_w
  have hb : |c i * v i| ≤ 3 * ∑ w ∈ Finset.univ.erase i, v w := by
    rw [hci_eq, abs_neg]
    calc |∑ w ∈ Finset.univ.erase i, c w * v w|
        ≤ ∑ w ∈ Finset.univ.erase i, |c w * v w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ Finset.univ.erase i, 3 * v w := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          rw [abs_mul, abs_of_pos (hpos w)]
          have hcw : |c w| ≤ 3 := by have := hbox w; rw [abs_le]; omega
          nlinarith [hpos w, abs_nonneg (c w)]
      _ = 3 * ∑ w ∈ Finset.univ.erase i, v w := by rw [Finset.mul_sum]
  have hlt : |c i * v i| < v i := lt_of_le_of_lt hb hbig
  have habs : |c i| * v i = |c i * v i| := by rw [abs_mul, abs_of_pos (hpos i)]
  have hfactor : |c i| * v i < 1 * v i := by rw [habs, one_mul]; exact hlt
  have hlt1 : |c i| < 1 := lt_of_mul_lt_mul_right hfactor (le_of_lt (hpos i))
  have h0 : (0 : ℤ) ≤ |c i| := abs_nonneg _
  have : |c i| = 0 := by omega
  exact abs_eq_zero.mp this

/-- **The decoupling factorization.**  A dominant runner `i`
(`3·∑_{w≠i} v_w < v_i`) carries no vanishing weight, so the family mass is
`5/2` times the mass of the family with runner `i` removed. -/
theorem vanMass_decouple {k : ℕ} (v : Fin (k + 1) → ℤ) (hpos : ∀ w, 0 < v w)
    (i : Fin (k + 1)) (hbig : 3 * (∑ w ∈ Finset.univ.erase i, v w) < v i) :
    vanMass (k + 1) v = (5 / 2 : ℝ) * vanMass k (fun j' => v (i.succAbove j')) := by
  have hfilter : (vanFilter (k + 1) v).filter (fun c => c i = 0) = vanFilter (k + 1) v :=
    Finset.filter_true_of_mem (fun c hc => van_decouple_ci v hpos i hbig c hc)
  rw [vanMass_eq_vanFilter, ← hfilter, ← vanMass_sub_slice]

end LRSpectrumFull
