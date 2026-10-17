/-
# The grid bridge

`nid_natCast_div` — at the rational time `a/N` the nearest-integer distance is
exactly the circular distance `min (a % N, N - a % N)` over `N`.  This is the
single point of contact between the Prime Filtering world (pure `ℕ` arithmetic
in `ℤ/N`) and the loneliness world (`nearestIntDist` on `ℝ`); it is what
`five_runners` crosses at `t = μ/5^{m+1+g}`.

It lives in its own module so the Prime Filtering tower does not drag in the
scaling lemmas of `Delta2MLScale`, whose `gap_scale`/`ML_scale` names collide
with the (positive-multiplier) versions in `SpectrumSymmetry`.
-/
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull

/-- **The grid bridge**: at the rational time `a/N` the nearest-integer
distance is exactly the circular distance `min (a % N) (N - a % N)` over `N`.
This is the one line where the Prime Filtering world (pure `ℕ` arithmetic in
`ℤ/N`) meets the loneliness world (`nearestIntDist` on `ℝ`). -/
theorem nid_natCast_div (N a : ℕ) (hN : 0 < N) :
    nearestIntDist ((a : ℝ) / (N : ℝ))
      = ((min (a % N) (N - a % N) : ℕ) : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmlt : a % N < N := Nat.mod_lt _ hN
  have hdm : ((N * (a / N) + a % N : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod a N)
  have hsplit : (a : ℝ) / N = ((a / N : ℕ) : ℝ) + ((a % N : ℕ) : ℝ) / N := by
    field_simp
    push_cast at hdm ⊢
    linarith [hdm]
  have hfr : Int.fract ((a : ℝ) / N) = ((a % N : ℕ) : ℝ) / N := by
    rw [hsplit, show ((a / N : ℕ) : ℝ) = (((a / N : ℕ) : ℤ) : ℝ) from (Int.cast_natCast _).symm,
      add_comm, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr
      ⟨by positivity, by rw [div_lt_one hNR]; exact_mod_cast hmlt⟩
  unfold nearestIntDist
  rw [hfr]
  have hsub : (1 : ℝ) - ((a % N : ℕ) : ℝ) / N = (((N - a % N : ℕ)) : ℝ) / N := by
    rw [Nat.cast_sub (le_of_lt hmlt)]
    field_simp
  rw [hsub, min_div_div_right (le_of_lt hNR), Nat.cast_min]

end LRSpectrumFull
