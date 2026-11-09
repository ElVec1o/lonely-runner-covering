/-
# Dense window at m = 94: the branch tree for the two-uncovered saved state 416

The state has two uncovered low speeds, 67 and 75.  Three leaves, each a pinned cover-capacity
certificate (`floor_of_pinned_cover`, module `Delta2PinnedCover`):

* leaf B: 67 is not a speed                                  (`Delta2CoverRangeS94s416B`, |I| = 1, sum c = 92);
* leaf C: 67 is a speed, 75 is not a speed                   (`Delta2CoverRangeS94s416C`, |I| = 1, sum c = 92);
* leaf A: 67 and 75 are both speeds                          (`Delta2CoverRangeS94s416A`, |I| = 0, sum c = 93).

`pinned_tree_three` says the three cases are exhaustive.  Certificates: `data/dense/m94_lean/certs/`.
-/
import LRSpectrumFull.Delta2PinnedCover
import LRSpectrumFull.Delta2CoverRangeS94s416A
import LRSpectrumFull.Delta2CoverRangeS94s416B
import LRSpectrumFull.Delta2CoverRangeS94s416C

namespace LRSpectrumFull

/-- **Dense window at m = 94** (`2m+1 = 189`): every 94 distinct positive velocities bounded by
188 meet the floor `1/95`.  Branch tree on the speeds 67 and 75 (three pinned cover-capacity leaves). -/
theorem dense_floor_m94 (v : Fin 94 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 188) :
    1 / (95 : ℝ) ≤ ML v :=
  pinned_tree_three 67 75 v (1 / (95 : ℝ) ≤ ML v)
    (fun hB => leaf94_s416B v hv hinj hden hB)
    (fun ha hb => leaf94_s416C v hv hinj hden hb ha)
    (fun ha hb => leaf94_s416A v hv hinj hden ha hb)

end LRSpectrumFull
