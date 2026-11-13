/-
# The four-runner statement for every primitive sorted speed vector of sum at most 195

`sLRC4_le195`: for natural numbers `0 < a < b < c < d` with `gcd (gcd a b) (gcd c d) = 1` and `a+b+c+d ≤ 195`,
`S4 ![a,b,c,d]`: for every real phase vector there is a real time at which all four runners are at circular
distance at least `1/5` from the origin (`S4`/`GoodR`/`tpDist` as in `D0Bridge`, `RFiveBase`, `TPSmall`).

Assembled from the range theorems of `S4R_*`, the five earlier probe modules `S4Range*`, and the `S4B_*` blocked
ranges, through the layers `S4A_<aa>` (one per `a`) and `S4All_<k>` (groups of ten values of `a`).
Corollaries (generic part in `S4Cor`): arbitrary injective positive `Fin 4 → ℕ` with gcd 1 and sum ≤ 195, and the same
without the gcd hypothesis.
-/
import LRSpectrumFull.S4All_1
import LRSpectrumFull.S4All_2
import LRSpectrumFull.S4All_3
import LRSpectrumFull.S4All_4
import LRSpectrumFull.S4All_5
import LRSpectrumFull.S4Cor

namespace LRSpectrumFull
namespace D0

theorem sLRC4_le195 : ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → a + b + c + d ≤ 195 → S4 ![a, b, c, d] := by
  intro a b c d ha hab hbc hcd hg hs
  have hcase : (1 ≤ a ∧ a ≤ 10) ∨ (11 ≤ a ∧ a ≤ 20) ∨ (21 ≤ a ∧ a ≤ 30) ∨ (31 ≤ a ∧ a ≤ 40) ∨
      (41 ≤ a ∧ a ≤ 47) := by omega
  rcases hcase with h | h | h | h | h
  · exact S4All_1 a b c d h.1 h.2 hab hbc hcd hs hg
  · exact S4All_2 a b c d h.1 h.2 hab hbc hcd hs hg
  · exact S4All_3 a b c d h.1 h.2 hab hbc hcd hs hg
  · exact S4All_4 a b c d h.1 h.2 hab hbc hcd hs hg
  · exact S4All_5 a b c d h.1 h.2 hab hbc hcd hs hg

theorem sLRC4_le195_fin (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hg : Finset.univ.gcd v = 1) (hs : ∑ i, v i ≤ 195) : S4 v :=
  cor_fin sLRC4_le195 v hpos hinj hg hs

theorem sLRC4_le195_any (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hs : ∑ i, v i ≤ 195) : S4 v :=
  cor_any sLRC4_le195 v hpos hinj hs

/-- fully unfolded restatement: real phases, `GoodR` and `tpDist` unfolded to `|x - round x|` -/
example : ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → a + b + c + d ≤ 195 →
    ∀ φ : Fin 4 → ℝ, ∃ t : ℝ, ∀ i : Fin 4,
      (1 : ℝ) / 5 ≤ |((![a, b, c, d] i : ℕ) : ℝ) * t + φ i - round (((![a, b, c, d] i : ℕ) : ℝ) * t + φ i)| :=
  fun a b c d ha hab hbc hcd hg hs φ => sLRC4_le195 a b c d ha hab hbc hcd hg hs φ

-- sanity instances
example : S4 ![1, 2, 3, 4] := sLRC4_le195 1 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num)
example : S4 ![1, 3, 4, 7] := sLRC4_le195 1 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num)
example : S4 ![10, 20, 30, 40] := sLRC4_le195_any ![10, 20, 30, 40] (by decide) (by decide)
  (by simp [Fin.sum_univ_four])

#print axioms sLRC4_le195
#print axioms sLRC4_le195_fin
#print axioms sLRC4_le195_any

end D0
end LRSpectrumFull
