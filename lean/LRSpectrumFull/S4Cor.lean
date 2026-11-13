/-
# Corollaries of the sum-bounded four-runner statement, generic in the sorted/primitive statement `H`

`H` is the statement of `sLRC4_le195` (four sorted positive speeds, gcd 1, sum at most 195, then `S4`).  This file does
NOT import the range data; `S4Final` instantiates `H`.

* `cor_fin`  : an arbitrary injective positive `v : Fin 4 → ℕ` with `Finset.univ.gcd v = 1` and `∑ v i ≤ 195`
               (sorting by `Tuple.sort` and `S4_of_cover` from `S4Perm`).
* `cor_any`  : the same without the gcd hypothesis (rescale by `g = gcd`; the sum only decreases; the time is `t / g`).
-/
import LRSpectrumFull.S4Perm

namespace LRSpectrumFull
namespace D0

/-- the statement of `sLRC4_le195` -/
def SortedStmt : Prop :=
  ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d → Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 →
    a + b + c + d ≤ 195 → S4 ![a, b, c, d]

theorem cor_fin (H : SortedStmt) (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hg : Finset.univ.gcd v = 1) (hs : ∑ i, v i ≤ 195) : S4 v := by
  let σ : Equiv.Perm (Fin 4) := Tuple.sort v
  let w : Fin 4 → ℕ := fun i => v (σ i)
  have hmono : Monotone w := Tuple.monotone_sort v
  have hinjw : Function.Injective w := hinj.comp σ.injective
  have hsm : StrictMono w := hmono.strictMono_of_injective hinjw
  have hsum : ∑ i, w i = ∑ i, v i := Equiv.sum_comp σ v
  have hgw : Finset.univ.gcd w = 1 := by
    apply Nat.dvd_one.mp
    rw [← hg]
    apply Finset.dvd_gcd
    intro j _
    have := Finset.gcd_dvd (f := w) (Finset.mem_univ (σ.symm j))
    simpa [w] using this
  have hg4 : Nat.gcd (Nat.gcd (w 0) (w 1)) (Nat.gcd (w 2) (w 3)) = 1 := by
    apply Nat.dvd_one.mp
    rw [← hgw]
    apply Finset.dvd_gcd
    intro i _
    fin_cases i
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hs4 : w 0 + w 1 + w 2 + w 3 ≤ 195 := by
    have h4 : ∑ i, w i = w 0 + w 1 + w 2 + w 3 := Fin.sum_univ_four w
    omega
  have key' : S4 ![w 0, w 1, w 2, w 3] :=
    H (w 0) (w 1) (w 2) (w 3) (hpos _)
      (hsm (by decide : (0 : Fin 4) < 1)) (hsm (by decide : (1 : Fin 4) < 2))
      (hsm (by decide : (2 : Fin 4) < 3)) hg4 hs4
  have hw : w = ![w 0, w 1, w 2, w 3] := by
    funext i
    fin_cases i <;> rfl
  have key : S4 w := by rw [hw]; exact key'
  exact S4_of_cover hinj (fun r => ⟨σ r, rfl⟩) (fun j => ⟨σ.symm j, by simp [w]⟩) key

theorem cor_any (H : SortedStmt) (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hs : ∑ i, v i ≤ 195) : S4 v := by
  obtain ⟨u, hu, hgu⟩ := Finset.extract_gcd v (Finset.univ_nonempty (α := Fin 4))
  set g : ℕ := Finset.univ.gcd v with hg
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · exfalso
      have := hu 0 (Finset.mem_univ _)
      rw [h0, zero_mul] at this
      exact (hpos 0).ne' this
    · exact h0
  have upos : ∀ i, 0 < u i := by
    intro i
    have := hpos i
    rw [hu i (Finset.mem_univ _)] at this
    exact Nat.pos_of_mul_pos_left this
  have uinj : Function.Injective u := by
    intro i j hij
    apply hinj
    rw [hu i (Finset.mem_univ _), hu j (Finset.mem_univ _), hij]
  have usum : ∑ i, u i ≤ 195 := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hs
    have h1 := hu i (Finset.mem_univ _)
    have h2 : 1 * u i ≤ g * u i := Nat.mul_le_mul_right _ hgpos
    omega
  have hSu : S4 u := cor_fin H u upos uinj hgu usum
  intro φ
  obtain ⟨t, ht⟩ := hSu φ
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  refine ⟨t / g, fun i => ?_⟩
  have e : (v i : ℝ) * (t / g) + φ i = (u i : ℝ) * t + φ i := by
    rw [hu i (Finset.mem_univ _)]
    push_cast
    field_simp
  show 1 / 5 ≤ tpDist ((v i : ℝ) * (t / g) + φ i)
  rw [e]
  exact ht i

#print axioms cor_fin
#print axioms cor_any

end D0
end LRSpectrumFull
