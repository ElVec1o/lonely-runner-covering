/-
# Theorem R5 (real phases): gcd-free corollaries

* `R5_tp`  : the statement of `R5_core` in the form `1/5 ≤ tpDist (v i * t + φ i)`, with no gcd hypothesis:
             four distinct positive speeds, at least one divisible by 5 and at least one not divisible by 5.
* `R5_gcd` : four distinct positive speeds with `g = gcd` and `5 ∣ v i / g` for some `i`.  (`R5` itself is the case
             `g = 1`.)  Proof: `R5` for `v / g` at the rescaled time `t' / g`.

Note: "some `v i` divisible by 5" alone is NOT enough without a gcd hypothesis, since `(5,10,15,20)` is then
allowed and contains `sLRC(4)` for `(1,2,3,4)`; the hypothesis of `R5_gcd` is the correct normalised one.
-/
import LRSpectrumFull.RFiveFinal

namespace LRSpectrumFull

theorem R5_tp (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hslow : ∃ i, 5 ∣ v i) (hfree : ∃ i, ¬ 5 ∣ v i) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ tpDist ((v i : ℝ) * t + φ i) :=
  R5_core v hpos hinj hslow hfree φ

theorem R5_gcd (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (h5 : ∃ i, 5 ∣ v i / Finset.univ.gcd v) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ tpDist ((v i : ℝ) * t + φ i) := by
  obtain ⟨u, hu, hgu⟩ := Finset.extract_gcd v (Finset.univ_nonempty (α := Fin 4))
  set g : ℕ := Finset.univ.gcd v with hg
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · exfalso
      have := hu 0 (Finset.mem_univ _)
      rw [h0, zero_mul] at this
      exact (hpos 0).ne' this
    · exact h0
  have hdiv : ∀ i, v i / g = u i := by
    intro i
    rw [hu i (Finset.mem_univ _)]
    exact Nat.mul_div_cancel_left _ hgpos
  have upos : ∀ i, 0 < u i := by
    intro i
    have := hpos i
    rw [hu i (Finset.mem_univ _)] at this
    exact Nat.pos_of_mul_pos_left this
  have uinj : Function.Injective u := by
    intro i j hij
    apply hinj
    rw [hu i (Finset.mem_univ _), hu j (Finset.mem_univ _), hij]
  have u5 : ∃ i, 5 ∣ u i := by
    obtain ⟨i, hi⟩ := h5
    exact ⟨i, by rw [← hdiv i]; exact hi⟩
  obtain ⟨t, ht⟩ := R5 u upos uinj hgu u5 φ
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  refine ⟨t / g, fun i => ?_⟩
  have e : (v i : ℝ) * (t / g) + φ i = (u i : ℝ) * t + φ i := by
    rw [hu i (Finset.mem_univ _)]
    push_cast
    field_simp
  rw [e]
  exact ht i

end LRSpectrumFull
