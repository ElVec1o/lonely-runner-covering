/-
# TP' at prime N = m + 1: the "free" case (pigeonhole at times j/p)

For a prime `p` and `p - 1` runners with integer speeds `v i` and phases `s i / p`, if no runner has both
`p ∣ v i` and `p ∣ s i` ("pinned at 0 for every time j/p"), then some time `t = j / p` puts every runner at
distance `≥ 1/p` from an integer.  Proof: runner `i` is bad at `j` iff `v i * j + s i ≡ 0 (mod p)`, which excludes at
most one residue `j`; `p - 1` runners exclude at most `p - 1 < p` residues.
Hand proof: private/INVENTION_2026_11/TP4_REPORT.md (Level-1 pigeonhole).
-/
import LRSpectrumFull.TPThreeR

namespace LRSpectrumFull

lemma tp_residue (p : ℕ) (hp : 2 ≤ p) (N : ℤ) (hN : (N : ℤ) % p ≠ 0) :
    1 / (p : ℝ) ≤ tpDist ((N : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpZ : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
  set w : ℤ := N / p with hw
  set r : ℤ := N % p with hr
  have hdiv : (p : ℤ) * w + r = N := Int.mul_ediv_add_emod N p
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hpZ.ne'
  have hrp : r < p := Int.emod_lt_of_pos _ hpZ
  have hr1 : 1 ≤ r := by omega
  have hx : (N : ℝ) / p = (w : ℝ) + (r : ℝ) / p := by
    have h' : ((p * w + r : ℤ) : ℝ) = (N : ℝ) := by rw [hdiv]
    push_cast at h'
    field_simp
    linarith
  rw [hx]
  have e1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have e2 : (r : ℝ) ≤ p - 1 := by
    have : (r : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : r + 1 ≤ (p : ℤ))
    linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  refine tpDist_ge_win _ _ w ?_ ?_ (by positivity) ?_
  · have : 1 / (p : ℝ) ≤ (r : ℝ) / p := by
      apply div_le_div_of_nonneg_right e1 hpR.le
    linarith
  · have : (r : ℝ) / p ≤ 1 - 1 / (p : ℝ) := by
      rw [div_le_iff₀ hpR]
      have : (1 - 1 / (p : ℝ)) * p = p - 1 := by field_simp
      linarith
    linarith
  · rw [div_le_iff₀ hpR] ; nlinarith

theorem TP_prime_free (p : ℕ) [hp : Fact p.Prime] (v : Fin (p - 1) → ℕ) (s : Fin (p - 1) → ℤ)
    (h : ∀ i, ¬((p : ℤ) ∣ (v i : ℤ) ∧ (p : ℤ) ∣ s i)) :
    ∃ t : ℝ, ∀ i, 1 / (p : ℝ) ≤ tpDist ((v i : ℝ) * t + (s i : ℝ) / p) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  -- the excluded residue of runner i
  let f : Fin (p - 1) → ZMod p := fun i => -((s i : ZMod p) / (v i : ZMod p))
  have hcard : (Finset.univ.image f).card < Fintype.card (ZMod p) := by
    have h1 : (Finset.univ.image f).card ≤ Fintype.card (Fin (p - 1)) := Finset.card_image_le
    rw [Fintype.card_fin] at h1
    rw [ZMod.card]
    omega
  obtain ⟨j, hj⟩ : ∃ j : ZMod p, j ∉ Finset.univ.image f := by
    by_contra hcon
    push Not at hcon
    have : Finset.univ ⊆ Finset.univ.image f := fun j _ => hcon j
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    omega
  refine ⟨(j.val : ℝ) / p, fun i => ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hrewrite : (v i : ℝ) * ((j.val : ℝ) / p) + (s i : ℝ) / p
      = (((v i : ℤ) * (j.val : ℤ) + s i : ℤ) : ℝ) / p := by
    push_cast; field_simp
  rw [hrewrite]
  apply tp_residue p hp2
  intro hmod
  have hdvd : (p : ℤ) ∣ (v i : ℤ) * (j.val : ℤ) + s i := Int.dvd_of_emod_eq_zero hmod
  have hz : (((v i : ℤ) * (j.val : ℤ) + s i : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  by_cases hv0 : (v i : ZMod p) = 0
  · rw [hv0, zero_mul, zero_add] at hz
    have hs : (p : ℤ) ∣ s i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
    have hv : (p : ℤ) ∣ (v i : ℤ) := by
      have : ((v i : ℤ) : ZMod p) = 0 := by exact_mod_cast hv0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
    exact h i ⟨hv, hs⟩
  · apply hj
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    show -((s i : ZMod p) / (v i : ZMod p)) = j
    have : (s i : ZMod p) = -((v i : ZMod p) * j) := by linear_combination hz
    rw [this]
    field_simp

end LRSpectrumFull
