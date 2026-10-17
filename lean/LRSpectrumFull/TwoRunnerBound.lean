/-
# Milestone 24: the uniform two-runner bound `D(p,q) ≤ 1/6`

Extends the two-runner theory to **all** coprime pairs. The exact value
`D(p,q) = 1/(2(p+q))` was proved (M9–M10) only for `p+q` odd; here we add
the `p+q` even case (both `p, q` odd), where the deep hole `t = 1/2` puts
both runners at distance `1/2`, giving `D = 0`. The uniform consequence

    D(p, q) ≤ 1/6   for every coprime (p, q),

is what the **product-subtorus** case of the `δ₂` classification needs
(each 2-dim component is a two-runner subtorus). No `sorry`.
-/

import LRSpectrumFull.GeneralLower
import LRSpectrumFull.MultiRunner
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- `‖m + 1/2‖ = 1/2` for any integer `m`. -/
theorem nearestIntDist_int_add_half (m : ℤ) : nearestIntDist ((m : ℝ) + 1 / 2) = 1 / 2 := by
  rw [add_comm, nearestIntDist_add_int]
  have hf : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr (by norm_num)
  simp only [nearestIntDist, hf]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, min_self]

/-- Rank-1 permutation invariance of the D-value (from `D_comp_le`). -/
theorem D_perm1 {k : ℕ} (v : Fin (k + 1) → ℤ) (σ : Equiv.Perm (Fin (k + 1))) :
    D (v ∘ ⇑σ) = D v := by
  apply le_antisymm
  · exact D_comp_le v ⇑σ
  · have h := D_comp_le (v ∘ ⇑σ) ⇑σ.symm
    rwa [show ((v ∘ ⇑σ) ∘ ⇑σ.symm) = v from by funext i; simp] at h

/-- The two-runner D-value is symmetric in `p, q`. -/
theorem D_vpair_comm (p q : ℕ) : D (vpair q p) = D (vpair p q) := by
  have hsw : vpair q p = vpair p q ∘ ⇑(Equiv.swap (0 : Fin 2) 1) := by
    funext i; fin_cases i <;>
      simp [vpair, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hsw, D_perm1]

/-- The two-runner gap is symmetric in `p, q` (the runner-distance
multiset is the same). -/
theorem gap_vpair_comm (p q : ℕ) (t : ℝ) : gap (vpair p q) t = gap (vpair q p) t := by
  have key : ∀ a b : ℕ, gap (vpair a b) t ≤ gap (vpair b a) t := by
    intro a b
    apply le_gap
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · have h := gap_le (vpair a b) t 1; rw [vpair_one] at h; rw [vpair_zero]; exact h
    · have h := gap_le (vpair a b) t 0; rw [vpair_zero] at h; rw [vpair_one]; exact h
  exact le_antisymm (key p q) (key q p)

/-- The exact-value bound `(p+q−1)/(2(p+q)) ≥ 1/3` whenever `p+q ≥ 3`. -/
private theorem val_ge_third {X : ℝ} (hX : 3 ≤ X) : (1 : ℝ) / 3 ≤ (X - 1) / (2 * X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXne : X ≠ 0 := ne_of_gt hX0
  rw [← sub_nonneg]
  have heq : (X - 1) / (2 * X) - 1 / 3 = (X - 3) / (6 * X) := by field_simp; ring
  rw [heq]
  apply div_nonneg (by linarith) (by linarith)

/-- For both `p, q` odd, the deep hole `t = 1/2` puts both runners at
distance `1/2`: `1/2 ≤ gap (vpair p q) (1/2)`. -/
theorem gap_vpair_half (p q : ℕ) (hpo : Odd p) (hqo : Odd q) :
    (1 / 2 : ℝ) ≤ gap (vpair p q) (1 / 2) := by
  obtain ⟨m, hm⟩ := hpo
  obtain ⟨n, hn⟩ := hqo
  have hpr : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hm
  have hqr : (q : ℝ) = 2 * n + 1 := by exact_mod_cast hn
  apply le_gap
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · have e : ((vpair p q 0 : ℝ)) * (1 / 2) = (m : ℝ) + 1 / 2 := by
      simp only [vpair, Matrix.cons_val_zero, Int.cast_natCast]; rw [hpr]; ring
    rw [e]; exact le_of_eq (nearestIntDist_int_add_half m).symm
  · have e : ((vpair p q 1 : ℝ)) * (1 / 2) = (n : ℝ) + 1 / 2 := by
      simp only [vpair, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
        Int.cast_natCast]; rw [hqr]; ring
    rw [e]; exact le_of_eq (nearestIntDist_int_add_half n).symm

/-- When both `p, q` are odd, `D(p,q) = 0 ≤ 1/6`. -/
theorem D_le_one_sixth_both_odd (p q : ℕ) (hpo : Odd p) (hqo : Odd q) :
    D (vpair p q) ≤ 1 / 6 := by
  have hML : (1 / 2 : ℝ) ≤ ML (vpair p q) := le_trans (gap_vpair_half p q hpo hqo) (gap_le_ML _ _)
  simp only [D]; linarith

/-- **Uniform two-runner bound:** `D(p, q) ≤ 1/6` for every coprime
`(p, q)` with `1 ≤ p, q`. -/
theorem D_le_one_sixth (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    D (vpair p q) ≤ 1 / 6 := by
  have hbound : ∀ a b : ℕ, 1 ≤ a → 2 ≤ b → D (vpair a b) ≤ 1 / (2 * ((a : ℝ) + b)) →
      D (vpair a b) ≤ 1 / 6 := by
    intro a b ha hb hD
    have h3 : (6 : ℝ) ≤ 2 * ((a : ℝ) + b) := by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have : 1 / (2 * ((a : ℝ) + b)) ≤ 1 / 6 := by
      apply one_div_le_one_div_of_le (by norm_num) h3
    linarith
  rcases Nat.even_or_odd p with hpe | hpo
  · rcases Nat.even_or_odd q with hqe | hqo
    · exfalso
      have hg : Nat.gcd p q = 1 := hcop
      have h2 : 2 ∣ Nat.gcd p q := Nat.dvd_gcd hpe.two_dvd hqe.two_dvd
      rw [hg] at h2; omega
    · -- p even, q odd: apply the exact bound to (q, p)
      have hp2 : 2 ≤ p := by have := hpe.two_dvd; omega
      rw [← D_vpair_comm p q]
      exact hbound q p hq hp2
        (D_le_general q p hq hp hqo (by
          obtain ⟨m, hm⟩ := hqo; obtain ⟨n, hn⟩ := hpe; exact ⟨m + n, by omega⟩)
          hcop.symm)
  · rcases Nat.even_or_odd q with hqe | hqo
    · -- p odd, q even
      have hq2 : 2 ≤ q := by have := hqe.two_dvd; omega
      exact hbound p q hp hq2
        (D_le_general p q hp hq hpo (by
          obtain ⟨m, hm⟩ := hpo; obtain ⟨n, hn⟩ := hqe; exact ⟨m + n, by omega⟩)
          hcop)
    · exact D_le_one_sixth_both_odd p q hpo hqo

/-- **Witness with gap `≥ 1/3`:** for every coprime `(p, q)` there is a
time where both runners are `≥ 1/3` from the integers. (`ML ≥ 1/3`,
attained.) This is what the product-subtorus argument samples. -/
theorem exists_gap_ge_third (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ t : ℝ, (1 : ℝ) / 3 ≤ gap (vpair p q) t := by
  rcases Nat.even_or_odd p with hpe | hpo
  · rcases Nat.even_or_odd q with hqe | hqo
    · exfalso
      have hg : Nat.gcd p q = 1 := hcop
      have h2 := Nat.dvd_gcd hpe.two_dvd hqe.two_dvd
      rw [hg] at h2; omega
    · -- p even, q odd
      have hp2 : 2 ≤ p := by have := hpe.two_dvd; omega
      obtain ⟨t, ht⟩ := exists_gap_ge_general q p hq hp hqo
        (by obtain ⟨m, hm⟩ := hqo; obtain ⟨n, hn⟩ := hpe; exact ⟨m + n, by omega⟩) hcop.symm
      refine ⟨t, ?_⟩
      rw [gap_vpair_comm p q]
      have hX : (3 : ℝ) ≤ (q : ℝ) + p := by
        have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      linarith [ht, val_ge_third hX]
  · rcases Nat.even_or_odd q with hqe | hqo
    · -- p odd, q even
      have hq2 : 2 ≤ q := by have := hqe.two_dvd; omega
      obtain ⟨t, ht⟩ := exists_gap_ge_general p q hp hq hpo
        (by obtain ⟨m, hm⟩ := hpo; obtain ⟨n, hn⟩ := hqe; exact ⟨m + n, by omega⟩) hcop
      refine ⟨t, ?_⟩
      have hX : (3 : ℝ) ≤ (p : ℝ) + q := by
        have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
        have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
        linarith
      linarith [ht, val_ge_third hX]
    · -- both odd
      exact ⟨1 / 2, le_trans (by norm_num) (gap_vpair_half p q hpo hqo)⟩

end LRSpectrumFull
