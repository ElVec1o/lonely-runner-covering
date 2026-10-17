/-
T2 on one-entry modifications (2026-09-24).

Family: speeds 1..m with the entry r replaced by w (m = k+1).
* `ML_ge_two_div_of_unit` : if `q ∣ a*r - 1` and no speed is `≡ 0, r, -r (mod q)`, then
  `2/q ≤ ML v` (witness time `a/q`).
* `oneEntry_ML_ge` : for the one-entry family, with `k+1 < q`, `(k+1+r < q ∨ q = 2r)`,
  `q ∣ a*r - 1` and `w ≢ 0, ±r (mod q)`, `2/q ≤ ML v`.
* `oneEntry_T2` : the case `q = 2m+1`, coprimality form: `2/(2m+1) ≤ ML v`.
No hypothesis `(m+1) ∣ w` is needed.
-/
import Mathlib
import LRSpectrumFull.RoomFCU_compress

namespace LRSpectrumFull.T2Sub

open LRSpectrumFull
open LRSpectrumFull.RoomFCUCompress (ML_ge_of_residues)

/-- Unit-inverse transfer: a congruence for `x*a` becomes one for `x`. -/
theorem dvd_transfer (q a r x c : ℤ) (har : q ∣ a * r - 1) (h : q ∣ x * a - c) :
    q ∣ x - c * r := by
  have e : x - c * r = r * (x * a - c) - x * (a * r - 1) := by ring
  rw [e]
  exact dvd_sub (dvd_mul_of_dvd_right h r) (dvd_mul_of_dvd_right har x)

theorem ML_ge_two_div_of_unit {k : ℕ} (v : Fin (k + 1) → ℤ) (q a r : ℤ) (hq : 0 < q)
    (har : q ∣ a * r - 1)
    (h : ∀ i, ¬ q ∣ v i ∧ ¬ q ∣ v i - r ∧ ¬ q ∣ v i + r) :
    (2 : ℝ) / q ≤ ML v := by
  have := ML_ge_of_residues v q a 2 q hq (by norm_num) hq (fun i => ?_)
  · exact_mod_cast this
  obtain ⟨h0, h1, h2⟩ := h i
  set s := v i * a % q with hs
  have hs0 : 0 ≤ s := Int.emod_nonneg _ hq.ne'
  have hsq : s < q := Int.emod_lt_of_pos _ hq
  have hd : q ∣ v i * a - s := by
    refine ⟨v i * a / q, ?_⟩
    have := Int.emod_add_ediv (v i * a) q
    rw [← hs] at this; linarith
  have n0 : s ≠ 0 := by
    intro e; rw [e] at hd
    exact h0 (by simpa using dvd_transfer q a r (v i) 0 har (by simpa using hd))
  have n1 : s ≠ 1 := by
    intro e; rw [e] at hd
    exact h1 (by simpa using dvd_transfer q a r (v i) 1 har hd)
  have n2 : s ≠ q - 1 := by
    intro e
    have hd' : q ∣ v i * a - (-1) := by
      have : v i * a - (-1) = (v i * a - s) + q * 1 := by rw [e]; ring
      rw [this]; exact dvd_add hd (dvd_mul_right q 1)
    have := dvd_transfer q a r (v i) (-1) har hd'
    exact h2 (by simpa [sub_neg_eq_add] using this)
  have hlo : 2 ≤ s := by omega
  have hhi : s ≤ q - 2 := by omega
  constructor <;> nlinarith

/-- The one-entry family: `1..k+1` with the entry `r` replaced by `w`. -/
def oneEntry (k : ℕ) (r w : ℤ) : Fin (k + 1) → ℤ :=
  fun i => if (i : ℤ) + 1 = r then w else (i : ℤ) + 1

theorem oneEntry_ML_ge (k : ℕ) (r w q a : ℤ) (hr1 : 1 ≤ r) (hrm : r ≤ k + 1)
    (hq : (k : ℤ) + 1 < q) (hqr : (k : ℤ) + 1 + r < q ∨ q = 2 * r)
    (har : q ∣ a * r - 1)
    (hw0 : ¬ q ∣ w) (hw1 : ¬ q ∣ w - r) (hw2 : ¬ q ∣ w + r) :
    (2 : ℝ) / q ≤ ML (oneEntry k r w) := by
  refine ML_ge_two_div_of_unit _ q a r (by omega) har (fun i => ?_)
  unfold oneEntry
  split_ifs with hi
  · exact ⟨hw0, hw1, hw2⟩
  · have hj1 : (1 : ℤ) ≤ (i : ℤ) + 1 := by omega
    have hjm : (i : ℤ) + 1 ≤ k + 1 := by have := i.isLt; omega
    set j : ℤ := (i : ℤ) + 1 with hj
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      have : 0 < c := by nlinarith
      nlinarith
    · rintro ⟨c, hc⟩
      rcases lt_trichotomy c 0 with h | h | h
      · nlinarith
      · subst h; apply hi; linarith
      · nlinarith
    · rintro ⟨c, hc⟩
      have c1 : 0 < c := by nlinarith
      rcases hqr with hqr | hqr
      · nlinarith
      · have c2 : c < 2 := by nlinarith
        have : c = 1 := by omega
        subst this; apply hi; linarith

/-- T2 for the one-entry family at `q = 2m+1`, `m = k+1`. -/
theorem oneEntry_T2 (k : ℕ) (r w : ℤ) (hr1 : 1 ≤ r) (hrm : r ≤ k + 1)
    (hcop : IsCoprime r (2 * ((k : ℤ) + 1) + 1))
    (hw0 : ¬ (2 * ((k : ℤ) + 1) + 1) ∣ w) (hw1 : ¬ (2 * ((k : ℤ) + 1) + 1) ∣ w - r)
    (hw2 : ¬ (2 * ((k : ℤ) + 1) + 1) ∣ w + r) :
    (2 : ℝ) / (2 * ((k : ℝ) + 1) + 1) ≤ ML (oneEntry k r w) := by
  obtain ⟨u, t, hut⟩ := hcop
  have := oneEntry_ML_ge k r w (2 * ((k : ℤ) + 1) + 1) u hr1 hrm (by omega) (Or.inl (by omega))
    ⟨-t, by linarith⟩ hw0 hw1 hw2
  push_cast at this
  exact this

/-- Second witness, time `1/r`: if `2r > m` and `r ∤ w` then `1/r ≤ ML`. -/
theorem oneEntry_ML_ge_inv (k : ℕ) (r w : ℤ) (hr1 : 1 ≤ r) (hrm : r ≤ k + 1)
    (h2r : (k : ℤ) + 1 < 2 * r) (hw : ¬ r ∣ w) :
    (1 : ℝ) / r ≤ ML (oneEntry k r w) := by
  have hr0 : (0 : ℤ) < r := by omega
  have key : ∀ x : ℤ, ¬ r ∣ x → 1 * r ≤ r * (x * 1 % r) ∧ 1 * r ≤ r * (r - x * 1 % r) := by
    intro x hx
    have hs0 : 0 ≤ x * 1 % r := Int.emod_nonneg _ hr0.ne'
    have hsr : x * 1 % r < r := Int.emod_lt_of_pos _ hr0
    have hne : x * 1 % r ≠ 0 := by
      intro e; exact hx (by simpa using Int.dvd_of_emod_eq_zero e)
    have h1 : 1 ≤ x * 1 % r := by omega
    have h2 : 1 ≤ r - x * 1 % r := by omega
    exact ⟨by nlinarith, by nlinarith⟩
  have := ML_ge_of_residues (oneEntry k r w) r 1 1 r hr0 (by norm_num) hr0 (fun i => ?_)
  · exact_mod_cast this
  apply key
  unfold oneEntry
  split_ifs with hi
  · exact hw
  · have hj1 : (1 : ℤ) ≤ (i : ℤ) + 1 := by omega
    have hjm : (i : ℤ) + 1 ≤ k + 1 := by have := i.isLt; omega
    rintro ⟨c, hc⟩
    have c1 : 0 < c := by nlinarith
    have c2 : c < 2 := by nlinarith
    have : c = 1 := by omega
    subst this; apply hi; linarith

/-- The `1/r` witness already meets the T2 target `2/(2m+1)`. -/
theorem oneEntry_T2_inv (k : ℕ) (r w : ℤ) (hr1 : 1 ≤ r) (hrm : r ≤ k + 1)
    (h2r : (k : ℤ) + 1 < 2 * r) (hw : ¬ r ∣ w) :
    (2 : ℝ) / (2 * ((k : ℝ) + 1) + 1) ≤ ML (oneEntry k r w) := by
  refine le_trans ?_ (oneEntry_ML_ge_inv k r w hr1 hrm h2r hw)
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrk : (r : ℝ) ≤ k + 1 := by exact_mod_cast hrm
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  linarith

end LRSpectrumFull.T2Sub
