/-
Room O6 (2026-09-29), formalization queue row 1.

Goddyn-Wong, Integers 6 (2006) A38, Theorem 3.1, second half ("LR >= 1/n" step, p.9), read as an
arithmetic statement: under the GCD condition, `n` divides no speed `m_r * r`, `1 <= r <= n-1`.
Convention: their `n` = our `m + 1`.

Weakening relative to the paper's proof: the paper uses Lemma 2.1 (any floor(r/2)+1 consecutive
integers contain one coprime to r, via Bertrand) to get `(m_r - 1)(n - r) <= r/2`.  Only the weaker
bound `m_r (n - r) < n` is needed for non-divisibility, and it follows from the trivial fact that
any `r` consecutive positive integers contain one congruent to 1 mod r.  No Bertrand, no
hypotheses added; the hypothesis `n >= 5` is not needed, nor `some m_r >= 2`.
-/
import Mathlib

namespace LRSpectrumFull.RoomO6

/-- Divisor-completeness of a speed vector with `k+1` speeds (target runner count `k+2`), in the
inline form used by `RoomA4_rosenfeld.BridgeDisjunctionQPrimInd2`. -/
def DivisorComplete {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ j : ℕ, 2 ≤ j → j ≤ k + 2 → ∃ i, (j : ℤ) ∣ v i

/-- GCD condition of Goddyn-Wong Theorem 3.1 (`n` runners, multiplier vector `mu`). -/
def GCDCondition (n : ℕ) (mu : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ n - 1 → 2 ≤ mu r →
    ∀ b : ℕ, n - r ≤ b → b < mu r * (n - r) → 1 < Nat.gcd r b

/-- Weak form of Lemma 2.1: among any `r` consecutive positive integers `a, ..., a+r-1`
there is one coprime to `r` (namely one that is 1 mod r). -/
theorem exists_coprime_in_window (r a : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) :
    ∃ b, a ≤ b ∧ b < a + r ∧ Nat.gcd r b = 1 := by
  obtain ⟨s, hs, hq⟩ : ∃ s, s < r ∧ r * ((a + r - 2) / r) + s = a + r - 2 :=
    ⟨(a + r - 2) % r, Nat.mod_lt _ hr, Nat.div_add_mod _ _⟩
  refine ⟨r * ((a + r - 2) / r) + 1, by omega, by omega, ?_⟩
  simp

/-- Key size bound: under the GCD condition and `mu r >= 2`, `mu r * (n - r) < n`. -/
theorem mul_sub_lt (n : ℕ) (mu : ℕ → ℕ) (h : GCDCondition n mu) (r : ℕ)
    (hr1 : 1 ≤ r) (hrn : r ≤ n - 1) (h2 : 2 ≤ mu r) : mu r * (n - r) < n := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_coprime_in_window r (n - r) hr1 (by omega)
  have := h r hr1 hrn h2 b hb1 (by omega)
  omega

/-- **O6, arithmetic core.**  Under the GCD condition `n` divides no `mu r * r`, `1 <= r <= n-1`. -/
theorem not_dvd_speed (n : ℕ) (mu : ℕ → ℕ) (hmu : ∀ r, 1 ≤ mu r) (h : GCDCondition n mu)
    (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n - 1) : ¬ n ∣ mu r * r := by
  intro hd
  have hpos : 0 < mu r * (n - r) := Nat.mul_pos (hmu r) (by omega)
  have hlt : mu r * (n - r) < n := by
    by_cases h2 : 2 ≤ mu r
    · exact mul_sub_lt n mu h r hr1 hrn h2
    · have : mu r = 1 := by have := hmu r; omega
      rw [this]; omega
  have hsum : mu r * r + mu r * (n - r) = n * mu r := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega), Nat.mul_comm]
  have hd2 : n ∣ mu r * (n - r) := by
    have : n ∣ mu r * r + mu r * (n - r) := hsum ▸ Dvd.intro _ rfl
    exact (Nat.dvd_add_right hd).mp this
  exact absurd (Nat.le_of_dvd hpos hd2) (by omega)

/-- **O6 (VERIFIED target).**  Speeds `mu (i+1) * (i+1)`, `i : Fin (k+1)`, `n = k+2` runners.
Under the GCD condition the vector is not divisor-complete (it misses `j = n`). -/
theorem not_divisorComplete (k : ℕ) (mu : ℕ → ℕ) (hmu : ∀ r, 1 ≤ mu r)
    (h : GCDCondition (k + 2) mu) :
    ¬ DivisorComplete (fun i : Fin (k + 1) => ((mu (i.val + 1) * (i.val + 1) : ℕ) : ℤ)) := by
  intro hDC
  obtain ⟨i, hi⟩ := hDC (k + 2) (by omega) le_rfl
  have hi' : (k + 2) ∣ mu (i.val + 1) * (i.val + 1) := by
    simp only at hi
    exact_mod_cast hi
  exact not_dvd_speed (k + 2) mu hmu h (i.val + 1) (by omega) (by have := i.isLt; omega) hi'

end LRSpectrumFull.RoomO6
