/-
# The sweep lemma

A step of the collaborator's programme for the full lonely runner conjecture.  With `b` a missing
arithmetic-progression speed and `Q = n + r` for `b ≤ r < n`, the time `b⁻¹/Q` leaves every PRESENT
progression speed lonely, so the sweep isolates the replacement speeds as the only possible
blockers.

The mechanism is that `Q < 2n` makes the loneliness threshold `1/n` exceed `1/Q` by less than a
factor two, so a speed is bad only at residue `0`, `1` or `Q-1`, and each of those is excluded.

Their note records this lemma as proved; it is formalized here so that the surrounding fixed-k
argument can cite a machine-checked statement.
-/

import Mathlib
namespace LRSpectrumFull

/-- **The sweep lemma (VERIFIED).**

Let `b` be a missing arithmetic-progression speed, choose `r` with `b ≤ r ≤ n-1`, set `Q = n + r`,
and let `a` be an inverse of `b` modulo `Q`.  Then at the time `a/Q` every PRESENT speed
`1 ≤ k ≤ n-1`, `k ≠ b`, is lonely: its distance to the integers is at least `1/n`.

Since `Q = n + r < 2n`, a speed is bad only at residue `0`, `1` or `Q-1`.  Residue `0` forces
`Q ∣ k`, impossible for `1 ≤ k < Q`.  Residue `1` forces `k ≡ b`, which is the missing speed.
Residue `Q-1` forces `k = Q - b = n + r - b ≥ n`, above the whole progression.

This is the step that protects the untouched part of the progression while the replacements are
attacked; the conclusion is stated as `Q ≤ n * dist`, the loneliness condition at threshold `1/n`. -/
theorem sweep_protects (n r b k a Q : ℕ) (hQ : Q = n + r) (hbr : b ≤ r) (hrn : r < n)
    (hb1 : 1 ≤ b) (hab : a * b % Q = 1)
    (hk1 : 1 ≤ k) (hkn : k < n) (hkb : k ≠ b) :
    Q ≤ n * min (k * a % Q) (Q - k * a % Q) := by
  have hQpos : 0 < Q := by omega
  have hlt : k * a % Q < Q := Nat.mod_lt _ hQpos
  -- a is invertible mod Q
  have hcop : Nat.Coprime a Q := by
    have : Nat.gcd a Q ∣ 1 := by
      have h1 : Nat.gcd a Q ∣ a * b := Dvd.dvd.mul_right (Nat.gcd_dvd_left a Q) b
      have h2 : Nat.gcd a Q ∣ Q := Nat.gcd_dvd_right a Q
      have h3 : Nat.gcd a Q ∣ a * b % Q := (Nat.dvd_mod_iff h2).mpr h1
      rwa [hab] at h3
    exact Nat.eq_one_of_dvd_one this
  -- residue is not 0
  have hne0 : k * a % Q ≠ 0 := by
    intro h0
    have hdvd : Q ∣ k * a := Nat.dvd_of_mod_eq_zero h0
    have : Q ∣ k := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd)
    have := Nat.le_of_dvd (by omega) this
    omega
  -- residue is not 1: that forces k = b
  have hne1 : k * a % Q ≠ 1 := by
    intro h1
    -- k*a = 1 = b*a mod Q, so Q divides (k-b)*a, hence Q divides k-b
    have hba : b * a % Q = 1 := by rw [Nat.mul_comm]; exact hab
    have hkb' : (k * a) % Q = (b * a) % Q := by rw [h1, hba]
    have : k % Q = b % Q := by
      have := (Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hcop.symm) hkb')
      exact this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact hkb this
  -- residue is not Q-1: that forces k = Q - b >= n
  have hneQ1 : k * a % Q ≠ Q - 1 := by
    intro hm1
    have hba : b * a % Q = 1 := by rw [Nat.mul_comm]; exact hab
    have hsum : ((k + b) * a) % Q = 0 := by
      rw [Nat.add_mul, Nat.add_mod, hm1, hba]
      have : Q - 1 + 1 = Q := by omega
      rw [this, Nat.mod_self]
    have hdvd : Q ∣ (k + b) * a := Nat.dvd_of_mod_eq_zero hsum
    have hkbQ : Q ∣ (k + b) := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd)
    have := Nat.le_of_dvd (by omega) hkbQ
    omega
  -- so the residue lies in [2, Q-2] and n * 2 >= Q
  have h2 : 2 ≤ min (k * a % Q) (Q - k * a % Q) := by omega
  have hmul : n * 2 ≤ n * min (k * a % Q) (Q - k * a % Q) := Nat.mul_le_mul_left n h2
  omega

end LRSpectrumFull
