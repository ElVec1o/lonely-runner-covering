import Mathlib

/-!
# ROOM FCU, Hilbert seat: arithmetic core of "Goddyn–Wong tight instances avoid (m+1) | speed"

Goddyn–Wong criterion (as quoted in Zhang 2608.13599, Thm 1.1 / Thm 5.1): with `n` runners
(`n - 1` speeds), removed speed `r ∈ [1, n-1]`, multiplier `mm ≥ 1`, `s = n - r`, the accelerated
speed is `r * mm` and the criterion is `∀ b ∈ [s, mm*s - 1], 1 < gcd r b`.

`gw_not_dvd`: the criterion forces `¬ n ∣ r * mm`.
`gw_family_not_dvd`: every speed `r * mm r` of a multi-acceleration family in which each
accelerated runner meets the criterion is not divisible by `n`.
Consequence (with Lemma 4, RoomA4_rosenfeld): such instances are certified at t = 1/n and none
is divisor-complete, so none lies in the FloorCruxU class.
-/

namespace LRSpectrumFull.RoomFCUHilbert

/-- Any `r` consecutive naturals starting at `s` contain one coprime to `r`. -/
lemma exists_coprime_in_window (r s : ℕ) (hr : 0 < r) :
    ∃ b, s ≤ b ∧ b < s + r ∧ Nat.gcd r b = 1 := by
  set t := (r + 1 - s % r) % r with ht
  have htlt : t < r := Nat.mod_lt _ hr
  have hsr : s % r < r := Nat.mod_lt s hr
  have hb : (s + t) % r = 1 % r := by
    have e2 : (s + t) % r = (s % r + t % r) % r := Nat.add_mod _ _ _
    have e3 : t % r = t := by rw [ht, Nat.mod_mod]
    have e1 : (s % r + (r + 1 - s % r)) % r = ((s % r) % r + (r + 1 - s % r) % r) % r :=
      Nat.add_mod _ _ _
    rw [Nat.mod_mod] at e1
    have e4 : s % r + (r + 1 - s % r) = r + 1 := by omega
    rw [e4, Nat.add_mod_left] at e1
    rw [e2, e3, ht, ← e1]
  refine ⟨s + t, by omega, by omega, ?_⟩
  calc Nat.gcd r (s + t) = Nat.gcd ((s + t) % r) r := Nat.gcd_rec r (s + t)
    _ = Nat.gcd (1 % r) r := by rw [hb]
    _ = Nat.gcd r 1 := (Nat.gcd_rec r 1).symm
    _ = 1 := Nat.gcd_one_right r

/-- Arithmetic core: the Goddyn–Wong gcd criterion excludes `n ∣ r * mm`. -/
theorem gw_not_dvd (n r mm : ℕ) (hr : 0 < r) (hrn : r < n) (hmm : 0 < mm)
    (hcrit : ∀ b, n - r ≤ b → b < mm * (n - r) → 1 < Nat.gcd r b) :
    ¬ n ∣ r * mm := by
  rintro ⟨k, hk⟩
  set s := n - r with hs
  have hn : n = r + s := by omega
  rw [hn] at hk
  -- k < mm, since r < n
  have hkmm : k + 1 ≤ mm := by
    by_contra h
    push Not at h
    have : (r + s) * mm ≤ (r + s) * k := Nat.mul_le_mul_left _ (by omega)
    have hs0 : 0 < s := by omega
    nlinarith
  -- the window [s, mm*s) has length at least r
  have hwin : r + s ≤ mm * s := by
    have := Nat.mul_le_mul_left (r + s) hkmm
    nlinarith
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_coprime_in_window r s hr
  have := hcrit b (by omega) (by omega)
  omega

/-- Multi-acceleration families: speeds `r * mult r` for `r ∈ [1, n-1]`; if each accelerated
runner (`mult r ≥ 2`) meets the criterion, no speed is divisible by `n`. -/
theorem gw_family_not_dvd (n : ℕ) (mult : ℕ → ℕ) (hpos : ∀ r, 0 < mult r)
    (hcrit : ∀ r, 0 < r → r < n → 2 ≤ mult r →
      ∀ b, n - r ≤ b → b < mult r * (n - r) → 1 < Nat.gcd r b) :
    ∀ r, 0 < r → r < n → ¬ n ∣ r * mult r := by
  intro r hr hrn
  by_cases h2 : 2 ≤ mult r
  · exact gw_not_dvd n r (mult r) hr hrn (hpos r) (hcrit r hr hrn h2)
  · have h1 : mult r = 1 := by have := hpos r; omega
    rw [h1, Nat.mul_one]
    intro hd
    exact absurd (Nat.le_of_dvd hr hd) (by omega)

end LRSpectrumFull.RoomFCUHilbert
