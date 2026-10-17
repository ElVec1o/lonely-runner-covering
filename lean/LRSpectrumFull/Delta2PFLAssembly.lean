/-
# The 3+1 assembly: chase → four safe runners

`pfl_three_one` — for the residual shape of the five-runner Prime Filtering
(three elements at level `0`, one at the top level, `m ≥ 1`), the decided
chase `chase_core` produces a single multiplier `μ = (j+1)·(1 + k·5^m)`
prime to `5` making all four elements safe: the three level-`0` chains run
through `digit_add` + `transfer_one`, the top element through
`toplevel_safe`.
-/
import LRSpectrumFull.Delta2PFLDigits

namespace LRSpectrumFull

/-- Carry-to-`Bool` bridge: for `c ≤ 1` the indicator of `decide (c = 1)`
recovers `c`. -/
theorem ite_carry (c : ℕ) (h : c ≤ 1) :
    (if decide (c = 1) then (1 : ℕ) else 0) = c := by
  interval_cases c <;> simp

/-- `chaseVal` at `j = 0` (multiplier `1`). -/
theorem chaseVal_mk0 (q : Fin 5) (c2 c3 : Bool) (r k : Fin 5) (h : (0 : ℕ) < 3) :
    chaseVal q c2 c3 r ⟨0, h⟩ k = q.val + k.val * (1 * r.val) := rfl

/-- `chaseVal` at `j = 1` (multiplier `2`). -/
theorem chaseVal_mk1 (q : Fin 5) (c2 c3 : Bool) (r k : Fin 5) (h : (1 : ℕ) < 3) :
    chaseVal q c2 c3 r ⟨1, h⟩ k
      = 2 * q.val + (if c2 then 1 else 0) + k.val * (2 * r.val) := rfl

/-- `chaseVal` at `j = 2` (multiplier `3`). -/
theorem chaseVal_mk2 (q : Fin 5) (c2 c3 : Bool) (r k : Fin 5) (h : (2 : ℕ) < 3) :
    chaseVal q c2 c3 r ⟨2, h⟩ k
      = 3 * q.val + (if c2 then 1 else 0) + (if c3 then 1 else 0)
        + k.val * (3 * r.val) := rfl

/-- The chase multipliers `j + 1 ∈ {1,2,3}` are prime to `5`. -/
theorem not_five_dvd_j (j : Fin 3) : ¬ 5 ∣ (j.val + 1) := by
  have h3 : j.val < 3 := j.isLt
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  omega

/-- The level-`0` stock multipliers `1 + k·5^m` are prime to `5` when `m ≥ 1`. -/
theorem not_five_dvd_lambda (m kv : ℕ) (hm : 1 ≤ m) : ¬ 5 ∣ (1 + kv * 5 ^ m) := by
  intro hdvd
  obtain ⟨c, hc⟩ := dvd_pow_self 5 (by omega : m ≠ 0)
  obtain ⟨e, he⟩ := hdvd
  rw [hc] at he
  have h2 : kv * (5 * c) = 5 * (kv * c) := by ring
  rw [h2] at he
  omega

/-- A level-`0` element has nonzero class mod `5`. -/
theorem mod5_ne_zero (d : ℕ) (hd : ¬ 5 ∣ d) (h : d % 5 < 5) :
    (⟨d % 5, h⟩ : Fin 5) ≠ 0 := by
  intro he
  exact hd (Nat.dvd_of_mod_eq_zero (congrArg Fin.val he))

/-- **One level-`0` element is safe under the chase multiplier.**  Feeding the
digit `q`, class `r`, and the two `digit_add` carries of a level-`0` element
into the chase conditions at `(j,k)` makes `(j+1)·(1 + k·5^m)·d` land in the
safe arc: the digit of `(j+1)·d` is the `chaseVal` base by the chain
identities, and the `1 + k·5^m` shift adds `k·(j+1)·d ≡ k·(j+1)·r` by the
transfer identity. -/
theorem safe_of_chase (m d : ℕ) (j : Fin 3) (k : Fin 5) (q r : Fin 5) (c₂ c₃ : ℕ)
    (hc₂ : c₂ ≤ 1) (hc₃ : c₃ ≤ 1)
    (hq : q.val = (d % (5 * 5 ^ m)) / 5 ^ m)
    (hr : r.val = d % 5)
    (h2 : ((d + d) % (5 * 5 ^ m)) / 5 ^ m
        = (((d % (5 * 5 ^ m)) / 5 ^ m + (d % (5 * 5 ^ m)) / 5 ^ m) + c₂) % 5)
    (h3 : ((2 * d + d) % (5 * 5 ^ m)) / 5 ^ m
        = ((((2 * d) % (5 * 5 ^ m)) / 5 ^ m + (d % (5 * 5 ^ m)) / 5 ^ m) + c₃) % 5)
    (hne0 : chaseVal q (decide (c₂ = 1)) (decide (c₃ = 1)) r j k % 5 ≠ 0)
    (hne4 : chaseVal q (decide (c₂ = 1)) (decide (c₃ = 1)) r j k % 5 ≠ 4) :
    5 ^ m ≤ cdist (5 * 5 ^ m) ((j.val + 1) * (1 + k.val * 5 ^ m) * d) := by
  have hP : 0 < 5 ^ m := pow_pos (by norm_num) m
  obtain ⟨jv, hjv⟩ := j
  have hJv : ((⟨jv, hjv⟩ : Fin 3)).val = jv := rfl
  rw [hJv]
  have hx : (jv + 1) * (1 + k.val * 5 ^ m) * d
      = (1 + k.val * 5 ^ m) * ((jv + 1) * d) := by ring
  rw [hx]
  apply safe_of_digit (5 ^ m) hP
  have T := transfer_one m 0 k.val ((jv + 1) * d) (Nat.zero_le m)
  rw [Nat.sub_zero, pow_zero, one_mul] at T
  rw [T]
  interval_cases jv
  · -- multiplier 1
    rw [chaseVal_mk0] at hne0 hne4
    rw [show ((0 : ℕ) + 1) = 1 from rfl]
    simp only [one_mul] at hne0 hne4 ⊢
    have hsh : (k.val * d) % 5 = (k.val * r.val) % 5 := by
      rw [hr, Nat.mul_mod, Nat.mul_mod k.val (d % 5),
        Nat.mod_mod_of_dvd d (dvd_refl 5)]
    omega
  · -- multiplier 2
    rw [chaseVal_mk1] at hne0 hne4
    rw [ite_carry c₂ hc₂] at hne0 hne4
    rw [show ((1 : ℕ) + 1) = 2 from rfl]
    have hdig : ((2 * d) % (5 * 5 ^ m)) / 5 ^ m
        = (((d % (5 * 5 ^ m)) / 5 ^ m + (d % (5 * 5 ^ m)) / 5 ^ m) + c₂) % 5 := by
      rw [two_mul]
      exact h2
    rw [hdig]
    have hsh : (k.val * (2 * d)) % 5 = (k.val * (2 * r.val)) % 5 := by
      rw [hr, Nat.mul_mod, Nat.mul_mod k.val (2 * (d % 5)), Nat.mul_mod 2 d,
        Nat.mul_mod 2 (d % 5), Nat.mod_mod_of_dvd d (dvd_refl 5)]
    omega
  · -- multiplier 3
    rw [chaseVal_mk2] at hne0 hne4
    rw [ite_carry c₂ hc₂, ite_carry c₃ hc₃] at hne0 hne4
    rw [show ((2 : ℕ) + 1) = 3 from rfl]
    have hdig2 : ((2 * d) % (5 * 5 ^ m)) / 5 ^ m
        = (((d % (5 * 5 ^ m)) / 5 ^ m + (d % (5 * 5 ^ m)) / 5 ^ m) + c₂) % 5 := by
      rw [two_mul]
      exact h2
    have hdig3 : ((3 * d) % (5 * 5 ^ m)) / 5 ^ m
        = ((((2 * d) % (5 * 5 ^ m)) / 5 ^ m + (d % (5 * 5 ^ m)) / 5 ^ m) + c₃) % 5 := by
      rw [show (3 : ℕ) * d = 2 * d + d from by ring]
      exact h3
    rw [hdig3, hdig2]
    have hsh : (k.val * (3 * d)) % 5 = (k.val * (3 * r.val)) % 5 := by
      rw [hr, Nat.mul_mod, Nat.mul_mod k.val (3 * (d % 5)), Nat.mul_mod 3 d,
        Nat.mul_mod 3 (d % 5), Nat.mod_mod_of_dvd d (dvd_refl 5)]
    omega

/-- **The 3+1 assembly.**  Three elements prime to `5` and one exactly at the
top level `m ≥ 1`: the chase produces a single multiplier `μ` prime to `5`
putting all four in the safe arc of `ℤ/5^{m+1}`. -/
theorem pfl_three_one (m : ℕ) (hm : 1 ≤ m) (d₁ d₂ d₃ t : ℕ)
    (h₁ : ¬ 5 ∣ d₁) (h₂ : ¬ 5 ∣ d₂) (h₃ : ¬ 5 ∣ d₃) (ht : ¬ 5 ∣ t) :
    ∃ μ, ¬ 5 ∣ μ ∧
      5 ^ m ≤ cdist (5 * 5 ^ m) (μ * d₁) ∧
      5 ^ m ≤ cdist (5 * 5 ^ m) (μ * d₂) ∧
      5 ^ m ≤ cdist (5 * 5 ^ m) (μ * d₃) ∧
      5 ^ m ≤ cdist (5 * 5 ^ m) (μ * (5 ^ m * t)) := by
  have hP : 0 < 5 ^ m := pow_pos (by norm_num) m
  obtain ⟨c12, hc12le, hc12⟩ := digit_add (5 ^ m) hP d₁ d₁
  obtain ⟨c13, hc13le, hc13⟩ := digit_add (5 ^ m) hP (2 * d₁) d₁
  obtain ⟨c22, hc22le, hc22⟩ := digit_add (5 ^ m) hP d₂ d₂
  obtain ⟨c23, hc23le, hc23⟩ := digit_add (5 ^ m) hP (2 * d₂) d₂
  obtain ⟨c32, hc32le, hc32⟩ := digit_add (5 ^ m) hP d₃ d₃
  obtain ⟨c33, hc33le, hc33⟩ := digit_add (5 ^ m) hP (2 * d₃) d₃
  obtain ⟨j, k, e10, e14, e20, e24, e30, e34⟩ :=
    chase_core
      ⟨(d₁ % (5 * 5 ^ m)) / 5 ^ m, digit_lt_five (5 ^ m) hP d₁⟩
      ⟨(d₂ % (5 * 5 ^ m)) / 5 ^ m, digit_lt_five (5 ^ m) hP d₂⟩
      ⟨(d₃ % (5 * 5 ^ m)) / 5 ^ m, digit_lt_five (5 ^ m) hP d₃⟩
      ⟨d₁ % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨d₂ % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨d₃ % 5, Nat.mod_lt _ (by norm_num)⟩
      (decide (c12 = 1)) (decide (c13 = 1))
      (decide (c22 = 1)) (decide (c23 = 1))
      (decide (c32 = 1)) (decide (c33 = 1))
      (mod5_ne_zero d₁ h₁ _) (mod5_ne_zero d₂ h₂ _) (mod5_ne_zero d₃ h₃ _)
  refine ⟨(j.val + 1) * (1 + k.val * 5 ^ m),
    five_not_dvd_mul (not_five_dvd_j j) (not_five_dvd_lambda m k.val hm),
    ?_, ?_, ?_, ?_⟩
  · exact safe_of_chase m d₁ j k _ _ c12 c13 hc12le hc13le rfl rfl hc12 hc13 e10 e14
  · exact safe_of_chase m d₂ j k _ _ c22 c23 hc22le hc23le rfl rfl hc22 hc23 e20 e24
  · exact safe_of_chase m d₃ j k _ _ c32 c33 hc32le hc33le rfl rfl hc32 hc33 e30 e34
  · exact toplevel_safe m _ t
      (five_not_dvd_mul (not_five_dvd_j j) (not_five_dvd_lambda m k.val hm)) ht

end LRSpectrumFull
