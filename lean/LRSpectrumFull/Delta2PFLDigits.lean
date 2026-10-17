/-
# Prime-filtering digit layer, p = 5 — the prototype

The single point of failure of the Barajas–Serra five-runner formalization is
the leading-digit calculus over `ℤ/5^{m+1}` with *symbolic* `m`.  This module
prototypes it over `ℕ` with the modulus abstracted as `N = 5·P` (`P = 5^m`
never enters `omega`):

* `digit_add_mul_P` — adding `c·P` shifts the leading digit `(x % N)/P` by
  exactly `c` modulo `5`, carry-free (the low part `x % P` is untouched);
* `transfer_one` — the multiplier `1 + k·5^{m-j}` acting on `x = 5^j·y`
  shifts the digit by `k·y % 5`: the Prime Filtering transfer identity;
* `safe_of_digit` — digit in `{1,2,3}` forces `cdist N x ≥ P`, i.e.
  `‖x/N‖ ≥ 1/5`: the sufficient arc condition the chases consume.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

namespace LRSpectrumFull

/-- Circular distance to `0` in `ℤ/N`, on natural representatives. -/
def cdist (N x : ℕ) : ℕ := min (x % N) (N - x % N)

/-- **Carry-free digit shift.**  Adding `c·P` to `x` shifts the leading digit
`(x % (5P))/P` by `c` modulo `5`; the low part is untouched. -/
theorem digit_add_mul_P (P : ℕ) (hP : 0 < P) (x c : ℕ) :
    ((x + c * P) % (5 * P)) / P = (((x % (5 * P)) / P) + c) % 5 := by
  -- decompose x % (5P) = a·P + b with a < 5, b < P
  set r := x % (5 * P) with hr
  have hrlt : r < 5 * P := Nat.mod_lt _ (by positivity)
  set a := r / P with ha
  set b := r % P with hb
  have hdecomp : r = a * P + b := by
    rw [ha, hb, mul_comm]
    exact (Nat.div_add_mod r P).symm
  have hblt : b < P := Nat.mod_lt _ hP
  have halt : a < 5 := by
    by_contra h
    push_neg at h
    have : 5 * P ≤ a * P := Nat.mul_le_mul_right P h
    omega
  -- reduce x to r inside the mod
  have hstep1 : (x + c * P) % (5 * P) = (r + c * P) % (5 * P) := by
    have hx : x + c * P = (x % (5 * P) + c * P) + 5 * P * (x / (5 * P)) := by
      have h := Nat.div_add_mod x (5 * P)
      omega
    rw [hx, Nat.add_mul_mod_self_left, ← hr]
  -- (a + c) splits into 5-quotient and 5-remainder
  have hsplit : a + c = ((a + c) / 5) * 5 + (a + c) % 5 := by
    rw [mul_comm]
    exact (Nat.div_add_mod (a + c) 5).symm
  have hmod5 : (a + c) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  -- r + cP = ((a+c)/5)·(5P) + ((a+c)%5)·P + b
  have hval : r + c * P = ((a + c) / 5) * (5 * P) + (((a + c) % 5) * P + b) := by
    calc r + c * P = (a + c) * P + b := by rw [hdecomp]; ring
      _ = (((a + c) / 5) * 5 + (a + c) % 5) * P + b := by rw [← hsplit]
      _ = ((a + c) / 5) * (5 * P) + (((a + c) % 5) * P + b) := by ring
  have hsmall : ((a + c) % 5) * P + b < 5 * P := by
    have h1 : ((a + c) % 5) * P ≤ 4 * P := Nat.mul_le_mul_right P (by omega)
    omega
  have hval' : r + c * P = (((a + c) % 5) * P + b) + ((a + c) / 5) * (5 * P) := by
    rw [hval]; ring
  have hstep2 : (r + c * P) % (5 * P) = ((a + c) % 5) * P + b := by
    rw [hval', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsmall]
  have hstep3 : (((a + c) % 5) * P + b) / P = (a + c) % 5 := by
    rw [show ((a + c) % 5) * P + b = b + ((a + c) % 5) * P from by ring,
      Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hblt, zero_add]
  rw [hstep1, hstep2, hstep3]

/-- The multiplier algebra: `(1 + k·5^{m-j})·(5^j·y) = 5^j·y + (k·y)·5^m`. -/
theorem lambda_mul_eq (m j k y : ℕ) (hj : j ≤ m) :
    (1 + k * 5 ^ (m - j)) * (5 ^ j * y) = 5 ^ j * y + (k * y) * 5 ^ m := by
  have hpow : 5 ^ (m - j) * 5 ^ j = 5 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  calc (1 + k * 5 ^ (m - j)) * (5 ^ j * y)
      = 5 ^ j * y + (k * y) * (5 ^ (m - j) * 5 ^ j) := by ring
    _ = 5 ^ j * y + (k * y) * 5 ^ m := by rw [hpow]

/-- Multiples of `P` reduce mod `5` inside `ℤ/5P`. -/
theorem mul_P_mod (P t : ℕ) : (t * P) % (5 * P) = (t % 5) * P :=
  Nat.mul_mod_mul_right P t 5

/-- **The transfer identity** (Prime Filtering, `p = 5`): the multiplier
`1 + k·5^{m-j}` shifts the leading digit of `x = 5^j·y` by `k·y` modulo `5`. -/
theorem transfer_one (m j k y : ℕ) (hj : j ≤ m) :
    (((1 + k * 5 ^ (m - j)) * (5 ^ j * y)) % (5 * 5 ^ m)) / 5 ^ m
      = (((5 ^ j * y % (5 * 5 ^ m)) / 5 ^ m) + k * y) % 5 := by
  have hP : 0 < 5 ^ m := pow_pos (by norm_num) m
  rw [lambda_mul_eq m j k y hj]
  exact digit_add_mul_P (5 ^ m) hP (5 ^ j * y) (k * y)

/-- **The sufficient arc condition**: leading digit in `{1,2,3}` forces
`cdist (5P) x ≥ P` — the runner is at distance `≥ 1/5` around the circle. -/
theorem safe_of_digit (P : ℕ) (hP : 0 < P) (x : ℕ)
    (h : (x % (5 * P)) / P = 1 ∨ (x % (5 * P)) / P = 2 ∨ (x % (5 * P)) / P = 3) :
    P ≤ cdist (5 * P) x := by
  set r := x % (5 * P) with hr
  have hrlt : r < 5 * P := Nat.mod_lt _ (by positivity)
  have hlow : P ≤ r := by
    rcases h with h | h | h <;>
    · by_contra hc
      push_neg at hc
      have : r / P = 0 := Nat.div_eq_of_lt hc
      omega
  have hhigh : r < 4 * P := by
    rcases h with h | h | h <;>
    · by_contra hc
      push_neg at hc
      have h4 : 4 ≤ r / P := Nat.le_div_iff_mul_le hP |>.mpr (by omega)
      omega
  unfold cdist
  rw [← hr]
  omega

/-- **The top-level carry law**: multiplying by `j ∈ {1,…,4}` sends the leading
digit `a` to `j·a + c` modulo `5` for some carry `c < j` — the multiplier stock
`Λ_m = {1,2,3,4}` moves digits by controlled jumps. -/
theorem transfer_top (P : ℕ) (hP : 0 < P) (x j : ℕ) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) :
    ∃ c < j, ((j * x) % (5 * P)) / P = (j * ((x % (5 * P)) / P) + c) % 5 := by
  set r := x % (5 * P) with hr
  set a := r / P with ha
  set b := r % P with hb
  have hdecomp : r = a * P + b := by
    rw [ha, hb, mul_comm]
    exact (Nat.div_add_mod r P).symm
  have hblt : b < P := Nat.mod_lt _ hP
  have hstep1 : (j * x) % (5 * P) = (j * r) % (5 * P) := by
    have h := Nat.div_add_mod x (5 * P)
    rw [← hr] at h
    have hx : j * x = j * r + 5 * P * (j * (x / (5 * P))) := by
      calc j * x = j * (5 * P * (x / (5 * P)) + r) := by rw [h]
        _ = j * r + 5 * P * (j * (x / (5 * P))) := by ring
    rw [hx, Nat.add_mul_mod_self_left]
  have hjr : j * r = j * b + (j * a) * P := by
    rw [hdecomp]
    ring
  have hj4b : j * b ≤ 4 * b := Nat.mul_le_mul_right b hj4
  have hjb5 : j * b < 5 * P := by omega
  have hjblt : j * b < j * P :=
    mul_lt_mul_of_pos_left hblt (by omega : 0 < j)
  have helt : (j * b) / P < j := by
    rw [Nat.div_lt_iff_lt_mul hP]
    exact hjblt
  refine ⟨(j * b) / P, helt, ?_⟩
  have hfinal : ((j * r) % (5 * P)) / P = ((j * b % (5 * P)) / P + j * a) % 5 :=
    hjr ▸ digit_add_mul_P P hP (j * b) (j * a)
  rw [hstep1, hfinal, Nat.mod_eq_of_lt hjb5, ha]
  omega

/-- **Level freezing**: a multiplier at level `j` leaves every element of level
`i > j` untouched modulo `N = 5^{m+1}` — its perturbation carries valuation
`≥ m + 1`.  This is what makes the downward induction of the Prime Filtering
Lemma possible: fixing level `j` does not disturb the levels already fixed. -/
theorem transfer_one_frozen (m j i k y : ℕ) (hji : j < i) (hi : i ≤ m) :
    ((1 + k * 5 ^ (m - j)) * (5 ^ i * y)) % (5 * 5 ^ m) = (5 ^ i * y) % (5 * 5 ^ m) := by
  have hpow : 5 ^ (m - j) * 5 ^ i = 5 * 5 ^ m * 5 ^ (i - j - 1) := by
    rw [← pow_add, show 5 * 5 ^ m = 5 ^ (m + 1) from (pow_succ 5 m).symm ▸ (mul_comm (5 ^ m) 5) ▸ rfl,
      ← pow_add]
    congr 1
    omega
  have hsplit : (1 + k * 5 ^ (m - j)) * (5 ^ i * y)
      = 5 ^ i * y + (k * y * 5 ^ (i - j - 1)) * (5 * 5 ^ m) := by
    calc (1 + k * 5 ^ (m - j)) * (5 ^ i * y)
        = 5 ^ i * y + (k * y) * (5 ^ (m - j) * 5 ^ i) := by ring
      _ = 5 ^ i * y + (k * y) * (5 * 5 ^ m * 5 ^ (i - j - 1)) := by rw [hpow]
      _ = 5 ^ i * y + (k * y * 5 ^ (i - j - 1)) * (5 * 5 ^ m) := by ring
  rw [hsplit, Nat.add_mul_mod_self_right]

/-- The level-`j` multipliers are prime to `5` (`j < m`): they are `≡ 1 mod 5`. -/
theorem lambda_not_dvd (m j k : ℕ) (hj : j < m) : ¬ (5 ∣ (1 + k * 5 ^ (m - j))) := by
  intro h
  have h5 : (5 : ℕ) ∣ k * 5 ^ (m - j) :=
    Dvd.dvd.mul_left (dvd_pow_self 5 (by omega : m - j ≠ 0)) k
  have h1 : (5 : ℕ) ∣ 1 := by
    rw [add_comm] at h
    exact (Nat.dvd_add_right h5).mp h
  omega

/-- **The level pigeonhole, mod-5 core**: for any two unit slopes and any two
starting digits, one of the five shifts `k` avoids the forbidden digits `{0,4}`
for both — each element forbids at most two of the five `k` (the shift is a
bijection), and `2 + 2 < 5`.  Kernel decide over `5⁴` profiles. -/
theorem level_pigeonhole_core : ∀ (a₁ a₂ y₁ y₂ : Fin 5), y₁ ≠ 0 → y₂ ≠ 0 →
    ∃ k : Fin 5, ((a₁.val + k.val * y₁.val) % 5 ≠ 0 ∧ (a₁.val + k.val * y₁.val) % 5 ≠ 4)
      ∧ ((a₂.val + k.val * y₂.val) % 5 ≠ 0 ∧ (a₂.val + k.val * y₂.val) % 5 ≠ 4) := by
  decide

/-- Reduction of the shifted digit modulo `5`. -/
theorem shift_mod (aa YY kk : ℕ) :
    (aa + kk * YY) % 5 = (aa % 5 + kk * (YY % 5)) % 5 := by
  conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd aa (dvd_refl 5),
    Nat.mod_mod_of_dvd YY (dvd_refl 5)]

/-- **The level pigeonhole**, general form: two elements with slopes prime to
`5` admit a common shift `k < 5` whose digits avoid `{0,4}` for both. -/
theorem level_pigeonhole (a₁ a₂ Y₁ Y₂ : ℕ) (h₁ : ¬ 5 ∣ Y₁) (h₂ : ¬ 5 ∣ Y₂) :
    ∃ k < 5, ((a₁ + k * Y₁) % 5 ≠ 0 ∧ (a₁ + k * Y₁) % 5 ≠ 4)
      ∧ ((a₂ + k * Y₂) % 5 ≠ 0 ∧ (a₂ + k * Y₂) % 5 ≠ 4) := by
  have hY₁ : Y₁ % 5 ≠ 0 := fun h => h₁ (Nat.dvd_of_mod_eq_zero h)
  have hY₂ : Y₂ % 5 ≠ 0 := fun h => h₂ (Nat.dvd_of_mod_eq_zero h)
  have h5 : (0:ℕ) < 5 := by norm_num
  obtain ⟨k, ⟨hk1a, hk1b⟩, ⟨hk2a, hk2b⟩⟩ :=
    level_pigeonhole_core ⟨a₁ % 5, Nat.mod_lt _ h5⟩ ⟨a₂ % 5, Nat.mod_lt _ h5⟩
      ⟨Y₁ % 5, Nat.mod_lt _ h5⟩ ⟨Y₂ % 5, Nat.mod_lt _ h5⟩
      (fun h => hY₁ (by simpa using congrArg Fin.val h))
      (fun h => hY₂ (by simpa using congrArg Fin.val h))
  refine ⟨k.val, k.isLt, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rw [shift_mod] <;> assumption

/-- **The two-element level step**: two elements at level `j` (slopes prime to
`5`) admit a multiplier `λ = 1 + k·5^{m-j}` in the level-`j` stock whose action
puts both leading digits outside `{0,4}` — i.e. both runners land in the safe
arc.  Combined with `transfer_one_frozen` (higher levels unmoved) this is the
inductive step of the Prime Filtering Lemma. -/
theorem pfl_level_two (m j : ℕ) (hjm : j ≤ m) (y₁ y₂ : ℕ)
    (hy₁ : ¬ 5 ∣ y₁) (hy₂ : ¬ 5 ∣ y₂) :
    ∃ k < 5,
      ((((1 + k * 5 ^ (m - j)) * (5 ^ j * y₁)) % (5 * 5 ^ m)) / 5 ^ m ≠ 0
        ∧ (((1 + k * 5 ^ (m - j)) * (5 ^ j * y₁)) % (5 * 5 ^ m)) / 5 ^ m ≠ 4)
      ∧ ((((1 + k * 5 ^ (m - j)) * (5 ^ j * y₂)) % (5 * 5 ^ m)) / 5 ^ m ≠ 0
        ∧ (((1 + k * 5 ^ (m - j)) * (5 ^ j * y₂)) % (5 * 5 ^ m)) / 5 ^ m ≠ 4) := by
  obtain ⟨k, hk5, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ :=
    level_pigeonhole ((5 ^ j * y₁ % (5 * 5 ^ m)) / 5 ^ m)
      ((5 ^ j * y₂ % (5 * 5 ^ m)) / 5 ^ m) y₁ y₂ hy₁ hy₂
  refine ⟨k, hk5, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    rw [transfer_one m j k _ hjm] <;> assumption

/-- Products of two non-multiples of `5` are non-multiples of `5`. -/
theorem mul_mod5_ne : ∀ (a b : Fin 5), a ≠ 0 → b ≠ 0 → (a.val * b.val) % 5 ≠ 0 := by
  decide

theorem five_not_dvd_mul {a b : ℕ} (ha : ¬ 5 ∣ a) (hb : ¬ 5 ∣ b) : ¬ 5 ∣ (a * b) := by
  have h5 : (0 : ℕ) < 5 := by norm_num
  have ha' : a % 5 ≠ 0 := fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hb' : b % 5 ≠ 0 := fun h => hb (Nat.dvd_of_mod_eq_zero h)
  intro hdvd
  have h' : (a * b) % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  exact mul_mod5_ne ⟨a % 5, Nat.mod_lt _ h5⟩ ⟨b % 5, Nat.mod_lt _ h5⟩
    (fun hc => ha' (by simpa using congrArg Fin.val hc))
    (fun hc => hb' (by simpa using congrArg Fin.val hc))
    (by rw [← Nat.mul_mod]; exact h')

/-- Safety of the element `5^lev · slope` under the multiplier `μ`: its
residue keeps circular distance `≥ 5^m` from `0` — i.e. the runner is in the
safe arc at time `μ/5^{m+1}`. -/
def SafeAt (m μ lev slope : ℕ) : Prop :=
  5 ^ m ≤ cdist (5 * 5 ^ m) (μ * (5 ^ lev * slope))

/-- Digits are `< 5`. -/
theorem digit_lt_five (P : ℕ) (hP : 0 < P) (x : ℕ) : (x % (5 * P)) / P < 5 := by
  rw [Nat.div_lt_iff_lt_mul hP]
  have h : x % (5 * P) < 5 * P := Nat.mod_lt _ (by positivity)
  omega

/-- **Top-level elements are automatically safe** under any multiplier prime
to `5`: their residue is a nonzero multiple of `5^m`, at distance `≥ 5^m`
from `0` on the circle. -/
theorem toplevel_safe (m μ z : ℕ) (hμ : ¬ 5 ∣ μ) (hz : ¬ 5 ∣ z) :
    SafeAt m μ m z := by
  unfold SafeAt cdist
  have hP : 0 < 5 ^ m := pow_pos (by norm_num) m
  have hmod : (μ * (5 ^ m * z)) % (5 * 5 ^ m) = 5 ^ m * ((μ * z) % 5) := by
    rw [show μ * (5 ^ m * z) = 5 ^ m * (μ * z) from by ring,
      show 5 * 5 ^ m = 5 ^ m * 5 from by ring, Nat.mul_mod_mul_left]
  rw [hmod]
  have h5 : ¬ 5 ∣ (μ * z) := five_not_dvd_mul hμ hz
  have hz5 : (μ * z) % 5 ≠ 0 := fun h => h5 (Nat.dvd_of_mod_eq_zero h)
  have hz5' : (μ * z) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  set R := (μ * z) % 5 with hR
  have h₁ : 5 ^ m ≤ 5 ^ m * R := Nat.le_mul_of_pos_right _ (by omega)
  have h₂ : 5 ^ m * R ≤ 4 * 5 ^ m := by
    calc 5 ^ m * R ≤ 5 ^ m * 4 := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * 5 ^ m := by ring
  omega

/-- **Freezing at the `cdist` level**: a level-`j` multiplier does not change
the circular distance of any element of level `i > j`. -/
theorem cdist_frozen (m j i k y μ : ℕ) (hji : j < i) (him : i ≤ m) :
    cdist (5 * 5 ^ m) ((1 + k * 5 ^ (m - j)) * (μ * (5 ^ i * y)))
      = cdist (5 * 5 ^ m) (μ * (5 ^ i * y)) := by
  unfold cdist
  rw [show (1 + k * 5 ^ (m - j)) * (μ * (5 ^ i * y))
      = (1 + k * 5 ^ (m - j)) * (5 ^ i * (μ * y)) from by ring,
    transfer_one_frozen m j i k (μ * y) hji him,
    show 5 ^ i * (μ * y) = μ * (5 ^ i * y) from by ring]

/-- **The Prime Filtering composition** (downward induction): if every level
below `m` holds at most two elements, a product of stock multipliers puts
every element of level `≥ t` in the safe arc.  Elements are `(level, slope)`
pairs with slopes prime to `5`. -/
theorem pfl_compose_aux (m : ℕ) (L : List (ℕ × ℕ))
    (hslope : ∀ p ∈ L, ¬ 5 ∣ p.2) (hlev : ∀ p ∈ L, p.1 ≤ m)
    (hcount : ∀ j, j < m → (L.filter (fun p => p.1 = j)).length ≤ 2) :
    ∀ d t, m - t ≤ d →
      ∃ μ, ¬ 5 ∣ μ ∧ ∀ p ∈ L, t ≤ p.1 → SafeAt m μ p.1 p.2 := by
  intro d
  induction d with
  | zero =>
    intro t hd
    refine ⟨1, by norm_num, fun p hp hpt => ?_⟩
    have hpm : p.1 = m := by have := hlev p hp; omega
    rw [hpm] at *
    exact toplevel_safe m 1 p.2 (by norm_num) (hslope p hp)
  | succ d ih =>
    intro t hd
    by_cases htm : m ≤ t
    · refine ⟨1, by norm_num, fun p hp hpt => ?_⟩
      have hpm : p.1 = m := by have := hlev p hp; omega
      rw [hpm] at *
      exact toplevel_safe m 1 p.2 (by norm_num) (hslope p hp)
    · push_neg at htm
      obtain ⟨μ', hμ', hsafe'⟩ := ih (t + 1) (by omega)
      -- the elements at level t (at most two)
      have hcnt := hcount t htm
      have hmem_filter : ∀ p ∈ L, p.1 = t → p ∈ L.filter (fun p => p.1 = t) := by
        intro p hp hpt
        exact List.mem_filter.mpr ⟨hp, by simp [hpt]⟩
      have hslope_filter : ∀ p ∈ L.filter (fun p => p.1 = t), ¬ 5 ∣ p.2 :=
        fun p hp => hslope p (List.mem_filter.mp hp).1
      -- pick slopes y₁ y₂ (duplicating when fewer than two)
      obtain ⟨y₁, y₂, hy₁, hy₂, hcover⟩ :
          ∃ y₁ y₂, ¬ 5 ∣ y₁ ∧ ¬ 5 ∣ y₂ ∧
            ∀ p ∈ L, p.1 = t → p.2 = y₁ ∨ p.2 = y₂ := by
        rcases hfilt : L.filter (fun p => p.1 = t) with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, rest⟩⟩⟩
        · exact ⟨1, 1, by norm_num, by norm_num, fun p hp hpt => by
            have := hmem_filter p hp hpt
            rw [hfilt] at this
            simp at this⟩
        · refine ⟨p₁.2, p₁.2, ?_, ?_, fun p hp hpt => ?_⟩
          · exact hslope_filter p₁ (by rw [hfilt]; simp)
          · exact hslope_filter p₁ (by rw [hfilt]; simp)
          · have := hmem_filter p hp hpt
            rw [hfilt] at this
            simp at this
            subst this
            exact Or.inl rfl
        · refine ⟨p₁.2, p₂.2, ?_, ?_, fun p hp hpt => ?_⟩
          · exact hslope_filter p₁ (by rw [hfilt]; simp)
          · exact hslope_filter p₂ (by rw [hfilt]; simp)
          · have := hmem_filter p hp hpt
            rw [hfilt] at this
            simp at this
            rcases this with h | h <;> [exact Or.inl (by rw [h]); exact Or.inr (by rw [h])]
        · exfalso
          rw [hfilt] at hcnt
          simp at hcnt
      -- the level-t multiplier from the pigeonhole
      have hy₁' : ¬ 5 ∣ (μ' * y₁) := five_not_dvd_mul hμ' hy₁
      have hy₂' : ¬ 5 ∣ (μ' * y₂) := five_not_dvd_mul hμ' hy₂
      obtain ⟨k, hk5, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ :=
        pfl_level_two m t (le_of_lt htm) (μ' * y₁) (μ' * y₂) hy₁' hy₂'
      set lam := 1 + k * 5 ^ (m - t) with hlam
      have hlam5 : ¬ 5 ∣ lam := lambda_not_dvd m t k htm
      refine ⟨lam * μ', ?_, fun p hp hpt => ?_⟩
      · exact five_not_dvd_mul hlam5 hμ'
      rcases eq_or_lt_of_le hpt with hpt' | hpt'
      · -- level t: the pigeonhole digit
        have hP : 0 < 5 ^ m := pow_pos (by norm_num) m
        have hcases := hcover p hp hpt'.symm
        have hre : (lam * μ') * (5 ^ p.1 * p.2) = lam * (5 ^ t * (μ' * p.2)) := by
          rw [← hpt']
          ring
        unfold SafeAt
        rw [hre]
        have hdig : ∀ z, ¬ 5 ∣ (μ' * z) →
            ((lam * (5 ^ t * (μ' * z))) % (5 * 5 ^ m)) / 5 ^ m ≠ 0 →
            ((lam * (5 ^ t * (μ' * z))) % (5 * 5 ^ m)) / 5 ^ m ≠ 4 →
            5 ^ m ≤ cdist (5 * 5 ^ m) (lam * (5 ^ t * (μ' * z))) := by
          intro z _ hz0 hz4
          have hlt := digit_lt_five (5 ^ m) hP (lam * (5 ^ t * (μ' * z)))
          refine safe_of_digit (5 ^ m) hP _ ?_
          set D := ((lam * (5 ^ t * (μ' * z))) % (5 * 5 ^ m)) / 5 ^ m with hD
          interval_cases D
          · exact absurd rfl hz0
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd rfl hz4
        rcases hcases with hcase | hcase <;> rw [hcase]
        · exact hdig y₁ hy₁' h1a h1b
        · exact hdig y₂ hy₂' h2a h2b
      · -- level > t: frozen
        have hre : (lam * μ') * (5 ^ p.1 * p.2) = lam * (μ' * (5 ^ p.1 * p.2)) := by ring
        unfold SafeAt
        rw [hre, hlam, cdist_frozen m t p.1 k p.2 μ' hpt' (hlev p hp)]
        exact hsafe' p hp hpt'

/-- **The Prime Filtering Lemma** (`p = 5`, Corollary-3 form): a family whose
levels below `m` each hold at most two elements admits a multiplier prime to
`5` putting every element in the safe arc. -/
theorem pfl_compose (m : ℕ) (L : List (ℕ × ℕ))
    (hslope : ∀ p ∈ L, ¬ 5 ∣ p.2) (hlev : ∀ p ∈ L, p.1 ≤ m)
    (hcount : ∀ j, j < m → (L.filter (fun p => p.1 = j)).length ≤ 2) :
    ∃ μ, ¬ 5 ∣ μ ∧ ∀ p ∈ L, SafeAt m μ p.1 p.2 := by
  obtain ⟨μ, hμ, h⟩ := pfl_compose_aux m L hslope hlev hcount m 0 (by omega)
  exact ⟨μ, hμ, fun p hp => h p hp (Nat.zero_le _)⟩

/-- **The chain law**: the leading digit of a sum is the sum of the digits
plus a carry of at most one. -/
theorem digit_add (P : ℕ) (hP : 0 < P) (a b : ℕ) :
    ∃ c ≤ 1, ((a + b) % (5 * P)) / P
      = (((a % (5 * P)) / P + (b % (5 * P)) / P) + c) % 5 := by
  set ra := a % (5 * P) with hra
  set rb := b % (5 * P) with hrb
  have hstep : (a + b) % (5 * P) = (ra + rb) % (5 * P) := by
    have h1 := Nat.div_add_mod a (5 * P)
    have h2 := Nat.div_add_mod b (5 * P)
    rw [← hra] at h1
    rw [← hrb] at h2
    have hx : a + b = ((ra + rb) + 5 * P * (a / (5 * P))) + 5 * P * (b / (5 * P)) := by
      omega
    rw [hx, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
  set qa := ra / P with hqa
  set ba := ra % P with hba
  set qb := rb / P with hqb
  set bb := rb % P with hbb
  have hda : ra = qa * P + ba := by
    rw [hqa, hba, mul_comm]
    exact (Nat.div_add_mod ra P).symm
  have hdb : rb = qb * P + bb := by
    rw [hqb, hbb, mul_comm]
    exact (Nat.div_add_mod rb P).symm
  have hbalt : ba < P := Nat.mod_lt _ hP
  have hbblt : bb < P := Nat.mod_lt _ hP
  have hsum : ra + rb = (ba + bb) + (qa + qb) * P := by
    rw [hda, hdb]
    ring
  have hbb5 : ba + bb < 5 * P := by omega
  have hd := digit_add_mul_P P hP (ba + bb) (qa + qb)
  have hcarry : ((ba + bb) % (5 * P)) / P = (ba + bb) / P := by
    rw [Nat.mod_eq_of_lt hbb5]
  have hcle : (ba + bb) / P ≤ 1 := by
    have h2 : (ba + bb) / P < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
    omega
  refine ⟨(ba + bb) / P, hcle, ?_⟩
  rw [hstep, hsum, hd, hcarry]
  omega

/-- The digit of the chase after top multiplier `j+1` and level-`0` shift `k`,
as a function of the base digit `q`, the two carries, and the class `r`. -/
def chaseVal (q : Fin 5) (c2 c3 : Bool) (r : Fin 5) (j : Fin 3) (k : Fin 5) : ℕ :=
  (match j with
    | 0 => q.val
    | 1 => 2 * q.val + (if c2 then 1 else 0)
    | 2 => 3 * q.val + (if c2 then 1 else 0) + (if c3 then 1 else 0))
  + k.val * ((j.val + 1) * r.val)

/-- The bad bit of profile `(q,c₂,c₃,r)` at slot `(j,k)`: the chased digit
lands in the unsafe set `{0,4}`. -/
def maskBit (q : Fin 5) (c2 c3 : Bool) (r : Fin 5) (j : Fin 3) (k : Fin 5) : Bool :=
  decide (chaseVal q c2 c3 r j k % 5 = 0) || decide (chaseVal q c2 c3 r j k % 5 = 4)

/-- The 15-bit bad-set mask of a profile: bit `5j + k` records slot `(j,k)`. -/
def maskOf (q : Fin 5) (c2 c3 : Bool) (r : Fin 5) : ℕ :=
    (if maskBit q c2 c3 r 0 0 then 1 else 0)
  + (if maskBit q c2 c3 r 0 1 then 2 else 0)
  + (if maskBit q c2 c3 r 0 2 then 4 else 0)
  + (if maskBit q c2 c3 r 0 3 then 8 else 0)
  + (if maskBit q c2 c3 r 0 4 then 16 else 0)
  + (if maskBit q c2 c3 r 1 0 then 32 else 0)
  + (if maskBit q c2 c3 r 1 1 then 64 else 0)
  + (if maskBit q c2 c3 r 1 2 then 128 else 0)
  + (if maskBit q c2 c3 r 1 3 then 256 else 0)
  + (if maskBit q c2 c3 r 1 4 then 512 else 0)
  + (if maskBit q c2 c3 r 2 0 then 1024 else 0)
  + (if maskBit q c2 c3 r 2 1 then 2048 else 0)
  + (if maskBit q c2 c3 r 2 2 then 4096 else 0)
  + (if maskBit q c2 c3 r 2 3 then 8192 else 0)
  + (if maskBit q c2 c3 r 2 4 then 16384 else 0)

/-- The 40 bad-set masks realized by the 80 live profiles (`r ≠ 0`), sorted.
Computed externally; certified below by `mask_complete`. -/
def chaseMasks : List ℕ :=
  [3274, 3476, 3625, 3860, 5411, 5464, 5720, 5766, 6258, 6548, 6697, 6921,
   9393, 9560, 9798, 9862, 10417, 10540, 10822, 10897, 12402, 12485, 12850,
   13065, 17509, 17610, 17802, 18196, 18604, 18732, 18755, 19089, 20652,
   20771, 20803, 21080, 24677, 24773, 24970, 25138]

set_option maxHeartbeats 1000000 in
/-- Every live profile's mask is on the list: the dedup is complete. -/
theorem mask_complete : ∀ (q : Fin 5) (c2 c3 : Bool) (r : Fin 5), r ≠ 0 →
    maskOf q c2 c3 r ∈ chaseMasks := by
  decide

set_option maxHeartbeats 2000000 in
/-- Reading a bit of the packed mask recovers the bad-bit predicate. -/
theorem mask_testBit : ∀ (q : Fin 5) (c2 c3 : Bool) (r : Fin 5) (j : Fin 3) (k : Fin 5),
    Nat.testBit (maskOf q c2 c3 r) (5 * j.val + k.val) = maskBit q c2 c3 r j k := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **The chase over masks**: any three realized masks (taken sorted; the wrapper
below symmetrizes) leave a common clear slot `(j,k)`.  `11{,}480` sorted triples
of cheap bit tests — the OOM-safe replacement for a `512{,}000`-profile monolith. -/
theorem mask_triple : ∀ m₁ ∈ chaseMasks, ∀ m₂ ∈ chaseMasks, ∀ m₃ ∈ chaseMasks,
    m₁ ≤ m₂ → m₂ ≤ m₃ →
    ∃ (j : Fin 3) (k : Fin 5),
      Nat.testBit m₁ (5 * j.val + k.val) = false ∧
      Nat.testBit m₂ (5 * j.val + k.val) = false ∧
      Nat.testBit m₃ (5 * j.val + k.val) = false := by
  decide

/-- Symmetrization of `mask_triple` over the six orderings. -/
theorem mask_triple' (m₁ m₂ m₃ : ℕ) (h₁ : m₁ ∈ chaseMasks) (h₂ : m₂ ∈ chaseMasks)
    (h₃ : m₃ ∈ chaseMasks) :
    ∃ (j : Fin 3) (k : Fin 5),
      Nat.testBit m₁ (5 * j.val + k.val) = false ∧
      Nat.testBit m₂ (5 * j.val + k.val) = false ∧
      Nat.testBit m₃ (5 * j.val + k.val) = false := by
  rcases Nat.le_total m₁ m₂ with h12 | h12
  · rcases Nat.le_total m₂ m₃ with h23 | h23
    · exact mask_triple m₁ h₁ m₂ h₂ m₃ h₃ h12 h23
    · rcases Nat.le_total m₁ m₃ with h13 | h13
      · obtain ⟨j, k, b1, b3, b2⟩ := mask_triple m₁ h₁ m₃ h₃ m₂ h₂ h13 h23
        exact ⟨j, k, b1, b2, b3⟩
      · obtain ⟨j, k, b3, b1, b2⟩ := mask_triple m₃ h₃ m₁ h₁ m₂ h₂ h13 h12
        exact ⟨j, k, b1, b2, b3⟩
  · rcases Nat.le_total m₁ m₃ with h13 | h13
    · obtain ⟨j, k, b2, b1, b3⟩ := mask_triple m₂ h₂ m₁ h₁ m₃ h₃ h12 h13
      exact ⟨j, k, b1, b2, b3⟩
    · rcases Nat.le_total m₂ m₃ with h23 | h23
      · obtain ⟨j, k, b2, b3, b1⟩ := mask_triple m₂ h₂ m₃ h₃ m₁ h₁ h23 h13
        exact ⟨j, k, b1, b2, b3⟩
      · obtain ⟨j, k, b3, b2, b1⟩ := mask_triple m₃ h₃ m₂ h₂ m₁ h₁ h23 h12
        exact ⟨j, k, b1, b2, b3⟩

/-- A clear bad-bit means the chased digit avoids `{0,4}`. -/
theorem maskBit_false {q : Fin 5} {c2 c3 : Bool} {r : Fin 5} {j : Fin 3} {k : Fin 5}
    (h : maskBit q c2 c3 r j k = false) :
    chaseVal q c2 c3 r j k % 5 ≠ 0 ∧ chaseVal q c2 c3 r j k % 5 ≠ 4 := by
  unfold maskBit at h
  constructor
  · intro h0
    rw [h0] at h
    exact absurd h (by decide)
  · intro h4
    rw [h4] at h
    exact absurd h (by decide)

/-- **The 3+1 chase, decided**: for every triple of digit chains (adversarial
carries) and every triple of nonzero classes — no sign normalization — some
top multiplier `j+1 ∈ {1,2,3}` and level-`0` shift `k` put all three digits
outside `{0,4}`.  Proved by the mask dedup: the `80` live profiles realize
exactly the `40` masks of `chaseMasks` (`mask_complete`), and every sorted
mask triple leaves a clear slot (`mask_triple`). -/
theorem chase_core : ∀ (q₁ q₂ q₃ r₁ r₂ r₃ : Fin 5) (a₂ a₃ b₂ b₃ d₂ d₃ : Bool),
    r₁ ≠ 0 → r₂ ≠ 0 → r₃ ≠ 0 →
    ∃ (j : Fin 3) (k : Fin 5),
      chaseVal q₁ a₂ a₃ r₁ j k % 5 ≠ 0 ∧ chaseVal q₁ a₂ a₃ r₁ j k % 5 ≠ 4 ∧
      chaseVal q₂ b₂ b₃ r₂ j k % 5 ≠ 0 ∧ chaseVal q₂ b₂ b₃ r₂ j k % 5 ≠ 4 ∧
      chaseVal q₃ d₂ d₃ r₃ j k % 5 ≠ 0 ∧ chaseVal q₃ d₂ d₃ r₃ j k % 5 ≠ 4 := by
  intro q₁ q₂ q₃ r₁ r₂ r₃ a₂ a₃ b₂ b₃ d₂ d₃ h₁ h₂ h₃
  obtain ⟨j, k, hb₁, hb₂, hb₃⟩ :=
    mask_triple' (maskOf q₁ a₂ a₃ r₁) (maskOf q₂ b₂ b₃ r₂) (maskOf q₃ d₂ d₃ r₃)
      (mask_complete q₁ a₂ a₃ r₁ h₁) (mask_complete q₂ b₂ b₃ r₂ h₂)
      (mask_complete q₃ d₂ d₃ r₃ h₃)
  rw [mask_testBit q₁ a₂ a₃ r₁ j k] at hb₁
  rw [mask_testBit q₂ b₂ b₃ r₂ j k] at hb₂
  rw [mask_testBit q₃ d₂ d₃ r₃ j k] at hb₃
  obtain ⟨e10, e14⟩ := maskBit_false hb₁
  obtain ⟨e20, e24⟩ := maskBit_false hb₂
  obtain ⟨e30, e34⟩ := maskBit_false hb₃
  exact ⟨j, k, e10, e14, e20, e24, e30, e34⟩

end LRSpectrumFull

