/-
# De-trust: integer-witness certificate bridge

The finite n=3 classification certificates (`triple_certs`) currently discharge
`2/7 ≤ mgapQ (col v) ![a/b]` by `native_decide` (Lean.ofReduceBool trust axiom).

Here we replace the rational computation by a PURE INTEGER predicate `certOK`, whose
truth on the data is kernel-checkable by `decide` (no compiler trust). The bridge
`certOK_sound` proves, once and for all, that the integer conditions
`2b ≤ 7·((c·a) mod b) ≤ 5b` for every coordinate `c` imply `2/7 ≤ mgapQ (col v) ![a/b]`.

Key fact: for `b > 0`, `Int.fract ((n:ℚ)/b) = ((n mod b : ℤ):ℚ)/b`, so
`nidQ (c·(a/b)) = min(r, b−r)/b` with `r = (c·a) mod b ∈ [0,b)`, and `≥ 2/7 ⟺
2b ≤ 7r ∧ 7r ≤ 5b`. All conditions are integer (no `Rat` kernel reduction). No `sorry`.
-/
import LRSpectrumFull.RationalCert
import LRSpectrumFull.Coherence
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull

/-- For `b > 0`, the fractional part of `n/b` is `(n mod b)/b`. -/
theorem fract_intCast_div (n b : ℤ) (hb : 0 < b) :
    Int.fract ((n : ℚ) / (b : ℚ)) = ((n % b : ℤ) : ℚ) / (b : ℚ) := by
  have hbne : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have htn : ((b.toNat : ℤ)) = b := Int.toNat_of_nonneg hb.le
  have hfloor : ⌊(n : ℚ) / (b : ℚ)⌋ = n / b := by
    have h := Rat.floor_intCast_div_natCast n b.toNat
    have hc : ((b.toNat : ℕ) : ℚ) = (b : ℚ) := by exact_mod_cast htn
    rw [hc, htn] at h
    exact h
  have hmod : ((n % b : ℤ) : ℚ) = (n : ℚ) - (b : ℚ) * ((n / b : ℤ) : ℚ) := by
    have h3 : (n % b : ℤ) = n - b * (n / b) := by
      have := Int.emod_add_mul_ediv n b; omega
    rw [h3]; push_cast; ring
  rw [Int.fract, hfloor, hmod]
  field_simp

/-- **Core bridge.** If a rational `q` equals `num/B` (`B > 0`) and `r = num mod B`
satisfies `2B ≤ 7r ∧ 7r ≤ 5B`, then `2/7 ≤ nidQ q`. -/
theorem nidQ_ge_of_num (q : ℚ) (num B : ℤ) (hB : 0 < B) (hq : q = (num : ℚ) / (B : ℚ))
    (h1 : 2 * B ≤ 7 * (num % B)) (h2 : 7 * (num % B) ≤ 5 * B) :
    (2 : ℚ) / 7 ≤ nidQ q := by
  subst hq
  have hBpos : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  set r : ℤ := num % B with hr
  have hfr : Int.fract ((num : ℚ) / (B : ℚ)) = (r : ℚ) / (B : ℚ) := fract_intCast_div num B hB
  unfold nidQ
  rw [hfr]
  have e1 : (2 : ℚ) / 7 ≤ (r : ℚ) / (B : ℚ) := by
    rw [le_div_iff₀ hBpos]
    have : (2 : ℚ) * (B : ℚ) ≤ 7 * (r : ℚ) := by exact_mod_cast h1
    linarith
  have e2 : (2 : ℚ) / 7 ≤ 1 - (r : ℚ) / (B : ℚ) := by
    have hrw : (1 : ℚ) - (r : ℚ) / (B : ℚ) = ((B : ℚ) - (r : ℚ)) / (B : ℚ) := by field_simp
    rw [hrw, le_div_iff₀ hBpos]
    have : 7 * (r : ℚ) ≤ 5 * (B : ℚ) := by exact_mod_cast h2
    linarith
  exact le_min e1 e2

/-- **Per-coordinate bridge (1 column).** -/
theorem nidQ_ge_of_int (c a b : ℤ) (hb : 0 < b)
    (h1 : 2 * b ≤ 7 * ((c * a) % b)) (h2 : 7 * ((c * a) % b) ≤ 5 * b) :
    (2 : ℚ) / 7 ≤ nidQ ((c : ℚ) * ((a : ℚ) / (b : ℚ))) :=
  nidQ_ge_of_num _ (c * a) b hb (by push_cast; ring) h1 h2

/-- **Per-coordinate bridge (2 columns).** `c0·(a0/b0) + c1·(a1/b1) = num/(b0·b1)` with
`num = c0·a0·b1 + c1·a1·b0`. -/
theorem nidQ_ge_of_int2 (c0 c1 a0 b0 a1 b1 : ℤ) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (h1 : 2 * (b0 * b1) ≤ 7 * ((c0 * a0 * b1 + c1 * a1 * b0) % (b0 * b1)))
    (h2 : 7 * ((c0 * a0 * b1 + c1 * a1 * b0) % (b0 * b1)) ≤ 5 * (b0 * b1)) :
    (2 : ℚ) / 7 ≤ nidQ ((c0 : ℚ) * ((a0 : ℚ) / (b0 : ℚ)) + (c1 : ℚ) * ((a1 : ℚ) / (b1 : ℚ))) := by
  have hb0' : (b0 : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hb1' : (b1 : ℚ) ≠ 0 := by exact_mod_cast hb1.ne'
  refine nidQ_ge_of_num _ (c0 * a0 * b1 + c1 * a1 * b0) (b0 * b1) (mul_pos hb0 hb1) ?_ h1 h2
  push_cast; field_simp

/-- Bool certificate predicate over one triple datum `((p,q,r),(a,b))` — pure integer
arithmetic, kernel-`decide`-able. -/
def certOK (p : (ℤ × ℤ × ℤ) × ℤ × ℤ) : Bool :=
  let t := p.1; let a := p.2.1; let b := p.2.2
  let chk : ℤ → Bool := fun c =>
    decide (2 * b ≤ 7 * ((c * a) % b)) && decide (7 * ((c * a) % b) ≤ 5 * b)
  decide (0 < b) && chk t.1 && chk t.2.1 && chk t.2.2

/-- **Soundness of the integer certificate (self-contained form).** `certOK` on a triple datum
forces the rational gap bound `2/7 ≤ mgapQ (col ![t1,t2,t3]) ![a/b]`. -/
theorem certOK_sound (t1 t2 t3 a b : ℤ) (hp : certOK ((t1, t2, t3), (a, b)) = true) :
    (2 : ℚ) / 7 ≤ mgapQ (col ![t1, t2, t3]) ![(a : ℚ) / (b : ℚ)] := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hb, hc1⟩, hc2⟩, hc3⟩ := hp
  unfold mgapQ
  rw [Finset.le_inf'_iff]
  intro i _
  have hsum : (∑ j, ((col (![t1, t2, t3]) i j : ℚ)) * (![(a : ℚ) / (b : ℚ)] : Fin 1 → ℚ) j)
      = ((![t1, t2, t3] i : ℚ)) * ((a : ℚ) / (b : ℚ)) := by
    simp [col, Fin.sum_univ_one]
  rw [hsum]
  fin_cases i
  · simpa using nidQ_ge_of_int t1 a b hb hc1.1 hc1.2
  · simpa using nidQ_ge_of_int t2 a b hb hc2.1 hc2.2
  · simpa using nidQ_ge_of_int t3 a b hb hc3.1 hc3.2

/-- 2-column Bool certificate over a `Fin 4 × Fin 2` matrix with witness `(a0/b0, a1/b1)`. -/
def certOK2 (M : Fin 4 → Fin 2 → ℤ) (a0 b0 a1 b1 : ℤ) : Bool :=
  let B := b0 * b1
  let chk : ℤ → ℤ → Bool := fun c0 c1 =>
    let num := c0 * a0 * b1 + c1 * a1 * b0
    decide (2 * B ≤ 7 * (num % B)) && decide (7 * (num % B) ≤ 5 * B)
  decide (0 < b0) && decide (0 < b1) &&
    chk (M 0 0) (M 0 1) && chk (M 1 0) (M 1 1) && chk (M 2 0) (M 2 1) && chk (M 3 0) (M 3 1)

/-- **Soundness of the 2-column certificate.** `certOK2` forces the rational gap bound. -/
theorem certOK2_sound (M : Fin 4 → Fin 2 → ℤ) (a0 b0 a1 b1 : ℤ)
    (hp : certOK2 M a0 b0 a1 b1 = true) :
    (2 : ℚ) / 7 ≤ mgapQ M ![(a0 : ℚ) / (b0 : ℚ), (a1 : ℚ) / (b1 : ℚ)] := by
  simp only [certOK2, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨hb0, hb1⟩, h0⟩, h1⟩, h2⟩, h3⟩ := hp
  unfold mgapQ
  rw [Finset.le_inf'_iff]
  intro i _
  have hsum : (∑ j, ((M i j : ℚ)) *
      (![(a0 : ℚ) / (b0 : ℚ), (a1 : ℚ) / (b1 : ℚ)] : Fin 2 → ℚ) j)
      = (M i 0 : ℚ) * ((a0 : ℚ) / (b0 : ℚ)) + (M i 1 : ℚ) * ((a1 : ℚ) / (b1 : ℚ)) := by
    simp [Fin.sum_univ_two]
  rw [hsum]
  fin_cases i
  · simpa using nidQ_ge_of_int2 (M 0 0) (M 0 1) a0 b0 a1 b1 hb0 hb1 h0.1 h0.2
  · simpa using nidQ_ge_of_int2 (M 1 0) (M 1 1) a0 b0 a1 b1 hb0 hb1 h1.1 h1.2
  · simpa using nidQ_ge_of_int2 (M 2 0) (M 2 1) a0 b0 a1 b1 hb0 hb1 h2.1 h2.2
  · simpa using nidQ_ge_of_int2 (M 3 0) (M 3 1) a0 b0 a1 b1 hb0 hb1 h3.1 h3.2

end LRSpectrumFull
