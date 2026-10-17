/-
Room FCU, compression round (2026-09-24).

Every room certificate re-derived from `RoomFCUModerator.ML_ge_of_escape`:
if every speed has an integer representative `r_i ≡ v_i a (mod q)` with
`r_i/q + v_i ε ∈ [δ, 1 - δ]`, then `δ ≤ ML v`.

* `ML_ge_of_residues`  : the case `ε = 0`, `δ = A/B`, stated on exact integer residues.
* `ML_ge_of_goodAt`    : the bridge from the brief's integer witness test (`RoomFCUTao.goodAt`).
* `window_via_escape`, `window_iff_via_escape` : Tao's window lemma is the per-family check that
  feeds `ε = 0`; the ML conclusion is one line.
* `famF_via_escape`    : Theorem F in ML form, `ML ≥ (m+1)/(mj+m+1)` (the Ramanujan module only
  states the residue inequalities).
* `lemmaP_quant`, `lemmaP_via_escape` : Lemma P with `ε = -2/(q(2W-1))`; the escape form gives
  the quantitative bound `ML ≥ 2W/(q(2W-1))`, strictly above `1/q`.
* `lonely_iff_escape`  : the collapsed statement.  `δ ≤ ML v` iff some base point and some
  escape certify it.  The proof takes `q = 1`, so the collapsed statement has no content unless
  `q` (and `ε`) are constrained: its whole content is the bound on the level.
* `rational_point_of_lt` : for `δ < ML v` the escape can be taken with `ε = 0` and canonical
  residues (a rational lonely time), still with no bound on `q`.

`RoomFCUGoddyn.fast_runner_floor` is NOT re-derived: its base point is a real maximiser of the
sub-family and its per-speed condition comes from the induction hypothesis plus Lipschitz, not
from a residue check; through `lonely_iff_escape` it is only a degenerate (`q = 1`) instance.
-/
import Mathlib
import LRSpectrumFull.RoomFCU_moderator
import LRSpectrumFull.RoomFCU_lemmaP
import LRSpectrumFull.RoomFCU_tao
import LRSpectrumFull.RoomFCU_ramanujan
import LRSpectrumFull.RoomFCU_goddyn

namespace LRSpectrumFull.RoomFCUCompress

open LRSpectrumFull
open LRSpectrumFull.RoomFCUModerator (ML_ge_of_escape)

/-! ### Zero escape on integer residues -/

theorem ML_ge_of_residues {k : ℕ} (v : Fin (k + 1) → ℤ) (q a A B : ℤ) (hq : 0 < q)
    (hA : 0 < A) (hB : 0 < B)
    (h : ∀ i, A * q ≤ B * (v i * a % q) ∧ A * q ≤ B * (q - v i * a % q)) :
    (A : ℝ) / B ≤ ML v := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  refine ML_ge_of_escape v q a hq 0 _ (div_pos (by exact_mod_cast hA) hBR) (fun i => ?_)
  obtain ⟨h1, h2⟩ := h i
  set r := v i * a % q
  have h1' : (A : ℝ) * q ≤ (r : ℝ) * B := by
    have : A * q ≤ r * B := by rw [mul_comm r]; exact h1
    exact_mod_cast this
  have h2' : (A : ℝ) * q ≤ ((q : ℝ) - r) * B := by
    have : A * q ≤ (q - r) * B := by rw [mul_comm (q - r)]; exact h2
    exact_mod_cast this
  have e : (1 : ℝ) - (r : ℝ) / q = ((q : ℝ) - r) / q := by field_simp
  refine ⟨v i * a / q, r, (Int.ediv_add_emod _ _).symm, ?_, ?_⟩
  · rw [mul_zero, add_zero, div_le_div_iff₀ hBR hqR]; exact h1'
  · rw [mul_zero, add_zero]
    have : (A : ℝ) / B ≤ ((q : ℝ) - r) / q := by rw [div_le_div_iff₀ hBR hqR]; exact h2'
    linarith

/-- Bridge from the brief's integer witness test at `a/q` (target `1/(m+1)`). -/
theorem ML_ge_of_goodAt {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (m q a : ℕ)
    (hq : 0 < q) (h : ∀ i, RoomFCUTao.goodAt m q a (v i).toNat) :
    1 / ((m : ℝ) + 1) ≤ ML v := by
  have H := ML_ge_of_residues v q a 1 ((m : ℤ) + 1) (by exact_mod_cast hq) one_pos (by positivity)
    (fun i => by
      have hx : ((v i).toNat : ℤ) = v i := Int.toNat_of_nonneg (hv i).le
      have hlt : (v i).toNat * a % q < q := Nat.mod_lt _ hq
      have hg := h i
      unfold RoomFCUTao.goodAt at hg
      have g1 : q ≤ (m + 1) * ((v i).toNat * a % q) :=
        hg.trans (Nat.mul_le_mul_left _ (min_le_left _ _))
      have g2 : q ≤ (m + 1) * (q - (v i).toNat * a % q) :=
        hg.trans (Nat.mul_le_mul_left _ (min_le_right _ _))
      have hr : (((v i).toNat * a % q : ℕ) : ℤ) = v i * (a : ℤ) % (q : ℤ) := by
        push_cast; rw [hx]
      have g1' : ((q : ℕ) : ℤ) ≤ ((m : ℤ) + 1) * (((v i).toNat * a % q : ℕ) : ℤ) := by
        exact_mod_cast g1
      have g2' : ((q : ℕ) : ℤ) ≤ ((m : ℤ) + 1) * (((q - (v i).toNat * a % q : ℕ)) : ℤ) := by
        exact_mod_cast g2
      rw [Nat.cast_sub hlt.le, hr] at g2'
      rw [hr] at g1'
      exact ⟨by linarith, by linarith⟩)
  push_cast at H
  exact H

/-! ### Tao's window lemma -/

theorem window_via_escape {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (m q : ℕ)
    (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1)) (hdiv : ∀ i, ¬ q ∣ (v i).toNat)
    (hcount : 2 * (Finset.univ.filter (fun i => Nat.Coprime q (v i).toNat)).card
      < Nat.totient q) :
    1 / ((m : ℝ) + 1) ≤ ML v := by
  obtain ⟨a, -, -, ha⟩ :=
    RoomFCUTao.window_witness_of_count m q (fun i => (v i).toNat) h1 h2 hdiv hcount
  exact ML_ge_of_goodAt v hv m q a (by omega) ha

theorem window_iff_via_escape {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (m q a : ℕ)
    (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1)) (hdiv : ∀ i, ¬ q ∣ (v i).toNat)
    (ha : Nat.Coprime q a)
    (hmiss : ∀ i, (v i).toNat * a % q ≠ 1 ∧ (v i).toNat * a % q ≠ q - 1) :
    1 / ((m : ℝ) + 1) ≤ ML v :=
  ML_ge_of_goodAt v hv m q a (by omega)
    ((RoomFCUTao.window_witness_iff m q a (fun i => (v i).toNat) h1 h2 hdiv ha).mpr hmiss)

/-! ### Ramanujan's Theorem F in ML form -/

theorem famF_via_escape (m j : ℕ) (hj : m + 1 < 2 * j) (hjm : j ≤ m)
    (hcop : Nat.Coprime j (m + 1)) {k : ℕ} (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, ∃ x ∈ RoomFCURamanujan.famF m j, v i = (x : ℤ)) :
    ((m : ℝ) + 1) / ((m : ℝ) * j + m + 1) ≤ ML v := by
  obtain ⟨s, hs⟩ := RoomFCURamanujan.famF_lonely m j hj hjm hcop
  have hj0 : (0 : ℤ) < j := by exact_mod_cast (show 0 < j by omega)
  have hD : (0 : ℤ) < (m : ℤ) * j + m + 1 := by positivity
  have H := ML_ge_of_residues v ((j : ℤ) * ((m : ℤ) * j + m + 1)) ((s : ℤ) * ((m : ℤ) * j + m + 1) + 1)
    ((m : ℤ) + 1) ((m : ℤ) * j + m + 1) (by positivity) (by positivity) hD (fun i => by
      obtain ⟨x, hx, hvx⟩ := hv i
      obtain ⟨h1, h2⟩ := hs x hx
      have hr : ((x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) : ℕ) : ℤ)
          = v i * ((s : ℤ) * ((m : ℤ) * j + m + 1) + 1) % ((j : ℤ) * ((m : ℤ) * j + m + 1)) := by
        rw [hvx]; push_cast; rfl
      have h1' : ((j : ℤ) * ((m : ℤ) + 1)) ≤
          ((x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) : ℕ) : ℤ) := by
        exact_mod_cast h1
      have h2' : ((x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) : ℕ) : ℤ)
          + (j : ℤ) * ((m : ℤ) + 1) ≤ (j : ℤ) * ((m : ℤ) * j + m + 1) := by
        exact_mod_cast h2
      rw [hr] at h1' h2'
      constructor <;> nlinarith)
  push_cast at H
  exact H

/-! ### Lemma P as a first-order escape -/

/-- Quantitative Lemma P: under the hypotheses of `RoomFCUErdos.LemmaP_statement`,
`ML v ≥ 2W / (q (2W - 1))` with `W = v i0`, `q = k + 2`.  Witness: base point `a/q`
(`a = u⁻¹ mod q`), escape `ε = -2/(q(2W-1))`. -/
theorem lemmaP_quant (k : ℕ) (hk : 2 ≤ k) (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (i0 : Fin (k + 1)) (hdiv : ((k + 2 : ℕ) : ℤ) ∣ v i0)
    (hoth : ∀ i, i ≠ i0 → ¬ (((k + 2 : ℕ) : ℤ) ∣ v i) ∧ v i < v i0)
    (hu : ∃ u : ℕ, Nat.Coprime u (k + 2) ∧ ∀ i, ¬ (v i ≡ (u : ℤ) [ZMOD ((k + 2 : ℕ) : ℤ)])) :
    2 * (v i0 : ℝ) / ((((k + 2 : ℕ) : ℤ) : ℝ) * (2 * v i0 - 1)) ≤ ML v := by
  obtain ⟨u, hcop, hmiss⟩ := hu
  obtain ⟨a, hua⟩ := Int.mod_coprime hcop
  set q : ℤ := ((k + 2 : ℕ) : ℤ) with hqdef
  set W : ℤ := v i0 with hW
  have hq4 : (4 : ℤ) ≤ q := by rw [hqdef]; push_cast; omega
  have hW1 : (1 : ℤ) ≤ W := hv i0
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
  have hY : (0 : ℝ) < 2 * (W : ℝ) - 1 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    linarith
  have hQ : (0 : ℝ) < q * (2 * (W : ℝ) - 1) := mul_pos hqR hY
  -- the real part, cleared of denominators
  have key : ∀ (x r : ℤ), 2 * W ≤ r * (2 * W - 1) - 2 * x →
      r * (2 * W - 1) - 2 * x ≤ q * (2 * W - 1) - 2 * W →
      2 * (W : ℝ) / (q * (2 * W - 1)) ≤ (r : ℝ) / q + (x : ℝ) * (-2 / (q * (2 * W - 1))) ∧
      (r : ℝ) / q + (x : ℝ) * (-2 / (q * (2 * W - 1))) ≤ 1 - 2 * (W : ℝ) / (q * (2 * W - 1)) := by
    intro x r h1 h2
    have e1 : (r : ℝ) / q + (x : ℝ) * (-2 / (q * (2 * W - 1)))
        = ((r : ℝ) * (2 * W - 1) - 2 * x) / (q * (2 * W - 1)) := by field_simp; ring
    have e2 : (1 : ℝ) - 2 * (W : ℝ) / (q * (2 * W - 1))
        = ((q : ℝ) * (2 * W - 1) - 2 * W) / (q * (2 * W - 1)) := by field_simp
    rw [e1, e2]
    exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast h1) hQ.le,
      div_le_div_of_nonneg_right (by exact_mod_cast h2) hQ.le⟩
  refine ML_ge_of_escape v q a (by omega) (-2 / (q * (2 * W - 1))) (2 * (W : ℝ) / (q * (2 * W - 1)))
    (div_pos (by linarith) hQ) (fun i => ?_)
  by_cases hi : i = i0
  · -- the multiple of `q` sits at the origin and escapes backwards to `1 - δ`
    subst hi
    obtain ⟨c, hc⟩ := hdiv
    refine ⟨c * a - 1, q, by rw [← hW, hc]; ring, key W q ?_ le_rfl⟩
    nlinarith
  · -- a non-multiple has residue `r ∈ [2, q-1]` and moves by less than `1/q`
    obtain ⟨hnd, hlt⟩ := hoth i hi
    set r := v i * a % q with hr
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hrq : r < q := Int.emod_lt_of_pos _ (by omega)
    have hvr : v i ≡ r * u [ZMOD q] :=
      calc v i = v i * 1 := (mul_one _).symm
        _ ≡ v i * (u * a) [ZMOD q] := hua.symm.mul_left _
        _ = v i * a * u := by ring
        _ ≡ r * u [ZMOD q] := ((Int.mod_modEq _ _).symm.mul_right _)
    have hrne0 : r ≠ 0 := fun h0 => hnd (Int.modEq_zero_iff_dvd.mp (by rwa [h0, zero_mul] at hvr))
    have hrne1 : r ≠ 1 := fun h1 => hmiss i (by rwa [h1, one_mul] at hvr)
    have hr2 : 2 ≤ r := by omega
    have hvi : 1 ≤ v i := hv i
    refine ⟨v i * a / q, r, (Int.ediv_add_emod _ _).symm, key (v i) r ?_ ?_⟩
    · nlinarith
    · nlinarith

theorem lemmaP_via_escape : RoomFCUErdos.LemmaP_statement := by
  intro k hk v hv i0 hdiv hoth hu
  have H := lemmaP_quant k hk v hv i0 hdiv hoth hu
  have hW : (1 : ℝ) ≤ v i0 := by exact_mod_cast hv i0
  have hq : (((k + 2 : ℕ) : ℤ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hq] at H
  refine lt_of_lt_of_le ?_ H
  rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith

/-! ### The collapsed statement and its scope -/

/-- Collapsed statement: a family is `δ`-lonely iff some base point `a/q` and escape `ε`
certify it.  The forward direction uses `q = 1`, `a = 0`, `ε = t` for a maximiser `t`: the
statement is true for every family and says nothing until `q` and `ε` are constrained. -/
theorem lonely_iff_escape {k : ℕ} (v : Fin (k + 1) → ℤ) (δ : ℝ) (hδ : 0 < δ) :
    δ ≤ ML v ↔ ∃ q a : ℤ, ∃ ε : ℝ, 0 < q ∧ ∀ i, ∃ N r : ℤ, v i * a = q * N + r ∧
      δ ≤ (r : ℝ) / q + (v i : ℝ) * ε ∧ (r : ℝ) / q + (v i : ℝ) * ε ≤ 1 - δ := by
  constructor
  · intro h
    obtain ⟨t, -, ht⟩ := exists_gap_eq_ML v
    refine ⟨1, 0, t, one_pos, fun i => ⟨⌊(v i : ℝ) * t⌋, -⌊(v i : ℝ) * t⌋, by ring, ?_⟩⟩
    have hg : δ ≤ nearestIntDist ((v i : ℝ) * t) := (h.trans ht.symm.le).trans (gap_le v t i)
    unfold nearestIntDist at hg
    have hf : ((-⌊(v i : ℝ) * t⌋ : ℤ) : ℝ) / ((1 : ℤ) : ℝ) + (v i : ℝ) * t
        = Int.fract ((v i : ℝ) * t) := by
      rw [Int.fract]; push_cast; ring
    rw [hf]
    exact ⟨(le_min_iff.mp hg).1, by linarith [(le_min_iff.mp hg).2]⟩
  · rintro ⟨q, a, ε, hq, h⟩
    exact ML_ge_of_escape v q a hq ε δ hδ h

/-- Below `ML v` the escape can be taken with `ε = 0` and the canonical residues: a rational
lonely time `a/q`.  No bound on `q` is asserted; O4 says no affine bound in `m` is known to
suffice for the certificate kinds tested. -/
theorem rational_point_of_lt {k : ℕ} (v : Fin (k + 1) → ℤ) (δ : ℝ) (h : δ < ML v) :
    ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ ∀ i,
      δ ≤ ((v i * a % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) ∧
      ((v i * a % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) ≤ 1 - δ := by
  obtain ⟨t0, -, ht0⟩ := exists_gap_eq_ML v
  have hU : IsOpen {t : ℝ | δ < gap v t} := isOpen_lt continuous_const (gap_continuous v)
  obtain ⟨x, hx⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨t0, by simpa [Set.mem_setOf_eq, ht0] using h⟩
  refine ⟨x.den, x.num, x.pos, fun i => ?_⟩
  have hg : δ ≤ nearestIntDist ((v i : ℝ) * (x : ℝ)) := (le_of_lt hx).trans (gap_le v _ i)
  have hfr : Int.fract ((v i : ℝ) * (x : ℝ))
      = ((v i * x.num % (x.den : ℤ) : ℤ) : ℝ) / (x.den : ℝ) := by
    rw [Rat.cast_def, ← mul_div_assoc]
    have := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := v i * x.num) (n := x.den)
    push_cast at this ⊢
    exact this
  unfold nearestIntDist at hg
  rw [hfr] at hg
  exact ⟨(le_min_iff.mp hg).1, by linarith [(le_min_iff.mp hg).2]⟩

end LRSpectrumFull.RoomFCUCompress
