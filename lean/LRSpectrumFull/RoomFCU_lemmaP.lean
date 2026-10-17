/-
Room FCU: Lemma P (one-sided perturbation of the time `a/q`), `q = k+2`.

If exactly one speed `W = v i0` is divisible by `q`, it is the strictly largest speed, and
some unit `u` mod `q` is the residue of no speed, then `1/q < ML v`.

Proof.  Let `a` be an inverse of `u` mod `q`, `D = 2W - 1`, and
`t = a/q - 2/(q D)`.  Write `v_i a = q N_i + r_i`, `0 <= r_i < q`, and `d_i = 2 v_i / D`.
Then `v_i t = N_i + (r_i - d_i)/q`.
* `i = i0`: `r = 0`, `d = 2W/(2W-1)` lies in `(1, q-1)`, so
  `v_i t = (N - 1) + (q - d)/q` with `1 < q - d < q - 1`.
* `i != i0`: `r != 0` (else `q | v_i`) and `r != 1` (else `v_i = u` mod `q`), so
  `2 <= r <= q - 1`; `0 < d < 1` since `v_i <= W - 1`; hence `1 < r - d < q - 1`.
In both cases `1/q < ||v_i t||`.  This replaces the paper's constant
`c = min 2 ((1 + W/V)/2)` by `c = 2W/(2W-1)`, which needs no second-largest speed.
-/
import Mathlib
import LRSpectrumFull.RoomFCU_erdos

namespace LRSpectrumFull.RoomFCULemmaP

open LRSpectrumFull

/-- If `y = M + x/q` with `1 < x < q - 1`, then `1/q < ||y||`. -/
theorem one_div_lt_nid (q : ℝ) (hq : 0 < q) (M : ℤ) (x y : ℝ)
    (hy : y = (M : ℝ) + x / q) (h1 : 1 < x) (h2 : x < q - 1) :
    1 / q < nearestIntDist y := by
  have hxq0 : 0 ≤ x / q := div_nonneg (by linarith) hq.le
  have hxq1 : x / q < 1 := (div_lt_one hq).mpr (by linarith)
  have hf : Int.fract (x / q) = x / q := Int.fract_eq_self.mpr ⟨hxq0, hxq1⟩
  rw [hy, add_comm, nearestIntDist_add_int]
  unfold nearestIntDist
  rw [hf, lt_min_iff]
  constructor
  · exact div_lt_div_of_pos_right h1 hq
  · rw [show (1 : ℝ) - x / q = (q - x) / q by field_simp]
    exact div_lt_div_of_pos_right (by linarith) hq

theorem lemmaP : RoomFCUErdos.LemmaP_statement := by
  intro k hk v hv i0 hdiv hoth hu
  obtain ⟨u, hcop, hmiss⟩ := hu
  set q : ℤ := ((k + 2 : ℕ) : ℤ) with hqdef
  have hq4 : (4 : ℤ) ≤ q := by rw [hqdef]; push_cast; omega
  -- modular inverse of `u`
  set a : ℤ := Nat.gcdA u (k + 2) with ha
  have hbez := Nat.gcd_eq_gcd_ab u (k + 2)
  rw [Nat.Coprime.gcd_eq_one hcop] at hbez
  have hua : (u : ℤ) * a ≡ 1 [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨Nat.gcdB u (k + 2), by rw [hqdef]; push_cast at hbez ⊢; linarith⟩
  set W : ℤ := v i0 with hW
  have hW1 : (1 : ℤ) ≤ W := hv i0
  set t : ℝ := (a : ℝ) / q - 2 / ((q : ℝ) * (2 * W - 1)) with ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
  have hq4R : (4 : ℝ) ≤ q := by exact_mod_cast hq4
  have hDR : (0 : ℝ) < 2 * (W : ℝ) - 1 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    linarith
  -- the decomposition `v_i t = N + (r - d)/q`
  have hdecomp : ∀ i, (v i : ℝ) * t =
      (((v i * a) / q : ℤ) : ℝ) + ((((v i * a) % q : ℤ) : ℝ) - 2 * v i / (2 * W - 1)) / q := by
    intro i
    have h := Int.ediv_add_emod (v i * a) q
    have hR : (q : ℝ) * (((v i * a) / q : ℤ) : ℝ) + (((v i * a) % q : ℤ) : ℝ)
        = (v i : ℝ) * a := by exact_mod_cast h
    have e1 : (v i : ℝ) * t = ((v i : ℝ) * a) / q - 2 * v i / (2 * W - 1) / q := by
      rw [ht, div_div, mul_comm (2 * (W : ℝ) - 1) (q : ℝ)]; ring
    rw [e1, ← hR]
    field_simp
    ring
  have key : ∀ i, 1 / (q : ℝ) < nearestIntDist ((v i : ℝ) * t) := by
    intro i
    by_cases hi : i = i0
    · rw [hi]
      have hr0 : (v i0 * a) % q = 0 :=
        Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdiv a)
      have hWR : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      refine one_div_lt_nid q hqR ((v i0 * a) / q - 1) (q - 2 * W / (2 * W - 1)) _ ?_ ?_ ?_
      · rw [hdecomp i0, hr0]
        push_cast
        field_simp
        ring
      · have hd2 : 2 * (W : ℝ) / (2 * W - 1) ≤ 2 := by
          rw [div_le_iff₀ hDR]; linarith
        linarith
      · have hd1 : 1 < 2 * (W : ℝ) / (2 * W - 1) := by
          rw [lt_div_iff₀ hDR]; linarith
        linarith
    · obtain ⟨hnd, hlt⟩ := hoth i hi
      set r := (v i * a) % q with hr
      have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
      have hrq : r < q := Int.emod_lt_of_pos _ (by omega)
      have hvr : v i ≡ r * u [ZMOD q] := by
        have h1 : v i * (u * a) ≡ v i * 1 [ZMOD q] := hua.mul_left _
        have h2 : v i * a ≡ r [ZMOD q] := (Int.mod_modEq _ _).symm
        have h3 := h2.mul_right (u : ℤ)
        rw [mul_one] at h1
        calc v i ≡ v i * (u * a) [ZMOD q] := h1.symm
          _ = v i * a * u := by ring
          _ ≡ r * u [ZMOD q] := h3
      have hrne0 : r ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hvr
        exact hnd ((Int.modEq_zero_iff_dvd).mp hvr)
      have hrne1 : r ≠ 1 := by
        intro h1
        rw [h1, one_mul] at hvr
        exact hmiss i hvr
      have hr2 : (2 : ℤ) ≤ r := by omega
      have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      have hrqR : (r : ℝ) ≤ q - 1 := by
        have : r ≤ q - 1 := by omega
        exact_mod_cast this
      have hvi1 : (1 : ℝ) ≤ v i := by exact_mod_cast hv i
      have hviW : (v i : ℝ) ≤ W - 1 := by
        have : v i ≤ W - 1 := by omega
        exact_mod_cast this
      have hd0 : 0 < 2 * (v i : ℝ) / (2 * W - 1) := div_pos (by linarith) hDR
      have hd1 : 2 * (v i : ℝ) / (2 * W - 1) < 1 := by
        rw [div_lt_one hDR]; linarith
      refine one_div_lt_nid q hqR ((v i * a) / q) (r - 2 * v i / (2 * W - 1)) _ (hdecomp i) ?_ ?_
      · linarith
      · linarith
  -- strict floor
  have hgap : 1 / (q : ℝ) < gap v t := by
    unfold gap
    rw [Finset.lt_inf'_iff]
    intro i _
    exact key i
  have hML : gap v t ≤ ML v := le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩
  have hqk : (q : ℝ) = (k : ℝ) + 2 := by rw [hqdef]; push_cast; ring
  rw [← hqk]
  exact lt_of_lt_of_le hgap hML

end LRSpectrumFull.RoomFCULemmaP
