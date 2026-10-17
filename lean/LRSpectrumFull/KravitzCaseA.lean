/-
# Kravitz Theorem 7.2, Case A: two speeds share a factor `≥ 3` ⟹ `ML ≥ 1/3`

This is the pre-jump branch of Kravitz's proof (Combin. Theory 1 (2021), arXiv:1912.06034).
It covers, in particular, the *entire pairwise-non-coprime regime*: every pairwise-non-coprime
primitive triple has two coordinates sharing an odd prime `≥ 3` (its three shared primes are
distinct, so ≥2 of them are `≥ 3`), so this case applies. `1/3 ≥ 2/7`, hence `D ≤ 1/6 < 3/14`.

We first develop the `1/3`-band analogues of the `2/7`-band `nid` lemmas in `Sweep.lean`.
See `paper/dev_notes/kravitz_path_to_piece_A.md`. No `sorry`.
-/

import LRSpectrumFull.Sweep
import LRSpectrumFull.NearestInteger
import LRSpectrumFull.Confinement
import LRSpectrumFull.DValue

namespace LRSpectrumFull

/-- A real number in the middle band `[1/3, 2/3]` is `≥ 1/3` from the integers. -/
theorem nid_ge_one_third (y : ℝ) (h1 : 1 / 3 ≤ y) (h2 : y ≤ 2 / 3) :
    1 / 3 ≤ nearestIntDist y := by
  rcases le_or_gt y (1 / 2) with h | h
  · rw [nearestIntDist_eq_self_of_le_half y (by linarith) h]; linarith
  · have e : nearestIntDist y = nearestIntDist (1 - y) := by
      rw [show (1 : ℝ) - y = -y + ((1 : ℤ) : ℝ) by push_cast; ring,
        nearestIntDist_add_int, nearestIntDist_neg]
    rw [e, nearestIntDist_eq_self_of_le_half (1 - y) (by linarith) (by linarith)]
    linarith

/-- Integer residue band ⟹ `nid ≥ 1/3`. If `m ≤ 3N ≤ 2m` then `‖N/m‖ ≥ 1/3`. -/
theorem nid_ge_of_band_third (N m : ℤ) (hm : 0 < m) (hlo : m ≤ 3 * N) (hhi : 3 * N ≤ 2 * m) :
    1 / 3 ≤ nearestIntDist ((N : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply nid_ge_one_third
  · rw [le_div_iff₀ hmR]
    have h : (m : ℝ) ≤ 3 * N := by exact_mod_cast hlo
    linarith
  · rw [div_le_iff₀ hmR]
    have h : (3 : ℝ) * N ≤ 2 * m := by exact_mod_cast hhi
    linarith

/-- Runner band ⟹ `nid ≥ 1/3`, accounting for the integer part `c`. -/
theorem nid_runner_third (a k m c : ℤ) (hm : 0 < m)
    (hlo : m ≤ 3 * (a * k - c * m)) (hhi : 3 * (a * k - c * m) ≤ 2 * m) :
    1 / 3 ≤ nearestIntDist ((a : ℝ) * ((k : ℝ) / (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))
  have e : (a : ℝ) * ((k : ℝ) / (m : ℝ))
      = ((a * k - c * m : ℤ) : ℝ) / (m : ℝ) + ((c : ℤ) : ℝ) := by
    field_simp; push_cast; ring
  rw [e, nearestIntDist_add_int]
  exact nid_ge_of_band_third (a * k - c * m) m hm hlo hhi

/-- **Case A core (witness form).** Two speeds `v₁ = g·w₁`, `v₂ = g·w₂` share the factor
`g ≥ 3` (`N := w₁ + w₂`). Given a residue witness `(m, cm)` putting the shared pair into the
`1/3`-band at the pair-sum modulus `N`, and a pre-jump witness `(h, ch)` putting the third
runner `v₃` into the `1/3`-band at modulus `gN` (at the *same* time `t = (m+N·h)/(gN)`,
since `g | v₁,v₂` makes the pre-jump invisible to them), we get `ML(v₁,v₂,v₃) ≥ 1/3`.
This is the analytic heart of Kravitz's Case A; the existence of the two witnesses is the
remaining (elementary modular-inverse) step. No `sorry`. -/
theorem ML_ge_third_caseA_witness (v₁ v₂ v₃ g w₁ w₂ N m h cm ch : ℤ)
    (hg : 3 ≤ g) (hN : 0 < N)
    (hv₁ : v₁ = g * w₁) (hv₂ : v₂ = g * w₂) (hNdef : N = w₁ + w₂)
    (hlo : N ≤ 3 * (w₁ * m - cm * N)) (hhi : 3 * (w₁ * m - cm * N) ≤ 2 * N)
    (hhlo : g * N ≤ 3 * (v₃ * (m + N * h) - ch * (g * N)))
    (hhhi : 3 * (v₃ * (m + N * h) - ch * (g * N)) ≤ 2 * (g * N)) :
    1 / 3 ≤ ML ![v₁, v₂, v₃] := by
  have hg0 : 0 < g := by omega
  have hgN : 0 < g * N := by positivity
  refine le_trans ?_
    (gap_le_ML ![v₁, v₂, v₃] (((m + N * h : ℤ) : ℝ) / ((g * N : ℤ) : ℝ)))
  apply le_gap
  intro i
  fin_cases i
  · -- v₁ : nid_runner_third v₁ (m+N·h) (g·N) (cm + w₁·h)
    show 1 / 3 ≤ nearestIntDist ((v₁ : ℝ) * (((m + N * h : ℤ) : ℝ) / ((g * N : ℤ) : ℝ)))
    refine nid_runner_third v₁ (m + N * h) (g * N) (cm + w₁ * h) hgN ?_ ?_
    · have key : v₁ * (m + N * h) - (cm + w₁ * h) * (g * N) = g * (w₁ * m - cm * N) := by
        rw [hv₁]; ring
      rw [key]; nlinarith [hlo, mul_le_mul_of_nonneg_left hlo hg0.le]
    · have key : v₁ * (m + N * h) - (cm + w₁ * h) * (g * N) = g * (w₁ * m - cm * N) := by
        rw [hv₁]; ring
      rw [key]; nlinarith [hhi, mul_le_mul_of_nonneg_left hhi hg0.le]
  · -- v₂ : nid_runner_third v₂ (m+N·h) (g·N) (w₂·h + (m - cm - 1))
    show 1 / 3 ≤ nearestIntDist ((v₂ : ℝ) * (((m + N * h : ℤ) : ℝ) / ((g * N : ℤ) : ℝ)))
    refine nid_runner_third v₂ (m + N * h) (g * N) (w₂ * h + (m - cm - 1)) hgN ?_ ?_
    · have key : v₂ * (m + N * h) - (w₂ * h + (m - cm - 1)) * (g * N)
          = g * (N - (w₁ * m - cm * N)) := by
        rw [hv₂, hNdef]; ring
      rw [key]; nlinarith [hhi, mul_le_mul_of_nonneg_left hhi hg0.le]
    · have key : v₂ * (m + N * h) - (w₂ * h + (m - cm - 1)) * (g * N)
          = g * (N - (w₁ * m - cm * N)) := by
        rw [hv₂, hNdef]; ring
      rw [key]; nlinarith [hlo, mul_le_mul_of_nonneg_left hlo hg0.le]
  · -- v₃ : direct
    show 1 / 3 ≤ nearestIntDist ((v₃ : ℝ) * (((m + N * h : ℤ) : ℝ) / ((g * N : ℤ) : ℝ)))
    exact nid_runner_third v₃ (m + N * h) (g * N) ch hgN hhlo hhhi

/-- **Pair-witness existence.** Since `gcd(w₁, N) = 1` (as `N = w₁+w₂` with `gcd(w₁,w₂)=1`),
the shared pair can be placed in the `1/3`-band at modulus `N`: there is `(m, cm)` with
`w₁·m − cm·N` a band residue. Pure Bézout. -/
theorem caseA_pair_witness (w₁ N : ℤ) (hN : 3 ≤ N) (hcop : IsCoprime w₁ N) :
    ∃ m cm : ℤ, N ≤ 3 * (w₁ * m - cm * N) ∧ 3 * (w₁ * m - cm * N) ≤ 2 * N := by
  obtain ⟨a, b, hab⟩ := hcop          -- a * w₁ + b * N = 1
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : ℤ, N ≤ 3 * ρ ∧ 3 * ρ ≤ 2 * N := by
    refine ⟨(N + 2) / 3, ?_, ?_⟩ <;> omega
  refine ⟨a * ρ, -b * ρ, ?_, ?_⟩
  · have key : w₁ * (a * ρ) - (-b * ρ) * N = ρ := by linear_combination ρ * hab
    rw [key]; exact hρ1
  · have key : w₁ * (a * ρ) - (-b * ρ) * N = ρ := by linear_combination ρ * hab
    rw [key]; exact hρ2

/-- **Pre-jump witness existence.** With the pair-witness `m` fixed, the third runner `v₃`
(coprime to `g`, since `g | v₁,v₂` and the triple is primitive) can be placed into the
`1/3`-band at modulus `gN` by a pre-jump `h`: the achievable residues `v₃·(m+N·h) mod gN`
form a coset of `N·ℤ`, and the band (width `≥ N` for `g ≥ 3`) meets it. Construction:
a band element `σ ≡ v₃·m (mod N)`, then `h` solving `v₃·h ≡ (σ−v₃m)/N (mod g)` via Bézout. -/
theorem caseA_prejump_witness (v₃ g N m : ℤ) (hg : 3 ≤ g) (hN : 0 < N)
    (hcop : IsCoprime v₃ g) :
    ∃ h ch : ℤ, g * N ≤ 3 * (v₃ * (m + N * h) - ch * (g * N))
      ∧ 3 * (v₃ * (m + N * h) - ch * (g * N)) ≤ 2 * (g * N) := by
  -- A band element σ = lo + r ≡ v₃·m (mod N) inside [gN/3, 2gN/3], with σ − v₃m = N·K
  obtain ⟨σ, K, hσlo, hσhi, hK⟩ :
      ∃ σ K : ℤ, g * N ≤ 3 * σ ∧ 3 * σ ≤ 2 * (g * N) ∧ σ - v₃ * m = N * K := by
    set M := g * N with hMdef
    have hM3 : 3 * N ≤ M := by rw [hMdef]; nlinarith
    set lo := (M + 2) / 3 with hlodef
    have hqe : (v₃ * m - lo) % N + N * ((v₃ * m - lo) / N) = v₃ * m - lo :=
      Int.emod_add_mul_ediv _ _
    set r := (v₃ * m - lo) % N with hrdef
    set q := (v₃ * m - lo) / N with hqdef
    have hr0 : 0 ≤ r := by rw [hrdef]; exact Int.emod_nonneg _ (by omega)
    have hrN : r < N := by rw [hrdef]; exact Int.emod_lt_of_pos _ (by omega)
    exact ⟨lo + r, -q, by omega, by omega, by linear_combination hqe⟩
  -- Bézout: a'·v₃ + b'·g = 1 ;  h = a'·K,  ch = -b'·K  give the band element σ
  obtain ⟨a', b', hab'⟩ := hcop
  refine ⟨a' * K, -b' * K, ?_, ?_⟩
  · have key : v₃ * (m + N * (a' * K)) - (-b' * K) * (g * N) = σ := by
      linear_combination (N * K) * hab' - hK
    rw [key]; exact hσlo
  · have key : v₃ * (m + N * (a' * K)) - (-b' * K) * (g * N) = σ := by
      linear_combination (N * K) * hab' - hK
    rw [key]; exact hσhi

/-- **Kravitz Case A (unconditional).** If two speeds share the factor `g = gcd(v₁,v₂) ≥ 3`
(so `v₁ = g·w₁`, `v₂ = g·w₂` with `gcd(w₁,w₂) = 1`, whence `gcd(w₁, w₁+w₂) = 1`) and the
triple is primitive enough that `gcd(v₃, g) = 1`, then `ML(v₁,v₂,v₃) ≥ 1/3`. Assembled from
the witness core + the two existence lemmas. (`1/3 ≥ 2/7`, so this closes `D ≤ 3/14` for the
entire shared-factor-`≥3` regime — in particular every pairwise-non-coprime triple.) -/
theorem ML_ge_third_caseA (v₁ v₂ v₃ g w₁ w₂ N : ℤ) (hg : 3 ≤ g) (hN : 3 ≤ N)
    (hv₁ : v₁ = g * w₁) (hv₂ : v₂ = g * w₂) (hNdef : N = w₁ + w₂)
    (hcop1 : IsCoprime w₁ N) (hcop3 : IsCoprime v₃ g) :
    1 / 3 ≤ ML ![v₁, v₂, v₃] := by
  obtain ⟨m, cm, hlo, hhi⟩ := caseA_pair_witness w₁ N hN hcop1
  obtain ⟨h, ch, hhlo, hhhi⟩ := caseA_prejump_witness v₃ g N m hg (by omega) hcop3
  exact ML_ge_third_caseA_witness v₁ v₂ v₃ g w₁ w₂ N m h cm ch hg (by omega)
    hv₁ hv₂ hNdef hlo hhi hhlo hhhi

/-- **Demonstration.** The pairwise-non-coprime triple `(10,15,6)` (the pair `10,15` shares
`g = 5 ≥ 3`) is closed by Case A: `ML ≥ 1/3`. -/
example : 1 / 3 ≤ ML ![10, 15, 6] :=
  ML_ge_third_caseA 10 15 6 5 2 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ⟨-2, 1, by ring⟩ ⟨1, -1, by ring⟩

end LRSpectrumFull





