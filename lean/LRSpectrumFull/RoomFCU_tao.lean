import Mathlib

/-!
# ROOM FCU, Tao-lens seat: the window level lemma

Conventions: `m` speeds, target gap `1/(m+1)`. The witness test at the time `a/q` for a speed `v`
is the integer test of the brief: `q ≤ (m+1) * min r (q - r)` with `r = v*a % q`.

For a level `q` in the window `m+1 < q ≤ 2(m+1)`, a unit `a` and a speed `v` with `q ∤ v`:

* `goodAt_iff_window`: `v` passes the test at `a/q` iff `v*a % q ∉ {1, q-1}`.
  (Non-units are automatically good; a unit `v` is bad for exactly the two units `a ≡ ±v⁻¹`.)
* `card_badUnits_le`: at most two units are bad for `v`, and none if `v` is not coprime to `q`.
* `window_witness_of_count`: if no speed is divisible by `q` and
  `2 * #{i | Coprime q (v i)} < φ q`, some unit `a < q` is a common witness.

Independent-model Bonferroni check (`bonferroni_m12`): with `S_j = C(12,j) (2/13)^j` the odd
truncations of order 1 and 3 exceed 1 and the one of order 5 is below 1.
-/

namespace LRSpectrumFull.RoomFCUTao

/-- Witness test of the brief at the time `a/q` for the speed `v`, target gap `1/(m+1)`. -/
def goodAt (m q a v : ℕ) : Prop := q ≤ (m + 1) * min (v * a % q) (q - v * a % q)

instance (m q a v : ℕ) : Decidable (goodAt m q a v) := by unfold goodAt; infer_instance

theorem goodAt_iff_window (m q a v : ℕ) (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1))
    (ha : Nat.Coprime q a) (hv : ¬ q ∣ v) :
    goodAt m q a v ↔ (v * a % q ≠ 1 ∧ v * a % q ≠ q - 1) := by
  have hq : 0 < q := by omega
  have hrlt : v * a % q < q := Nat.mod_lt _ hq
  have hr0 : v * a % q ≠ 0 := by
    intro h
    exact hv (ha.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h))
  unfold goodAt
  constructor
  · intro h
    constructor
    · intro hr1
      rw [hr1] at h
      have hmin : min 1 (q - 1) = 1 := by omega
      rw [hmin] at h
      omega
    · intro hr1
      rw [hr1] at h
      have hmin : min (q - 1) (q - (q - 1)) = 1 := by omega
      rw [hmin] at h
      omega
  · rintro ⟨hn1, hn2⟩
    have hmin : 2 ≤ min (v * a % q) (q - v * a % q) := by omega
    calc q ≤ 2 * (m + 1) := h2
      _ = (m + 1) * 2 := by ring
      _ ≤ (m + 1) * min (v * a % q) (q - v * a % q) := Nat.mul_le_mul_left _ hmin

/-- Units below `q` that fail the test for `v`. -/
def badUnits (m q v : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => Nat.Coprime q a ∧ ¬ goodAt m q a v)

/-- If `v*a % q ∈ {1, q-1}` then `v` is coprime to `q`. -/
theorem coprime_of_mod_pm_one (q a v : ℕ) (hq : 2 ≤ q)
    (h : v * a % q = 1 ∨ v * a % q = q - 1) : Nat.Coprime v q := by
  have hmod : v * a % q ≡ v * a [MOD q] := Nat.mod_modEq _ _
  have hg : Nat.gcd (v * a % q) q = Nat.gcd (v * a) q := hmod.gcd_eq
  have hco : Nat.Coprime (v * a) q := by
    unfold Nat.Coprime
    rw [← hg]
    rcases h with h | h
    · rw [h]; exact Nat.gcd_one_left q
    · rw [h]
      have : Nat.Coprime q (q - 1) := (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_one_right q)
      exact this.symm
  exact Nat.Coprime.coprime_dvd_left (Dvd.intro a rfl) hco

theorem card_badUnits_le (m q v : ℕ) (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1)) (hv : ¬ q ∣ v) :
    (badUnits m q v).card ≤ (if Nat.Coprime q v then 2 else 0) := by
  have hq2 : 2 ≤ q := by omega
  have hsub : ∀ a ∈ badUnits m q v, v * a % q = 1 ∨ v * a % q = q - 1 := by
    intro a ha
    simp only [badUnits, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨_, hca, hbad⟩ := ha
    rw [goodAt_iff_window m q a v h1 h2 hca hv] at hbad
    by_contra hc
    push Not at hc
    exact hbad hc
  split_ifs with hcop
  · -- injective map a ↦ v*a % q into {1, q-1}
    have hinj : Set.InjOn (fun a => v * a % q) (badUnits m q v : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, badUnits] at hx hy
      have hm : v * x ≡ v * y [MOD q] := hxy
      have := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime, Nat.gcd_comm] using hcop) hm
      exact Nat.ModEq.eq_of_lt_of_lt this hx.1 hy.1
    have hmaps : ∀ a ∈ badUnits m q v, (fun a => v * a % q) a ∈ ({1, q - 1} : Finset ℕ) := by
      intro a ha
      rcases hsub a ha with h | h <;> simp [h]
    calc (badUnits m q v).card ≤ ({1, q - 1} : Finset ℕ).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ ≤ 2 := Finset.card_le_two
  · have : badUnits m q v = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      exact hcop (coprime_of_mod_pm_one q a v hq2 (hsub a ha)).symm
    simp [this]

/-- Window count criterion: fewer than `φ(q)/2` speeds coprime to `q`, none divisible by `q`,
gives a common witness `a/q`. -/
theorem window_witness_of_count {n : ℕ} (m q : ℕ) (v : Fin n → ℕ)
    (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1)) (hv : ∀ i, ¬ q ∣ v i)
    (hcount : 2 * (Finset.univ.filter (fun i => Nat.Coprime q (v i))).card < Nat.totient q) :
    ∃ a, a < q ∧ Nat.Coprime q a ∧ ∀ i, goodAt m q a (v i) := by
  classical
  set U := (Finset.range q).filter (fun a => Nat.Coprime q a) with hU
  set Bad := Finset.univ.biUnion (fun i => badUnits m q (v i)) with hBad
  have hcardBad : Bad.card < U.card := by
    have hUc : U.card = Nat.totient q := by rw [Nat.totient_eq_card_coprime]
    calc Bad.card ≤ ∑ i, (badUnits m q (v i)).card := Finset.card_biUnion_le
      _ ≤ ∑ i, (if Nat.Coprime q (v i) then 2 else 0) :=
          Finset.sum_le_sum (fun i _ => card_badUnits_le m q (v i) h1 h2 (hv i))
      _ = 2 * (Finset.univ.filter (fun i => Nat.Coprime q (v i))).card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
            mul_comm]
      _ < Nat.totient q := hcount
      _ = U.card := hUc.symm
  obtain ⟨a, haU, haB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardBad
  simp only [hU, Finset.mem_filter, Finset.mem_range] at haU
  refine ⟨a, haU.1, haU.2, fun i => ?_⟩
  by_contra hbad
  apply haB
  simp only [hBad, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, by simp only [badUnits, Finset.mem_filter, Finset.mem_range]; exact ⟨haU.1, haU.2, hbad⟩⟩

/-- Exact covering form: at a window level, a unit `a` is a common witness iff no coprime speed
satisfies `v*a ≡ ±1 (mod q)`. -/
theorem window_witness_iff {n : ℕ} (m q a : ℕ) (v : Fin n → ℕ)
    (h1 : m + 1 < q) (h2 : q ≤ 2 * (m + 1)) (hv : ∀ i, ¬ q ∣ v i) (ha : Nat.Coprime q a) :
    (∀ i, goodAt m q a (v i)) ↔ ∀ i, v i * a % q ≠ 1 ∧ v i * a % q ≠ q - 1 := by
  constructor
  · intro h i; exact (goodAt_iff_window m q a (v i) h1 h2 ha (hv i)).mp (h i)
  · intro h i; exact (goodAt_iff_window m q a (v i) h1 h2 ha (hv i)).mpr (h i)

/-- Independent model at m = 12 (13 runners): odd Bonferroni truncations of order 1 and 3 of
`P(∪ B_i)` exceed 1; order 5 is below 1. `S_j = C(12,j) (2/13)^j`. -/
theorem bonferroni_m12 :
    let S : ℕ → ℚ := fun j => (Nat.choose 12 j : ℚ) * (2 / 13) ^ j
    1 < S 1 ∧ 1 < S 1 - S 2 + S 3 ∧ S 1 - S 2 + S 3 - S 4 + S 5 < 1 := by
  intro S
  simp only [S]
  norm_num [Nat.choose]

end LRSpectrumFull.RoomFCUTao
