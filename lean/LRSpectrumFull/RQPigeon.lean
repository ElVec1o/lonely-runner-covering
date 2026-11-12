/-
# RQ, module P: the pigeonhole for two free runners, `q ≥ 7`, `q ≠ 8`

Paper: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 1 ("exact residue counts") and the "different classes"
clause of Theorem T.  A runner `(v, φ)` with `v` coprime to `q` is bad at `t = (j + x)/q` only if some integer
`m ≡ v j (mod q)` lies in an open interval of length `2q/5`; there are at most `⌈2q/5⌉ = (2q-1)/5 + 1` such residues.
Two such runners leave a common good `j` as soon as `2 ⌈2q/5⌉ < q`, i.e. `q ≥ 7`, `q ≠ 8` (no hypothesis on
the classes of the two speeds is needed).

* `lemSR2`          : Lemma S for two runners (distinct positive speeds).
* `badSet`, `card_bad_le` : the bad `j ∈ [0, q)` of a coprime runner number at most `(2q-1)/5 + 1`.
* `exists_two_good` : the pigeonhole.
-/
import LRSpectrumFull.RQThree

namespace LRSpectrumFull

lemma lemSR2 (a b : ℕ) (pa : 0 < a) (pb : 0 < b) (hab : a ≠ b) (φa φb : ℝ) :
    ∃ x : ℝ, GoodR a φa x ∧ GoodR b φb x := by
  obtain ⟨x, hx⟩ := lemSR (ι := ℕ) (a + b) (fun i => if i = 0 then a else b)
    (fun i => if i = 0 then φa else φb) (Finset.range 2)
    (by
      intro i hi
      rw [Finset.mem_range] at hi
      interval_cases i <;> simp [pa, pb])
    (by
      intro i hi k hk h
      rw [Finset.mem_range] at hi hk
      interval_cases i <;> interval_cases k <;> simp at h ⊢ <;> omega)
    (by simp) (le_of_eq (by simp [Finset.sum_range_succ]))
  exact ⟨x, by simpa using hx 0 (by simp), by simpa using hx 1 (by simp)⟩

open Classical in
/-- the `j ∈ [0, q)` at which the runner `(v, φ)` is bad at time `(j + x)/q` -/
noncomputable def badSet (q v : ℕ) (φ x : ℝ) : Finset ℕ :=
  (Finset.range q).filter (fun j : ℕ => ¬ GoodR v φ ((((j : ℤ) : ℝ) + x) / q))

open Classical in
lemma mem_badSet {q v : ℕ} {φ x : ℝ} {j : ℕ} :
    j ∈ badSet q v φ x ↔ j < q ∧ ¬ GoodR v φ ((((j : ℤ) : ℝ) + x) / q) := by
  unfold badSet
  rw [Finset.mem_filter, Finset.mem_range]

lemma card_bad_le (q : ℕ) (hq : 0 < q) (v : ℕ) (hcop : Nat.Coprime v q) (φ x : ℝ) :
    (badSet q v φ x).card ≤ (2 * q - 1) / 5 + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : (0 : ℤ) < q := by exact_mod_cast hq
  have hcopZ : IsCoprime (q : ℤ) (v : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  set c : ℝ := -((v : ℝ) * x + q * φ) with hc
  set N : ℤ := ⌊c - (q : ℝ) / 5⌋ with hN
  have f1 : (N : ℝ) ≤ c - (q : ℝ) / 5 := Int.floor_le _
  have f2 : c - (q : ℝ) / 5 < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have key : ∀ j : ℕ, ¬ GoodR v φ ((((j : ℤ) : ℝ) + x) / q) →
      ∃ r : ℤ, 0 ≤ r ∧ 5 * r < 2 * (q : ℤ) ∧
        ∃ n : ℤ, (v : ℤ) * (j : ℤ) - (N + 1) = r + (q : ℤ) * n := by
    intro j hj
    unfold GoodR at hj
    obtain ⟨n, hn⟩ := exists_near_of_not_good hj
    have h1 := near_to_int q hq v φ x (j : ℤ) n hn
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    set m : ℤ := (v : ℤ) * (j : ℤ) - (q : ℤ) * n with hm
    have hNm : N < m := by
      have : (N : ℝ) < m := by rw [← hc] at h1a; linarith
      exact_mod_cast this
    have hm2 : 5 * (m - N - 1) < 2 * (q : ℤ) := by
      have : (5 : ℝ) * ((m : ℝ) - N - 1) < 2 * q := by rw [← hc] at h1b; linarith
      exact_mod_cast this
    refine ⟨m - N - 1, by omega, hm2, n, ?_⟩
    rw [hm]; ring
  have hmaps : ∀ j ∈ badSet q v φ x, ((((v : ℤ) * j - (N + 1)) % (q : ℤ)).toNat) ∈
      Finset.range ((2 * q - 1) / 5 + 1) := by
    intro j hj
    obtain ⟨-, hjb⟩ := mem_badSet.mp hj
    obtain ⟨r, hr0, hr1, n, hrn⟩ := key j hjb
    have hmod : ((v : ℤ) * j - (N + 1)) % (q : ℤ) = r := by
      rw [hrn, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt hr0 (by omega)
    rw [hmod, Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun j : ℕ => (((v : ℤ) * j - (N + 1)) % (q : ℤ)).toNat)
      (badSet q v φ x : Set ℕ) := by
    intro j hj k hk hfjk
    obtain ⟨hjq, -⟩ := mem_badSet.mp (Finset.mem_coe.mp hj)
    obtain ⟨hkq, -⟩ := mem_badSet.mp (Finset.mem_coe.mp hk)
    have h0 : ∀ a : ℤ, 0 ≤ a % (q : ℤ) := fun a => Int.emod_nonneg a hQ.ne'
    have hA := h0 ((v : ℤ) * j - (N + 1))
    have hB := h0 ((v : ℤ) * k - (N + 1))
    have hfjk' : (((v : ℤ) * j - (N + 1)) % (q : ℤ)).toNat
        = (((v : ℤ) * k - (N + 1)) % (q : ℤ)).toNat := hfjk
    have heq : ((v : ℤ) * j - (N + 1)) % (q : ℤ) = ((v : ℤ) * k - (N + 1)) % (q : ℤ) := by
      generalize ((v : ℤ) * j - (N + 1)) % (q : ℤ) = A at hA hfjk' ⊢
      generalize ((v : ℤ) * k - (N + 1)) % (q : ℤ) = B at hB hfjk' ⊢
      omega
    have hmod : Int.ModEq (q : ℤ) ((v : ℤ) * j - (N + 1)) ((v : ℤ) * k - (N + 1)) := heq
    have hdvd := Int.modEq_iff_dvd.mp hmod
    have e : ((v : ℤ) * k - (N + 1)) - ((v : ℤ) * j - (N + 1)) = (v : ℤ) * ((k : ℤ) - j) := by ring
    rw [e] at hdvd
    have h3 : (q : ℤ) ∣ ((k : ℤ) - j) := by
      first
        | exact hcopZ.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
        | exact hcopZ.dvd_of_dvd_mul_right hdvd
        | exact hcopZ.dvd_of_dvd_mul_left hdvd
    obtain ⟨c', hc'⟩ := h3
    rcases lt_trichotomy c' 0 with h | h | h
    · exfalso
      have e2 : (q : ℤ) * (-c') = (j : ℤ) - k := by linarith
      exact no_mult_between q (-c') hQ (by rw [e2]; nlinarith) (by rw [e2]; omega)
    · have : (k : ℤ) - j = 0 := by rw [hc', h]; ring
      omega
    · exfalso
      exact no_mult_between q c' hQ (by nlinarith) (by rw [← hc']; omega)
  calc (badSet q v φ x).card
      ≤ (Finset.range ((2 * q - 1) / 5 + 1)).card :=
        Finset.card_le_card_of_injOn _ (fun j hj => hmaps j hj) hinj
    _ = (2 * q - 1) / 5 + 1 := Finset.card_range _

/-- Two runners with speeds coprime to `q ∈ {7} ∪ [9, ∞)` have a common good `j`, for every `x`. -/
theorem exists_two_good (q : ℕ) (h7 : 7 ≤ q) (h8 : q ≠ 8) (va vb : ℕ) (ha : Nat.Coprime va q)
    (hb : Nat.Coprime vb q) (φa φb x : ℝ) :
    ∃ j : ℤ, GoodR va φa (((j : ℝ) + x) / q) ∧ GoodR vb φb (((j : ℝ) + x) / q) := by
  classical
  by_contra hcon
  push Not at hcon
  have hq : 0 < q := by omega
  have hsub : Finset.range q ⊆ badSet q va φa x ∪ badSet q vb φb x := by
    intro j hj
    rw [Finset.mem_union]
    by_cases hga : GoodR va φa ((((j : ℤ) : ℝ) + x) / q)
    · right
      exact mem_badSet.mpr ⟨Finset.mem_range.mp hj, hcon (j : ℤ) hga⟩
    · left
      exact mem_badSet.mpr ⟨Finset.mem_range.mp hj, hga⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (badSet q va φa x) (badSet q vb φb x)
  have h3 := card_bad_le q hq va ha φa x
  have h4 := card_bad_le q hq vb hb φb x
  rw [Finset.card_range] at h1
  omega

end LRSpectrumFull
