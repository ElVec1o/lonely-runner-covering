import Mathlib

/-!
# E6 session 16: finite Z/7 facts of Barajas-Serra Section 6

All statements are about subsets of `ZMod 7` (the sets of `q`-values of the classes `A1, A2, A4`,
normalized so that the class of `A1` is `1`; then the multiplier `lambda_k in Lambda_0` sends
`q(d)` to `q(d) + j k` for `d in A_j`). `ell X` is the paper's `l(X)`: the length of the shortest
cyclic interval of `ZMod 7` containing `X` (`ell emptyset = 0`).

Proof method: every finset of `ZMod 7` is `ofMask n` for some `n < 128`; the statements are
transferred to bitmasks and closed by kernel `decide` (no `native_decide`). Rust falsification
first: (development file, not part of this archive), lem5prof.rs, eq14.rs`,
(development file, not part of this archive), z7extra.rs`.
-/

namespace LRSpectrumFull.BarajasSerra.Z7

/-- `l(X)`: length of the shortest cyclic interval `{a, a+1, ..., a+l-1}` containing `X`. -/
def ell (X : Finset (ZMod 7)) : ℕ :=
  ((List.range 8).find? (fun l => decide (∃ a : ZMod 7, ∀ x ∈ X, (x - a).val < l))).getD 7

/-- The finset with bitmask `n`. -/
def ofMask (n : ℕ) : Finset (ZMod 7) := Finset.univ.filter (fun x => n.testBit x.val = true)

@[simp] theorem mem_ofMask (n : ℕ) (x : ZMod 7) : x ∈ ofMask n ↔ n.testBit x.val = true := by
  simp [ofMask]

theorem exists_ofMask (X : Finset (ZMod 7)) : ∃ n < 128, X = ofMask n := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by ext x; simp⟩
  | insert a X _ ih =>
    obtain ⟨n, hn, rfl⟩ := ih
    refine ⟨n ||| 2 ^ a.val, ?_, ?_⟩
    · have ha : a.val < 7 := ZMod.val_lt a
      have h1 : n < 2 ^ 7 := by norm_num; omega
      have h2 : 2 ^ a.val < 2 ^ 7 := Nat.pow_lt_pow_right (by norm_num) ha
      have := Nat.or_lt_two_pow h1 h2
      simpa using this
    · ext x
      simp only [Finset.mem_insert, mem_ofMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro (rfl | h)
        · exact Or.inr rfl
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (ZMod.val_injective 7 h).symm

/-- `l` on masks (computational form). -/
def ellM (n : ℕ) : ℕ :=
  ((List.range 8).find? (fun l => decide (∃ a : ZMod 7, ∀ x : ZMod 7, n.testBit x.val = true →
    (x - a).val < l))).getD 7

theorem ell_ofMask (n : ℕ) : ell (ofMask n) = ellM n := by
  simp only [ell, ellM, mem_ofMask]

/-- Masks with a given `l`, as literal lists. -/
def byEll : ℕ → List ℕ
  | 0 => [0]
  | 1 => [1, 2, 4, 8, 16, 32, 64]
  | 2 => [3, 6, 12, 24, 48, 65, 96]
  | 3 => [5, 7, 10, 14, 20, 28, 33, 40, 56, 66, 67, 80, 97, 112]
  | 4 => [9, 11, 13, 15, 17, 18, 22, 26, 30, 34, 35, 36, 44, 49, 52, 60, 68, 69, 70, 71, 72, 81, 88,
          98, 99, 104, 113, 120]
  | 5 => [19, 21, 23, 25, 27, 29, 31, 37, 38, 39, 41, 42, 46, 50, 51, 54, 57, 58, 62, 73, 74, 75, 76,
          77, 78, 79, 82, 83, 84, 89, 92, 100, 101, 102, 103, 105, 108, 114, 115, 116, 121, 124]
  | 6 => [43, 45, 47, 53, 55, 59, 61, 63, 85, 86, 87, 90, 91, 93, 94, 95, 106, 107, 109, 110, 111,
          117, 118, 119, 122, 123, 125, 126]
  | _ => [127]

theorem mem_byEll_aux : ∀ n < 128, n ∈ byEll (ellM n) := by decide +kernel

theorem mem_byEll (X : Finset (ZMod 7)) : ∃ n ∈ byEll (ell X), X = ofMask n := by
  obtain ⟨n, hn, rfl⟩ := exists_ofMask X
  exact ⟨n, by rw [ell_ofMask]; exact mem_byEll_aux n hn, rfl⟩

/-- `Q + c` avoids the forbidden set `{0, 6}`. -/
def Avoid (Q : Finset (ZMod 7)) (c : ZMod 7) : Prop := ∀ x ∈ Q, x + c ≠ 0 ∧ x + c ≠ 6

/-- `lambda_k` is good for all of `A = A1 ∪ A2 ∪ A4`. -/
def Good (Q1 Q2 Q4 : Finset (ZMod 7)) (k : ZMod 7) : Prop :=
  Avoid Q1 k ∧ Avoid Q2 (2 * k) ∧ Avoid Q4 (4 * k)

instance (Q : Finset (ZMod 7)) (c : ZMod 7) : Decidable (Avoid Q c) := by
  unfold Avoid; infer_instance
instance (Q1 Q2 Q4 : Finset (ZMod 7)) (k : ZMod 7) : Decidable (Good Q1 Q2 Q4 k) := by
  unfold Good; infer_instance

/-- Some `lambda_k in Lambda_0` is good. -/
def GoodSome (Q1 Q2 Q4 : Finset (ZMod 7)) : Prop := ∃ k, Good Q1 Q2 Q4 k

instance (Q1 Q2 Q4 : Finset (ZMod 7)) : Decidable (GoodSome Q1 Q2 Q4) := by
  unfold GoodSome; infer_instance

/-- The exceptional configuration of Lemma 5: `e~(d, d') = 2 q(d) - q(d') in {2, 4}` for all
`d in A2`, `d' in A4`. -/
def Exc5 (Q2 Q4 : Finset (ZMod 7)) : Prop := ∀ i ∈ Q2, ∀ j ∈ Q4, 2 * i - j = 2 ∨ 2 * i - j = 4

instance (Q2 Q4 : Finset (ZMod 7)) : Decidable (Exc5 Q2 Q4) := by
  unfold Exc5; infer_instance

/-! ## Lemma 5, corrected -/

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem lemma5_core : ∀ l1 < 6, ∀ l2 < 6, ∀ l4 < 6, l1 + l2 + l4 ≤ 5 → ¬ (l1 = 1 ∧ max l2 l4 = 3) →
    ∀ n1 ∈ byEll l1, ∀ n2 ∈ byEll l2, ∀ n4 ∈ byEll l4,
    GoodSome (ofMask n1) (ofMask n2) (ofMask n4) ∨
    (l1 = 3 ∧ l2 = 1 ∧ l4 = 1 ∧ Exc5 (ofMask n2) (ofMask n4)) := by
  decide +kernel

theorem ell_lt_of_sum {a b c : ℕ} (h : a + b + c ≤ 5) : a < 6 ∧ b < 6 ∧ c < 6 := by omega

/-- **Lemma 5, corrected** (plan `section6_plan.md`, Lemma 5 erratum). If
`l(A1) + l(A2) + l(A4) <= 5` and not (`l(A1) = 1` and `max(l(A2), l(A4)) = 3`), then some
`lambda_k in Lambda_0` is good, unless `(l(A1), l(A2), l(A4)) = (3,1,1)` and `e~(d, d') in {2,4}`
for all `d in A2`, `d' in A4`. -/
theorem lemma5 (Q1 Q2 Q4 : Finset (ZMod 7)) (h : ell Q1 + ell Q2 + ell Q4 ≤ 5)
    (hc : ¬ (ell Q1 = 1 ∧ max (ell Q2) (ell Q4) = 3)) :
    (∃ k, Good Q1 Q2 Q4 k) ∨
    (ell Q1 = 3 ∧ ell Q2 = 1 ∧ ell Q4 = 1 ∧ ∀ i ∈ Q2, ∀ j ∈ Q4, 2 * i - j = 2 ∨ 2 * i - j = 4) := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, h2, rfl⟩ := mem_byEll Q2
  obtain ⟨n4, h4, rfl⟩ := mem_byEll Q4
  obtain ⟨a, b, c⟩ := ell_lt_of_sum h
  exact lemma5_core _ a _ b _ c h hc n1 h1 n2 h2 n4 h4

/-- Lemma 5 is FALSE as printed: `Q1 = {0}`, `Q2 = {3}`, `Q4 = {2, 4}` (profile `(1,1,3)`). -/
theorem lemma5_as_printed_false : ¬ ∀ Q1 Q2 Q4 : Finset (ZMod 7), ell Q1 + ell Q2 + ell Q4 ≤ 5 →
    (∃ k, Good Q1 Q2 Q4 k) ∨
    (ell Q1 = 3 ∧ ell Q2 = 1 ∧ ell Q4 = 1 ∧ ∀ i ∈ Q2, ∀ j ∈ Q4, 2 * i - j = 2 ∨ 2 * i - j = 4) := by
  intro h
  have h' := h {0} {3} {2, 4} (by decide +kernel)
  revert h'
  decide +kernel

/-! ## Lemma 6 (as printed; `q(A1) ⊆ {1, ..., l(A1)}`, `1 ∈ q(A1)`, `d` the element with `q(d) = 1`) -/

def Norm1 (Q : Finset (ZMod 7)) (l : ℕ) : Prop := (1 : ZMod 7) ∈ Q ∧ ∀ x ∈ Q, 1 ≤ x.val ∧ x.val ≤ l
instance (Q : Finset (ZMod 7)) (l : ℕ) : Decidable (Norm1 Q l) := by unfold Norm1; infer_instance
def P6i4 (Q4 : Finset (ZMod 7)) : Prop := ∀ j ∈ Q4, 2 * j - 1 ≠ 4 ∧ 2 * j - 1 ≠ 6
instance (Q : Finset (ZMod 7)) : Decidable (P6i4 Q) := by unfold P6i4; infer_instance
def P6i2 (Q2 : Finset (ZMod 7)) : Prop := ∀ i ∈ Q2, 2 - i ≠ 2 ∧ 2 - i ≠ 3
instance (Q : Finset (ZMod 7)) : Decidable (P6i2 Q) := by unfold P6i2; infer_instance
def P6ii (Q2 : Finset (ZMod 7)) : Prop := ∀ i : ZMod 7, i ∈ Q2 → i + 1 ∈ Q2 → 2 - i ≠ 4
instance (Q : Finset (ZMod 7)) : Decidable (P6ii Q) := by unfold P6ii; infer_instance

set_option synthInstance.maxSize 2048 in
theorem lemma6_i_core : ∀ n1 ∈ byEll 5, Norm1 (ofMask n1) 5 →
    (∀ n4 ∈ byEll 1, P6i4 (ofMask n4) → GoodSome (ofMask n1) ∅ (ofMask n4)) ∧
    (∀ n2 ∈ byEll 1, P6i2 (ofMask n2) → GoodSome (ofMask n1) (ofMask n2) ∅) := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem lemma6_ii_core : ∀ n1 ∈ byEll 4, Norm1 (ofMask n1) 4 →
    (∀ n4 ∈ byEll 2, GoodSome (ofMask n1) ∅ (ofMask n4)) ∧
    (∀ n2 ∈ byEll 2, P6ii (ofMask n2) → GoodSome (ofMask n1) (ofMask n2) ∅) := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem lemma6_iii_core : ∀ n1 ∈ byEll 3, Norm1 (ofMask n1) 3 →
    ∀ n2 ∈ byEll 3, GoodSome (ofMask n1) (ofMask n2) ∅ := by
  decide +kernel

theorem ell_eq_zero_iff (Q : Finset (ZMod 7)) : ell Q = 0 ↔ Q = ∅ := by
  obtain ⟨n, hn, rfl⟩ := exists_ofMask Q
  revert n
  decide +kernel

/-- **Lemma 6 (i)**. -/
theorem lemma6_i (Q1 Q2 Q4 : Finset (ZMod 7)) (hn : (1 : ZMod 7) ∈ Q1)
    (hQ : ∀ x ∈ Q1, 1 ≤ x.val ∧ x.val ≤ ell Q1)
    (h : (ell Q1 = 5 ∧ ell Q2 = 0 ∧ ell Q4 = 1 ∧ ∀ j ∈ Q4, 2 * j - 1 ≠ 4 ∧ 2 * j - 1 ≠ 6) ∨
         (ell Q1 = 5 ∧ ell Q2 = 1 ∧ ell Q4 = 0 ∧ ∀ i ∈ Q2, 2 - i ≠ 2 ∧ 2 - i ≠ 3)) :
    ∃ k, Good Q1 Q2 Q4 k := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, h2, rfl⟩ := mem_byEll Q2
  obtain ⟨n4, h4, rfl⟩ := mem_byEll Q4
  rcases h with ⟨e1, e2, e4, hp⟩ | ⟨e1, e2, e4, hp⟩
  · rw [e1] at h1 hQ; rw [e4] at h4
    rw [(ell_eq_zero_iff _).1 e2]
    exact (lemma6_i_core n1 h1 ⟨hn, hQ⟩).1 n4 h4 hp
  · rw [e1] at h1 hQ; rw [e2] at h2
    rw [(ell_eq_zero_iff _).1 e4]
    exact (lemma6_i_core n1 h1 ⟨hn, hQ⟩).2 n2 h2 hp

/-- **Lemma 6 (ii)**: `q(A2) = {i, i+1}` and `e~(d, d') = 2 - i ≠ 4` for `d'` with `q(d') = i`. -/
theorem lemma6_ii (Q1 Q2 Q4 : Finset (ZMod 7)) (hn : (1 : ZMod 7) ∈ Q1)
    (hQ : ∀ x ∈ Q1, 1 ≤ x.val ∧ x.val ≤ ell Q1)
    (h : (ell Q1 = 4 ∧ ell Q2 = 0 ∧ ell Q4 = 2) ∨
         (ell Q1 = 4 ∧ ell Q2 = 2 ∧ ell Q4 = 0 ∧ ∀ i : ZMod 7, i ∈ Q2 → i + 1 ∈ Q2 → 2 - i ≠ 4)) :
    ∃ k, Good Q1 Q2 Q4 k := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, h2, rfl⟩ := mem_byEll Q2
  obtain ⟨n4, h4, rfl⟩ := mem_byEll Q4
  rcases h with ⟨e1, e2, e4⟩ | ⟨e1, e2, e4, hp⟩
  · rw [e1] at h1 hQ; rw [e4] at h4
    rw [(ell_eq_zero_iff _).1 e2]
    exact (lemma6_ii_core n1 h1 ⟨hn, hQ⟩).1 n4 h4
  · rw [e1] at h1 hQ; rw [e2] at h2
    rw [(ell_eq_zero_iff _).1 e4]
    exact (lemma6_ii_core n1 h1 ⟨hn, hQ⟩).2 n2 h2 hp

/-- **Lemma 6 (iii)**. -/
theorem lemma6_iii (Q1 Q2 Q4 : Finset (ZMod 7)) (hn : (1 : ZMod 7) ∈ Q1)
    (hQ : ∀ x ∈ Q1, 1 ≤ x.val ∧ x.val ≤ ell Q1)
    (h : ell Q1 = 3 ∧ ell Q2 = 3 ∧ ell Q4 = 0) : ∃ k, Good Q1 Q2 Q4 k := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, h2, rfl⟩ := mem_byEll Q2
  obtain ⟨e1, e2, e4⟩ := h
  rw [e1] at h1 hQ; rw [e2] at h2
  rw [(ell_eq_zero_iff _).1 e4]
  exact lemma6_iii_core n1 h1 ⟨hn, hQ⟩ n2 h2

/-! ## Lemma 12 (`|A1| = 3`, `|A2| = 2`, `A4 = ∅`) -/

set_option synthInstance.maxSize 2048 in
theorem lemma12_i_core : ∀ l1 < 4, ∀ n1 ∈ byEll l1, ∀ n2 < 128, (ofMask n2).card ≤ 2 →
    GoodSome (ofMask n1) (ofMask n2) ∅ := by
  decide +kernel

def Start4 (Q : Finset (ZMod 7)) (a : ZMod 7) : Prop := a ∈ Q ∧ ∀ x ∈ Q, (x - a).val < 4
instance (Q : Finset (ZMod 7)) (a : ZMod 7) : Decidable (Start4 Q a) := by
  unfold Start4; infer_instance
def P12 (Q2 : Finset (ZMod 7)) (a : ZMod 7) : Prop :=
  ∀ i ∈ Q2, 2 * a - i = 0 ∨ 2 * a - i = 1 ∨ 2 * a - i = 6
instance (Q : Finset (ZMod 7)) (a : ZMod 7) : Decidable (P12 Q a) := by
  unfold P12; infer_instance

set_option synthInstance.maxSize 2048 in
theorem lemma12_ii_core : ∀ n1 ∈ byEll 4, (ofMask n1).card ≤ 3 → ∀ a : ZMod 7,
    Start4 (ofMask n1) a → ∀ n2 < 128, (ofMask n2).card ≤ 2 → P12 (ofMask n2) a →
    GoodSome (ofMask n1) (ofMask n2) ∅ := by
  decide +kernel

/-- **Lemma 12 (i)**: `l(A1) <= 3`. -/
theorem lemma12_i (Q1 Q2 : Finset (ZMod 7)) (h2 : Q2.card ≤ 2) (h : ell Q1 ≤ 3) :
    ∃ k, Good Q1 Q2 ∅ k := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, hn2, rfl⟩ := exists_ofMask Q2
  exact lemma12_i_core _ (by omega) n1 h1 n2 hn2 h2

/-- **Lemma 12 (ii)**: `l(A1) = 4`, `q(A1) ⊆ {q(d), ..., q(d)+3}`, `e~(d, d') ∈ {0, 1, 6}` for all
`d' ∈ A2`. -/
theorem lemma12_ii (Q1 Q2 : Finset (ZMod 7)) (h1c : Q1.card ≤ 3) (h2 : Q2.card ≤ 2)
    (h : ell Q1 = 4) (a : ZMod 7) (ha : a ∈ Q1) (hQ : ∀ x ∈ Q1, (x - a).val < 4)
    (he : ∀ i ∈ Q2, 2 * a - i = 0 ∨ 2 * a - i = 1 ∨ 2 * a - i = 6) :
    ∃ k, Good Q1 Q2 ∅ k := by
  obtain ⟨n1, h1, rfl⟩ := mem_byEll Q1
  obtain ⟨n2, hn2, rfl⟩ := exists_ofMask Q2
  rw [h] at h1
  exact lemma12_ii_core n1 h1 h1c a ⟨ha, hQ⟩ n2 hn2 h2 he

/-! ## Eq. (14) (Section 6.5: `|A1| = 3`, `|A4| = 2`, `A2 = ∅`) -/

set_option synthInstance.maxSize 2048 in
theorem eq14_core : ∀ l1 < 5, ∀ l4 < 4, ((l1 ≤ 3 ∧ l4 ≤ 3) ∨ (l1 ≤ 4 ∧ l4 ≤ 2)) →
    ∀ n1 ∈ byEll l1, (ofMask n1).card ≤ 3 → ∀ n4 ∈ byEll l4, (ofMask n4).card ≤ 2 →
    GoodSome (ofMask n1) ∅ (ofMask n4) := by
  decide +kernel

/-- **Eq. (14)**: if `l(A1) <= 3, l(A4) <= 3` or `l(A1) <= 4, l(A4) <= 2`, some `lambda_k` is good. -/
theorem eq14 (Q1 Q4 : Finset (ZMod 7)) (h1 : Q1.card ≤ 3) (h4 : Q4.card ≤ 2)
    (h : (ell Q1 ≤ 3 ∧ ell Q4 ≤ 3) ∨ (ell Q1 ≤ 4 ∧ ell Q4 ≤ 2)) : ∃ k, Good Q1 ∅ Q4 k := by
  obtain ⟨n1, m1, rfl⟩ := mem_byEll Q1
  obtain ⟨n4, m4, rfl⟩ := mem_byEll Q4
  exact eq14_core _ (by omega) _ (by omega) h n1 m1 h1 n4 m4 h4

/-! ## Remark 8, the `Z/7` part (after the carry step `q(x) - q(y) ∈ q(x - y) + {0, 1}`) -/

def Diff (X : Finset (ZMod 7)) (S : Finset (ZMod 7)) : Prop := ∀ x ∈ X, ∀ y ∈ X, x - y ∈ S
instance (X S : Finset (ZMod 7)) : Decidable (Diff X S) := by unfold Diff; infer_instance

theorem remark8_core : ∀ n < 128, (Diff (ofMask n) {6, 0, 1} → ell (ofMask n) ≤ 2) ∧
    (Diff (ofMask n) {5, 6, 0, 1, 2} → ell (ofMask n) ≤ 3) := by
  decide +kernel

/-- Remark 8 (i), `Z/7` part: `X - X ⊆ {6, 0, 1}` implies `l(X) <= 2`. -/
theorem remark8_i_z7 (X : Finset (ZMod 7)) (h : ∀ x ∈ X, ∀ y ∈ X, x - y ∈ ({6, 0, 1} : Finset (ZMod 7))) :
    ell X ≤ 2 := by
  obtain ⟨n, hn, rfl⟩ := exists_ofMask X
  exact (remark8_core n hn).1 h

/-- Remark 8 (ii), `Z/7` part: `X - X ⊆ {5, 6, 0, 1, 2}` implies `l(X) <= 3`. -/
theorem remark8_ii_z7 (X : Finset (ZMod 7))
    (h : ∀ x ∈ X, ∀ y ∈ X, x - y ∈ ({5, 6, 0, 1, 2} : Finset (ZMod 7))) : ell X ≤ 3 := by
  obtain ⟨n, hn, rfl⟩ := exists_ofMask X
  exact (remark8_core n hn).2 h

/-! ## Section 6.1, 6.3, 6.5, 6.6: the finite `Z/7` claims (checked first in `e6s16/sec6b.rs`) -/

/-- 6.1, `nu(E) = {m}`: `Z/7` minus two points, scaled by `(i - j)⁻¹`, has `l <= 5`. -/
theorem sec61_rescale : ∀ i j : ZMod 7, i ≠ j → ∃ u : ZMod 7, u * (i - j) = 1 ∧
    ell ((Finset.univ \ {i, j}).image (u * ·)) ≤ 5 := by
  decide +kernel

/-- 6.3, `h = m`: the eight bad pairs `(e~34, e~45)`; `q(d3) = 1`, `q(d4) = i`, `q(d5) = j`,
`lambda_0, lambda_1` both fail. -/
def bad63 : Finset (ZMod 7 × ZMod 7) := {(2, 4), (2, 5), (3, 2), (3, 3), (4, 3), (4, 4), (5, 1), (5, 2)}

theorem sec63_bad_pairs : ∀ i j : ZMod 7,
    ((i = 0 ∨ i = 6 ∨ j = 0 ∨ j = 6) ∧ (i + 2 = 0 ∨ i + 2 = 6 ∨ j + 4 = 0 ∨ j + 4 = 6)) ↔
    (2 - i, 2 * i - j) ∈ bad63 := by
  decide +kernel

/-- 6.3, `h = m`: one of the four pairs `(a - e1, b - e2)`, `e1, e2 ∈ {0,1}`, is not bad. -/
theorem sec63_escape : ∀ a b : ZMod 7, ∃ e1 e2 : ZMod 7, (e1 = 0 ∨ e1 = 1) ∧ (e2 = 0 ∨ e2 = 1) ∧
    (a - e1, b - e2) ∉ bad63 := by
  decide +kernel

/-- 6.5 (ii.1)(b): `q(A1) = {1,2,3}`, `q(A4) = {i, i+4}`; one of `lambda_0, lambda_1, lambda_2` is
good iff `i ∉ {2, 6}`. -/
theorem sec65b : ∀ i : ZMod 7, (∃ k : ZMod 7, k.val < 3 ∧ Good {1, 2, 3} ∅ {i, i + 4} k) ↔
    (i ≠ 2 ∧ i ≠ 6) := by
  decide +kernel

/-- 6.6 (a), eq. (16), with `q(lambda_k A2) = {2k - a, 2k - a + 1}` (from (13); the paper prints
`a - 2k`, a sign typo; the printed bad list is the one for the correct sign). `a = e~(d2,d4)`,
`b = e~(d2,d5)`. -/
def bad16 : Finset (ZMod 7 × ZMod 7) := {(4, 2), (4, 4), (5, 4), (6, 4), (6, 6)}

theorem sec66a_eq16 : ∀ a b : ZMod 7,
    (∃ k : ZMod 7, 1 ≤ k.val ∧ k.val ≤ 3 ∧ Avoid {k, k + 2, 2 * k - a, 2 * k - a + 1, 4 * b + 4 * k} 0) ↔
    (a, b) ∉ bad16 := by
  decide +kernel

theorem sec66a_levels : ∀ a b : ZMod 7, (a, b) ∈ bad16 →
      (a = 4 ∨ a = 5 ∨ a = 6) ∧ ((a = 3 ∨ a = 4 ∨ a = 5) → b = 2 ∨ b = 4) ∧
      ((a = 5 ∨ a = 6 ∨ a = 0) → b = 4 ∨ b = 6) := by
  decide +kernel

theorem sec66a_escape : ∀ a b : ZMod 7, ∃ e1 e2 : ZMod 7, (e1 = 0 ∨ e1 = 1) ∧ (e2 = 0 ∨ e2 = 1) ∧
      (a - e1, b - e2) ∉ bad16 := by
  decide +kernel

/-- 6.6 (b): `q(lambda_k A2) = {k, k+2}`, `q(lambda_k A1) = {4a+4k, 4a+4k+1}`,
`q(lambda_k d5) = 4 (b + q(lambda_k d2))` (from (13); the paper's `a - b + k` is wrong). The
failing pairs have `a ∈ {2, 4}`; so `a ∉ {2, 4}` suffices (the paper excludes `{2, 4, 6}`, which
has `l = 5` and is not reachable by Lemma 7 (i)). -/
def bad66b : Finset (ZMod 7 × ZMod 7) := {(2, 3), (2, 5), (4, 2), (4, 4)}

theorem sec66b : ∀ a b : ZMod 7,
    (∃ k : ZMod 7, 1 ≤ k.val ∧ k.val ≤ 3 ∧
      Avoid {k, k + 2, 4 * a + 4 * k, 4 * a + 4 * k + 1, 4 * (b + (4 * a + 4 * k))} 0) ↔
    (a, b) ∉ bad66b := by
  decide +kernel

end LRSpectrumFull.BarajasSerra.Z7
