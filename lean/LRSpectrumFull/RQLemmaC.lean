/-
# RQ, module C: Lemma C (modulus 8, two free runners in different classes)

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "Lemma C (q = 8, v_b = ±3 v_a mod 8)".
In the coordinate `z = v_a j` the bad integers of `a` lie in a block of 4 consecutive residues mod 8 and those of
`b` in `μ⁻¹ ·` (a block of 4), `μ ∈ {3, 5}` (`μ⁻¹ = μ` mod 8).  Finite part: for `μ ∈ {3, 5}` two such
blocks never cover `ZMod 8` (`lemmaC3`, `lemmaC5`, by kernel `decide`; the controls `μ ∈ {1, 7}` do cover).

* `blk8`, `lemmaC3`, `lemmaC5`, `lemmaC1_covers`, `lemmaC7_covers` : the finite part and its controls.
* `mem_blk8_of_near` : integers within `8/5` of a real `c` form a block `{N, ..., N+3}`.
* `lemmaC_real`      : the real-phase statement: some `j` is good for both runners, for every `x`.
-/
import LRSpectrumFull.RQWindow

namespace LRSpectrumFull

/-- four consecutive residues mod 8 -/
def blk8 (s : ZMod 8) : Finset (ZMod 8) := {s, s + 1, s + 2, s + 3}

lemma lemmaC3 : ∀ s t : ZMod 8, ∃ z : ZMod 8, z ∉ blk8 s ∧ 3 * z ∉ blk8 t := by decide

lemma lemmaC5 : ∀ s t : ZMod 8, ∃ z : ZMod 8, z ∉ blk8 s ∧ 5 * z ∉ blk8 t := by decide

/-- negative control: `μ = 1` (same class) does allow a covering pair of blocks -/
lemma lemmaC1_covers : ¬ ∀ s t : ZMod 8, ∃ z : ZMod 8, z ∉ blk8 s ∧ 1 * z ∉ blk8 t := by decide

/-- negative control: `μ = 7 = -1` -/
lemma lemmaC7_covers : ¬ ∀ s t : ZMod 8, ∃ z : ZMod 8, z ∉ blk8 s ∧ 7 * z ∉ blk8 t := by decide

lemma mem_blk8_of_near (c : ℝ) (m : ℤ) (h : |(m : ℝ) - c| < ((8 : ℕ) : ℝ) / 5) :
    (m : ZMod 8) ∈ blk8 ((⌊c - 8 / 5⌋ + 1 : ℤ) : ZMod 8) := by
  have e8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
  rw [e8] at h
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have f1 := Int.floor_le (c - 8 / 5)
  have f2 := Int.lt_floor_add_one (c - 8 / 5)
  have g1 : ⌊c - 8 / 5⌋ + 1 ≤ m := by
    have h3 : ((⌊c - 8 / 5⌋ : ℤ) : ℝ) < m := by linarith
    have h4 : ⌊c - 8 / 5⌋ < m := by exact_mod_cast h3
    omega
  have g2 : m ≤ ⌊c - 8 / 5⌋ + 4 := by
    have h3 : (m : ℝ) < ((⌊c - 8 / 5⌋ : ℤ) : ℝ) + 5 := by linarith
    have h4 : m < ⌊c - 8 / 5⌋ + 5 := by exact_mod_cast h3
    omega
  obtain ⟨r, hm, hr4⟩ : ∃ r : ℕ, m = ⌊c - 8 / 5⌋ + 1 + r ∧ r < 4 :=
    ⟨(m - (⌊c - 8 / 5⌋ + 1)).toNat, by omega, by omega⟩
  have hc : (m : ZMod 8) = ((⌊c - 8 / 5⌋ + 1 : ℤ) : ZMod 8) + (r : ZMod 8) := by
    rw [hm]
    push_cast
    ring
  rw [hc]
  interval_cases r <;> simp [blk8]

theorem lemmaC_real (va vb : ℕ) (hcop : Nat.Coprime va 8) (μ : ℤ) (hμ : μ = 3 ∨ μ = 5)
    (hrel : (vb : ZMod 8) = (μ : ZMod 8) * va) (φa φb x : ℝ) :
    ∃ j : ℤ, GoodR va φa (((j : ℝ) + x) / ((8 : ℕ) : ℝ)) ∧
      GoodR vb φb (((j : ℝ) + x) / ((8 : ℕ) : ℝ)) := by
  have h8 : (8 : ZMod 8) = 0 := by decide
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ZMod 8,
      z ∉ blk8 ((⌊(-((va : ℝ) * x + ((8 : ℕ) : ℝ) * φa)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8) ∧
      (μ : ZMod 8) * z ∉ blk8 ((⌊(-((vb : ℝ) * x + ((8 : ℕ) : ℝ) * φb)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8) := by
    rcases hμ with rfl | rfl
    · obtain ⟨z, h1, h2⟩ := lemmaC3 ((⌊(-((va : ℝ) * x + ((8 : ℕ) : ℝ) * φa)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8)
        ((⌊(-((vb : ℝ) * x + ((8 : ℕ) : ℝ) * φb)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8)
      exact ⟨z, h1, by simpa using h2⟩
    · obtain ⟨z, h1, h2⟩ := lemmaC5 ((⌊(-((va : ℝ) * x + ((8 : ℕ) : ℝ) * φa)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8)
        ((⌊(-((vb : ℝ) * x + ((8 : ℕ) : ℝ) * φb)) - 8 / 5⌋ + 1 : ℤ) : ZMod 8)
      exact ⟨z, h1, by simpa using h2⟩
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hA : (A : ZMod 8) * (va : ZMod 8) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod 8) hAB
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [ZMod.natCast_self] at h
    simpa using h
  have hj : (va : ZMod 8) * (((A * (z.val : ℤ)) : ℤ) : ZMod 8) = z := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    calc (va : ZMod 8) * ((A : ZMod 8) * z) = ((A : ZMod 8) * (va : ZMod 8)) * z := by ring
      _ = z := by rw [hA, one_mul]
  refine ⟨A * (z.val : ℤ), ?_, ?_⟩
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n1, hn1⟩ := exists_near_of_not_good hbad
    have h1 := near_to_int 8 (by norm_num) va φa x (A * (z.val : ℤ)) n1 hn1
    have h2 := mem_blk8_of_near _ _ h1
    have hm0 : (((((8 : ℕ) : ℤ) * n1 : ℤ)) : ZMod 8) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (dvd_mul_right _ _)
    have hm : ((((va : ℤ) * (A * (z.val : ℤ)) - ((8 : ℕ) : ℤ) * n1 : ℤ)) : ZMod 8) = z := by
      rw [Int.cast_sub, hm0, sub_zero, Int.cast_mul, Int.cast_natCast]
      exact hj
    rw [hm] at h2
    exact hz1 h2
  · by_contra hbad
    unfold GoodR at hbad
    obtain ⟨n2, hn2⟩ := exists_near_of_not_good hbad
    have h1 := near_to_int 8 (by norm_num) vb φb x (A * (z.val : ℤ)) n2 hn2
    have h2 := mem_blk8_of_near _ _ h1
    have hm0 : (((((8 : ℕ) : ℤ) * n2 : ℤ)) : ZMod 8) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (dvd_mul_right _ _)
    have hm : ((((vb : ℤ) * (A * (z.val : ℤ)) - ((8 : ℕ) : ℤ) * n2 : ℤ)) : ZMod 8) = (μ : ZMod 8) * z := by
      rw [Int.cast_sub, hm0, sub_zero, Int.cast_mul, Int.cast_natCast, hrel, mul_assoc, hj]
    rw [hm] at h2
    exact hz2 h2

end LRSpectrumFull
