/-
# RQ, module T: three runners at one time (`lemSR3`) and Theorem P3

Paper proof: INVENTION_2026_11/ROOMS/OPUS_F4_2026_11_12.md, Section 3, "P3 (three share a factor)":
`q ≥ 2` divides three of the four speeds and not the fourth.  Lemma S (`lemSR`, threshold `1/5`) on the three
quotients `v_i / q` gives an offset `x`; the one free runner is then good at some `(j + x)/q` (`exists_free_j`).

* `lemSR3` : `lemSR` for three explicit runners (distinct positive speeds, real phases).
* `P3`     : the theorem.
-/
import LRSpectrumFull.RQWindow
import LRSpectrumFull.RFiveLemS

namespace LRSpectrumFull

lemma lemSR3 (a b c : ℕ) (pa : 0 < a) (pb : 0 < b) (pc : 0 < c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (φa φb φc : ℝ) :
    ∃ x : ℝ, GoodR a φa x ∧ GoodR b φb x ∧ GoodR c φc x := by
  obtain ⟨x, hx⟩ := lemSR (ι := ℕ) (∑ i ∈ Finset.range 3, (if i = 0 then a else if i = 1 then b else c))
    (fun i => if i = 0 then a else if i = 1 then b else c)
    (fun i => if i = 0 then φa else if i = 1 then φb else φc) (Finset.range 3)
    (by
      intro i hi
      rw [Finset.mem_range] at hi
      interval_cases i <;> simp [pa, pb, pc])
    (by
      intro i hi k hk h
      rw [Finset.mem_range] at hi hk
      interval_cases i <;> interval_cases k <;> simp at h ⊢ <;> omega)
    (by simp) le_rfl
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa using hx 0 (by simp)
  · simpa using hx 1 (by simp)
  · simpa using hx 2 (by simp)

/-- Theorem P3: four distinct positive speeds, `q ≥ 2` divides all but one of them (`z`), `q ∤ v z`,
arbitrary real phases: some time puts every runner at distance `≥ 1/5` from `ℤ`. -/
theorem P3 (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (q : ℕ) (hq : 2 ≤ q)
    (z : Fin 4) (hz : ¬ q ∣ v z) (hall : ∀ i, i ≠ z → q ∣ v i) (φ : Fin 4 → ℝ) :
    ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t := by
  have hq0 : 0 < q := by omega
  obtain ⟨x, hx⟩ := lemSR (∑ i ∈ Finset.univ.erase z, v i / q) (fun i => v i / q) φ
    (Finset.univ.erase z)
    (fun i hi => Nat.div_pos (Nat.le_of_dvd (hpos i) (hall i (Finset.ne_of_mem_erase hi))) hq0)
    (fun i hi k hk hik => by
      apply hinj
      have hi' := hall i (Finset.ne_of_mem_erase hi)
      have hk' := hall k (Finset.ne_of_mem_erase hk)
      have hik' : v i / q = v k / q := hik
      calc v i = v i / q * q := (Nat.div_mul_cancel hi').symm
        _ = v k / q * q := by rw [hik']
        _ = v k := Nat.div_mul_cancel hk')
    (by simp) le_rfl
  obtain ⟨j, hj⟩ := exists_free_j q hq0 (v z) hz (φ z) x
  refine ⟨((j : ℝ) + x) / q, fun i => ?_⟩
  by_cases hiz : i = z
  · subst hiz
    exact hj
  · have hmem : i ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hiz, Finset.mem_univ _⟩
    have h' : GoodR (v i / q) (φ i) x := hx i hmem
    obtain ⟨u, hu⟩ := hall i hiz
    rw [hu] at h' ⊢
    rw [Nat.mul_div_cancel_left u hq0] at h'
    exact (goodR_mulq q u hq0 (φ i) x j).2 h'

end LRSpectrumFull
