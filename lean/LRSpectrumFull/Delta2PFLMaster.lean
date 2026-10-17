/-
# The Prime Filtering master: dichotomy and dispatch, p = 5

`pfl_master` — for any four `5`-levels `a,b,c,e ≤ M` (with `0` and `M`
attained) and coprime slopes, some multiplier prime to `5` puts all four
elements `5^lev · s` in the safe arc of `ℤ/5^{M+1}`.  The level partition
either holds at most two elements per level below `M` (Prime Filtering
composition `pfl_compose`) or is the `3+1` shape (three at level `0`, one
at the top — the decided chase `pfl_three_one`); the dichotomy is pure
pigeonhole on four levels.
-/
import LRSpectrumFull.Delta2PFLAssembly

namespace LRSpectrumFull

/-- Every positive natural splits off its `5`-level: `d = 5^l · s` with
`¬ 5 ∣ s` (fuel recursion). -/
theorem exists_level_aux : ∀ fuel d : ℕ, 0 < d → d ≤ fuel →
    ∃ l s, d = 5 ^ l * s ∧ ¬ 5 ∣ s := by
  intro fuel
  induction fuel with
  | zero => intro d hd hle; omega
  | succ f ih =>
    intro d hd hle
    by_cases h5 : 5 ∣ d
    · obtain ⟨d', hd'⟩ := h5
      have h1 : 0 < d' := by omega
      have h2 : d' ≤ f := by omega
      obtain ⟨l, s, hls, hns⟩ := ih d' h1 h2
      exact ⟨l + 1, s, by rw [hd', hls]; ring, hns⟩
    · exact ⟨0, d, by simp, h5⟩

/-- Every positive natural is `5^l · s` with `s` prime to `5`. -/
theorem exists_level (d : ℕ) (hd : 0 < d) : ∃ l s, d = 5 ^ l * s ∧ ¬ 5 ∣ s :=
  exists_level_aux d d hd (le_refl d)

/-- Length of a level-filter over an explicit four-element list, as an
indicator sum. -/
theorem filter_len4 (a b c e sa sb sc se jl : ℕ) :
    (([(a, sa), (b, sb), (c, sc), (e, se)] : List (ℕ × ℕ)).filter
        (fun p => p.1 = jl)).length
      = (if a = jl then 1 else 0) + (if b = jl then 1 else 0)
        + (if c = jl then 1 else 0) + (if e = jl then 1 else 0) := by
  by_cases h1 : a = jl <;> by_cases h2 : b = jl <;> by_cases h3 : c = jl <;>
    by_cases h4 : e = jl <;>
    simp [List.filter, h1, h2, h3, h4]

/-- **The Prime Filtering master, `p = 5`.**  Four levels `≤ M` attaining
`0` and `M`, coprime slopes: some multiplier prime to `5` makes all four
elements safe in `ℤ/5^{M+1}`.  Dichotomy: `≤ 2` per level below `M`
(`pfl_compose`) or the `3+1` shape (`pfl_three_one`). -/
theorem pfl_master (a b c e sa sb sc se M : ℕ)
    (hsa : ¬ 5 ∣ sa) (hsb : ¬ 5 ∣ sb) (hsc : ¬ 5 ∣ sc) (hse : ¬ 5 ∣ se)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (heM : e ≤ M)
    (h0 : a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0)
    (hM : a = M ∨ b = M ∨ c = M ∨ e = M) :
    ∃ μ, ¬ 5 ∣ μ ∧
      5 ^ M ≤ cdist (5 * 5 ^ M) (μ * (5 ^ a * sa)) ∧
      5 ^ M ≤ cdist (5 * 5 ^ M) (μ * (5 ^ b * sb)) ∧
      5 ^ M ≤ cdist (5 * 5 ^ M) (μ * (5 ^ c * sc)) ∧
      5 ^ M ≤ cdist (5 * 5 ^ M) (μ * (5 ^ e * se)) := by
  by_cases hsh : ∀ jl, jl < M →
      ((([(a, sa), (b, sb), (c, sc), (e, se)] : List (ℕ × ℕ)).filter
        (fun p => p.1 = jl)).length ≤ 2)
  · -- at most two elements per level below the top: Prime Filtering composition
    obtain ⟨μ, hμ, hall⟩ := pfl_compose M [(a, sa), (b, sb), (c, sc), (e, se)]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hsa
        · exact hsb
        · exact hsc
        · exact hse)
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact haM
        · exact hbM
        · exact hcM
        · exact heM)
      hsh
    exact ⟨μ, hμ,
      hall (a, sa) (by simp), hall (b, sb) (by simp),
      hall (c, sc) (by simp), hall (e, se) (by simp)⟩
  · -- some level below the top holds three elements: the 3+1 shape
    push_neg at hsh
    obtain ⟨jl, hjl, hgt⟩ := hsh
    rw [filter_len4] at hgt
    have hM1 : 1 ≤ M := by omega
    by_cases hA : a = jl <;> by_cases hB : b = jl <;> by_cases hC : c = jl <;>
      by_cases hE : e = jl <;> simp [hA, hB, hC, hE] at hgt
    -- the five surviving cases: at least three of the four levels equal jl
    · -- a = b = c = e = jl < M: impossible, M is attained
      omega
    · -- a = b = c = jl, e ≠ jl: top is e, jl = 0
      have h1 : jl = 0 ∧ e = M := by omega
      obtain ⟨μ, hμ, HA, HB, HC, HT⟩ :=
        pfl_three_one M hM1 sa sb sc se hsa hsb hsc hse
      refine ⟨μ, hμ, ?_, ?_, ?_, ?_⟩
      · rw [show a = 0 by omega]; simpa using HA
      · rw [show b = 0 by omega]; simpa using HB
      · rw [show c = 0 by omega]; simpa using HC
      · rw [show e = M by omega]; exact HT
    · -- a = b = e = jl, c ≠ jl: top is c
      have h1 : jl = 0 ∧ c = M := by omega
      obtain ⟨μ, hμ, HA, HB, HE, HT⟩ :=
        pfl_three_one M hM1 sa sb se sc hsa hsb hse hsc
      refine ⟨μ, hμ, ?_, ?_, ?_, ?_⟩
      · rw [show a = 0 by omega]; simpa using HA
      · rw [show b = 0 by omega]; simpa using HB
      · rw [show c = M by omega]; exact HT
      · rw [show e = 0 by omega]; simpa using HE
    · -- a = c = e = jl, b ≠ jl: top is b
      have h1 : jl = 0 ∧ b = M := by omega
      obtain ⟨μ, hμ, HA, HC, HE, HT⟩ :=
        pfl_three_one M hM1 sa sc se sb hsa hsc hse hsb
      refine ⟨μ, hμ, ?_, ?_, ?_, ?_⟩
      · rw [show a = 0 by omega]; simpa using HA
      · rw [show b = M by omega]; exact HT
      · rw [show c = 0 by omega]; simpa using HC
      · rw [show e = 0 by omega]; simpa using HE
    · -- b = c = e = jl, a ≠ jl: top is a
      have h1 : jl = 0 ∧ a = M := by omega
      obtain ⟨μ, hμ, HB, HC, HE, HT⟩ :=
        pfl_three_one M hM1 sb sc se sa hsb hsc hse hsa
      refine ⟨μ, hμ, ?_, ?_, ?_, ?_⟩
      · rw [show a = M by omega]; exact HT
      · rw [show b = 0 by omega]; simpa using HB
      · rw [show c = 0 by omega]; simpa using HC
      · rw [show e = 0 by omega]; simpa using HE

end LRSpectrumFull
