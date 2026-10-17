/-
# The CASE-route assembly: δ₂(4) ≤ 3/14 from a normal-form band-gap

Wires the machine-checked front-end `nf_exists_sat` (every saturated 2-dim band
reduces to a `jkForm`) into the top-level supremum `delta2sat 3 = sSup (satBandSet 3)`.

The result: `δ₂(4) ≤ 3/14` follows from a **band-gap statement about normal forms
only** — `JkFormBandGap`: every `jkForm` with `mD < 1/4` has `mD ≤ 3/14`. This is a
sorry-free reduction; `JkFormBandGap` is the crisp remaining target, which splits
(`jkFormBandGap_of`) into:

* `hDeg` — the **degenerate** forms (some of `b,c,e,f` zero: Cases B/C/D). NB this
  is *not* a trivial cascade in the `mD` convention — a zero column entry does not
  strip (OBSTACLE 1); it needs a direct/modular witness (cf. `mD_const_col`, the
  `caseD` witness `![0,1/2]`).
* `hA` — the **non-degenerate** Case A (all of `b,c,e,f` nonzero), where the cascade
  bounds both `L₃` triples to `≤ 6`, finitizing into `CaseAEnumerate`.

No `sorry`.
-/
import LRSpectrumFull.NormalFormExists
import LRSpectrumFull.Saturation
import LRSpectrumFull.CaseA
import LRSpectrumFull.TripleNormalize

namespace LRSpectrumFull
open Finset

/-- The band-gap statement for **normal forms only**: every `jkForm` whose `mD`
lies below `1/4` in fact lies at or below `3/14` (the gap `(3/14, 1/4)` is empty
on normal forms). -/
def JkFormBandGap : Prop :=
  ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 →
    mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14

/-- **CASE-route assembly.** `δ₂(4) ≤ 3/14` reduces to the normal-form band-gap.
Every saturated band in the set is `mD`-equal to a `jkForm` with `a,d ≠ 0`
(`nf_exists_sat`), and membership supplies the `mD < 1/4` hypothesis. -/
theorem delta2sat_le_of_jkFormBandGap (h : JkFormBandGap) : delta2sat 3 ≤ 3 / 14 := by
  apply csSup_le ⟨mD Lsat, mD_Lsat_mem⟩
  rintro x ⟨M, hsat, hmD, hlt⟩
  obtain ⟨a, b, c, d, e, f, ha, hd, hjk⟩ := nf_exists_sat M hsat
  rw [← hmD, hjk]
  refine h a b c d e f ha hd ?_
  rw [← hjk, hmD]
  exact hlt

/-- The band-gap splits into the degenerate forms (Cases B/C/D) and the
fully-nondegenerate Case A. Both carry `a, d ≠ 0` (so both columns'
repeated entries are nonzero). -/
theorem jkFormBandGap_of
    (hDeg : ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → (b = 0 ∨ c = 0 ∨ e = 0 ∨ f = 0) →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14)
    (hA : ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 → f ≠ 0 →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14) :
    JkFormBandGap := by
  intro a b c d e f ha hd hlt
  by_cases hdeg : b = 0 ∨ c = 0 ∨ e = 0 ∨ f = 0
  · exact hDeg a b c d e f ha hd hdeg hlt
  · push_neg at hdeg
    exact hA a b c d e f ha hd hdeg.1 hdeg.2.1 hdeg.2.2.1 hdeg.2.2.2 hlt

/-! ## Case A reduces to the `(1,2,3)×(1,2,3)` kernel

Everything non-`Shaped123` is killed by the n=3 gap `D_triple_le`; what remains
is the kernel where *both* generator triples are `g·(1,2,3)`-shaped. -/

/-- Sign-evenness of `nearestIntDist` collapses the `v`-column's `(d,-d)` pair:
`D ![d,-d,e,f] = D ![d,d,e,f]`. -/
theorem D_neg1_4 (d e f : ℤ) : D ![d, -d, e, f] = D ![d, d, e, f] := by
  have e0 : (⟨0, by omega⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨1, by omega⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨2, by omega⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨3, by omega⟩ : Fin 4) = 3 := by decide
  have hg : gap ![d, -d, e, f] = gap ![d, d, e, f] := by
    funext t
    unfold gap
    congr 1
    funext i
    fin_cases i <;>
      simp only [e0, e1, e2, e3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Int.cast_neg, neg_mul,
        nearestIntDist_neg]
  unfold D ML
  rw [hg]

/-- **Cascade to the `v`-triple.** `mD (jkForm …) ≤ D ![d,e,f]` — cascade to
column 1, then `(d,-d)` collapses (`D_neg1_4`) and the duplicate `d` drops
(`D_dup`). The `v`-side analogue of `mD_jkForm_le_D_utriple`. -/
theorem mD_jkForm_le_D_vtriple (a b c d e f : ℤ) :
    mD (jkForm a b c d e f) ≤ D ![d, e, f] := by
  have h := mD_le_col (jkForm a b c d e f) 1
  rw [jkForm_col1, D_neg1_4, D_dup] at h
  exact h

/-- **Case A reduces to the kernel.** Granting the `(1,2,3)×(1,2,3)` kernel
(both triples `Shaped123`, `mD < 1/4`), every fully-nondegenerate Case-A form is
in the band-gap: a non-`Shaped123` `u`- or `v`-triple is excluded by `D_triple_le`. -/
theorem caseA_bandGap_of_kernel
    (hKer : ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 → f ≠ 0 →
      Shaped123 a b c → Shaped123 d e f →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14) :
    ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 → f ≠ 0 →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14 := by
  intro a b c d e f ha hd hb hc he hf hlt
  by_cases hu : Shaped123 a b c
  · by_cases hv : Shaped123 d e f
    · exact hKer a b c d e f ha hd hb hc he hf hu hv hlt
    · exact le_trans (mD_jkForm_le_D_vtriple a b c d e f) (D_triple_le d e f hd he hf hv)
  · exact le_trans (mD_jkForm_le_D_utriple a b c d e f) (D_triple_le a b c ha hb hc hu)

/-! ## Column scaling: reduce `g·(1,2,3)` to the primitive `(1,2,3)` kernel

`mD` is invariant under scaling a generator triple by a nonzero `g` (the real
plane is unchanged) — `mD_colMul` with a diagonal matrix. This lets the `hKer`
target be stated on the *primitive* `(1,2,3)×(1,2,3)` forms. -/

/-- Scaling the `u`-triple by `g ≠ 0` preserves `mD`. -/
theorem mD_jkForm_scale_col0 (a b c d e f g : ℤ) (hg : g ≠ 0) :
    mD (jkForm (g * a) (g * b) (g * c) d e f) = mD (jkForm a b c d e f) := by
  have e0 : (⟨0, by omega⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨1, by omega⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨2, by omega⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨3, by omega⟩ : Fin 4) = 3 := by decide
  have c0 : (⟨0, by omega⟩ : Fin 2) = 0 := by decide
  have c1 : (⟨1, by omega⟩ : Fin 2) = 1 := by decide
  have heq : jkForm (g * a) (g * b) (g * c) d e f
      = colMul (jkForm a b c d e f) ![![g, 0], ![0, 1]] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [colMul, jkForm, e0, e1, e2, e3, c0, c1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] <;> ring
  rw [heq]
  exact mD_colMul (jkForm a b c d e f) ![![g, 0], ![0, 1]] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have : ((g : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hg
    simpa using this)

/-- Scaling the `v`-triple by `g ≠ 0` preserves `mD`. -/
theorem mD_jkForm_scale_col1 (a b c d e f g : ℤ) (hg : g ≠ 0) :
    mD (jkForm a b c (g * d) (g * e) (g * f)) = mD (jkForm a b c d e f) := by
  have e0 : (⟨0, by omega⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨1, by omega⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨2, by omega⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨3, by omega⟩ : Fin 4) = 3 := by decide
  have c0 : (⟨0, by omega⟩ : Fin 2) = 0 := by decide
  have c1 : (⟨1, by omega⟩ : Fin 2) = 1 := by decide
  have heq : jkForm a b c (g * d) (g * e) (g * f)
      = colMul (jkForm a b c d e f) ![![1, 0], ![0, g]] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [colMul, jkForm, e0, e1, e2, e3, c0, c1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] <;> ring
  rw [heq]
  exact mD_colMul (jkForm a b c d e f) ![![1, 0], ![0, g]] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have : ((g : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hg
    simpa using this)

/-- A `Shaped123` triple factors as `g · (primitive (1,2,3)-triple)`. -/
theorem shaped123_factor {a b c : ℤ} (h : Shaped123 a b c) :
    ∃ g : ℤ, 0 < g ∧ g ∣ a ∧ g ∣ b ∧ g ∣ c ∧
      ({|a / g|, |b / g|, |c / g|} : Multiset ℤ) = {1, 2, 3} := by
  obtain ⟨g, hg, hm⟩ := h
  have hdvdabs : ∀ x ∈ ({|a|, |b|, |c|} : Multiset ℤ), g ∣ x := by
    intro x hx
    rw [hm] at hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with h | h | h
    · rw [h]
    · rw [h]; exact dvd_mul_left g 2
    · rw [h]; exact dvd_mul_left g 3
  have dvd_of : ∀ x : ℤ, g ∣ |x| → g ∣ x := by
    intro x hx
    rcases abs_choice x with hc | hc
    · rwa [hc] at hx
    · rw [hc] at hx; exact dvd_neg.mp hx
  have ga : g ∣ a := dvd_of a (hdvdabs _ (by simp))
  have gb : g ∣ b := dvd_of b (hdvdabs _ (by simp))
  have gc : g ∣ c := dvd_of c (hdvdabs _ (by simp))
  refine ⟨g, hg, ga, gb, gc, ?_⟩
  have habs : ∀ x : ℤ, g ∣ x → g * |x / g| = |x| := by
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    rw [Int.mul_ediv_cancel_left _ hg.ne', abs_mul, abs_of_pos hg]
  have hinj : Function.Injective (fun x : ℤ => g * x) := fun x y h => mul_left_cancel₀ hg.ne' h
  apply Multiset.map_injective hinj
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hm ⊢
  rw [habs a ga, habs b gb, habs c gc, hm, mul_one, mul_comm g 2, mul_comm g 3]

/-- **`hKer` reduces to the finite primitive kernel.** Granting the `(1,2,3)×(1,2,3)`
band-gap on *primitive* triples (`{|a|,|b|,|c|} = {1,2,3}`), the full kernel follows
by scaling each `Shaped123` triple down by its common factor `g`. -/
theorem hKer_of_prim
    (hPrim : ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 → f ≠ 0 →
      ({|a|, |b|, |c|} : Multiset ℤ) = {1, 2, 3} → ({|d|, |e|, |f|} : Multiset ℤ) = {1, 2, 3} →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14) :
    ∀ a b c d e f : ℤ, a ≠ 0 → d ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 → f ≠ 0 →
      Shaped123 a b c → Shaped123 d e f →
      mD (jkForm a b c d e f) < 1 / 4 → mD (jkForm a b c d e f) ≤ 3 / 14 := by
  intro a b c d e f ha hd hb hc he hf hu hv hlt
  obtain ⟨g, hg, ga, gb, gc, habc⟩ := shaped123_factor hu
  obtain ⟨g', hg', gd, ge, gf, hdef⟩ := shaped123_factor hv
  set a' := a / g; set b' := b / g; set c' := c / g
  set d' := d / g'; set e' := e / g'; set f' := f / g'
  have hae : a = g * a' := (Int.mul_ediv_cancel' ga).symm
  have hbe : b = g * b' := (Int.mul_ediv_cancel' gb).symm
  have hce : c = g * c' := (Int.mul_ediv_cancel' gc).symm
  have hde : d = g' * d' := (Int.mul_ediv_cancel' gd).symm
  have hee : e = g' * e' := (Int.mul_ediv_cancel' ge).symm
  have hfe : f = g' * f' := (Int.mul_ediv_cancel' gf).symm
  have key : mD (jkForm a b c d e f) = mD (jkForm a' b' c' d' e' f') := by
    rw [hae, hbe, hce, mD_jkForm_scale_col0 a' b' c' d e f g hg.ne',
        hde, hee, hfe, mD_jkForm_scale_col1 a' b' c' d' e' f' g' hg'.ne']
  rw [key]
  refine hPrim a' b' c' d' e' f' ?_ ?_ ?_ ?_ ?_ ?_ habc hdef ?_
  · intro h; exact ha (by rw [hae, h, mul_zero])
  · intro h; exact hd (by rw [hde, h, mul_zero])
  · intro h; exact hb (by rw [hbe, h, mul_zero])
  · intro h; exact hc (by rw [hce, h, mul_zero])
  · intro h; exact he (by rw [hee, h, mul_zero])
  · intro h; exact hf (by rw [hfe, h, mul_zero])
  · rw [← key]; exact hlt

-- axiom audit
#print axioms delta2sat_le_of_jkFormBandGap
#print axioms jkFormBandGap_of
#print axioms caseA_bandGap_of_kernel
#print axioms mD_jkForm_scale_col0
#print axioms hKer_of_prim

end LRSpectrumFull
