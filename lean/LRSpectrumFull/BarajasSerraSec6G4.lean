import LRSpectrumFull.BarajasSerraSec6_3

/-!
# E6 session 20: G4 (the WLOG layer of Section 6) and case (a) for `m ≥ 2`

Five level-0 speeds (`7 ∤ d i`), arbitrary residues mod 7. The six VERIFIED subsection statements
`sec61`, ..., `sec66` assume a class normalisation relative to a base speed. Here:
* sign flip: `fl m x = x * (7^(m+1) - 1) ≡ -x (mod 7^(m+1))`, `R (fl m x) = - R x`, and
  `qq m (lam x) + qq m (lam (fl m x)) = 6` (`qq_neg`), so `q ∉ {0,6}` is flip-invariant;
* after flips every `R` lies in `{1,2,4}` (the index-2 subgroup of `(ZMod 7)ˣ`); relative to a
  suitable base the class counts are one of `(5,0,0), (4,1,0), (4,0,1), (3,2,0), (3,0,2), (3,1,1),
  (2,2,1)`, the hypotheses of the six subsections. No unit rescaling is needed: the subsection
  statements are relative to `R` of their first speed.
Falsified first: (development file, not part of this archive) (all 7776 residue 5-tuples, 0 failures; negative
controls: dropping any one of the seven patterns leaves 96 to 2880 tuples uncovered).
The 243-case dispatcher below was emitted by `e6s20/gen.py`.
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- a multiplier prime to 7 keeping every speed of `L` off `q ∈ {0, 6}`. -/
def Good (m : ℕ) (L : List ℕ) : Prop :=
  ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ L, qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6

theorem good_sub {m : ℕ} {L L' : List ℕ} (h : Good m L) (hs : ∀ x ∈ L', x ∈ L) : Good m L' := by
  obtain ⟨lam, hl, hx⟩ := h
  exact ⟨lam, hl, fun x hx' => hx x (hs x hx')⟩

set_option hygiene false in
macro "sub5" : tactic => `(tactic| (intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp))

theorem mod7_of_R {x y : ℕ} (hx : ¬ 7 ∣ x) (hy : ¬ 7 ∣ y) (h : R x = R y) : x % 7 = y % 7 := by
  rw [R_of_not_dvd hx, R_of_not_dvd hy] at h
  have := (ZMod.natCast_eq_natCast_iff' _ _ 7).mp h
  simpa [Nat.mod_mod] using this

/-! ## adapters: the six subsection statements in list form -/

theorem ad500 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = R a1) (r5 : R a5 = R a1) : Good m [a1, a2, a3, a4, a5] := by
  have c : ∀ i : Fin 5, (![a1, a2, a3, a4, a5] i) % 7 = a1 % 7 := by
    intro i; fin_cases i
    · rfl
    · exact mod7_of_R n2 n1 r2
    · exact mod7_of_R n3 n1 r3
    · exact mod7_of_R n4 n1 r4
    · exact mod7_of_R n5 n1 r5
  obtain ⟨lam, hl, h⟩ := sec61 m hm ![a1, a2, a3, a4, a5]
    (by intro i; fin_cases i <;> assumption) (fun i j => by rw [c i, c j])
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [h 0, h 1, h 2, h 3, h 4]

theorem ad41 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = R a1) (j : ZMod 7) (hj : j = 2 ∨ j = 4) (r5 : R a5 = j * R a1) :
    Good m [a1, a2, a3, a4, a5] := by
  have c : ∀ i : Fin 4, (![a1, a2, a3, a4] i) % 7 = a1 % 7 := by
    intro i; fin_cases i
    · rfl
    · exact mod7_of_R n2 n1 r2
    · exact mod7_of_R n3 n1 r3
    · exact mod7_of_R n4 n1 r4
  obtain ⟨lam, hl, h, h5⟩ := sec62 m hm ![a1, a2, a3, a4]
    (by intro i; fin_cases i <;> assumption) (fun i j => by rw [c i, c j]) a5 n5 j hj (by simpa using r5)
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [h 0, h 1, h 2, h 3, h5]

theorem ad410 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = R a1) (r5 : R a5 = 2 * R a1) : Good m [a1, a2, a3, a4, a5] :=
  ad41 m hm a1 a2 a3 a4 a5 n1 n2 n3 n4 n5 r2 r3 r4 2 (Or.inl rfl) r5

theorem ad401 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = R a1) (r5 : R a5 = 4 * R a1) : Good m [a1, a2, a3, a4, a5] :=
  ad41 m hm a1 a2 a3 a4 a5 n1 n2 n3 n4 n5 r2 r3 r4 4 (Or.inr rfl) r5

theorem cls3 {a1 a2 a3 : ℕ} (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2) (n3 : ¬ 7 ∣ a3) (r2 : R a2 = R a1)
    (r3 : R a3 = R a1) : ∀ i j : Fin 3, (![a1, a2, a3] i) % 7 = (![a1, a2, a3] j) % 7 := by
  have c : ∀ i : Fin 3, (![a1, a2, a3] i) % 7 = a1 % 7 := by
    intro i; fin_cases i
    · rfl
    · exact mod7_of_R n2 n1 r2
    · exact mod7_of_R n3 n1 r3
  intro i j; rw [c i, c j]

theorem nd3 {a1 a2 a3 : ℕ} (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2) (n3 : ¬ 7 ∣ a3) :
    ∀ i : Fin 3, ¬ 7 ∣ ![a1, a2, a3] i := by
  intro i; fin_cases i <;> assumption

theorem ad320 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = 2 * R a1) (r5 : R a5 = 2 * R a1) : Good m [a1, a2, a3, a4, a5] := by
  obtain ⟨lam, hl, h, h4, h5⟩ := sec64 m hm ![a1, a2, a3] (nd3 n1 n2 n3) (cls3 n1 n2 n3 r2 r3)
    a4 a5 n4 n5 (by simpa using r4) (by simpa using r5)
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [h 0, h 1, h 2, h4, h5]

theorem ad302 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = 4 * R a1) (r5 : R a5 = 4 * R a1) : Good m [a1, a2, a3, a4, a5] := by
  obtain ⟨lam, hl, h, h4, h5⟩ := sec65 m hm ![a1, a2, a3] (nd3 n1 n2 n3) (cls3 n1 n2 n3 r2 r3)
    a4 a5 n4 n5 (by simpa using r4) (by simpa using r5)
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [h 0, h 1, h 2, h4, h5]

theorem ad311 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = R a1)
    (r4 : R a4 = 2 * R a1) (r5 : R a5 = 4 * R a1) : Good m [a1, a2, a3, a4, a5] := by
  obtain ⟨lam, hl, h, h4, h5⟩ := sec63 m hm ![a1, a2, a3] (nd3 n1 n2 n3) (cls3 n1 n2 n3 r2 r3)
    a4 a5 n4 n5 (by simpa using r4) (by simpa using r5)
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [h 0, h 1, h 2, h4, h5]

theorem ad221 (m : ℕ) (hm : 2 ≤ m) (a1 a2 a3 a4 a5 : ℕ) (n1 : ¬ 7 ∣ a1) (n2 : ¬ 7 ∣ a2)
    (n3 : ¬ 7 ∣ a3) (n4 : ¬ 7 ∣ a4) (n5 : ¬ 7 ∣ a5) (r2 : R a2 = R a1) (r3 : R a3 = 2 * R a1)
    (r4 : R a4 = 2 * R a1) (r5 : R a5 = 4 * R a1) : Good m [a1, a2, a3, a4, a5] :=
  sec66 m hm a1 a2 a3 a4 a5 n1 n2 n3 n4 n5 r2 r3 r4 r5

/-! ## the dispatcher: all `R` in `{1, 2, 4}` -/

set_option maxHeartbeats 4000000 in
theorem good124 (m : ℕ) (hm : 2 ≤ m) (y0 y1 y2 y3 y4 : ℕ) (n0 : ¬ 7 ∣ y0) (n1 : ¬ 7 ∣ y1)
    (n2 : ¬ 7 ∣ y2) (n3 : ¬ 7 ∣ y3) (n4 : ¬ 7 ∣ y4)
    (h0 : R y0 = 1 ∨ R y0 = 2 ∨ R y0 = 4) (h1 : R y1 = 1 ∨ R y1 = 2 ∨ R y1 = 4)
    (h2 : R y2 = 1 ∨ R y2 = 2 ∨ R y2 = 4) (h3 : R y3 = 1 ∨ R y3 = 2 ∨ R y3 = 4)
    (h4 : R y4 = 1 ∨ R y4 = 2 ∨ R y4 = 4) : Good m [y0, y1, y2, y3, y4] := by
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4
  · exact good_sub (ad500 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y1 y2 n3 n4 n0 n1 n2 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y3 y2 n0 n1 n4 n3 n2 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y1 y3 n2 n4 n0 n1 n3 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y1 y4 n2 n3 n0 n1 n4 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y3 y4 n0 n2 n1 n3 n4 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y4 y3 n0 n2 n1 n4 n3 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y2 y1 n3 n4 n0 n2 n1 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h1, h3] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y2 y4 n0 n3 n1 n2 n4 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y2 y3 n0 n4 n1 n2 n3 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y3 y0 n1 n2 n4 n3 n0 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y4 y2 n0 n3 n1 n4 n2 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y3 y1 n2 n4 n0 n3 n1 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y3 y2 n0 n4 n1 n3 n2 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y2 y0 n1 n3 n4 n2 n0 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y2 y4 y0 n1 n3 n2 n4 n0 (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y4 y1 n2 n3 n0 n4 n1 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y2 y3 y0 n1 n4 n2 n3 n0 (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y3 y1 n0 n2 n4 n3 n1 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y2 y3 n1 n4 n0 n2 n3 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y2 y4 n1 n3 n0 n2 n4 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y2 y1 n0 n3 n4 n2 n1 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y2 y4 y1 n0 n3 n2 n4 n1 (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y3 y2 n1 n4 n0 n3 n2 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y2 y3 y1 n0 n4 n2 n3 n1 (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y1 y0 n2 n3 n4 n1 n0 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y1 y4 y0 n2 n3 n1 n4 n0 (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y4 y2 n1 n3 n0 n4 n2 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y1 y3 y0 n2 n4 n1 n3 n0 (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y3 y4 n1 n2 n0 n3 n4 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y4 y3 n1 n2 n0 n4 n3 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y1 y2 y0 n3 n4 n1 n2 n0 (by rw [h4, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h0, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y3 y4 n1 n2 n0 n3 n4 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y4 y3 n1 n2 n0 n4 n3 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y1 y2 y0 n3 n4 n1 n2 n0 (by rw [h4, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h0, h3] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y2 y4 n1 n3 n0 n2 n4 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y2 y3 n1 n4 n0 n2 n3 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y3 y1 n0 n2 n4 n3 n1 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y4 y2 n1 n3 n0 n4 n2 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y1 y3 y0 n2 n4 n1 n3 n0 (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y3 y2 n1 n4 n0 n3 n2 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y2 y1 n0 n3 n4 n2 n1 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y2 y4 y1 n0 n3 n2 n4 n1 (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y1 y4 y0 n2 n3 n1 n4 n0 (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y2 y3 y1 n0 n4 n2 n3 n1 (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y1 y0 n2 n3 n4 n1 n0 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y1 y4 n2 n3 n0 n1 n4 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y1 y3 n2 n4 n0 n1 n3 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y3 y2 n0 n1 n4 n3 n2 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad500 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y1 y2 n3 n4 n0 n1 n2 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y4 y1 n2 n3 n0 n4 n1 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y2 y3 y0 n1 n4 n2 n3 n0 (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y3 y1 n2 n4 n0 n3 n1 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y4 y2 n0 n3 n1 n4 n2 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y2 y4 y0 n1 n3 n2 n4 n0 (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y3 y2 n0 n4 n1 n3 n2 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y2 y0 n1 n3 n4 n2 n0 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y2 y1 n3 n4 n0 n2 n1 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h1, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y4 y3 n0 n2 n1 n4 n3 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y3 y4 n0 n2 n1 n3 n4 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y2 y3 n0 n4 n1 n2 n3 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y3 y0 n1 n2 n4 n3 n0 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y2 y4 n0 n3 n1 n2 n4 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y3 y0 n1 n2 n4 n3 n0 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y2 y3 n0 n4 n1 n2 n3 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y2 y4 n0 n3 n1 n2 n4 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y2 y0 n1 n3 n4 n2 n0 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y2 y4 y0 n1 n3 n2 n4 n0 (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y1 y3 y2 n0 n4 n1 n3 n2 (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y2 y3 y0 n1 n4 n2 n3 n0 (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y4 y1 n2 n3 n0 n4 n1 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y1 y4 y2 n0 n3 n1 n4 n2 (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y3 y1 n2 n4 n0 n3 n1 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y3 y4 n0 n2 n1 n3 n4 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y1 y4 y3 n0 n2 n1 n4 n3 (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y2 y1 n3 n4 n0 n2 n1 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h1, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y2 y3 y4 y1 y0 n2 n3 n4 n1 n0 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y1 y4 y0 n2 n3 n1 n4 n0 (by rw [h3, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y4 y2 y3 y1 n0 n4 n2 n3 n1 (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y1 y3 y0 n2 n4 n1 n3 n0 (by rw [h4, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y4 y2 n1 n3 n0 n4 n2 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y3 y2 y4 y1 n0 n3 n2 n4 n1 (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y3 y2 n1 n4 n0 n3 n2 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y3 y4 y2 y1 n0 n3 n4 n2 n1 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y1 y2 y0 n3 n4 n1 n2 n0 (by rw [h4, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide) (by rw [h0, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y4 y3 n1 n2 n0 n4 n3 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y1 y2 y3 y4 y0 n1 n2 n3 n4 n0 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y3 y0 y4 n1 n2 n3 n0 n4 (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y2 y0 y3 y4 n1 n2 n0 n3 n4 (by rw [h2, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y2 y4 y0 y3 n1 n2 n4 n0 n3 (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y3 y4 y1 y2 n0 n3 n4 n1 n2 (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y4 y0 y2 y3 n1 n4 n0 n2 n3 (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h3, h1] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y4 y3 y1 n0 n2 n4 n3 n1 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y1 y3 y0 y2 y4 n1 n3 n0 n2 n4 (by rw [h3, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide) (by rw [h4, h1] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y1 y3 y4 y0 y2 n1 n3 n4 n0 n2 (by rw [h3, h1] <;> decide) (by rw [h4, h1] <;> decide) (by rw [h0, h1] <;> decide) (by rw [h2, h1] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y4 y1 y3 n0 n2 n4 n1 n3 (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y2 y3 y1 y4 n0 n2 n3 n1 n4 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y2 y3 y4 y1 n0 n2 n3 n4 n1 (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h1, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y3 y4 y0 y1 y2 n3 n4 n0 n1 n2 (by rw [h4, h3] <;> decide) (by rw [h0, h3] <;> decide) (by rw [h1, h3] <;> decide) (by rw [h2, h3] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y4 y0 y1 y3 n2 n4 n0 n1 n3 (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h3, h2] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y4 y3 y2 n0 n1 n4 n3 n2 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad221 m hm y2 y3 y0 y1 y4 n2 n3 n0 n1 n4 (by rw [h3, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide) (by rw [h4, h2] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y2 y3 y4 y0 y1 n2 n3 n4 n0 n1 (by rw [h3, h2] <;> decide) (by rw [h4, h2] <;> decide) (by rw [h0, h2] <;> decide) (by rw [h1, h2] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y4 y2 y3 n0 n1 n4 n2 n3 (by rw [h1, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y3 y2 y4 n0 n1 n3 n2 n4 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y3 y4 y2 n0 n1 n3 n4 n2 (by rw [h1, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h2, h0] <;> decide)) (by sub5)
  · exact good_sub (ad320 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad311 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad302 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y4 y3 n0 n1 n2 n4 n3 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h4, h0] <;> decide) (by rw [h3, h0] <;> decide)) (by sub5)
  · exact good_sub (ad410 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad401 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)
  · exact good_sub (ad500 m hm y0 y1 y2 y3 y4 n0 n1 n2 n3 n4 (by rw [h1, h0] <;> decide) (by rw [h2, h0] <;> decide) (by rw [h3, h0] <;> decide) (by rw [h4, h0] <;> decide)) (by sub5)

/-! ## sign flip -/

/-- `fl m x ≡ -x (mod 7^(m+1))`. -/
def fl (m x : ℕ) : ℕ := x * (7 ^ (m + 1) - 1)

theorem one_le_N (m : ℕ) : 1 ≤ 7 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)

theorem not_dvd_fl (m : ℕ) {x : ℕ} (hx : ¬ 7 ∣ x) : ¬ 7 ∣ fl m x := by
  have h7 : ¬ 7 ∣ 7 ^ (m + 1) - 1 := by
    intro h
    have h1 : 7 ∣ 7 ^ (m + 1) := dvd_pow_self 7 (Nat.succ_ne_zero m)
    have h2 := Nat.dvd_sub h1 h
    have h3 : 7 ^ (m + 1) - (7 ^ (m + 1) - 1) = 1 := by have := one_le_N m; omega
    rw [h3] at h2; omega
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
  exacts [hx h, h7 h]

theorem R_fl (m : ℕ) {x : ℕ} (hx : ¬ 7 ∣ x) : R (fl m x) = - R x := by
  rw [R_of_not_dvd (not_dvd_fl m hx), R_of_not_dvd hx, ZMod.natCast_mod, ZMod.natCast_mod]
  unfold fl
  rw [Nat.cast_mul, Nat.cast_sub (one_le_N m)]
  have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
  push_cast
  rw [show ((7 : ZMod 7)) = ((7 : ℕ) : ZMod 7) by norm_num, h7, zero_pow (Nat.succ_ne_zero _)]
  ring

theorem qq_fl (m lam x : ℕ) (hm : 1 ≤ m) (hl : Nat.Coprime lam 7) (hx : ¬ 7 ∣ x) :
    qq m (lam * x) + qq m (lam * fl m x) = 6 := by
  apply qq_neg
  · have : lam * x + lam * fl m x = lam * x * 7 ^ (m + 1) := by
      unfold fl
      have h1 := one_le_N m
      calc lam * x + lam * (x * (7 ^ (m + 1) - 1)) = lam * x * (1 + (7 ^ (m + 1) - 1)) := by ring
        _ = lam * x * 7 ^ (m + 1) := by rw [Nat.add_sub_cancel' h1]
    rw [this]; exact (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_left _ _)
  · intro h
    have h7 : 7 ∣ 7 ^ m := dvd_pow_self 7 (by omega)
    exact not_dvd_mul hl (not_dvd_fl m hx) (h7.trans h)

theorem pick (m : ℕ) {x : ℕ} (hx : ¬ 7 ∣ x) :
    ∃ y, (y = x ∨ y = fl m x) ∧ ¬ 7 ∣ y ∧ (R y = 1 ∨ R y = 2 ∨ R y = 4) := by
  have hR := R_fl m hx
  rw [R_of_not_dvd hx] at hR
  have hRx := R_of_not_dvd hx
  have hk : x % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hk0 : x % 7 ≠ 0 := fun h => hx (Nat.dvd_of_mod_eq_zero h)
  generalize x % 7 = k at hR hRx hk hk0
  interval_cases k
  all_goals first
    | exact absurd rfl hk0
    | exact ⟨x, Or.inl rfl, hx, by rw [hRx]; decide⟩
    | exact ⟨fl m x, Or.inr rfl, not_dvd_fl m hx, by rw [hR]; decide⟩

theorem transfer {m lam x y : ℕ} (hm : 1 ≤ m) (hl : Nat.Coprime lam 7) (hx : ¬ 7 ∣ x)
    (hy : y = x ∨ y = fl m x) (hq : qq m (lam * y) ≠ 0 ∧ qq m (lam * y) ≠ 6) :
    qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  rcases hy with rfl | rfl
  · exact hq
  · have := qq_fl m lam x hm hl hx; omega

/-- **G4**: any five level-0 speeds admit a multiplier prime to 7 keeping all off `q ∈ {0,6}`. -/
theorem g4 (m : ℕ) (hm : 2 ≤ m) (d0 d1 d2 d3 d4 : ℕ) (n0 : ¬ 7 ∣ d0) (n1 : ¬ 7 ∣ d1)
    (n2 : ¬ 7 ∣ d2) (n3 : ¬ 7 ∣ d3) (n4 : ¬ 7 ∣ d4) : Good m [d0, d1, d2, d3, d4] := by
  obtain ⟨y0, e0, m0, h0⟩ := pick m n0
  obtain ⟨y1, e1, m1, h1⟩ := pick m n1
  obtain ⟨y2, e2, m2, h2⟩ := pick m n2
  obtain ⟨y3, e3, m3, h3⟩ := pick m n3
  obtain ⟨y4, e4, m4, h4⟩ := pick m n4
  obtain ⟨lam, hl, h⟩ := good124 m hm y0 y1 y2 y3 y4 m0 m1 m2 m3 m4 h0 h1 h2 h3 h4
  have hm1 : 1 ≤ m := by omega
  refine ⟨lam, hl, ?_⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact transfer hm1 hl n0 e0 (h y0 (by simp))
  · exact transfer hm1 hl n1 e1 (h y1 (by simp))
  · exact transfer hm1 hl n2 e2 (h y2 (by simp))
  · exact transfer hm1 hl n3 e3 (h y3 (by simp))
  · exact transfer hm1 hl n4 e4 (h y4 (by simp))

/-- **Case (a), `m ≥ 2`**: five level-0 speeds and one top speed (`nu = m`). -/
theorem case_a_ge2 (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℕ) (hd : ∀ i, ¬ 7 ∣ d i) (d6 : ℕ)
    (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 : ℝ) / 7 ≤ nearestIntDist (t * d i)) ∧
      (1 : ℝ) / 7 ≤ nearestIntDist (t * d6) := by
  obtain ⟨lam, hl, hg⟩ := g4 m hm (d 0) (d 1) (d 2) (d 3) (d 4) (hd 0) (hd 1) (hd 2) (hd 3) (hd 4)
  obtain ⟨t, ht, hall⟩ := witness_of_lam m lam hl [d 0, d 1, d 2, d 3, d 4] [d6] hg
    (by intro x hx; simp at hx; subst hx; exact ⟨h6, h6m⟩)
  refine ⟨t, ht, fun i => hall _ ?_, hall _ (by simp)⟩
  fin_cases i <;> simp

end LRSpectrumFull.BarajasSerra.Sec6
