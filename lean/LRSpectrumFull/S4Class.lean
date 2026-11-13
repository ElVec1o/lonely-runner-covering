/-
# S4 range: the Bool class test `classB` and its soundness

`classB a b c d : Bool` is the OR of seven cheap integer tests, each mirroring a census class (R5, G24, P3, T,
QGen (q = 4 is Q4), Q3, R7) and each sound by one of the class theorems
`R5_core`, `G24`, `P3`, `T`, `QGen`, `Q3_ndvd`, `R7_partial`.  No data is consulted.
`classB_sound : 0 < a → a < b → b < c → c < d → classB a b c d = true → S4 ![a,b,c,d]`.
The role assignments are all taken from a short list of index quadruples (`anyPerm`), so that no
permutation of the speeds has to be handled per class.
-/
import LRSpectrumFull.S4Perm
import LRSpectrumFull.RFiveCor
import LRSpectrumFull.RQThree
import LRSpectrumFull.RQGen
import LRSpectrumFull.RQT
import LRSpectrumFull.RQG24
import LRSpectrumFull.RSevenFinal
import LRSpectrumFull.RQ3Final

namespace LRSpectrumFull
namespace D0

/-- `anyLt n f`: some `q < n` has `f q = true` -/
def anyLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n + 1, f => f n || anyLt n f

theorem anyLt_true {n : ℕ} {f : ℕ → Bool} (h : anyLt n f = true) : ∃ q, q < n ∧ f q = true := by
  induction n with
  | zero => simp [anyLt] at h
  | succ n ih =>
    simp only [anyLt, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨q, hq, hf⟩ := ih h
      exact ⟨q, Nat.lt_succ_of_lt hq, hf⟩

/-- shared helpers: vectors of four positive distinct speeds -/
theorem hfun_pos {x y u w : ℕ} (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hw : 0 < w) :
    ∀ i, 0 < (![x, y, u, w] : Fin 4 → ℕ) i := vec_pos hx hy hu hw

/-! ### the seven Bool tests (scalar form) -/

/-- R5: some speed divisible by 5, some not -/
def r5B (a b c d : ℕ) : Bool :=
  decide ((a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0 ∨ d % 5 = 0) ∧ (a % 5 ≠ 0 ∨ b % 5 ≠ 0 ∨ c % 5 ≠ 0 ∨ d % 5 ≠ 0))

/-- P3, the slow triple is `x y u` and the free speed is `w` (`q` = the gcd of the triple) -/
def fP3 (x y u w : ℕ) : Bool :=
  decide (2 ≤ Nat.gcd (Nat.gcd x y) u ∧ ¬ Nat.gcd (Nat.gcd x y) u ∣ w)

/-- non-resonance of the slow speed `s` against the pair `a b` -/
def nonresB (s a b : ℕ) : Bool := decide (s ≠ a + b ∧ a ≠ b + s ∧ b ≠ a + s)

/-- T: slow pair `x y`, free pair `u w`, some `q ≥ 6` dividing `gcd x y` and coprime to `u` and `w` -/
def fT (x y u w : ℕ) : Bool :=
  decide (6 ≤ Nat.gcd x y) &&
  anyLt (Nat.gcd x y + 1) (fun q => decide (6 ≤ q ∧ q ∣ Nat.gcd x y ∧ Nat.Coprime u q ∧ Nat.Coprime w q))

/-- QGen (q = 4 is Q4) -/
def fQ (x y u w : ℕ) : Bool :=
  decide (4 ≤ Nat.gcd x y) && nonresB x u w && nonresB y u w &&
  anyLt (Nat.gcd x y + 1) (fun q => decide (4 ≤ q ∧ q ∣ Nat.gcd x y ∧ Nat.Coprime u q ∧ Nat.Coprime w q ∧
    (u % q = w % q ∨ (u + w) % q = 0)))

/-- Q3: `x y` multiples of 3, `u w` not, both slow speeds non-resonant -/
def fQ3 (x y u w : ℕ) : Bool :=
  decide (x % 3 = 0 ∧ y % 3 = 0 ∧ u % 3 ≠ 0 ∧ w % 3 ≠ 0) && nonresB x u w && nonresB y u w

/-- G24: `x y` odd, `u ≡ 2`, `w ≡ 0 (mod 4)`, `w` non-resonant against `x y` -/
def fG24 (x y u w : ℕ) : Bool :=
  decide (x % 2 = 1 ∧ y % 2 = 1 ∧ u % 4 = 2 ∧ w % 4 = 0) && nonresB w x y

/-- `x ~ y` modulo 7: congruent up to sign -/
def Sim7 (x y : ℕ) : Prop := x % 7 = y % 7 ∨ (x + y) % 7 = 0

instance (x y : ℕ) : Decidable (Sim7 x y) := by unfold Sim7; infer_instance

/-- R7 (patterns A and B with the exclusion clause), `x` is the multiple of 7, `y` the odd one out -/
def fR7 (x y u w : ℕ) : Bool :=
  decide (x % 7 = 0 ∧ y % 7 ≠ 0 ∧ u % 7 ≠ 0 ∧ w % 7 ≠ 0 ∧
    ((Sim7 y u ∧ Sim7 y w) ∨
     (Sim7 u w ∧ ¬ Sim7 y u ∧
       ¬ ((x = u + w ∨ u = w + x ∨ w = u + x) ∧ (u % 7 = (3 * y) % 7 ∨ (u + 3 * y) % 7 = 0)))))

/-- slow-pair classes -/
def fPair (x y u w : ℕ) : Bool := fT x y u w || fQ x y u w || fQ3 x y u w

/-- index quadruples: slow pair (first two) among four, free pair the rest -/
def pairL : List Perm4 := [(0,1,2,3), (0,2,1,3), (0,3,1,2), (1,2,0,3), (1,3,0,2), (2,3,0,1)]
/-- P3: the free speed is last -/
def p3L : List Perm4 := [(0,1,2,3), (0,1,3,2), (0,2,3,1), (1,2,3,0)]
/-- G24: `(a,b,e,s)` -/
def g24L : List Perm4 := [(2,3,1,0), (1,3,2,0), (1,2,3,0), (2,3,0,1), (0,3,2,1), (0,2,3,1),
  (1,3,0,2), (0,3,1,2), (0,1,3,2), (1,2,0,3), (0,2,1,3), (0,1,2,3)]
/-- R7: `(s,a,b,c)` -/
def r7L : List Perm4 := [(0,1,2,3), (0,2,1,3), (0,3,1,2), (1,0,2,3), (1,2,0,3), (1,3,0,2),
  (2,0,1,3), (2,1,0,3), (2,3,0,1), (3,0,1,2), (3,1,0,2), (3,2,0,1)]

theorem pairL_ok : ∀ p ∈ pairL, IsPerm p := by decide
theorem p3L_ok : ∀ p ∈ p3L, IsPerm p := by decide
theorem g24L_ok : ∀ p ∈ g24L, IsPerm p := by decide
theorem r7L_ok : ∀ p ∈ r7L, IsPerm p := by decide

/-- THE class test.  Cheap tests first. -/
def classB (a b c d : ℕ) : Bool :=
  r5B a b c d || anyPerm g24L fG24 a b c d || anyPerm p3L fP3 a b c d ||
  anyPerm pairL fPair a b c d || anyPerm r7L fR7 a b c d

/-! ### soundness of each scalar test -/

theorem nonresB_true {s a b : ℕ} (h : nonresB s a b = true) : s ≠ a + b ∧ a ≠ b + s ∧ b ≠ a + s := by
  simpa [nonresB] using h

theorem sound_P3 : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fP3 x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fP3, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  intro φ
  refine P3 ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw)
    (Nat.gcd (Nat.gcd x y) u) h2 3 hnd ?_ φ
  intro i hi
  fin_cases i
  · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_right _ _
  · exact absurd rfl hi

theorem sound_T : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fT x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fT, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨q, -, hq⟩ := anyLt_true h
  simp only [decide_eq_true_eq] at hq
  obtain ⟨h6, hqg, hcu, hcw⟩ := hq
  intro φ
  exact T ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw) q h6 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.dvd_trans hqg (Nat.gcd_dvd_left _ _)) (Nat.dvd_trans hqg (Nat.gcd_dvd_right _ _)) hcu hcw φ

theorem sound_Q : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fQ x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fQ, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h⟩ := h
  have r1 := nonresB_true h1
  have r2 := nonresB_true h2
  obtain ⟨q, -, hq⟩ := anyLt_true h
  simp only [decide_eq_true_eq] at hq
  obtain ⟨h4, hqg, hcu, hcw, hcls⟩ := hq
  have hcls' : (q : ℤ) ∣ (u : ℤ) - w ∨ (q : ℤ) ∣ (u : ℤ) + w := by
    rcases hcls with hc | hc
    · left
      have : u ≡ w [MOD q] := hc
      have := (Nat.modEq_iff_dvd.mp this)
      exact (dvd_sub_comm).mp this
    · right
      have := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hc)
      simpa using this
  intro φ
  exact QGen ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw) q h4 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.dvd_trans hqg (Nat.gcd_dvd_left _ _)) (Nat.dvd_trans hqg (Nat.gcd_dvd_right _ _)) hcu hcw
    hcls' r1 r2 φ

theorem sound_Q3 : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fQ3 x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fQ3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, h6⟩ := h
  have r1 := nonresB_true h5
  have r2 := nonresB_true h6
  intro φ
  exact Q3_ndvd ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw) 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
    (fun h => h3 (Nat.mod_eq_zero_of_dvd h)) (fun h => h4 (Nat.mod_eq_zero_of_dvd h)) r1 r2 φ

theorem sound_Pair : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fPair x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fPair, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact sound_T x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  · exact sound_Q x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  · exact sound_Q3 x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h

theorem sound_G24 : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fG24 x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fG24, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  have r := nonresB_true h5
  intro φ
  exact G24 ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw) 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h3 h4 r φ

theorem sound_R7 : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → u ≠ w → fR7 x y u w = true → S4q x y u w := by
  intro x y u w hx hy hu hw hxy hxu hxw hyu hyw huw h
  simp only [fR7, decide_eq_true_eq, Sim7] at h
  obtain ⟨h1, h2, h3, h4, hp⟩ := h
  have hpat : (((7 : ℤ) ∣ (y : ℤ) - u ∨ (7 : ℤ) ∣ (y : ℤ) + u) ∧
        ((7 : ℤ) ∣ (y : ℤ) - w ∨ (7 : ℤ) ∣ (y : ℤ) + w)) ∨
      (((7 : ℤ) ∣ (u : ℤ) - w ∨ (7 : ℤ) ∣ (u : ℤ) + w) ∧
        ¬ ((7 : ℤ) ∣ (y : ℤ) - u ∨ (7 : ℤ) ∣ (y : ℤ) + u) ∧
        ¬ ((x = u + w ∨ u = w + x ∨ w = u + x) ∧
          ((7 : ℤ) ∣ (u : ℤ) - 3 * y ∨ (7 : ℤ) ∣ (u : ℤ) + 3 * y))) := by
    omega
  intro φ
  exact R7_partial ![x, y, u, w] (vec_pos hx hy hu hw) (vec_inj hxy hxu hxw hyu hyw huw) 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.dvd_of_mod_eq_zero h1) (fun h => h2 (Nat.mod_eq_zero_of_dvd h))
    (fun h => h3 (Nat.mod_eq_zero_of_dvd h)) (fun h => h4 (Nat.mod_eq_zero_of_dvd h)) hpat φ

theorem sound_R5 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : r5B a b c d = true) : S4q a b c d := by
  simp only [r5B, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  intro φ
  have hs : ∃ i : Fin 4, 5 ∣ (![a, b, c, d] : Fin 4 → ℕ) i := by
    rcases h1 with h | h | h | h
    · exact ⟨0, Nat.dvd_of_mod_eq_zero h⟩
    · exact ⟨1, Nat.dvd_of_mod_eq_zero h⟩
    · exact ⟨2, Nat.dvd_of_mod_eq_zero h⟩
    · exact ⟨3, Nat.dvd_of_mod_eq_zero h⟩
  have hf : ∃ i : Fin 4, ¬ 5 ∣ (![a, b, c, d] : Fin 4 → ℕ) i := by
    rcases h2 with h | h | h | h
    · exact ⟨0, fun h' => h (Nat.mod_eq_zero_of_dvd h')⟩
    · exact ⟨1, fun h' => h (Nat.mod_eq_zero_of_dvd h')⟩
    · exact ⟨2, fun h' => h (Nat.mod_eq_zero_of_dvd h')⟩
    · exact ⟨3, fun h' => h (Nat.mod_eq_zero_of_dvd h')⟩
  exact R5_core ![a, b, c, d] (vec_pos ha hb hc hd) (vec_inj hab hac had hbc hbd hcd) hs hf φ

/-- THE soundness theorem of the class test. -/
theorem classB_sound {a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : classB a b c d = true) : S4 ![a, b, c, d] := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hd : 0 < d := by omega
  have h1 : a ≠ b := by omega
  have h2 : a ≠ c := by omega
  have h3 : a ≠ d := by omega
  have h4 : b ≠ c := by omega
  have h5 : b ≠ d := by omega
  have h6 : c ≠ d := by omega
  simp only [classB, Bool.or_eq_true] at h
  show S4q a b c d
  rcases h with (((h | h) | h) | h) | h
  · exact sound_R5 ha hb hc hd h1 h2 h3 h4 h5 h6 h
  · exact anyPerm_sound g24L g24L_ok fG24 sound_G24 ha hb hc hd h1 h2 h3 h4 h5 h6 h
  · exact anyPerm_sound p3L p3L_ok fP3 sound_P3 ha hb hc hd h1 h2 h3 h4 h5 h6 h
  · exact anyPerm_sound pairL pairL_ok fPair sound_Pair ha hb hc hd h1 h2 h3 h4 h5 h6 h
  · exact anyPerm_sound r7L r7L_ok fR7 sound_R7 ha hb hc hd h1 h2 h3 h4 h5 h6 h

end D0
end LRSpectrumFull
