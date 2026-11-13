/-
# S4 range loop with TWO certificate types (restated copy of `S4Loop`, which is not edited)

`Cert2` has three constructors: `d0` (depth-0 certificate, checked by `D0.recOK3`, exactly as `Cert.d0` of
`S4Loop`), `tc` (time cover checked INLINE by `TC.tcOK`) and `pre` (the vector must be listed in a list `L` of
vectors whose `S4` has been proved separately, one theorem per vector).  The inline `tc` check keeps every
intermediate kernel term of all records of a module alive (about 13 KB per elementary step: a module with 35 time
covers of 16k steps was killed by the watchdog at 10.8 GB), so for modules with many time covers the covers are
proved by separate theorems (a fresh kernel cache each) and the loop only does a membership test (`pre`).

`rangeOK2_sound`: hypothesis `PreOK L` (every listed vector satisfies `S4`), and `rangeB2 L a blo n cs = true`;
conclusion as `rangeOK_sound`:  ∀ b c d, blo ≤ b → b < blo + n → b < c → c < d → a+b+c+d ≤ 195 →
gcd (gcd a b) (gcd c d) = 1 → S4 ![a,b,c,d].   (`L = []` and no `pre` records: the original setting.)
-/
import LRSpectrumFull.S4Loop
import LRSpectrumFull.TCSound

namespace LRSpectrumFull
namespace D0

inductive Cert2
  /-- depth-0 certificate: `(b,c,d)` as literals and `k1 k2 k3` -/
  | d0 (vb vc vd : ℕ) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : ℤ) : Cert2
  /-- time cover checked inline: `(b,c,d)` as literals, denominator `q`, numerators -/
  | tc (vb vc vd q : ℕ) (times : List ℕ) : Cert2
  /-- the vector `(a,b,c,d)` is in the separately proved list -/
  | pre (vb vc vd : ℕ) : Cert2

/-- every listed vector satisfies `S4` -/
def PreOK (L : List (ℕ × ℕ × ℕ × ℕ)) : Prop := ∀ x ∈ L, S4 ![x.1, x.2.1, x.2.2.1, x.2.2.2]

def inL (L : List (ℕ × ℕ × ℕ × ℕ)) (a b c d : ℕ) : Bool :=
  L.any fun x => x.1 == a && x.2.1 == b && x.2.2.1 == c && x.2.2.2 == d

theorem inL_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a b c d : ℕ}
    (h : inL L a b c d = true) : S4 ![a, b, c, d] := by
  unfold inL at h
  obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hx2
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx2
  have := hL x hx
  rw [h1, h2, h3, h4] at this
  exact this

def certOK2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a b c d : ℕ) : Cert2 → Bool
  | .d0 vb vc vd a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 =>
      decide (b = vb ∧ c = vc ∧ d = vd) &&
      recOK3 ⟨(a : ℤ), (vb : ℤ), (vc : ℤ), (vd : ℤ), a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3⟩
  | .tc vb vc vd q times =>
      decide (b = vb ∧ c = vc ∧ d = vd) && TC.tcOK a b c d q times
  | .pre vb vc vd =>
      decide (b = vb ∧ c = vc ∧ d = vd) && inL L a b c d

theorem certOK2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a b c d : ℕ} {r : Cert2}
    (h : certOK2 L a b c d r = true) : S4 ![a, b, c, d] := by
  cases r with
  | tc vb vc vd q times =>
    simp only [certOK2, Bool.and_eq_true] at h
    exact TC.tc_sound a b c d q times h.2
  | pre vb vc vd =>
    simp only [certOK2, Bool.and_eq_true] at h
    exact inL_sound hL h.2
  | d0 vb vc vd a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 =>
    simp only [certOK2, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, h3⟩, h⟩ := h
    subst h1 h2 h3
    have := recOK3_sound _ h
    simpa [Rec.vn] using this

/-- one vector: skipped if not primitive; accepted if the NEXT record certifies it, else if `classB` holds
(no record consumed), else rejected. -/
def step2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a b c d : ℕ) (cs : List Cert2) : Option (List Cert2) :=
  if Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 then
    match cs with
    | [] => if classB a b c d then some cs else none
    | r :: rest => if certOK2 L a b c d r then some rest else if classB a b c d then some cs else none
  else some cs

theorem step2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a b c d : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) {cs cs' : List Cert2} (h : step2 L a b c d cs = some cs') :
    Claim a b c d := by
  intro hg
  unfold step2 at h
  rw [if_pos hg] at h
  cases cs with
  | nil =>
    simp only at h
    by_cases hc : classB a b c d = true
    · exact classB_sound ha hab hbc hcd hc
    · rw [if_neg hc] at h; simp at h
  | cons r rest =>
    simp only at h
    by_cases hr : certOK2 L a b c d r = true
    · exact certOK2_sound hL hr
    · rw [if_neg hr] at h
      by_cases hc : classB a b c d = true
      · exact classB_sound ha hab hbc hcd hc
      · rw [if_neg hc] at h; simp at h

def goD2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a b c : ℕ) : ℕ → ℕ → List Cert2 → Option (List Cert2)
  | 0, _, cs => some cs
  | n + 1, d, cs =>
    match step2 L a b c d cs with
    | none => none
    | some cs' => goD2 L a b c n (d + 1) cs'

def goC2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a b : ℕ) : ℕ → ℕ → List Cert2 → Option (List Cert2)
  | 0, _, cs => some cs
  | n + 1, c, cs =>
    match goD2 L a b c (195 - a - b - 2 * c) (c + 1) cs with
    | none => none
    | some cs' => goC2 L a b n (c + 1) cs'

def goB2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a : ℕ) : ℕ → ℕ → List Cert2 → Option (List Cert2)
  | 0, _, cs => some cs
  | n + 1, b, cs =>
    match goC2 L a b ((194 - a - b) / 2 - b) (b + 1) cs with
    | none => none
    | some cs' => goB2 L a n (b + 1) cs'

/-- the Bool checked by the kernel: the whole record list is consumed -/
def rangeB2 (L : List (ℕ × ℕ × ℕ × ℕ)) (a blo n : ℕ) (cs : List Cert2) : Bool :=
  match goB2 L a n blo cs with
  | some [] => true
  | _ => false

theorem goD2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a b c : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) :
    ∀ (n d : ℕ) (cs cs' : List Cert2), c < d → goD2 L a b c n d cs = some cs' →
      ∀ e, d ≤ e → e < d + n → Claim a b c e := by
  intro n
  induction n with
  | zero => intro d cs cs' _ _ e h1 h2; omega
  | succ n ih =>
    intro d cs cs' hcd h e h1 h2
    unfold goD2 at h
    cases hs : step2 L a b c d cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact step2_sound hL ha hab hbc hcd hs
      · exact ih (d + 1) cs1 cs' (by omega) h e (by omega) (by omega)

theorem goC2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    ∀ (n c : ℕ) (cs cs' : List Cert2), b < c → goC2 L a b n c cs = some cs' →
      ∀ e d, c ≤ e → e < c + n → e < d → a + b + e + d ≤ 195 → Claim a b e d := by
  intro n
  induction n with
  | zero => intro c cs cs' _ _ e d h1 h2; omega
  | succ n ih =>
    intro c cs cs' hbc h e d h1 h2 h3 h4
    unfold goC2 at h
    cases hs : goD2 L a b c (195 - a - b - 2 * c) (c + 1) cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact goD2_sound hL ha hab hbc _ _ cs cs1 (by omega) hs d (by omega) (by omega)
      · exact ih (c + 1) cs1 cs' (by omega) h e d (by omega) (by omega) h3 h4

theorem goB2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a : ℕ} (ha : 0 < a) :
    ∀ (n b : ℕ) (cs cs' : List Cert2), a < b → goB2 L a n b cs = some cs' →
      ∀ e c d, b ≤ e → e < b + n → e < c → c < d → a + e + c + d ≤ 195 → Claim a e c d := by
  intro n
  induction n with
  | zero => intro b cs cs' _ _ e c d h1 h2; omega
  | succ n ih =>
    intro b cs cs' hab h e c d h1 h2 h3 h4 h5
    unfold goB2 at h
    cases hs : goC2 L a b ((194 - a - b) / 2 - b) (b + 1) cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact goC2_sound hL ha hab _ _ cs cs1 (by omega) hs c d (by omega) (by omega) h4 h5
      · exact ih (b + 1) cs1 cs' (by omega) h e c d (by omega) (by omega) h3 h4 h5

/-- THE glue theorem with two certificate types (and the `pre` list) -/
theorem rangeOK2_sound {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : PreOK L) {a blo n : ℕ} {cs : List Cert2}
    (ha : 0 < a) (hblo : a < blo) (h : rangeB2 L a blo n cs = true) :
    ∀ b c d : ℕ, blo ≤ b → b < blo + n → b < c → c < d → a + b + c + d ≤ 195 →
      Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro b c d h1 h2 h3 h4 h5 hg
  unfold rangeB2 at h
  cases hs : goB2 L a n blo cs with
  | none => rw [hs] at h; simp at h
  | some cs1 =>
    exact goB2_sound hL ha n blo cs cs1 hblo hs b c d h1 h2 h3 h4 h5 hg

end D0
end LRSpectrumFull
