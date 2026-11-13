/-
# S4 range: the lockstep loop and its soundness (the only trusted glue)

For a first speed `a` and a range of second speeds, `rangeB a blo n certs` enumerates, in a fixed order,
all `(b, c, d)` with `blo ≤ b < blo + n`, `b < c < d`, `a + b + c + d ≤ 195`.  A non-primitive vector is
skipped; a primitive one is accepted if `classB a b c d = true` (no data), and otherwise consumes the NEXT
record of `certs`, which must pass its checker `certOK`; at the end the record list must be exhausted.
`rangeOK_sound` says: if `rangeB a blo n certs = true`, then `S4 ![a,b,c,d]` for every primitive such
`(b,c,d)` with `a < blo`.  The data (`certs`) is untrusted: only this file, `S4Class`, `D0Fast` and the
class theorems are.

Records are a sum type.  `Cert.d0` carries the three integer vectors `k1 k2 k3` of a depth-0 certificate
(`D0Fast.recOK3` on the speed vector `(a,b,c,d)` of the loop and these 12 integers).  `Cert.other` is a
placeholder for a second certificate type: it is REJECTED for now (`certOK = false`).  To add a type later:
one constructor, one clause of `certOK`, one clause of `certOK_sound`.
-/
import LRSpectrumFull.S4Class
import LRSpectrumFull.D0Fast

namespace LRSpectrumFull
namespace D0

inductive Cert
  /-- carries `(b,c,d)` as literals (checked equal to the loop's vector) and `k1 k2 k3` -/
  | d0 (vb vc vd : ℕ) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : ℤ) : Cert
  | other : Cert

def certOK (a b c d : ℕ) : Cert → Bool
  | .d0 vb vc vd a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 =>
      decide (b = vb ∧ c = vc ∧ d = vd) &&
      recOK3 ⟨(a : ℤ), (vb : ℤ), (vc : ℤ), (vd : ℤ), a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3⟩
  | .other => false

theorem certOK_sound {a b c d : ℕ} {r : Cert} (h : certOK a b c d r = true) : S4 ![a, b, c, d] := by
  cases r with
  | other => simp [certOK] at h
  | d0 vb vc vd a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 =>
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, h3⟩, h⟩ := h
    subst h1 h2 h3
    have := recOK3_sound _ h
    simpa [Rec.vn] using this

/-- one vector: skipped if not primitive; a primitive one is accepted if the NEXT record certifies it
(then `classB` is not evaluated: a failing `classB` is the expensive path in the kernel), else if
`classB` holds (no record consumed), else rejected. -/
def step (a b c d : ℕ) (cs : List Cert) : Option (List Cert) :=
  if Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 then
    match cs with
    | [] => if classB a b c d then some cs else none
    | r :: rest => if certOK a b c d r then some rest else if classB a b c d then some cs else none
  else some cs

/-- the statement for one vector -/
def Claim (a b c d : ℕ) : Prop := Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d]

theorem step_sound {a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    {cs cs' : List Cert} (h : step a b c d cs = some cs') : Claim a b c d := by
  intro hg
  unfold step at h
  rw [if_pos hg] at h
  cases cs with
  | nil =>
    simp only at h
    by_cases hc : classB a b c d = true
    · exact classB_sound ha hab hbc hcd hc
    · rw [if_neg hc] at h; simp at h
  | cons r rest =>
    simp only at h
    by_cases hr : certOK a b c d r = true
    · exact certOK_sound hr
    · rw [if_neg hr] at h
      by_cases hc : classB a b c d = true
      · exact classB_sound ha hab hbc hcd hc
      · rw [if_neg hc] at h; simp at h

def goD (a b c : ℕ) : ℕ → ℕ → List Cert → Option (List Cert)
  | 0, _, cs => some cs
  | n + 1, d, cs =>
    match step a b c d cs with
    | none => none
    | some cs' => goD a b c n (d + 1) cs'

def goC (a b : ℕ) : ℕ → ℕ → List Cert → Option (List Cert)
  | 0, _, cs => some cs
  | n + 1, c, cs =>
    match goD a b c (195 - a - b - 2 * c) (c + 1) cs with
    | none => none
    | some cs' => goC a b n (c + 1) cs'

def goB (a : ℕ) : ℕ → ℕ → List Cert → Option (List Cert)
  | 0, _, cs => some cs
  | n + 1, b, cs =>
    match goC a b ((194 - a - b) / 2 - b) (b + 1) cs with
    | none => none
    | some cs' => goB a n (b + 1) cs'

/-- the Bool checked by the kernel: the whole record list is consumed -/
def rangeB (a blo n : ℕ) (cs : List Cert) : Bool :=
  match goB a n blo cs with
  | some [] => true
  | _ => false

theorem goD_sound {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∀ (n d : ℕ) (cs cs' : List Cert), c < d → goD a b c n d cs = some cs' →
      ∀ e, d ≤ e → e < d + n → Claim a b c e := by
  intro n
  induction n with
  | zero => intro d cs cs' _ _ e h1 h2; omega
  | succ n ih =>
    intro d cs cs' hcd h e h1 h2
    unfold goD at h
    cases hs : step a b c d cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact step_sound ha hab hbc hcd hs
      · exact ih (d + 1) cs1 cs' (by omega) h e (by omega) (by omega)

theorem goC_sound {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    ∀ (n c : ℕ) (cs cs' : List Cert), b < c → goC a b n c cs = some cs' →
      ∀ e d, c ≤ e → e < c + n → e < d → a + b + e + d ≤ 195 → Claim a b e d := by
  intro n
  induction n with
  | zero => intro c cs cs' _ _ e d h1 h2; omega
  | succ n ih =>
    intro c cs cs' hbc h e d h1 h2 h3 h4
    unfold goC at h
    cases hs : goD a b c (195 - a - b - 2 * c) (c + 1) cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact goD_sound ha hab hbc _ _ cs cs1 (by omega) hs d (by omega) (by omega)
      · exact ih (c + 1) cs1 cs' (by omega) h e d (by omega) (by omega) h3 h4

theorem goB_sound {a : ℕ} (ha : 0 < a) :
    ∀ (n b : ℕ) (cs cs' : List Cert), a < b → goB a n b cs = some cs' →
      ∀ e c d, b ≤ e → e < b + n → e < c → c < d → a + e + c + d ≤ 195 → Claim a e c d := by
  intro n
  induction n with
  | zero => intro b cs cs' _ _ e c d h1 h2; omega
  | succ n ih =>
    intro b cs cs' hab h e c d h1 h2 h3 h4 h5
    unfold goB at h
    cases hs : goC a b ((194 - a - b) / 2 - b) (b + 1) cs with
    | none => rw [hs] at h; simp at h
    | some cs1 =>
      rw [hs] at h
      simp only at h
      rcases Nat.eq_or_lt_of_le h1 with he | he
      · subst he
        exact goC_sound ha hab _ _ cs cs1 (by omega) hs c d (by omega) (by omega) h4 h5
      · exact ih (b + 1) cs1 cs' (by omega) h e c d (by omega) (by omega) h3 h4 h5

/-- THE glue theorem: a successful `rangeB` proves the statement for every primitive vector of the range. -/
theorem rangeOK_sound {a blo n : ℕ} {cs : List Cert} (ha : 0 < a) (hblo : a < blo)
    (h : rangeB a blo n cs = true) :
    ∀ b c d : ℕ, blo ≤ b → b < blo + n → b < c → c < d → a + b + c + d ≤ 195 →
      Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro b c d h1 h2 h3 h4 h5 hg
  unfold rangeB at h
  cases hs : goB a n blo cs with
  | none => rw [hs] at h; simp at h
  | some cs1 =>
    exact goB_sound ha n blo cs cs1 hblo hs b c d h1 h2 h3 h4 h5 hg

/-- all `b > a`: the whole first speed `a` (the range `a < b ≤ (192 - a)/3` contains every admissible `b`) -/
theorem rangeA_sound {a : ℕ} {cs : List Cert} (ha : 0 < a)
    (h : rangeB a (a + 1) ((192 - a) / 3 - a) cs = true) :
    ∀ b c d : ℕ, a < b → b < c → c < d → a + b + c + d ≤ 195 →
      Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by
  intro b c d h1 h2 h3 h4 hg
  exact rangeOK_sound ha (Nat.lt_succ_self a) h b c d (by omega) (by omega) h2 h3 h4 hg

end D0
end LRSpectrumFull
