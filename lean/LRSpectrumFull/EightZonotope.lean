/-
# B1: explicit generators `u_1,...,u_7` of the "quotient by v" lattice `Z^7 / Zv`

Part of (development file, not part of this archive)'s B1 row, blocking (eventually, via B2-B9, not
attempted here) `bridge31`/`MSSGap7` in `EightMSS.lean`. See (development file, not part of this archive) for
the full hand-derivation and adversarial review (Rule 6) BEFORE this Lean file was written,
including a correction caught there by a concrete falsification check (Rule 3): the kernel-exactness
claim (Claim C below) genuinely needs `gcd(w) = 1`, unlike the other two claims.

**What this file formalizes and why (see `b1_notes.md` section 0 for the full argument).** The
task's draft framing asked for `u : Fin 7 → (Fin 6 → ℤ)` with `(c ↦ ∑ c_i u_i)` bijecting
`{c : ∑ c_i v_i = 0}` onto `ℤ^6`. That property is FALSE in general (checked by hand on
`v = (2,3)`, index `13 = |v|^2 ≠ 1`). The property that actually matches Prop 1.5's own wording
("`Z^n + Rv` collapses onto the lattice `Z^{n-1}`") is the QUOTIENT statement: `u_i := Φ(e_i)`
for an explicit linear surjection `Φ : ℤ^7 → ℤ^6` with `Φ(v) = 0` and `ker Φ = ℤ·v` exactly. This
file constructs such a `Φ` (as `phiAux`) via a recursive Bezout "peel the last two coordinates"
construction and proves the three needed properties (NEED-1/2/3 in `b1_notes.md`).

Status (Rule 0 labels), updated across sessions: `phiAux`/`LRZgens` are DEF. `phiAux_self` (Claim
A) is PROVED, unconditionally. `phiAux_surjective` (Claim B) is PROVED, under a CORRECTED
hypothesis found by falsification (Rule 3): `∀ i, w i ≠ 0`, not "unconditional" as `b1_notes.md`
claimed — see the correction note before `unimod2_solve` below for the counterexample
(`w = (1,0,0)`, `gcd w = 1`, not surjective). `LRZgens_eq`/`LRZgens_span` are PROVED (the latter
under `∀ i, 0 < v i`, matching this project's standing hypothesis on `v`, which implies the
corrected nonzero hypothesis). `phiAux_ker` (Claim C, both directions) is PROVED: the earlier
session's blocker (`Finset.gcd`/`Int.gcd` API-bridging gap for propagating `gcd w = 1` down the
recursion to `w'`) is closed by `gcd_snoc_eq` (mutual-divisibility argument via
`dvd_antisymm_of_normalize_eq`, avoiding the `GCDMonoid.gcd`-vs-`Int.gcd` identification entirely).
`LRZ` (B2, `zonotope_plan.md`), `zero_mem_LRZ`, `LRZ_apply`, `LRZ_bounded`, `LRZ_nonempty` are
DEF/PROVED.
-/

import Mathlib
import LRSpectrumFull.MaxLoneliness
import LRSpectrumFull.EightMSS

namespace LRSpectrumFull.EightZonotope

open Finset
open scoped Pointwise

/-- The recursive "peel the last two coordinates via Bezout" construction. Given a parameter
vector `w : Fin (k+1) → ℤ` and an input `c` of the same shape, returns a vector of one fewer
coordinate. See `b1_notes.md` section 1 for the derivation and section 2 for the adversarial
review of the three claims below. -/
def phiAux : (k : ℕ) → (Fin (k + 1) → ℤ) → (Fin (k + 1) → ℤ) → (Fin k → ℤ)
  | 0, _, _ => Fin.elim0
  | (k + 1), w, c =>
      let a := w (Fin.last (k + 1))
      let b := (Fin.init w) (Fin.last k)
      let g : ℤ := Int.gcd b a
      let s := Int.gcdA b a
      let t := Int.gcdB b a
      let p := -a / g
      let q := b / g
      let w' := Fin.snoc (Fin.init (Fin.init w)) g
      let ac := c (Fin.last (k + 1))
      let bc := (Fin.init c) (Fin.last k)
      let c' := Fin.snoc (Fin.init (Fin.init c)) (s * bc + t * ac)
      Fin.snoc (phiAux k w' c') (p * bc + q * ac)

/-- The n = 7 specialization: `LRZgens v i` is the image of the `i`-th standard basis vector
under `phiAux 6 v`, i.e. `u_i := Φ(e_i)`. -/
def LRZgens (v : Fin 7 → ℤ) : Fin 7 → (Fin 6 → ℤ) :=
  fun i => phiAux 6 v (fun j => if j = i then 1 else 0)

/-- Unfolding lemma for the successor case of `phiAux`, stated with named local defs so later
proofs can `rw`/`simp` with it instead of fighting the raw `let`-block. This is definitionally
`rfl` (it is exactly the equation the pattern match compiles to). -/
theorem phiAux_succ (k : ℕ) (w c : Fin (k + 2) → ℤ) :
    phiAux (k + 1) w c =
      Fin.snoc
        (phiAux k
          (Fin.snoc (Fin.init (Fin.init w))
            (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ))
          (Fin.snoc (Fin.init (Fin.init c))
            (Int.gcdA (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) * Fin.init c (Fin.last k) +
              Int.gcdB (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) * c (Fin.last (k + 1)))))
        (-(w (Fin.last (k + 1))) /
              (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) * Fin.init c (Fin.last k) +
            Fin.init w (Fin.last k) /
              (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) * c (Fin.last (k + 1))) :=
  rfl

/-- **Claim A** (unconditional, no `gcd` hypothesis needed — see `b1_notes.md` section 2b):
`Φ_w(w) = 0`. -/
theorem phiAux_self : ∀ (k : ℕ) (w : Fin (k + 1) → ℤ), phiAux k w w = 0 := by
  intro k
  induction k with
  | zero => intro w; funext i; exact i.elim0
  | succ k ih =>
      intro w
      rw [phiAux_succ]
      set b := Fin.init w (Fin.last k) with hb
      set a := w (Fin.last (k + 1)) with ha
      set g : ℤ := (Int.gcd b a : ℤ) with hg
      have hgab : g = b * Int.gcdA b a + a * Int.gcdB b a := Int.gcd_eq_gcd_ab b a
      have hgpos : g ≠ 0 ∨ (b = 0 ∧ a = 0) := by
        rcases eq_or_ne (Int.gcd b a) 0 with h0 | h0
        · right
          have := Int.gcd_eq_zero_iff.mp h0
          exact this
        · left; rw [hg]; exact_mod_cast h0
      funext i
      induction i using Fin.lastCases with
      | last =>
          simp only [Fin.snoc_last, Pi.zero_apply]
          rcases hgpos with hgne | ⟨hb0, ha0⟩
          · have hdvdb : g ∣ b := by rw [hg]; exact Int.gcd_dvd_left b a
            have hdvda : g ∣ a := by rw [hg]; exact Int.gcd_dvd_right b a
            obtain ⟨b', hb'⟩ := hdvdb
            obtain ⟨a', ha'⟩ := hdvda
            have e1 : -a / g = -a' := by
              rw [ha', show -(g * a') = g * (-a') by ring, Int.mul_ediv_cancel_left _ hgne]
            have e2 : b / g = b' := by rw [hb', Int.mul_ediv_cancel_left _ hgne]
            rw [e1, e2, hb', ha']
            ring
          · simp [ha0, hb0]
      | cast i =>
          simp only [Fin.snoc_castSucc]
          have hc' : Fin.snoc (Fin.init (Fin.init w)) (Int.gcdA b a * b + Int.gcdB b a * a) =
              Fin.snoc (Fin.init (Fin.init w)) g := by
            rw [show Int.gcdA b a * b + Int.gcdB b a * a = b * Int.gcdA b a + a * Int.gcdB b a from
              by ring, ← hgab]
          rw [hc']
          have := congrFun (ih (Fin.snoc (Fin.init (Fin.init w)) g)) i
          simpa using this

/- **Correction to `b1_notes.md` found by falsification (Rule 3) during this session.** The
notes claimed Claim B holds "unconditionally" and Claim C only needs `gcd w = 1`. Both are FALSE
as literally stated: take `w = (1,0,0) : Fin 3 → ℤ` (`gcd w = 1`). At the top recursive step
`b = w 1 = 0`, `a = w 2 = 0`, so `g = Int.gcd 0 0 = 0`, hence `p = -a/g = 0`, `q = b/g = 0`
(integer division by `0` is `0` in Lean), so the LAST output coordinate is
`p * bc + q * ac = 0` **for every input `c`**, independent of `w 0`. So `phiAux 2 (1,0,0)` misses
every target with nonzero last coordinate: not surjective, even though `gcd w = 1`. The
degeneracy is triggered by the two coordinates the recursion peels first both being `0`, not by
`gcd w`. The correct sufficient hypothesis (verified below) is `∀ i, w i ≠ 0` (all entries
individually nonzero) — strictly weaker than the positivity `∀ i, 0 < w i` that is the actual
standing hypothesis on `v` everywhere else in this project (`EightMSS.lean`), so this correction
does not block the intended application, only the earlier "no hypothesis needed" claim in the
notes. Key invariant used below: if `a ≠ 0` and `b ≠ 0` then `Int.gcd b a ≠ 0`, and this is
preserved down the recursion (the new last entry `g` of `w'` is again nonzero), so `∀ i, w i ≠ 0`
is a recursion-stable hypothesis, unlike `gcd w = 1` alone. -/

/-- Elementary fact: solving `s*x+t*y = c1`, `p*x+q*y = c2` for `(x,y)` when `s*q-t*p = 1`,
via the explicit inverse matrix `[[q,-t],[-p,s]]` of `[[s,t],[p,q]]`. Pure `ℤ`-algebra, no
induction; this is the "2x2 unimodular matrix is invertible over `ℤ`" fact used by both Claim B
and Claim C's Rule-6 paper proofs in `b1_notes.md` section 2. -/
theorem unimod2_solve (s t p q c1 c2 : ℤ) (hdet : s * q - t * p = 1) :
    s * (q * c1 - t * c2) + t * (-p * c1 + s * c2) = c1 ∧
      p * (q * c1 - t * c2) + q * (-p * c1 + s * c2) = c2 := by
  constructor
  · linear_combination c1 * hdet
  · linear_combination c2 * hdet

/-- If `a ≠ 0` and `b ≠ 0` then `Int.gcd b a ≠ 0` (as an integer). Elementary, used to show the
recursion never degenerates when all entries of `w` are nonzero. -/
theorem gcd_ne_zero_of_ne_zero {a b : ℤ} (ha : a ≠ 0) : (Int.gcd b a : ℤ) ≠ 0 := by
  intro h
  have h0 : Int.gcd b a = 0 := by exact_mod_cast h
  exact ha (Int.gcd_eq_zero_iff.mp h0).2

/-- Bookkeeping lemma: `Fin.snoc`/`Fin.init` commute with pointwise `+` and `ℤ`-scalar `•`, and
with pointwise evaluation. All four facts are `funext` + `Fin.lastCases` + `simp` routine, and are
the only glue needed to push `+`/`•` through `phiAux`'s recursive `Fin.snoc` structure below. -/
theorem snocAdd {n : ℕ} (f g : Fin n → ℤ) (a b : ℤ) :
    (Fin.snoc f a : Fin (n + 1) → ℤ) + Fin.snoc g b = Fin.snoc (f + g) (a + b) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem snocSmul {n : ℕ} (m : ℤ) (f : Fin n → ℤ) (a : ℤ) :
    m • (Fin.snoc f a : Fin (n + 1) → ℤ) = Fin.snoc (m • f) (m * a) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem initAdd {n : ℕ} (f g : Fin (n + 1) → ℤ) :
    Fin.init (f + g) = Fin.init f + Fin.init g := by
  funext i; simp [Fin.init]

theorem initSmul {n : ℕ} (m : ℤ) (f : Fin (n + 1) → ℤ) :
    Fin.init (m • f) = m • Fin.init f := by
  funext i; simp [Fin.init]

/-- The recursion preserves "all entries nonzero" (the corrected hypothesis, see the note above):
the new last entry `g` of `w'` is `Int.gcd b a` with `a, b` both nonzero, hence nonzero. -/
theorem phiAux_w'_ne_zero (k : ℕ) (w : Fin (k + 2) → ℤ) (hnz : ∀ i, w i ≠ 0) :
    ∀ i, Fin.snoc (Fin.init (Fin.init w))
        (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) i ≠ 0 := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa using gcd_ne_zero_of_ne_zero (b := Fin.init w (Fin.last k)) (hnz _)
  | cast i => simpa using hnz i.castSucc.castSucc

/-- **Claim B**, CORRECTED (see the falsification note above): `phiAux k w` is surjective
whenever all entries of `w` are nonzero. PROVED. -/
theorem phiAux_surjective (k : ℕ) (w : Fin (k + 1) → ℤ) (hnz : ∀ i, w i ≠ 0) :
    Function.Surjective (phiAux k w) := by
  induction k with
  | zero => intro target; exact ⟨fun _ => 0, funext fun i => i.elim0⟩
  | succ k ih =>
      intro target
      set b := Fin.init w (Fin.last k) with hb
      set a := w (Fin.last (k + 1)) with ha
      set g : ℤ := (Int.gcd b a : ℤ) with hg
      set s := Int.gcdA b a with hs
      set t := Int.gcdB b a with ht
      set p := -a / g with hp
      set q := b / g with hq
      set w' := Fin.snoc (Fin.init (Fin.init w)) g with hw'
      have hgne : g ≠ 0 := gcd_ne_zero_of_ne_zero (a := a) (b := b) (hnz _)
      have hgab : g = b * s + a * t := Int.gcd_eq_gcd_ab b a
      have hdet : s * q - t * p = 1 := by
        have hdvdb : g ∣ b := hg ▸ Int.gcd_dvd_left b a
        have hdvda : g ∣ a := hg ▸ Int.gcd_dvd_right b a
        obtain ⟨b', hb'⟩ := hdvdb
        obtain ⟨a', ha'⟩ := hdvda
        have e1 : p = -a' := by
          rw [hp, ha', show -(g * a') = g * (-a') by ring, Int.mul_ediv_cancel_left _ hgne]
        have e2 : q = b' := by rw [hq, hb', Int.mul_ediv_cancel_left _ hgne]
        rw [e1, e2]
        have hgab' : g = g * b' * s + g * a' * t := by rw [← hb', ← ha']; exact hgab
        have hgab'' : g * 1 = g * (b' * s + a' * t) := by rw [mul_one]; linear_combination hgab'
        have := mul_left_cancel₀ hgne hgab''
        linear_combination -this
      have hw'nz : ∀ i, w' i ≠ 0 := by
        rw [hw']; exact phiAux_w'_ne_zero k w (fun i => hnz i)
      obtain ⟨d, hd⟩ := ih w' hw'nz (Fin.init target)
      set y := d (Fin.last k) with hy
      set z := target (Fin.last k) with hz
      set bc := q * y - t * z with hbc
      set ac := -p * y + s * z with hac
      have hsolve := unimod2_solve s t p q y z hdet
      have hy_eq : s * bc + t * ac = y := by rw [hbc, hac]; exact hsolve.1
      have hz_eq : p * bc + q * ac = z := by rw [hbc, hac]; exact hsolve.2
      set c : Fin (k + 2) → ℤ := Fin.snoc (Fin.snoc (Fin.init d) bc) ac with hc
      refine ⟨c, ?_⟩
      rw [phiAux_succ]
      have hinitc : Fin.init c = Fin.snoc (Fin.init d) bc := by simp [hc]
      have hbc' : Fin.init c (Fin.last k) = bc := by simp [hinitc]
      have hac' : c (Fin.last (k + 1)) = ac := by simp [hc]
      have hinitinit : Fin.init (Fin.init c) = Fin.init d := by
        simp [hinitc]
      rw [show (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) = g from rfl,
        show Int.gcdA (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) = s from rfl,
        show Int.gcdB (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) = t from rfl,
        show -(w (Fin.last (k + 1))) / (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ)
          = p from rfl,
        show Fin.init w (Fin.last k) / (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ)
          = q from rfl,
        hbc', hac', hinitinit]
      have hc' : Fin.snoc (Fin.init d) (s * bc + t * ac) = d := by
        rw [hy_eq]; exact Fin.snoc_init_self d
      rw [hc', hd, hz_eq]
      exact Fin.snoc_init_self target

/-- Splitting lemma: the total gcd of `w` equals the total gcd of `w'` (the vector obtained by
replacing `w`'s last two coordinates by their `Int.gcd`). This is the "associativity of gcd"
fact making `Finset.univ.gcd w = 1` propagate down the `phiAux` recursion to `w'`, needed for
Claim C. Proved by mutual divisibility (`dvd_antisymm_of_normalize_eq`): a common divisor of `w`
divides `a,b` hence (Bezout, `Int.gcd_eq_gcd_ab`) divides `g = gcd b a`, hence divides every
coordinate of `w'`; conversely a common divisor of `w'` divides `g`, hence (`Int.gcd_dvd_left/right`)
divides both `a` and `b`, hence every coordinate of `w`. -/
theorem gcd_snoc_eq (k : ℕ) (w : Fin (k + 2) → ℤ) :
    Finset.univ.gcd w =
      Finset.univ.gcd
        (Fin.snoc (Fin.init (Fin.init w))
          ((Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ))) := by
  set b := Fin.init w (Fin.last k) with hb
  set a := w (Fin.last (k + 1)) with ha
  set g : ℤ := (Int.gcd b a : ℤ) with hg
  set w' := Fin.snoc (Fin.init (Fin.init w)) g with hw'
  have hgdvdb : g ∣ b := hg ▸ Int.gcd_dvd_left b a
  have hgdvda : g ∣ a := hg ▸ Int.gcd_dvd_right b a
  have hdg : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ g := by
    intro d hda hdb
    rw [hg, Int.gcd_eq_gcd_ab]
    exact dvd_add (hdb.mul_right _) (hda.mul_right _)
  apply dvd_antisymm_of_normalize_eq (Finset.normalize_gcd) (Finset.normalize_gcd)
  · apply Finset.dvd_gcd
    intro i _
    induction i using Fin.lastCases with
    | last =>
        show Finset.univ.gcd w ∣ w' (Fin.last k)
        rw [hw']; simp only [Fin.snoc_last]
        exact hdg _ (Finset.gcd_dvd (Finset.mem_univ (Fin.last (k + 1)))) (by
          show Finset.univ.gcd w ∣ b
          rw [hb]
          have := Finset.gcd_dvd (f := w) (s := (Finset.univ : Finset (Fin (k + 2))))
            (b := (Fin.last k).castSucc)
          simpa [Fin.init] using this)
    | cast i =>
        show Finset.univ.gcd w ∣ w' i.castSucc
        rw [hw']; simp only [Fin.snoc_castSucc]
        have := Finset.gcd_dvd (f := w) (s := (Finset.univ : Finset (Fin (k + 2))))
          (b := i.castSucc.castSucc)
        simpa [Fin.init] using this
  · apply Finset.dvd_gcd
    intro i _
    induction i using Fin.lastCases with
    | last =>
        show Finset.univ.gcd w' ∣ a
        exact dvd_trans (by
          have := Finset.gcd_dvd (f := w') (s := (Finset.univ : Finset (Fin (k + 1))))
            (b := Fin.last k)
          simpa [hw'] using this) hgdvda
    | cast i =>
        induction i using Fin.lastCases with
        | last =>
            show Finset.univ.gcd w' ∣ b
            exact dvd_trans (by
              have := Finset.gcd_dvd (f := w') (s := (Finset.univ : Finset (Fin (k + 1))))
                (b := Fin.last k)
              simpa [hw'] using this) hgdvdb
        | cast i =>
            show Finset.univ.gcd w' ∣ w i.castSucc.castSucc
            have := Finset.gcd_dvd (f := w') (s := (Finset.univ : Finset (Fin (k + 1))))
              (b := i.castSucc)
            simpa [hw', Fin.init] using this

/-- Additivity of `phiAux k w` in its input `c`. PROVED by induction on `k`, mirroring
`phiAux_self`'s recursive unfolding; every step of the recursion is a `ℤ`-linear combination of
`c`'s entries with coefficients depending only on `w`. -/
theorem phiAux_add (k : ℕ) (w c1 c2 : Fin (k + 1) → ℤ) :
    phiAux k w (c1 + c2) = phiAux k w c1 + phiAux k w c2 := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [phiAux_succ, phiAux_succ, phiAux_succ]
      set b := Fin.init w (Fin.last k)
      set a := w (Fin.last (k + 1))
      set g : ℤ := (Int.gcd b a : ℤ)
      set s := Int.gcdA b a
      set t := Int.gcdB b a
      set p := -a / g
      set q := b / g
      set w' := Fin.snoc (Fin.init (Fin.init w)) g
      have hinit : Fin.init (c1 + c2) = Fin.init c1 + Fin.init c2 := initAdd c1 c2
      have hlast : (c1 + c2) (Fin.last (k + 1)) = c1 (Fin.last (k + 1)) + c2 (Fin.last (k + 1)) := by
        simp
      have hinitinit : Fin.init (Fin.init (c1 + c2)) = Fin.init (Fin.init c1) + Fin.init (Fin.init c2) := by
        rw [initAdd, initAdd]
      rw [show Fin.init (c1 + c2) (Fin.last k) = Fin.init c1 (Fin.last k) + Fin.init c2 (Fin.last k) by
          rw [hinit]; rfl, hlast, hinitinit]
      have hc'eq : Fin.snoc (Fin.init (Fin.init c1) + Fin.init (Fin.init c2))
            (s * (Fin.init c1 (Fin.last k) + Fin.init c2 (Fin.last k)) +
              t * (c1 (Fin.last (k + 1)) + c2 (Fin.last (k + 1)))) =
          Fin.snoc (Fin.init (Fin.init c1)) (s * Fin.init c1 (Fin.last k) + t * c1 (Fin.last (k + 1))) +
            Fin.snoc (Fin.init (Fin.init c2)) (s * Fin.init c2 (Fin.last k) + t * c2 (Fin.last (k + 1))) := by
        rw [snocAdd]; ring_nf
      rw [hc'eq, ih w']
      rw [snocAdd]
      ring_nf

/-- Scalar-homogeneity of `phiAux k w` in its input `c`. PROVED, same structure as `phiAux_add`. -/
theorem phiAux_zsmul (k : ℕ) (w : Fin (k + 1) → ℤ) (m : ℤ) (c : Fin (k + 1) → ℤ) :
    phiAux k w (m • c) = m • phiAux k w c := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [phiAux_succ, phiAux_succ]
      set b := Fin.init w (Fin.last k)
      set a := w (Fin.last (k + 1))
      set g : ℤ := (Int.gcd b a : ℤ)
      set s := Int.gcdA b a
      set t := Int.gcdB b a
      set p := -a / g
      set q := b / g
      set w' := Fin.snoc (Fin.init (Fin.init w)) g
      have hinitinit : Fin.init (Fin.init (m • c)) = m • Fin.init (Fin.init c) := by
        rw [initSmul, initSmul]
      rw [show Fin.init (m • c) (Fin.last k) = m * Fin.init c (Fin.last k) by
          rw [initSmul]; rfl,
        show (m • c) (Fin.last (k + 1)) = m * c (Fin.last (k + 1)) by rfl, hinitinit]
      have hc'eq : Fin.snoc (m • Fin.init (Fin.init c))
            (s * (m * Fin.init c (Fin.last k)) + t * (m * c (Fin.last (k + 1)))) =
          m • Fin.snoc (Fin.init (Fin.init c)) (s * Fin.init c (Fin.last k) + t * c (Fin.last (k + 1))) := by
        rw [snocSmul]; ring_nf
      rw [hc'eq, ih w']
      rw [snocSmul]
      ring_nf

/-- The easy (`⟸`) half of Claim C, PROVED unconditionally: needs neither `hnz` nor `hw`, only
`phiAux_self` and `phiAux_zsmul` (both already proved above). Kept as its own lemma (used inside
`phiAux_ker` below) because it is independently useful and needs no hypothesis. -/
theorem phiAux_ker_backward (k : ℕ) (w c : Fin (k + 1) → ℤ) (h : ∃ m : ℤ, c = m • w) :
    phiAux k w c = 0 := by
  obtain ⟨m, rfl⟩ := h
  rw [phiAux_zsmul, phiAux_self]
  simp

/-- **Claim C**: the kernel of `phiAux k w` is exactly `ℤ·w`, needing `gcd w = 1` (per
`b1_notes.md`'s falsification check on `w = (2,4)`, section 2b) AND the `∀ i, w i ≠ 0` correction
found for Claim B (same degenerate-pair failure mode: if `gcd w = 1` but two consecutive peeled
entries are both `0`, e.g. `w = (1,0,0)`, `phiAux`'s output is identically `0` regardless of
input, so `ker = everything ≠ ℤ·w`). PROVED, both directions. The forward direction's earlier
blocker (propagating `Finset.univ.gcd w = 1` down the recursion to `w'`) is closed by
`gcd_snoc_eq` above; the rest of the forward direction mirrors `phiAux_surjective`'s determinant
algebra (`unimod2_solve`'s identity, here run in the "solution is unique" direction: `(bc,ac)` and
`(m*b, m*a)` both solve the same rank-2 system, so their difference is a homogeneous solution,
forced to `0` since `det = s*q - t*p = 1 ≠ 0`). Base case (`k = 0`): `Finset.univ.gcd w = 1` on
`Fin 1` gives `w 0 = ±1` (`normalize_eq_one`/`Int.isUnit_iff`), and `m := c 0 * w 0` works since
`w 0 * w 0 = 1`. -/
theorem phiAux_ker (k : ℕ) (w : Fin (k + 1) → ℤ) (hnz : ∀ i, w i ≠ 0)
    (hw : Finset.univ.gcd w = 1) :
    ∀ c : Fin (k + 1) → ℤ, phiAux k w c = 0 ↔ ∃ m : ℤ, c = m • w := by
  induction k with
  | zero =>
      intro c
      constructor
      · intro _
        have huniv : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x 0⟩
        rw [huniv, Finset.gcd_singleton] at hw
        have hunit : IsUnit (w 0) := normalize_eq_one.mp hw
        rcases Int.isUnit_iff.mp hunit with h1 | h1
        · exact ⟨c 0, by funext i; fin_cases i; simp [h1]⟩
        · exact ⟨-(c 0), by funext i; fin_cases i; simp [h1]⟩
      · intro _
        funext i; exact i.elim0
  | succ k ih =>
      intro c
      set b := Fin.init w (Fin.last k) with hb
      set a := w (Fin.last (k + 1)) with ha
      set g : ℤ := (Int.gcd b a : ℤ) with hg
      set s := Int.gcdA b a with hs
      set t := Int.gcdB b a with ht
      set p := -a / g with hp
      set q := b / g with hq
      set w' := Fin.snoc (Fin.init (Fin.init w)) g with hw'
      have hgne : g ≠ 0 := gcd_ne_zero_of_ne_zero (a := a) (b := b) (hnz _)
      have hgab : g = b * s + a * t := Int.gcd_eq_gcd_ab b a
      have hdvdb : g ∣ b := hg ▸ Int.gcd_dvd_left b a
      have hdvda : g ∣ a := hg ▸ Int.gcd_dvd_right b a
      obtain ⟨b', hb'⟩ := hdvdb
      obtain ⟨a', ha'⟩ := hdvda
      have e1 : p = -a' := by
        rw [hp, ha', show -(g * a') = g * (-a') by ring, Int.mul_ediv_cancel_left _ hgne]
      have e2 : q = b' := by rw [hq, hb', Int.mul_ediv_cancel_left _ hgne]
      have hpq0 : p * b + q * a = 0 := by rw [e1, e2, hb', ha']; ring
      have hdet : s * q - t * p = 1 := by
        rw [e1, e2]
        have hgab' : g = g * b' * s + g * a' * t := by rw [← hb', ← ha']; exact hgab
        have hgab'' : g * 1 = g * (b' * s + a' * t) := by rw [mul_one]; linear_combination hgab'
        have := mul_left_cancel₀ hgne hgab''
        linear_combination -this
      have hw'nz : ∀ i, w' i ≠ 0 := by
        rw [hw']; exact phiAux_w'_ne_zero k w hnz
      have hw'gcd : Finset.univ.gcd w' = 1 := by
        simp only [hw', hg, hb, ha]
        rw [← gcd_snoc_eq k w]; exact hw
      constructor
      · intro hc0
        rw [phiAux_succ] at hc0
        set bc := Fin.init c (Fin.last k) with hbc
        set ac := c (Fin.last (k + 1)) with hac
        have hlast : p * bc + q * ac = 0 := by
          have := congrFun hc0 (Fin.last k)
          simpa using this
        have hinit0 : phiAux k w' (Fin.snoc (Fin.init (Fin.init c)) (s * bc + t * ac)) = 0 := by
          funext i
          have := congrFun hc0 i.castSucc
          simpa using this
        obtain ⟨m, hm⟩ := (ih w' hw'nz hw'gcd _).mp hinit0
        have hlast_eq : s * bc + t * ac = m * g := by
          have := congrFun hm (Fin.last k)
          simpa [hw'] using this
        have hinit_eq : Fin.init (Fin.init c) = m • Fin.init (Fin.init w) := by
          funext i
          have := congrFun hm i.castSucc
          simpa [hw'] using this
        have h1 : s * (bc - m * b) + t * (ac - m * a) = 0 := by
          linear_combination hlast_eq + m * hgab
        have h2 : p * (bc - m * b) + q * (ac - m * a) = 0 := by
          linear_combination hlast - m * hpq0
        have hbc_eq : bc - m * b = 0 := by
          linear_combination q * h1 - t * h2 - (bc - m * b) * hdet
        have hac_eq : ac - m * a = 0 := by
          linear_combination -p * h1 + s * h2 - (ac - m * a) * hdet
        refine ⟨m, ?_⟩
        funext i
        induction i using Fin.lastCases with
        | last =>
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [← ha]
            linarith [hac_eq]
        | cast i =>
            induction i using Fin.lastCases with
            | last =>
                simp only [Pi.smul_apply, smul_eq_mul, Fin.snoc_castSucc]
                show Fin.init c (Fin.last k) = m * Fin.init w (Fin.last k)
                rw [← hb]
                linarith [hbc_eq]
            | cast i =>
                have := congrFun hinit_eq i
                simpa [Fin.init] using this
      · exact phiAux_ker_backward (k + 1) w c


theorem phiAux_zero (k : ℕ) (w : Fin (k + 1) → ℤ) : phiAux k w 0 = 0 := by
  have := phiAux_zsmul k w 0 w
  simpa using this

/-- `phiAux k w` commutes with finite `ℤ`-linear combinations of inputs. This is the "Z-linearity
in the input argument" the original `sorry` comments (`LRZgens_eq`/`LRZgens_span`) asked for,
assembled from `phiAux_add`/`phiAux_zero` by induction on the (finite) index set. -/
theorem phiAux_finsum (k : ℕ) (w : Fin (k + 1) → ℤ) {ι : Type*} [DecidableEq ι] (sset : Finset ι)
    (f : ι → Fin (k + 1) → ℤ) :
    phiAux k w (∑ i ∈ sset, f i) = ∑ i ∈ sset, phiAux k w (f i) := by
  classical
  induction sset using Finset.induction with
  | empty => simp [phiAux_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phiAux_add, ih]

/-- Standard-basis decomposition: `v = ∑ i, v i • e_i` where `e_i` is the `i`-th indicator
vector, matching `LRZgens`'s own definition `LRZgens v i = phiAux 6 v e_i`. -/
theorem sum_smul_single (v : Fin 7 → ℤ) :
    (∑ i : Fin 7, v i • (fun j => if j = i then (1 : ℤ) else 0)) = v := by
  funext j
  simp

/-- NEED-1 (eq 1.2): `∑_i v_i u_i = 0`, for `LRZgens`. PROVED, via `phiAux_self` (`phiAux 6 v v =
0`) transported through `phiAux_finsum`/`sum_smul_single` (linearity in the input argument, the
piece the earlier `sorry` was time-boxed out on this session). -/
theorem LRZgens_eq (v : Fin 7 → ℤ) : ∀ j, ∑ i, v i * LRZgens v i j = 0 := by
  intro j
  have hv : phiAux 6 v v = 0 := phiAux_self 6 v
  have hsum : phiAux 6 v (∑ i : Fin 7, v i • (fun j => if j = i then (1 : ℤ) else 0)) = 0 := by
    rw [sum_smul_single]; exact hv
  rw [phiAux_finsum 6 v Finset.univ (fun i => v i • (fun j => if j = i then (1 : ℤ) else 0))]
    at hsum
  simp only [phiAux_zsmul] at hsum
  have hj := congrFun hsum j
  simpa [LRZgens, Finset.sum_apply, smul_eq_mul] using hj

/-- NEED-2 (full rank / spans): the generators `LRZgens v` jointly span `ℤ^6`, PROVED for `v`
positive (the standing hypothesis on `v` everywhere else in this project, and in particular
implies the corrected nonzero hypothesis `phiAux_surjective` needs — see the falsification note
above). Given `z : Fin 6 → ℤ`, surjectivity (`phiAux_surjective`) gives `c` with `phiAux 6 v c =
z`; decomposing `c = ∑ i, c i • e_i` and pushing `phiAux 6 v` through the sum
(`phiAux_finsum`) exhibits `z` as the `ℤ`-linear combination `∑ i, c i • LRZgens v i`, which lies
in `Submodule.span ℤ (Set.range (LRZgens v))` by definition. -/
theorem LRZgens_span (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) :
    Submodule.span ℤ (Set.range (LRZgens v)) = (⊤ : Submodule ℤ (Fin 6 → ℤ)) := by
  rw [eq_top_iff]
  intro z _
  have hvnz : ∀ i, v i ≠ 0 := fun i => (hv i).ne'
  obtain ⟨c, hc⟩ := phiAux_surjective 6 v hvnz z
  have hcdecomp : c = ∑ i : Fin 7, c i • (fun j => if j = i then (1 : ℤ) else 0) :=
    (sum_smul_single c).symm
  rw [hcdecomp, phiAux_finsum 6 v Finset.univ
      (fun i => c i • (fun j => if j = i then (1 : ℤ) else 0))] at hc
  have hmem : z ∈ Submodule.span ℤ (Set.range (LRZgens v)) := by
    rw [← hc]
    refine Submodule.sum_mem _ ?_
    intro i _
    have : phiAux 6 v (c i • (fun j => if j = i then (1 : ℤ) else 0)) =
        c i • LRZgens v i := by
      rw [phiAux_zsmul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hmem

/-! ## Part 2 (B2): the zonotope `LRZ v` -/

/-- **B2**: the zonotope generated by `LRZgens v`, cast from `ℤ` to `ℝ` coordinatewise, as a
`Set (Fin 6 → ℝ)`: all `∑ i, t i • u i` with `t : Fin 7 → ℝ` ranging over the unit cube
`[0,1]^7`. Matches `zonotope_plan.md`'s B2 row. -/
def LRZ (v : Fin 7 → ℤ) : Set (Fin 6 → ℝ) :=
  {x | ∃ t : Fin 7 → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      x = ∑ i, t i • (fun j => ((LRZgens v i j : ℤ) : ℝ))}

/-- Sanity lemma (I6 item, trivial case): `0 ∈ LRZ v` for every `v`, witnessed by `t = 0`. -/
theorem zero_mem_LRZ (v : Fin 7 → ℤ) : (0 : Fin 6 → ℝ) ∈ LRZ v := by
  refine ⟨0, fun i => ⟨le_refl 0, zero_le_one⟩, ?_⟩
  simp

/-- Pointwise evaluation of a member of `LRZ v`: `x j = ∑ i, t i * u_i j` for the witnessing `t`.
Bookkeeping lemma used by the boundedness sanity check below. -/
theorem LRZ_apply {v : Fin 7 → ℤ} {x : Fin 6 → ℝ} (hx : x ∈ LRZ v) (j : Fin 6) :
    ∃ t : Fin 7 → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      x j = ∑ i, t i * ((LRZgens v i j : ℤ) : ℝ) := by
  obtain ⟨t, ht, hx⟩ := hx
  refine ⟨t, ht, ?_⟩
  rw [hx]
  simp [Finset.sum_apply]

/-- Sanity lemma (boundedness): every coordinate of every point of `LRZ v` is bounded by the sum
of the absolute values of that coordinate across the generators, independent of `v`'s sign
pattern. Cheap consequence of `0 ≤ t i ≤ 1`, no positivity hypothesis on `v` needed. -/
theorem LRZ_bounded (v : Fin 7 → ℤ) (x : Fin 6 → ℝ) (hx : x ∈ LRZ v) (j : Fin 6) :
    |x j| ≤ ∑ i : Fin 7, |((LRZgens v i j : ℤ) : ℝ)| := by
  obtain ⟨t, ht, hxj⟩ := LRZ_apply hx j
  rw [hxj]
  calc |∑ i : Fin 7, t i * ((LRZgens v i j : ℤ) : ℝ)|
      ≤ ∑ i : Fin 7, |t i * ((LRZgens v i j : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 7, |t i| * |((LRZgens v i j : ℤ) : ℝ)| := by
        simp [abs_mul]
    _ ≤ ∑ i : Fin 7, 1 * |((LRZgens v i j : ℤ) : ℝ)| := by
        refine Finset.sum_le_sum ?_
        intro i _
        have h1 : |t i| ≤ 1 := abs_le.mpr ⟨by linarith [(ht i).1], (ht i).2⟩
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = ∑ i : Fin 7, |((LRZgens v i j : ℤ) : ℝ)| := by simp

/-- `LRZ v` is nonempty (immediate from `zero_mem_LRZ`). -/
theorem LRZ_nonempty (v : Fin 7 → ℤ) : (LRZ v).Nonempty := ⟨0, zero_mem_LRZ v⟩

/-! ### Real-coefficient extension of `phiAux` (route B for `zproj_ker_subset_span`,
`b3_notes.md` §3a). `phiAuxR` mirrors `phiAux`'s recursive Bezout construction EXACTLY, with the
same integer parameter vector `w` (so the same `g,s,t,p,q` Bezout data, computed purely from `w`,
never from the input), but the input `c` and output are real-valued. Since every step of the
recursion acts on `c` only via integer-coefficient linear combinations, the identical recursion
typechecks with `c : Fin (k+1) → ℝ`, and the `linear_combination`/`ring` identities from
`phiAux_ker`'s proof (generic commutative-ring facts) port verbatim. This avoids the route-A
alternative (Mathlib `Module.rank`/`finrank` field-extension machinery), which was flagged as an
unverified-availability risk in the docstring above. -/
def phiAuxR : (k : ℕ) → (Fin (k + 1) → ℤ) → (Fin (k + 1) → ℝ) → (Fin k → ℝ)
  | 0, _, _ => Fin.elim0
  | (k + 1), w, c =>
      let a := w (Fin.last (k + 1))
      let b := (Fin.init w) (Fin.last k)
      let g : ℤ := Int.gcd b a
      let s := Int.gcdA b a
      let t := Int.gcdB b a
      let p := -a / g
      let q := b / g
      let w' := Fin.snoc (Fin.init (Fin.init w)) g
      let ac := c (Fin.last (k + 1))
      let bc := (Fin.init c) (Fin.last k)
      let c' := Fin.snoc (Fin.init (Fin.init c)) ((s : ℝ) * bc + (t : ℝ) * ac)
      Fin.snoc (phiAuxR k w' c') ((p : ℝ) * bc + (q : ℝ) * ac)

/-- Unfolding lemma for `phiAuxR`, real-coefficient analogue of `phiAux_succ`. `rfl`. -/
theorem phiAuxR_succ (k : ℕ) (w : Fin (k + 2) → ℤ) (c : Fin (k + 2) → ℝ) :
    phiAuxR (k + 1) w c =
      Fin.snoc
        (phiAuxR k
          (Fin.snoc (Fin.init (Fin.init w))
            (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ))
          (Fin.snoc (Fin.init (Fin.init c))
            ((Int.gcdA (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℝ) * Fin.init c (Fin.last k) +
              (Int.gcdB (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℝ) * c (Fin.last (k + 1)))))
        (((-(w (Fin.last (k + 1))) /
              (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) : ℤ) : ℝ) * Fin.init c (Fin.last k) +
            ((Fin.init w (Fin.last k) /
              (Int.gcd (Fin.init w (Fin.last k)) (w (Fin.last (k + 1))) : ℤ) : ℤ) : ℝ) * c (Fin.last (k + 1))) :=
  rfl

/-- Real-coefficient `Fin.snoc`/`Fin.init` bookkeeping, mirroring `snocAdd`/`snocSmul`/`initAdd`/
`initSmul` above but for `ℝ`-valued vectors and (for `snocSmulR`) a real scalar. -/
theorem snocAddR {n : ℕ} (f g : Fin n → ℝ) (a b : ℝ) :
    (Fin.snoc f a : Fin (n + 1) → ℝ) + Fin.snoc g b = Fin.snoc (f + g) (a + b) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem snocSmulR {n : ℕ} (r : ℝ) (f : Fin n → ℝ) (a : ℝ) :
    r • (Fin.snoc f a : Fin (n + 1) → ℝ) = Fin.snoc (r • f) (r * a) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem initAddR {n : ℕ} (f g : Fin (n + 1) → ℝ) :
    Fin.init (f + g) = Fin.init f + Fin.init g := by
  funext i; simp [Fin.init]

theorem initSmulR {n : ℕ} (r : ℝ) (f : Fin (n + 1) → ℝ) :
    Fin.init (r • f) = r • Fin.init f := by
  funext i; simp [Fin.init]

/-- Additivity of `phiAuxR k w` in its real input `c`. Mirrors `phiAux_add` verbatim (same
recursion, `s,t` cast to `ℝ`). -/
theorem phiAuxR_add (k : ℕ) (w : Fin (k + 1) → ℤ) (c1 c2 : Fin (k + 1) → ℝ) :
    phiAuxR k w (c1 + c2) = phiAuxR k w c1 + phiAuxR k w c2 := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [phiAuxR_succ, phiAuxR_succ, phiAuxR_succ]
      set b := Fin.init w (Fin.last k)
      set a := w (Fin.last (k + 1))
      set g : ℤ := (Int.gcd b a : ℤ)
      set s := Int.gcdA b a
      set t := Int.gcdB b a
      set p := -a / g
      set q := b / g
      set w' := Fin.snoc (Fin.init (Fin.init w)) g
      have hinit : Fin.init (c1 + c2) = Fin.init c1 + Fin.init c2 := initAddR c1 c2
      have hlast : (c1 + c2) (Fin.last (k + 1)) = c1 (Fin.last (k + 1)) + c2 (Fin.last (k + 1)) := by
        simp
      have hinitinit : Fin.init (Fin.init (c1 + c2)) = Fin.init (Fin.init c1) + Fin.init (Fin.init c2) := by
        rw [initAddR, initAddR]
      rw [show Fin.init (c1 + c2) (Fin.last k) = Fin.init c1 (Fin.last k) + Fin.init c2 (Fin.last k) by
          rw [hinit]; rfl, hlast, hinitinit]
      have hc'eq : Fin.snoc (Fin.init (Fin.init c1) + Fin.init (Fin.init c2))
            ((s : ℝ) * (Fin.init c1 (Fin.last k) + Fin.init c2 (Fin.last k)) +
              (t : ℝ) * (c1 (Fin.last (k + 1)) + c2 (Fin.last (k + 1)))) =
          Fin.snoc (Fin.init (Fin.init c1)) ((s : ℝ) * Fin.init c1 (Fin.last k) + (t : ℝ) * c1 (Fin.last (k + 1))) +
            Fin.snoc (Fin.init (Fin.init c2)) ((s : ℝ) * Fin.init c2 (Fin.last k) + (t : ℝ) * c2 (Fin.last (k + 1))) := by
        rw [snocAddR]; ring_nf
      rw [hc'eq, ih w']
      rw [snocAddR]
      ring_nf

/-- Real-scalar-homogeneity of `phiAuxR k w` in its input `c`. Mirrors `phiAux_zsmul`, with the
scalar `r : ℝ` (not just `ℤ`) since `c` itself is now real. -/
theorem phiAuxR_rsmul (k : ℕ) (w : Fin (k + 1) → ℤ) (r : ℝ) (c : Fin (k + 1) → ℝ) :
    phiAuxR k w (r • c) = r • phiAuxR k w c := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [phiAuxR_succ, phiAuxR_succ]
      set b := Fin.init w (Fin.last k)
      set a := w (Fin.last (k + 1))
      set g : ℤ := (Int.gcd b a : ℤ)
      set s := Int.gcdA b a
      set t := Int.gcdB b a
      set p := -a / g
      set q := b / g
      set w' := Fin.snoc (Fin.init (Fin.init w)) g
      have hinitinit : Fin.init (Fin.init (r • c)) = r • Fin.init (Fin.init c) := by
        rw [initSmulR, initSmulR]
      rw [show Fin.init (r • c) (Fin.last k) = r * Fin.init c (Fin.last k) by
          rw [initSmulR]; rfl,
        show (r • c) (Fin.last (k + 1)) = r * c (Fin.last (k + 1)) by rfl, hinitinit]
      have hc'eq : Fin.snoc (r • Fin.init (Fin.init c))
            ((s : ℝ) * (r * Fin.init c (Fin.last k)) + (t : ℝ) * (r * c (Fin.last (k + 1)))) =
          r • Fin.snoc (Fin.init (Fin.init c)) ((s : ℝ) * Fin.init c (Fin.last k) + (t : ℝ) * c (Fin.last (k + 1))) := by
        rw [snocSmulR]; ring_nf
      rw [hc'eq, ih w']
      rw [snocSmulR]
      ring_nf

theorem phiAuxR_zero (k : ℕ) (w : Fin (k + 1) → ℤ) : phiAuxR k w 0 = 0 := by
  have := phiAuxR_rsmul k w 0 0
  simpa using this

/-- `phiAuxR k w` commutes with finite `ℝ`-linear combinations of inputs. Mirrors `phiAux_finsum`. -/
theorem phiAuxR_finsum (k : ℕ) (w : Fin (k + 1) → ℤ) {ι : Type*} [DecidableEq ι] (sset : Finset ι)
    (f : ι → Fin (k + 1) → ℝ) :
    phiAuxR k w (∑ i ∈ sset, f i) = ∑ i ∈ sset, phiAuxR k w (f i) := by
  classical
  induction sset using Finset.induction with
  | empty => simp [phiAuxR_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phiAuxR_add, ih]

/-- Bridging lemma: `phiAuxR` agrees with (the real cast of) `phiAux` on integer-valued input.
Proved by induction mirroring `phiAux_succ`/`phiAuxR_succ` with `push_cast`. This is what lets
`phiAuxR_ker` (below) be transported into a statement about `zproj` (whose value is pinned by
`LRZgens`, itself defined via `phiAux` on integer basis vectors). -/
theorem phiAuxR_intCast (k : ℕ) (w c : Fin (k + 1) → ℤ) :
    phiAuxR k w (fun i => (c i : ℝ)) = fun i => ((phiAux k w c i : ℤ) : ℝ) := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [phiAuxR_succ, phiAux_succ]
      set b := Fin.init w (Fin.last k)
      set a := w (Fin.last (k + 1))
      set g : ℤ := (Int.gcd b a : ℤ)
      set s := Int.gcdA b a
      set t := Int.gcdB b a
      set p := -a / g
      set q := b / g
      set w' := Fin.snoc (Fin.init (Fin.init w)) g
      have hinitcast : Fin.init (fun i => (c i : ℝ)) = fun i => ((Fin.init c i : ℤ) : ℝ) := by
        funext i; simp [Fin.init]
      have hinitinitcast : Fin.init (Fin.init (fun i => (c i : ℝ)))
          = fun i => ((Fin.init (Fin.init c) i : ℤ) : ℝ) := by
        funext i; simp [Fin.init]
      rw [show Fin.init (fun i => (c i : ℝ)) (Fin.last k) = ((Fin.init c (Fin.last k) : ℤ) : ℝ) by
          rw [hinitcast],
        hinitinitcast]
      have hc'eq : Fin.snoc (fun i => ((Fin.init (Fin.init c) i : ℤ) : ℝ))
            ((s : ℝ) * ((Fin.init c (Fin.last k) : ℤ) : ℝ) + (t : ℝ) * ((c (Fin.last (k + 1)) : ℤ) : ℝ))
          = (fun i => ((Fin.snoc (Fin.init (Fin.init c))
              (s * Fin.init c (Fin.last k) + t * c (Fin.last (k + 1))) i : ℤ) : ℝ)) := by
        funext j
        induction j using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; push_cast; ring
        | cast j => simp
      rw [hc'eq, ih w']
      funext j
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; push_cast; ring
      | cast j => simp

/-- The "free half" fact (`ℝ·w ⊆ ker phiAuxR`), assembled from `phiAuxR_rsmul` +
`phiAuxR_intCast` + the already-PROVED `phiAux_self`, rather than a fresh induction. -/
theorem phiAuxR_rsmul_self (k : ℕ) (w : Fin (k + 1) → ℤ) (m : ℝ) :
    phiAuxR k w (m • (fun i => (w i : ℝ))) = 0 := by
  rw [phiAuxR_rsmul, phiAuxR_intCast, phiAux_self]
  funext i
  simp

/-- Standard-basis decomposition, real analogue of `sum_smul_single`. -/
theorem sum_smul_singleR (x : Fin 7 → ℝ) :
    (∑ i : Fin 7, x i • (fun j => if j = i then (1 : ℝ) else 0)) = x := by
  funext j
  simp

/-! ## Part 3 (B3): scalar lonely-time ↔ zonotope-membership dictionary

Formalizes `zonotope_plan.md`'s B3 row / Prop 1.5's dictionary, connecting THIS project's actual
currency (`gap`, `ML`, `nearestIntDist` from `MaxLoneliness.lean`) to membership in a shrunk
translate of `LRZ v`. See (development file, not part of this archive) for the full hand derivation (§1-3) and
adversarial review (§4) done BEFORE this code, per Rule 5/6 and the task instruction.

Status (Rule 0): `zproj`, `zonoCenterZ` DEF. `zproj_vcast_eq_zero` VERIFIED (real-coefficient
analogue of `LRZgens_eq`). `B3_forward` (the `⟹` direction of Prop 1.5's iff) VERIFIED, using only
`zproj_vcast_eq_zero`, `LRZ`'s definition, and `Int.fract`/`Int.floor` arithmetic — see
`b3_notes.md` §2. The former blocking gap, `zproj_ker_subset_span` (real-coefficient
kernel-exactness of the generator map, `b3_notes.md` §3a), is closed: VERIFIED via route B
(`phiAuxR`, the real-coefficient extension of `phiAux`, defined and its kernel-exactness proved
below by mirroring `phiAux_ker`'s induction). `B3_backward` and `B3_iff` (the full two-way
dictionary) are VERIFIED: `lake build` clean, zero `sorry`, axioms
`[propext, Classical.choice, Quot.sound]` only (checked via `lake env lean` on
(development file, not part of this archive)). -/

/-- Real-coefficient extension of the integer generator map `Φ` (`LRZgens`): same formula,
`zproj v c j = ∑_i c_i · u_i(j)`, but `c : Fin 7 → ℝ` instead of `Fin 7 → ℤ`. This is `Φ_ℝ` in
`b3_notes.md` §0. -/
noncomputable def zproj (v : Fin 7 → ℤ) (c : Fin 7 → ℝ) (j : Fin 6) : ℝ :=
  ∑ i, c i * ((LRZgens v i j : ℤ) : ℝ)

/-- The coordinatewise sum of all seven generators, `U` in `b3_notes.md` §0 (the zonotope's
center `x_v` is `(1/2 : ℝ) • ` this, matching MSS's Prop 1.5 / the task's framing). -/
noncomputable def zonoCenterZ (v : Fin 7 → ℤ) : Fin 6 → ℤ :=
  fun j => ∑ i, LRZgens v i j

/-- **Real-coefficient analogue of `LRZgens_eq`** (eq 1.2): `Φ_ℝ` kills the cast of `v` itself.
This is the "free" half (`ℝ·v ⊆ ker Φ_ℝ`) of the kernel-exactness fact `B3_iff`'s backward
direction needs; the other half (`ker Φ_ℝ ⊆ ℝ·v`) is `zproj_ker_subset_span` below, NOT proved
this session. PROVED here, via a direct cast of `LRZgens_eq`, no new machinery. -/
theorem zproj_vcast_eq_zero (v : Fin 7 → ℤ) (j : Fin 6) :
    zproj v (fun i => (v i : ℝ)) j = 0 := by
  have h := LRZgens_eq v j
  have h2 : ((∑ i, v i * LRZgens v i j : ℤ) : ℝ) = ∑ i, (v i : ℝ) * (LRZgens v i j : ℝ) := by
    push_cast; ring
  rw [h] at h2
  simpa [zproj] using h2.symm

/-- **B3, forward direction (PROVED)**: a lonely time `t` at gap `≥ δ` produces an explicit
integer point `z` with `(z - δ·U)/(1-2δ) ∈ LRZ v`. See `b3_notes.md` §2 for the derivation this
transcribes: `m := ⌊v_i t⌋`, `s := fract(v_i t) ∈ [δ,1-δ]`, `z := -Φ(m)`; then
`Φ_ℝ(s) = Φ_ℝ(t•v) - Φ(m) = 0 - Φ(m) = z` (using `zproj_vcast_eq_zero`), and unwinding
`s = δ + (1-2δ)τ` exhibits `τ ∈ [0,1]^7` as the `LRZ v`-membership witness. -/
theorem B3_forward (v : Fin 7 → ℤ) (t : ℝ) (delta : ℝ) (hd2 : delta < 1 / 2)
    (ht : delta ≤ gap v t) :
    ∃ z : Fin 6 → ℤ,
      (fun j => (((z j : ℝ) - delta * (zonoCenterZ v j : ℝ)) / (1 - 2 * delta))) ∈ LRZ v := by
  set m : Fin 7 → ℤ := fun i => ⌊(v i : ℝ) * t⌋ with hm
  set s : Fin 7 → ℝ := fun i => Int.fract ((v i : ℝ) * t) with hs
  have hs_eq : ∀ i, s i = (v i : ℝ) * t - (m i : ℝ) := by
    intro i
    rw [hs, hm]
    exact Int.self_sub_floor _
  have hpt : ∀ i, delta ≤ nearestIntDist ((v i : ℝ) * t) := fun i => ht.trans (gap_le v t i)
  have hsbound : ∀ i, delta ≤ s i ∧ s i ≤ 1 - delta := by
    intro i
    have h1 := hpt i
    unfold nearestIntDist at h1
    rw [hs]
    exact ⟨(le_min_iff.mp h1).1, by linarith [(le_min_iff.mp h1).2]⟩
  have hden : (1 - 2 * delta) ≠ 0 := by linarith
  set z : Fin 6 → ℤ := fun j => -(∑ i, m i * LRZgens v i j) with hz
  set tau : Fin 7 → ℝ := fun i => (s i - delta) / (1 - 2 * delta) with htau
  have htau01 : ∀ i, 0 ≤ tau i ∧ tau i ≤ 1 := by
    intro i
    have hpos : 0 < 1 - 2 * delta := by linarith
    refine ⟨div_nonneg (by linarith [(hsbound i).1]) hpos.le, ?_⟩
    rw [div_le_one hpos]
    linarith [(hsbound i).2]
  have hsi : ∀ i, s i = delta + (1 - 2 * delta) * tau i := by
    intro i
    have hcancel : tau i * (1 - 2 * delta) = s i - delta := by
      rw [htau]; exact div_mul_cancel₀ (s i - delta) hden
    linear_combination -hcancel
  refine ⟨z, tau, htau01, ?_⟩
  funext j
  have hkey : ∑ i, s i * ((LRZgens v i j : ℤ) : ℝ) = (z j : ℝ) := by
    have step : ∑ i, s i * ((LRZgens v i j : ℤ) : ℝ)
        = t * (∑ i, (v i : ℝ) * ((LRZgens v i j : ℤ) : ℝ))
          - ∑ i, (m i : ℝ) * ((LRZgens v i j : ℤ) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hs_eq i]; ring
    have hv0 : (∑ i, (v i : ℝ) * ((LRZgens v i j : ℤ) : ℝ)) = 0 := by
      have := zproj_vcast_eq_zero v j
      simpa [zproj] using this
    have hmcast : (∑ i, (m i : ℝ) * ((LRZgens v i j : ℤ) : ℝ))
        = ((∑ i, m i * LRZgens v i j : ℤ) : ℝ) := by push_cast; ring
    rw [step, hv0, hmcast]
    simp [hz]
  have hsum_s : ∑ i, s i * ((LRZgens v i j : ℤ) : ℝ)
      = delta * (zonoCenterZ v j : ℝ)
        + (1 - 2 * delta) * (∑ i, tau i * ((LRZgens v i j : ℤ) : ℝ)) := by
    have expand : ∀ i, s i * ((LRZgens v i j : ℤ) : ℝ)
        = delta * ((LRZgens v i j : ℤ) : ℝ)
          + (1 - 2 * delta) * (tau i * ((LRZgens v i j : ℤ) : ℝ)) := by
      intro i; rw [hsi i]; ring
    rw [Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    have hUcast : (zonoCenterZ v j : ℝ) = ∑ i, ((LRZgens v i j : ℤ) : ℝ) := by
      simp [zonoCenterZ]
    rw [hUcast]
  rw [hkey] at hsum_s
  have hgoal : (∑ i, tau i * ((LRZgens v i j : ℤ) : ℝ))
      = ((z j : ℝ) - delta * (zonoCenterZ v j : ℝ)) / (1 - 2 * delta) := by
    rw [eq_div_iff hden]
    linear_combination -hsum_s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hgoal]

/-- **Real-coefficient kernel-exactness of `phiAuxR`** (route B, `b3_notes.md` §3a), the
real-coefficient analogue of `phiAux_ker`. PROVED by mirroring `phiAux_ker`'s induction verbatim:
every algebraic fact used there (`hgab`, `hdet`, `hpq0`, `hw'nz`, `hw'gcd`) depends only on `w`
(never on the input), hence is reused UNCHANGED (as an integer fact, cast to `ℝ` where it meets
the now-real `c`); only the `c`-manipulation steps (`linear_combination`s) are re-run with real
casts inserted. The backward (`⟸`) direction is `phiAuxR_rsmul_self` (already assembled above from
`phiAux_self`, no fresh work). -/
theorem phiAuxR_ker (k : ℕ) (w : Fin (k + 1) → ℤ) (hnz : ∀ i, w i ≠ 0)
    (hw : Finset.univ.gcd w = 1) :
    ∀ c : Fin (k + 1) → ℝ, phiAuxR k w c = 0 ↔ ∃ m : ℝ, c = m • (fun i => (w i : ℝ)) := by
  induction k with
  | zero =>
      intro c
      constructor
      · intro _
        have huniv : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x 0⟩
        rw [huniv, Finset.gcd_singleton] at hw
        have hunit : IsUnit (w 0) := normalize_eq_one.mp hw
        rcases Int.isUnit_iff.mp hunit with h1 | h1
        · exact ⟨c 0, by funext i; fin_cases i; simp [h1]⟩
        · exact ⟨-(c 0), by funext i; fin_cases i; simp [h1]⟩
      · intro _
        funext i; exact i.elim0
  | succ k ih =>
      intro c
      set b := Fin.init w (Fin.last k) with hb
      set a := w (Fin.last (k + 1)) with ha
      set g : ℤ := (Int.gcd b a : ℤ) with hg
      set s := Int.gcdA b a with hs
      set t := Int.gcdB b a with ht
      set p := -a / g with hp
      set q := b / g with hq
      set w' := Fin.snoc (Fin.init (Fin.init w)) g with hw'
      have hgne : g ≠ 0 := gcd_ne_zero_of_ne_zero (a := a) (b := b) (hnz _)
      have hgab : g = b * s + a * t := Int.gcd_eq_gcd_ab b a
      have hdvdb : g ∣ b := hg ▸ Int.gcd_dvd_left b a
      have hdvda : g ∣ a := hg ▸ Int.gcd_dvd_right b a
      obtain ⟨b', hb'⟩ := hdvdb
      obtain ⟨a', ha'⟩ := hdvda
      have e1 : p = -a' := by
        rw [hp, ha', show -(g * a') = g * (-a') by ring, Int.mul_ediv_cancel_left _ hgne]
      have e2 : q = b' := by rw [hq, hb', Int.mul_ediv_cancel_left _ hgne]
      have hpq0 : p * b + q * a = 0 := by rw [e1, e2, hb', ha']; ring
      have hdet : s * q - t * p = 1 := by
        rw [e1, e2]
        have hgab' : g = g * b' * s + g * a' * t := by rw [← hb', ← ha']; exact hgab
        have hgab'' : g * 1 = g * (b' * s + a' * t) := by rw [mul_one]; linear_combination hgab'
        have := mul_left_cancel₀ hgne hgab''
        linear_combination -this
      have hw'nz : ∀ i, w' i ≠ 0 := by
        rw [hw']; exact phiAux_w'_ne_zero k w hnz
      have hw'gcd : Finset.univ.gcd w' = 1 := by
        simp only [hw', hg, hb, ha]
        rw [← gcd_snoc_eq k w]; exact hw
      have hgabR : (g : ℝ) = (b : ℝ) * (s : ℝ) + (a : ℝ) * (t : ℝ) := by exact_mod_cast hgab
      have hpq0R : (p : ℝ) * (b : ℝ) + (q : ℝ) * (a : ℝ) = 0 := by exact_mod_cast hpq0
      have hdetR : (s : ℝ) * (q : ℝ) - (t : ℝ) * (p : ℝ) = 1 := by exact_mod_cast hdet
      constructor
      · intro hc0
        rw [phiAuxR_succ] at hc0
        set bc := Fin.init c (Fin.last k) with hbc
        set ac := c (Fin.last (k + 1)) with hac
        have hlast : (p : ℝ) * bc + (q : ℝ) * ac = 0 := by
          have := congrFun hc0 (Fin.last k)
          simpa using this
        have hinit0 : phiAuxR k w' (Fin.snoc (Fin.init (Fin.init c)) ((s : ℝ) * bc + (t : ℝ) * ac)) = 0 := by
          funext i
          have := congrFun hc0 i.castSucc
          simpa using this
        obtain ⟨m, hm⟩ := (ih w' hw'nz hw'gcd _).mp hinit0
        have hlast_eq : (s : ℝ) * bc + (t : ℝ) * ac = m * (g : ℝ) := by
          have := congrFun hm (Fin.last k)
          simpa [hw'] using this
        have hinit_eq : Fin.init (Fin.init c) = m • (fun i => (Fin.init (Fin.init w) i : ℝ)) := by
          funext i
          have := congrFun hm i.castSucc
          simpa [hw'] using this
        have h1 : (s : ℝ) * (bc - m * (b : ℝ)) + (t : ℝ) * (ac - m * (a : ℝ)) = 0 := by
          linear_combination hlast_eq + m * hgabR
        have h2 : (p : ℝ) * (bc - m * (b : ℝ)) + (q : ℝ) * (ac - m * (a : ℝ)) = 0 := by
          linear_combination hlast - m * hpq0R
        have hbc_eq : bc - m * (b : ℝ) = 0 := by
          linear_combination (q : ℝ) * h1 - (t : ℝ) * h2 - (bc - m * (b : ℝ)) * hdetR
        have hac_eq : ac - m * (a : ℝ) = 0 := by
          linear_combination -(p : ℝ) * h1 + (s : ℝ) * h2 - (ac - m * (a : ℝ)) * hdetR
        refine ⟨m, ?_⟩
        funext i
        induction i using Fin.lastCases with
        | last =>
            simp only [Pi.smul_apply, smul_eq_mul]
            show ac = m * (a : ℝ)
            linarith [hac_eq]
        | cast i =>
            induction i using Fin.lastCases with
            | last =>
                simp only [Pi.smul_apply, smul_eq_mul, Fin.snoc_castSucc]
                show Fin.init c (Fin.last k) = m * (Fin.init w (Fin.last k) : ℝ)
                linarith [hbc_eq]
            | cast i =>
                have := congrFun hinit_eq i
                simpa [Fin.init] using this
      · rintro ⟨m, rfl⟩
        exact phiAuxR_rsmul_self (k + 1) w m

/-- `zproj` agrees with `phiAuxR` everywhere: both are `ℝ`-linear maps `(Fin 7 → ℝ) → (Fin 6 → ℝ)`
agreeing on the standard basis (`LRZgens v i = phiAux 6 v e_i` by definition, so `phiAuxR 6 v e_i =
phiAux 6 v e_i` cast, by `phiAuxR_intCast`); decomposing an arbitrary `x` via
`sum_smul_singleR` and pushing `phiAuxR` through the sum (`phiAuxR_finsum`/`phiAuxR_rsmul`)
identifies it with `zproj`'s own defining sum. -/
theorem zproj_eq_phiAuxR (v : Fin 7 → ℤ) (x : Fin 7 → ℝ) (j : Fin 6) :
    zproj v x j = phiAuxR 6 v x j := by
  have hdecomp : x = ∑ i : Fin 7, x i • (fun j => if j = i then (1 : ℝ) else 0) :=
    (sum_smul_singleR x).symm
  have hrhs : phiAuxR 6 v x j = ∑ i : Fin 7, x i * (LRZgens v i j : ℝ) := by
    conv_lhs => rw [hdecomp]
    rw [phiAuxR_finsum 6 v Finset.univ (fun i => x i • (fun j => if j = i then (1 : ℝ) else 0)),
      Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show phiAuxR 6 v (x i • (fun j => if j = i then (1 : ℝ) else 0)) j = x i * (LRZgens v i j : ℝ)
    rw [phiAuxR_rsmul]
    have hcast : (fun j => if j = i then (1 : ℝ) else 0)
        = (fun j => ((if j = i then (1 : ℤ) else 0 : ℤ) : ℝ)) := by
      funext j; split <;> simp
    rw [hcast, phiAuxR_intCast]
    simp only [Pi.smul_apply, smul_eq_mul, LRZgens]
  rw [hrhs]
  simp only [zproj]

/-- **B3a, closed.** Real-coefficient kernel-exactness of `Φ_ℝ` (`zproj`): if `Φ_ℝ(x) = 0` then
`x` is a real multiple of (the cast of) `v`. PROVED, via `zproj_eq_phiAuxR` (bridges `zproj` to
`phiAuxR`) and `phiAuxR_ker` (real-coefficient kernel-exactness, route B, proved above). This was
the single blocking atom for `B3_iff`'s backward direction. -/
theorem zproj_ker_subset_span (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i)
    (hgcd : Finset.univ.gcd v = 1) (x : Fin 7 → ℝ) (hx : ∀ j, zproj v x j = 0) :
    ∃ c : ℝ, x = fun i => c * (v i : ℝ) := by
  have hvnz : ∀ i, v i ≠ 0 := fun i => (hv i).ne'
  have hx' : phiAuxR 6 v x = 0 := by
    funext j
    rw [← zproj_eq_phiAuxR]
    exact hx j
  obtain ⟨c, hc⟩ := (phiAuxR_ker 6 v hvnz hgcd x).mp hx'
  refine ⟨c, ?_⟩
  funext i
  have := congrFun hc i
  simpa using this

/-- **B3, backward direction. VERIFIED.** A short composition (`b3_notes.md` §3): pick `s` from
the zonotope witness (`s_i := δ + (1-2δ)·τ_i`), `m : Fin 7 → ℤ` from `phiAux_surjective` with
`Φ(m) = -z`, apply `zproj_ker_subset_span` to `m + s` (which lies in `ker Φ_ℝ` since
`Φ_ℝ(m+s) = z + (-z) = 0`, the same computation as `B3_forward`'s `hkey` run backward) to get `c`
with `m+s = c•v`, then read off `nearestIntDist(v_i·c) = nearestIntDist(s_i) ≥ δ` (via
`nearestIntDist_add_int` and `nearestIntDist_ge`, since `s_i ∈ [δ,1-δ] ⊆ [0,1)`) and assemble with
`le_gap`. -/
theorem B3_backward (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hgcd : Finset.univ.gcd v = 1)
    (delta : ℝ) (hd0 : 0 < delta) (hd2 : delta < 1 / 2)
    (z : Fin 6 → ℤ)
    (hz : (fun j => (((z j : ℝ) - delta * (zonoCenterZ v j : ℝ)) / (1 - 2 * delta))) ∈ LRZ v) :
    ∃ t : ℝ, delta ≤ gap v t := by
  have hvnz : ∀ i, v i ≠ 0 := fun i => (hv i).ne'
  obtain ⟨tau, htau01, hzeq⟩ := hz
  set s : Fin 7 → ℝ := fun i => delta + (1 - 2 * delta) * tau i with hs
  have hden : (1 - 2 * delta) ≠ 0 := by linarith
  have hsbound : ∀ i, delta ≤ s i ∧ s i ≤ 1 - delta := by
    intro i
    have h1 := htau01 i
    constructor
    · simp only [hs]; nlinarith [h1.1]
    · simp only [hs]; nlinarith [h1.2]
  have hkey : ∀ j, ∑ i, s i * ((LRZgens v i j : ℤ) : ℝ) = (z j : ℝ) := by
    intro j
    have heq := congrFun hzeq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
    have hUcast : (zonoCenterZ v j : ℝ) = ∑ i, ((LRZgens v i j : ℤ) : ℝ) := by
      simp [zonoCenterZ]
    have expand : ∀ i, s i * ((LRZgens v i j : ℤ) : ℝ)
        = delta * ((LRZgens v i j : ℤ) : ℝ) + (1 - 2 * delta) * (tau i * ((LRZgens v i j : ℤ) : ℝ)) := by
      intro i; simp only [hs]; ring
    rw [Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hUcast, ← heq, mul_div_cancel₀ _ hden]
    ring
  obtain ⟨m, hm⟩ := phiAux_surjective 6 v hvnz (-z)
  have hzprojm : ∀ j, zproj v (fun i => (m i : ℝ)) j = -(z j : ℝ) := by
    intro j
    rw [zproj_eq_phiAuxR, phiAuxR_intCast, hm]
    simp
  have hzprojs : ∀ j, zproj v s j = (z j : ℝ) := by
    intro j
    simpa [zproj] using hkey j
  have hsum0 : ∀ j, zproj v (fun i => (m i : ℝ) + s i) j = 0 := by
    intro j
    have hadd : zproj v (fun i => (m i : ℝ) + s i) j
        = zproj v (fun i => (m i : ℝ)) j + zproj v s j := by
      simp only [zproj, add_mul, Finset.sum_add_distrib]
    rw [hadd, hzprojm, hzprojs]
    ring
  obtain ⟨c, hc⟩ := zproj_ker_subset_span v hv hgcd (fun i => (m i : ℝ) + s i) hsum0
  refine ⟨c, ?_⟩
  apply le_gap
  intro i
  have hci := congrFun hc i
  simp only at hci
  have hrw : (v i : ℝ) * c = s i + (m i : ℝ) := by linarith [hci]
  rw [hrw, nearestIntDist_add_int]
  exact nearestIntDist_ge (by linarith [(hsbound i).1, hd0]) (by linarith [(hsbound i).2, hd0, hd2])
    (hsbound i).1 (by linarith [(hsbound i).2])

/-- **B3 statement (Prop 1.5's dictionary). VERIFIED, full iff.**
`B3_forward` above proves the `→` direction unconditionally; `B3_backward` proves `←`. Kept as a
single named theorem (rather than just the two directions) so downstream (B7-B9) can cite one
`iff`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` only (standard). -/
theorem B3_iff (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hgcd : Finset.univ.gcd v = 1)
    (delta : ℝ) (hd0 : 0 < delta) (hd2 : delta < 1 / 2) :
    (∃ t : ℝ, delta ≤ gap v t) ↔
      (∃ z : Fin 6 → ℤ,
        (fun j => (((z j : ℝ) - delta * (zonoCenterZ v j : ℝ)) / (1 - 2 * delta))) ∈ LRZ v) := by
  constructor
  · rintro ⟨t, ht⟩; exact B3_forward v t delta hd2 ht
  · rintro ⟨z, hz⟩; exact B3_backward v hv hgcd delta hd0 hd2 z hz

/-! ## Part 4 (B4): successive minimum `lambda1` of the difference body `LRZ v - LRZ v`

Per `zonotope_plan.md`'s B4 row and Rule I8 (minimal generality), we specialize directly to the one
concrete family this project needs: `K_v := LRZ v - LRZ v`, rather than an abstract
symmetric-convex-body definition. Since `LRZ v = {∑ t i • u i | 0 ≤ t i ≤ 1}`, a direct unfolding
shows `LRZ v - LRZ v = {∑ s i • u i | -1 ≤ s i ≤ 1}` (write `s = t - t'`; conversely any
`s ∈ [-1,1]` splits as `t = max s 0 ∈ [0,1]`, `t' = max (-s) 0 ∈ [0,1]` with `s = t - t'`). We use
this `[-1,1]`-parametrized form directly in the definition of `lambda1`, avoiding the need for a
separate `LRZdiff` set and its own membership API: this is the "concrete formulation, easiest for
downstream B5/B7" alternative flagged by the task, chosen over the literal `LRZ v - LRZ v` Set
difference to avoid re-deriving the splitting lemma before every use. -/

/-- The `[-1,1]`-coefficient zonotope, definitionally equal to `LRZ v - LRZ v` (see
`LRZdiff_eq_sub` below). This is `K_v` in `zonotope_plan.md`'s notation. -/
def LRZdiff (v : Fin 7 → ℤ) : Set (Fin 6 → ℝ) :=
  {x | ∃ s : Fin 7 → ℝ, (∀ i, -1 ≤ s i ∧ s i ≤ 1) ∧
      x = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ))}

/-- `LRZdiff v` really is `LRZ v - LRZ v` (Minkowski difference of sets), justifying the name and
the docstring claim above. Not used downstream (B5/B7 work with `LRZdiff`'s `[-1,1]` form
directly), kept for the record / I6 sanity. -/
theorem LRZdiff_eq_sub (v : Fin 7 → ℤ) :
    LRZdiff v = LRZ v - LRZ v := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨∑ i, (max (s i) 0) • (fun j => ((LRZgens v i j : ℤ) : ℝ)),
      ⟨fun i => max (s i) 0, fun i => ⟨le_max_right _ _, by
        rcases le_total (s i) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h]; linarith [(hs i).2]⟩, rfl⟩,
      ∑ i, (max (-(s i)) 0) • (fun j => ((LRZgens v i j : ℤ) : ℝ)),
      ⟨fun i => max (-(s i)) 0, fun i => ⟨le_max_right _ _, by
        rcases le_total (-(s i)) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h]; linarith [(hs i).1]⟩, rfl⟩, ?_⟩
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases le_total (s i) 0 with h | h
    · simp [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -(s i))]
    · simp [max_eq_left h, max_eq_right (by linarith : -(s i) ≤ 0)]
  · rintro ⟨p, ⟨tp, htp, rfl⟩, q, ⟨tq, htq, rfl⟩, rfl⟩
    refine ⟨fun i => tp i - tq i, fun i => ⟨by linarith [(htp i).1, (htq i).2],
      by linarith [(htp i).2, (htq i).1]⟩, ?_⟩
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `0 ∈ LRZdiff v` (I6 trivial example), witnessed by `s = 0`. -/
theorem zero_mem_LRZdiff (v : Fin 7 → ℤ) : (0 : Fin 6 → ℝ) ∈ LRZdiff v := by
  exact ⟨0, fun i => ⟨by norm_num, by norm_num⟩, by simp⟩

/-- `LRZdiff v` is centrally symmetric: `x ∈ LRZdiff v → -x ∈ LRZdiff v`. Immediate from negating
the witness `s`; this is the symmetry hypothesis Minkowski's theorem needs (`h_symm` in
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`). -/
theorem LRZdiff_symm (v : Fin 7 → ℤ) (x : Fin 6 → ℝ) (hx : x ∈ LRZdiff v) :
    -x ∈ LRZdiff v := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨fun i => -(s i), fun i => ⟨by linarith [(hs i).2], by linarith [(hs i).1]⟩, ?_⟩
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **B4, DEFINITION VERSIONED v1.1 (I10), 2026-09-26.** The first successive minimum of
`K_v = LRZdiff v`: the infimum of `lambda > 0` such that `lambda • K_v` contains a nonzero point
of `ℤ^6`, matching MSS's `λ₁(K) := min{λ>0 : λK ∩ ℤ^d ≠ {0}}` (paper p.10) directly: the defining
condition below is literally "`z ∈ lam • K_v`", spelled out via `K_v`'s own `s ∈ [-1,1]^7`
parametrization (`∃ s, ∀ i, -lam ≤ s i ∧ s i ≤ lam, z = ∑ i, s i • u_i`, i.e. `s` ranges over
`[-lam,lam]^7` instead of `[-1,1]^7`), rather than introducing a separate scalar-multiplication-of-
a-`Set` operation.

**v1.0 (this session's B5 task, Part 1/Rule 6 finding, kept here for the record) was WRONG and is
RETRACTED.** v1.0 read `(fun j => lam * (z j : ℝ)) ∈ LRZdiff v`, i.e. "`lam * z ∈ K_v`" — the
reciprocal of the correct condition. This is degenerate: `K_v` is convex and contains `0`, so for
ANY fixed nonzero integer `z` with `LRZgens v 0 ≠ 0`, taking `s := fun i => if i = 0 then lam else
0` shows `lam * z ∈ K_v` (in the v1.0 sense, with `z := LRZgens v 0`) for **every** `lam ∈ (0,1]`
simultaneously (not just up to some threshold) — so v1.0's defining set contains `(lam,
LRZgens v 0)` for every `lam ∈ (0,1]`, hence v1.0's `lambda1 v = sInf (0,1] = 0` identically for
every `v` with `LRZgens v 0 ≠ 0` (essentially all `v`). v1.0's `lambda1` was thus NOT the
successive minimum at all: it was a constant-zero junk quantity, and `lambda1_le_one`'s proof
(below) only ever established the weak, uninformative bound `≤ 1`, never noticing the set was
actually unbounded below by open intervals reaching `0`. **This means the previously
orchestrator-confirmed "B4 PROVED and VERIFIED" milestone proved a true but mathematically
CONTENT-FREE statement** (`lambda1_nonneg`, `lambda1_le_one` both hold trivially of the constant
function `0`); nothing downstream had yet consumed `lambda1` (grepped: no reference outside this
file), so no other atom's label is affected by this correction, but B4's status here drops from
VERIFIED to the corrected v1.1 statement below, freshly proved in this session. -/
noncomputable def lambda1 (v : Fin 7 → ℤ) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧ ∃ z : Fin 6 → ℤ, z ≠ 0 ∧
    ∃ s : Fin 7 → ℝ, (∀ i, -lam ≤ s i ∧ s i ≤ lam) ∧
      (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ))}

/-- `lambda1 v ≥ 0` always (the defining set consists of positive reals; `Real.sInf_nonneg`
handles emptiness/unboundedness via the junk-value convention without needing a separate
nonemptiness argument). -/
theorem lambda1_nonneg (v : Fin 7 → ℤ) : 0 ≤ lambda1 v := by
  apply Real.sInf_nonneg
  rintro lam ⟨hlam, -⟩
  exact hlam.le

/-- **I6 non-vacuity / Rule 3 falsification check, smallest instance.** For `v` with `LRZgens v 0
≠ 0`, `lambda1 v ≤ 1`: take `z := LRZgens v 0`, `lam := 1`, witnessed by `s := fun i => if i = 0
then 1 else 0` in `LRZdiff v` (all other coordinates zero, so the sum collapses to the single `i =
0` term). This confirms the defining set is nonempty in the generic case (a definition with an
always-empty defining set would be vacuous, Rule I6 item 3) and pins a concrete numeric value used
as a sanity check before trusting the definition further. -/
theorem lambda1_le_one (v : Fin 7 → ℤ) (h0 : LRZgens v 0 ≠ 0) : lambda1 v ≤ 1 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro lam ⟨hlam, -⟩
    exact hlam.le
  · refine ⟨one_pos, LRZgens v 0, h0, fun i => if i = 0 then 1 else 0, fun i => ?_, ?_⟩
    · by_cases hi : i = 0 <;> simp [hi]
    · funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (0 : Fin 7)]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ _) h

/-- **B5 (MSS Lemma 2.5), corrected 2026-09-26 -- see `b5_notes_2026-09-26.md`.**

Reading arXiv:2411.06903 Section 2 in full (never done before this session) shows Lemma 2.5's
actual statement is: for a convex body `C subseteq R^d` and `l in N`, `|C cap Z^d| > l^d ==>
lambda_1(C - C) <= 1/l`, proved by the elementary pigeonhole: two lattice points of `C` colliding
mod `l` give a nonzero integer `w := (x-y)/l in Z^d cap (1/l)(C-C)`, hence `lambda_1(C-C) <= 1/l`
directly by definition of `lambda_1`. No volume/covolume/Minkowski machinery appears inside Lemma
2.5's own proof; that machinery (Minkowski's Theorem 2.4,
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) is used elsewhere in the paper,
not here -- the task's premise that B5 needs it does not hold for this specific lemma once the
proof is actually read.

**Where the 2026-09-25/26 `sorry` attempt (retracted) went wrong:** it counted lattice points of
an already-`l`-scaled copy of `LRZdiff v` (`z/l in LRZdiff v`) instead of `LRZ v` itself (`C`,
unscaled -- the zonotope, not its difference body). Dividing an already-scaled difference by `l` a
second time cancels the effect the count was supposed to buy, exactly reproducing the "`l`
cancels, only get `<= 1`" dead end. The fix is to count points of `LRZ v` (the paper's `C`)
directly, matching `C cap Z^d` in Lemma 2.5's own statement; `LRZdiff v = LRZ v - LRZ v` supplies
`C - C` (`LRZdiff_eq_sub`, unchanged).

**A second, independent bug was found in the same Rule 6 pass (I10 version bump on `lambda1`,
above `B4`'s definition): `lambda1`'s v1.0 defining condition (`lam * z in LRZdiff v`) was the
reciprocal of MSS's `lambda_1(K) := min{lambda : lambda K cap Z^d != {0}}` and was degenerate
(`= 0` identically for essentially all `v`), making the previously "VERIFIED" B4 milestone
content-free even though it type-checked. `lambda1` is corrected to v1.1 above (`z in lam . K_v`,
spelled out via `K_v`'s own `s`-parametrization); this proof uses v1.1.** -/
theorem B5_pigeonhole (v : Fin 7 → ℤ) (l : ℕ) (hl : 0 < l)
    (hcard : (l : ℕ) ^ 6 < {z : Fin 6 → ℤ | (fun j => ((z j : ℤ) : ℝ)) ∈ LRZ v}.ncard) :
    lambda1 v ≤ 1 / l := by
  haveI : NeZero l := ⟨hl.ne'⟩
  set S : Set (Fin 6 → ℤ) := {z : Fin 6 → ℤ | (fun j => ((z j : ℤ) : ℝ)) ∈ LRZ v} with hSdef
  have htcard : (Set.univ : Set (Fin 6 → ZMod l)).ncard = l ^ 6 := by
    rw [Set.ncard_univ]
    simp [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hlt : (Set.univ : Set (Fin 6 → ZMod l)).ncard < S.ncard := by
    rw [htcard]; exact hcard
  obtain ⟨x, hxS, y, hyS, hxy, hcol⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt
      (f := fun z : Fin 6 → ℤ => fun j => ((z j : ℤ) : ZMod l))
      (fun a _ => Set.mem_univ _)
  have hdvd : ∀ j, (l : ℤ) ∣ (x j - y j) := fun j =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub (y j) (x j) l).mp (congrFun hcol j).symm
  set z : Fin 6 → ℤ := fun j => (hdvd j).choose with hzdef
  have hzl : ∀ j, x j - y j = (l : ℤ) * z j := fun j => (hdvd j).choose_spec
  have hzne : z ≠ 0 := by
    intro hz0
    apply hxy
    funext j
    have hj := hzl j
    rw [congrFun hz0 j] at hj
    simp only [Pi.zero_apply, mul_zero] at hj
    linarith
  obtain ⟨tx, htx, hxeq⟩ := hxS
  obtain ⟨ty, hty, hyeq⟩ := hyS
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro lam ⟨hlam, -⟩
    exact hlam.le
  · refine ⟨by positivity, z, hzne, fun i => (tx i - ty i) / l, fun i => ?_, ?_⟩
    · have hlpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
      have h1 : (-1:ℝ) ≤ tx i - ty i := by linarith [(htx i).1, (hty i).2]
      have h2 : tx i - ty i ≤ (1:ℝ) := by linarith [(htx i).2, (hty i).1]
      constructor
      · show -(1 / (l:ℝ)) ≤ (tx i - ty i) / l
        rw [← neg_div]
        exact div_le_div_of_nonneg_right h1 hlpos.le
      · show (tx i - ty i) / l ≤ 1 / (l:ℝ)
        exact div_le_div_of_nonneg_right h2 hlpos.le
    · funext j
      have hlne : (l:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      have hcast : (z j : ℝ) = ((x j : ℝ) - (y j : ℝ)) / l := by
        have hc := congrArg (fun n : ℤ => (n : ℝ)) (hzl j)
        push_cast at hc
        rw [hc, mul_comm, mul_div_assoc, div_self hlne, mul_one]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hxej := congrFun hxeq j
      have hyej := congrFun hyeq j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hxej hyej
      rw [hcast, hxej, hyej, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring

/-! ### B7 atom (a): `lambda1`'s defining infimum is ATTAINED (constructive successive-minimum
witness), 2026-09-26 session.

Task scope for this session (per orchestrator): ONLY this attainment fact, not Prop 3.3/3.4's
determinant/genericity case split (a separate, later atom that consumes this one's output).

**Rule 3 falsification/sanity pass (done BEFORE writing any of the Lean below, per the task's
explicit instruction and this project's own B7 history of writing Lean too early).** Exact-rational
brute-force LP search (`/tmp/lam1check.py`, this session, min-max linear program over all integer
`z` in a bounded box, `scipy.optimize.linprog`, exact enough to trust for a go/no-go check):
for `v = (1,1,1,1,1,1,1)`, `lambda1 v = 0.5` exactly (rational), attained at a genuine LP vertex;
for `v = (2,3,1,4,1,1,1)`, `lambda1 v = 1/3` exactly, likewise attained at a vertex. Both searches
found a finite, attained minimum, not an unattained infimum approached only in a limit — this
supports the claim that attainment is TRUE (not merely plausible) before investing in the Lean
proof below, and specifically supports the "finitely many candidate `z`, each with an attained
per-`z` minimum norm, then a finite min over those" architecture used below (linprog itself solves
each per-`z` slice by finding a vertex of a compact polytope, exactly mirroring the compactness
argument formalized here).

**Proof architecture (Rule I8: discrete/finite argument, no abstract successive-minimum machinery
beyond what Mathlib gives for free).** `lambda1 v` is not reformulated as a `Finset`-indexed
literal `min` (I10 version bump not needed): the existing `sInf`-based v1.1 definition is kept
as the source of truth, and this section proves a THEOREM about it (attainment) rather than
replacing it, so no downstream `lambda1` reference needs updating. The proof:

1. For a FIXED candidate `z`, the set of `s : Fin 7 → ℝ` with `‖s‖ ≤ 1` (sup/Pi norm, matching the
   `[-1,1]^7` box exactly via `pi_norm_le_iff_of_nonneg`) AND solving the defining linear equation
   is `Metric.closedBall 0 1 ∩ (linear map)⁻¹' {target}`: compact (closed ball compact since
   `Fin 7 → ℝ` is a `ProperSpace`, `Pi.pi_properSpace`; intersected with a closed preimage of a
   singleton under a continuous — finite sum of coordinate-projection-times-constant — map).
   The extreme value theorem (`IsCompact.exists_isMinOn`) then gives, WHEN this set is nonempty
   (`z` is "feasible at radius 1"), an actual minimizer `s0`, not just an infimum: this is
   `exists_min_norm_slice` below.
2. `lambda1_le_one` (already PROVED) bounds `lambda1 v ≤ 1`, so only `z` reachable with `‖s‖ ≤ 1`
   can matter; such `z` has every coordinate bounded by `N := ∑_i ∑_j |LRZgens v i j|` (crude but
   sufficient triangle-inequality bound, `zcoord_bound` below), so only FINITELY many `z` need
   checking — `Fintype.piFinset` of `Finset.Icc (-N) N` in each coordinate.
3. `Finset.exists_min_image` over that finite candidate set (filtered to the feasible, nonzero
   ones — nonempty by the `LRZgens v 0` witness already used in `lambda1_le_one`) picks the overall
   minimizing `z`, whose per-`z` minimizer `s0` from step 1 is exactly the pair the theorem needs.
   Both inequalities of `lambda1 v = ‖s0‖` are proved directly against the `sInf` definition
   (`csInf_le` one way, an explicit lower-bound argument the other way using steps 1-2 on an
   arbitrary competing member of the defining set) rather than by rewriting `lambda1` itself, so
   the `sInf` stays canonical throughout. -/

/-- Step 1 helper. For a fixed integer target `z` (as a real vector) and generator matrix from
`LRZgens v`, IF some `s` in the closed unit sup-ball solves the linear equation, THEN a
norm-MINIMIZING such `s0` exists (the infimum over this compact slice is attained). This is the
extreme value theorem applied to a continuous (finite linear combination) map and a compact
(closed-ball-intersect-closed-preimage) domain; no successive-minimum-specific machinery beyond
this is used. -/
theorem exists_min_norm_slice (v : Fin 7 → ℤ) (z : Fin 6 → ℤ)
    (hfeas : ∃ s : Fin 7 → ℝ, ‖s‖ ≤ 1 ∧
      (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ))) :
    ∃ s0 : Fin 7 → ℝ, ‖s0‖ ≤ 1 ∧
      (fun j => (z j : ℝ)) = ∑ i, s0 i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) ∧
      ∀ s : Fin 7 → ℝ, ‖s‖ ≤ 1 →
        (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) → ‖s0‖ ≤ ‖s‖ := by
  set E : (Fin 7 → ℝ) → (Fin 6 → ℝ) :=
    fun s => ∑ i : Fin 7, s i • (fun j : Fin 6 => ((LRZgens v i j : ℤ) : ℝ)) with hEdef
  set target : Fin 6 → ℝ := (fun j => (z j : ℝ)) with htdef
  set Sset : Set (Fin 7 → ℝ) := Metric.closedBall (0 : Fin 7 → ℝ) 1 ∩ E ⁻¹' {target} with hSdef
  have hcont : Continuous E := by
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).smul continuous_const
  have hclosed : IsClosed (E ⁻¹' {target}) := isClosed_singleton.preimage hcont
  have hcompact : IsCompact Sset := (isCompact_closedBall (0 : Fin 7 → ℝ) 1).inter_right hclosed
  have hne : Sset.Nonempty := by
    obtain ⟨s, hs1, hs2⟩ := hfeas
    exact ⟨s, by simpa [Metric.mem_closedBall] using hs1, by simpa [hEdef, htdef] using hs2.symm⟩
  obtain ⟨s0, hs0mem, hmin⟩ :=
    hcompact.exists_isMinOn hne (f := norm) continuous_norm.continuousOn
  refine ⟨s0, ?_, ?_, ?_⟩
  · have := hs0mem.1
    simpa [Metric.mem_closedBall] using this
  · have := hs0mem.2
    simpa [hEdef, htdef, Set.mem_preimage, Set.mem_singleton_iff] using this.symm
  · intro s hs1 hs2
    have hsmem : s ∈ Sset := ⟨by simpa [Metric.mem_closedBall] using hs1,
      by simpa [hEdef, htdef, Set.mem_preimage, Set.mem_singleton_iff] using hs2.symm⟩
    exact hmin hsmem

/-- Step 2 helper: any `z` reached by a coefficient vector `s` with `‖s‖ ≤ 1` (sup norm) has every
coordinate bounded by the crude constant `N := ∑_i ∑_j |LRZgens v i j|`, by the triangle
inequality applied coordinatewise. -/
theorem zcoord_bound (v : Fin 7 → ℤ) (z : Fin 6 → ℤ) (s : Fin 7 → ℝ) (hs : ‖s‖ ≤ 1)
    (heq : (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ))) (j : Fin 6) :
    |z j| ≤ ∑ i : Fin 7, |LRZgens v i j| := by
  have hsi : ∀ i, |s i| ≤ 1 := by
    intro i
    have h := (pi_norm_le_iff_of_nonneg (x := s) (r := 1) (by norm_num)).mp hs i
    simpa [Real.norm_eq_abs] using h
  have hzj : (z j : ℝ) = ∑ i : Fin 7, s i * ((LRZgens v i j : ℤ) : ℝ) := by
    have h := congrFun heq j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hboundR : |(z j : ℝ)| ≤ ∑ i : Fin 7, ((|LRZgens v i j| : ℤ) : ℝ) := by
    rw [hzj]
    calc |∑ i : Fin 7, s i * ((LRZgens v i j : ℤ) : ℝ)|
        ≤ ∑ i : Fin 7, |s i * ((LRZgens v i j : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin 7, |s i| * |((LRZgens v i j : ℤ) : ℝ)| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
      _ ≤ ∑ i : Fin 7, 1 * |((LRZgens v i j : ℤ) : ℝ)| := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (hsi i) (abs_nonneg _)
      _ = ∑ i : Fin 7, ((|LRZgens v i j| : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl; intro i _
          rw [one_mul, Int.cast_abs]
  have hcast : ((∑ i : Fin 7, |LRZgens v i j| : ℤ) : ℝ) = ∑ i : Fin 7, ((|LRZgens v i j| : ℤ) : ℝ) := by
    push_cast; ring
  rw [← hcast] at hboundR
  have hzjcast : |(z j : ℝ)| = ((|z j| : ℤ) : ℝ) := by rw [Int.cast_abs]
  rw [hzjcast] at hboundR
  exact_mod_cast hboundR

/-- **B7 atom (a), the target of this session.** `lambda1`'s defining infimum is ATTAINED: there
is an actual nonzero integer vector `z` and coefficient vector `s` with every `s i` in
`[-lambda1 v, lambda1 v]` solving the equation, not merely an infimum approached in a limit.
Needs `LRZgens v 0 ≠ 0` (same hypothesis as `lambda1_le_one`, which this proof reuses to bound the
search and to seed a nonempty candidate set). -/
theorem lambda1_attained (v : Fin 7 → ℤ) (h0 : LRZgens v 0 ≠ 0) :
    ∃ z : Fin 6 → ℤ, z ≠ 0 ∧ ∃ s : Fin 7 → ℝ,
      (∀ i, -lambda1 v ≤ s i ∧ s i ≤ lambda1 v) ∧
      (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) := by
  classical
  set N : ℤ := ∑ i : Fin 7, ∑ j : Fin 6, |LRZgens v i j| with hNdef
  set cand : Finset (Fin 6 → ℤ) := Fintype.piFinset (fun _ : Fin 6 => Finset.Icc (-N) N) with hcanddef
  -- feasibility at radius 1, as a (classically decidable) predicate on z
  set feas : (Fin 6 → ℤ) → Prop := fun z => ∃ s : Fin 7 → ℝ, ‖s‖ ≤ 1 ∧
    (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) with hfeasdef
  set candNZ : Finset (Fin 6 → ℤ) := cand.filter (fun z => z ≠ 0 ∧ feas z) with hcandNZdef
  -- the seed witness z0 = LRZgens v 0, s = e_0, lam = 1
  have he0norm : ‖(fun i : Fin 7 => if i = (0 : Fin 7) then (1 : ℝ) else 0)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  have he0eq : (fun j => ((LRZgens v 0 j : ℤ) : ℝ))
      = ∑ i, (fun i : Fin 7 => if i = (0:Fin 7) then (1:ℝ) else 0) i •
          (fun j => ((LRZgens v i j : ℤ) : ℝ)) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (0 : Fin 7)]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hz0feas : feas (LRZgens v 0) :=
    ⟨fun i => if i = 0 then 1 else 0, he0norm, he0eq⟩
  have hcolN : ∀ j : Fin 6, ∑ i : Fin 7, |LRZgens v i j| ≤ N := by
    intro j
    rw [hNdef]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j' _ => abs_nonneg (LRZgens v i j')) (Finset.mem_univ j)
  have hz0bound : LRZgens v 0 ∈ cand := by
    rw [hcanddef, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    obtain ⟨s, hs1, hs2⟩ := hz0feas
    have hb := (zcoord_bound v (LRZgens v 0) s hs1 hs2 j).trans (hcolN j)
    exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
  have hz0candNZ : LRZgens v 0 ∈ candNZ := by
    rw [hcandNZdef, Finset.mem_filter]
    exact ⟨hz0bound, h0, hz0feas⟩
  have hcandNZ_ne : candNZ.Nonempty := ⟨LRZgens v 0, hz0candNZ⟩
  -- per-z minimizer, packaged as a total function on `Fin 6 → ℤ` via choice
  have hex : ∀ z : Fin 6 → ℤ, feas z → ∃ s0 : Fin 7 → ℝ, ‖s0‖ ≤ 1 ∧
      (fun j => (z j : ℝ)) = ∑ i, s0 i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) ∧
      ∀ s : Fin 7 → ℝ, ‖s‖ ≤ 1 →
        (fun j => (z j : ℝ)) = ∑ i, s i • (fun j => ((LRZgens v i j : ℤ) : ℝ)) → ‖s0‖ ≤ ‖s‖ :=
    fun z hz => exists_min_norm_slice v z hz
  choose! sOf hsOf using hex
  set mval : (Fin 6 → ℤ) → ℝ := fun z => if hz : feas z then ‖sOf z‖ else 0 with hmvaldef
  obtain ⟨zmin, hzmin_mem, hzmin_min⟩ := Finset.exists_min_image candNZ mval hcandNZ_ne
  have hzmin_feas : feas zmin := (Finset.mem_filter.mp hzmin_mem).2.2
  have hzmin_ne : zmin ≠ 0 := (Finset.mem_filter.mp hzmin_mem).2.1
  obtain ⟨hs0_le1, hs0_eq, hs0_min⟩ := hsOf zmin hzmin_feas
  set s0 := sOf zmin with hs0def
  set lam : ℝ := ‖s0‖ with hlamdef
  have hlam_mval : lam = mval zmin := by
    rw [hmvaldef, hlamdef, hs0def]; simp [hzmin_feas]
  have hmval_z0_le_one : mval (LRZgens v 0) ≤ 1 := by
    rw [hmvaldef]; simp only [hz0feas, dif_pos]
    exact ((hsOf (LRZgens v 0) hz0feas).2.2 _ he0norm he0eq).trans he0norm
  have hlam_le_one : lam ≤ 1 := by
    calc lam = mval zmin := hlam_mval
      _ ≤ mval (LRZgens v 0) := hzmin_min (LRZgens v 0) hz0candNZ
      _ ≤ 1 := hmval_z0_le_one
  -- `lam` is a lower bound of `lambda1`'s defining set: the hard direction.
  have hlb : ∀ x ∈ {lam' : ℝ | 0 < lam' ∧ ∃ z' : Fin 6 → ℤ, z' ≠ 0 ∧
      ∃ s' : Fin 7 → ℝ, (∀ i, -lam' ≤ s' i ∧ s' i ≤ lam') ∧
        (fun j => (z' j : ℝ)) = ∑ i, s' i • (fun j => ((LRZgens v i j : ℤ) : ℝ))}, lam ≤ x := by
    rintro lam' ⟨hlam'pos, z', hz'ne, s', hs'box, hs'eq⟩
    by_cases hcase : lam' ≤ 1
    · have hs'norm : ‖s'‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
        intro i
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hs'box i).1], by linarith [(hs'box i).2]⟩
      have hz'feas : feas z' := ⟨s', hs'norm, hs'eq⟩
      have hz'bound : z' ∈ cand := by
        rw [hcanddef, Fintype.mem_piFinset]
        intro j
        rw [Finset.mem_Icc]
        have hb := (zcoord_bound v z' s' hs'norm hs'eq j).trans (hcolN j)
        exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
      have hz'candNZ : z' ∈ candNZ := by
        rw [hcandNZdef, Finset.mem_filter]; exact ⟨hz'bound, hz'ne, hz'feas⟩
      have hstep1 : mval zmin ≤ mval z' := hzmin_min z' hz'candNZ
      have hstep2 : mval z' ≤ ‖s'‖ := by
        rw [hmvaldef]; simp only [hz'feas, dif_pos]
        exact (hsOf z' hz'feas).2.2 s' hs'norm hs'eq
      have hstep3 : ‖s'‖ ≤ lam' := by
        rw [pi_norm_le_iff_of_nonneg hlam'pos.le]
        intro i
        rw [Real.norm_eq_abs, abs_le]
        exact hs'box i
      calc lam = mval zmin := hlam_mval
        _ ≤ mval z' := hstep1
        _ ≤ ‖s'‖ := hstep2
        _ ≤ lam' := hstep3
    · push_neg at hcase
      exact hlam_le_one.trans hcase.le
  have hlam_le_lambda1 : lam ≤ lambda1 v := by
    unfold lambda1
    apply le_csInf _ hlb
    exact ⟨1, one_pos, LRZgens v 0, h0, fun i => if i = 0 then 1 else 0,
      fun i => by by_cases hi : i = 0 <;> simp [hi], he0eq⟩
  refine ⟨zmin, hzmin_ne, s0, ?_, hs0_eq⟩
  intro i
  have hcoord : ‖s0 i‖ ≤ ‖s0‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg s0)).mp (le_refl _) i
  rw [Real.norm_eq_abs] at hcoord
  have hcoord' : |s0 i| ≤ lam := by rw [hlamdef]; exact hcoord
  have := abs_le.mp (hcoord'.trans hlam_le_lambda1)
  exact this

/-! ### B6: the projection `T` along a short primitive vector (`zonotope_plan.md` row B6)

`zonotope_plan.md`'s B6 row asks for `projT w : (Fin 6 → ℝ) →L[ℝ] (Fin 5 → ℝ)` with
`ker = span {w}` and `T` restricted to `ℤ^6` surjecting onto `ℤ^5`, for `w : Fin 6 → ℤ` with
`IsPrimitive w` (i.e. `gcd w = 1`), built by "extend `w` to a basis of `ℤ^6`, project onto the
complementary coordinates" — structurally the same HNF-flavored construction as B1's `phiAux`,
now one dimension lower (`Fin 6 → Fin 5` instead of `Fin 7 → Fin 6`).

**Reuse check (task instruction: check this FIRST).** `phiAux`/`phiAuxR` are already stated for
generic `k : ℕ` with domain `Fin (k+1)`, so `phiAux 5 w` and `phiAuxR 5 w` (for `w : Fin 6 → ℤ`)
literally ARE this construction at the required dimension: `phiAux_ker 5 w` gives kernel-exactness
over `ℤ`, `phiAuxR_ker 5 w` gives it over `ℝ` (`ker = span_ℝ {w}`, exactly the B6 spec), and
`phiAux_surjective 5 w` gives surjectivity onto `ℤ^5`. So B6 reduces to a thin wrapper packaging
`phiAuxR 5 w` as a `LinearMap` plus restating these three facts at `k = 5`, with NO new
construction needed. This confirms the plan's guess.

**Where the plan's spec does not match what's actually available (found by comparing against B1's
own correction note, not re-derived from scratch here).** B1's docstring already record a
falsification (Rule 3) of the natural guess "`gcd w = 1` alone suffices": `w = (1,0,0)` has
`gcd w = 1` but `phiAux` collapses to the identically-`0` map on it, because two consecutive
"peeled" coordinates are both `0`. The plan's B6 row inherits the same wrong guess
(`hw : IsPrimitive w`, i.e. `gcd w = 1` alone). The actual hypothesis `phiAux_ker`/
`phiAux_surjective`/`phiAuxR_ker` need, and that this file uses below, is BOTH `∀ i, w i ≠ 0` AND
`Finset.univ.gcd w = 1` — matching B1's Claim B/C corrections exactly, transported one dimension
down. `IsPrimitive` (`gcd = 1`) alone is insufficient for B6 too; the same `w = (1,0,0,0,0,0)`-style
counterexample (gcd 1, but two adjacent zero coordinates) applies verbatim at `k = 5`.

Falsification/sanity check (Rule 3/6) on concrete small instances before building on this route:
`w = (1,1,1,1,1,1)` (all nonzero, gcd 1: both hypotheses hold, `projT_ker`/`projT_int_surjective`
apply) and `w = (2,3,1,1,1,1)` (same). `w = (1,0,1,1,1,1)` has `gcd = 1` but violates `∀i, w i ≠ 0`
(the `IsPrimitive`-only spec's blind spot): `projT` is still DEFINED on it (the def carries no
hypothesis, matching B1's `phiAux`/`LRZgens` pattern) but the ker/surjectivity theorems below do
not apply to it, exactly as `phiAux_ker`/`phiAux_surjective` do not. No claim is made about
`projT`'s behavior on such `w`; this is the same open edge B1 already flagged, not a new gap. -/

/-- `projT w : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)`, the B6 projection, built directly from `phiAuxR`
at `k = 5`. DEF, no hypothesis on `w` (matching `phiAux`/`LRZgens`'s pattern: the definition is
unconditional, the good properties below need `w`'s nonzero-entries + gcd-1 hypotheses). -/
def projT (w : Fin 6 → ℤ) : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun := phiAuxR 5 w
  map_add' := phiAuxR_add 5 w
  map_smul' := fun r x => by
    simpa using phiAuxR_rsmul 5 w r x

@[simp] theorem projT_apply (w : Fin 6 → ℤ) (x : Fin 6 → ℝ) :
    projT w x = phiAuxR 5 w x := rfl

/-- **B6, kernel part**: `ker (projT w) = span_ℝ {w}` exactly, for `w` with all entries nonzero
and `gcd w = 1`. PROVED, immediate restatement of `phiAuxR_ker` at `k = 5` via
`Submodule.mem_span_singleton`. -/
theorem projT_ker (w : Fin 6 → ℤ) (hnz : ∀ i, w i ≠ 0) (hw : Finset.univ.gcd w = 1) :
    ∀ x : Fin 6 → ℝ, projT w x = 0 ↔ x ∈ Submodule.span ℝ {(fun i => (w i : ℝ))} := by
  intro x
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := (phiAuxR_ker 5 w hnz hw x).mp hx
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩
    exact (phiAuxR_ker 5 w hnz hw x).mpr ⟨m, hm.symm⟩

/-- `projT w` agrees with (the real cast of) `phiAux 5 w` on integer input. Immediate from
`phiAuxR_intCast` at `k = 5`. -/
theorem projT_intCast (w c : Fin 6 → ℤ) :
    projT w (fun i => (c i : ℝ)) = fun j => ((phiAux 5 w c j : ℤ) : ℝ) := by
  simpa using phiAuxR_intCast 5 w c

/-- **B6, surjectivity part**: `projT w` restricted to `ℤ^6` (as integer-valued points, cast to
`ℝ`) surjects onto `ℤ^5` (likewise cast), for `w` with all entries nonzero. PROVED, immediate
restatement of `phiAux_surjective` at `k = 5` transported through `projT_intCast`. Note this
direction needs only `hnz`, not `hw` (matching `phiAux_surjective`'s own hypothesis list, which
has no gcd requirement — gcd 1 is needed only for the kernel to be exactly `ℤ·w`, not for
surjectivity of the quotient map itself). -/
theorem projT_int_surjective (w : Fin 6 → ℤ) (hnz : ∀ i, w i ≠ 0) :
    ∀ z : Fin 5 → ℤ, ∃ c : Fin 6 → ℤ, projT w (fun i => (c i : ℝ)) = fun j => ((z j : ℤ) : ℝ) := by
  intro z
  obtain ⟨c, hc⟩ := phiAux_surjective 5 w hnz z
  refine ⟨c, ?_⟩
  rw [projT_intCast, hc]

/-! ### B7: Theorem 3.1's projection (`zonotope_plan.md` row B7) — semantics pinned, not proved

`zonotope_plan.md`'s B7 row: the image `T(Z_v)` is, up to lattice translate, the zonotope
`Z_{v'}` for `v' = vprime v a b` (`extremalPair`'s output), `T = projT w` for `w` a short vector
(B5/B6). To STATE this at all we first need a target object: `Z_{v'}` lives one dimension lower
than `Z_v` (generators indexed by `Fin 6`, in `Fin 5 → ℝ`), and `LRZ`/`LRZgens` above are
hard-coded to the `Fin 7 → Fin 6` shape. Exactly as B6 reused `phiAux`/`phiAuxR` at `k = 5` rather
than rederiving, the SAME generic-`k` `phiAux`/`phiAuxR` already used for `projT` also supply the
one-dimension-lower generators for free: `LRZgens6 v' i := phiAux 5 v' e_i` for `v' : Fin 6 → ℤ`
is the literal transcription of `LRZgens`'s own definition with `(7,6) ↦ (6,5)`. This section
defines `LRZgens6`/`LRZ6` this way (DEF, mirrors `LRZgens`/`LRZ` verbatim, no new construction)
so that B7's actual geometric claim can be written down precisely. -/

/-- `LRZgens6 v'`, the `Fin 6 → Fin 5 → ℤ` generators of the ONE-DIMENSION-LOWER zonotope
`Z_{v'}`, for `v' : Fin 6 → ℤ` (e.g. `v' = vprime v a b`). Literal transcription of `LRZgens`
at `(7,6) ↦ (6,5)`, reusing `phiAux 5` exactly as `projT` does (with a DIFFERENT parameter vector:
`projT w` quotients along the short vector `w`, `LRZgens6 v'` quotients along `v'` itself — same
machinery, unrelated inputs, not to be confused, per the task's standing warning about `EightMSS`'s
`Fin 7 → Fin 6` objects vs this file's `Fin 6 → Fin 5` ones). -/
def LRZgens6 (v' : Fin 6 → ℤ) : Fin 6 → (Fin 5 → ℤ) :=
  fun i => phiAux 5 v' (fun j => if j = i then 1 else 0)

/-- `LRZ6 v'`, the zonotope in `Fin 5 → ℝ` generated by `LRZgens6 v'`. Literal transcription of
`LRZ` one dimension down. -/
def LRZ6 (v' : Fin 6 → ℤ) : Set (Fin 5 → ℝ) :=
  {x | ∃ t : Fin 6 → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      x = ∑ i, t i • (fun j => ((LRZgens6 v' i j : ℤ) : ℝ))}

theorem zero_mem_LRZ6 (v' : Fin 6 → ℤ) : (0 : Fin 5 → ℝ) ∈ LRZ6 v' := by
  refine ⟨0, fun i => ⟨le_refl 0, zero_le_one⟩, ?_⟩
  simp

theorem LRZ6_nonempty (v' : Fin 6 → ℤ) : (LRZ6 v').Nonempty := ⟨0, zero_mem_LRZ6 v'⟩

/-- **B7, `w`-choice lemma (PROVED, 2026-09-26, DEFINITION VERSIONED v1.1, I10).**
`w := LRZgens v a - LRZgens v b`, i.e. the difference of the two generators singled out by
`a b`, is exactly the vector along which `projT` merges `u_a` and `u_b`: `T(u_a) = T(u_b)`
unconditionally (no `hwnz`/`hwgcd` needed — `projT w` kills its own parameter `w` by
construction, `phiAuxR_rsmul_self`, regardless of whether `w` is primitive or nonzero). This is
the exact content of the v1.0 gap the orchestrator flagged ("`w` is not constrained to be the
actual short vector"): `w`'s role in `projT_image_eq_LRZ6` below is not to BE a shortest lattice
vector (that is a separate, unproved fact about `lambda1`/B5, still open), only to be the
direction that identifies `u_a` with `u_b`, which `w := u_a - u_b` supplies for free. See
(development file, not part of this archive) §1 for the hand derivation and the Minkowski-sum argument
(`t_a•u_a + t_b•u_b` ranges over `[0, 2u_a]` as `t_a,t_b` range over `[0,1]` independently once
`T u_a = T u_b`) showing this is consistent with `vprime`'s SUM merge rule (`v'_a = v_a + v_b`),
not the difference rule the earlier `thm31_notes.md` draft guessed and `EightMSS.lean` already
corrected. -/
theorem projT_merge_eq (v : Fin 7 → ℤ) (a b : Fin 7) :
    projT (LRZgens v a - LRZgens v b) (fun j => ((LRZgens v a j : ℤ) : ℝ))
      = projT (LRZgens v a - LRZgens v b) (fun j => ((LRZgens v b j : ℤ) : ℝ)) := by
  set w : Fin 6 → ℤ := LRZgens v a - LRZgens v b with hw
  have hcast : (fun j => ((LRZgens v a j : ℤ) : ℝ)) - (fun j => ((LRZgens v b j : ℤ) : ℝ))
      = (fun j => (w j : ℝ)) := by
    funext j
    simp only [hw, Pi.sub_apply]
    push_cast
    ring
  have h0 : projT w (fun j => (w j : ℝ)) = 0 := by
    have h := phiAuxR_rsmul_self 5 w 1
    simpa [projT_apply] using h
  have hlin :
      projT w ((fun j => ((LRZgens v a j : ℤ) : ℝ)) - (fun j => ((LRZgens v b j : ℤ) : ℝ)))
        = projT w (fun j => ((LRZgens v a j : ℤ) : ℝ))
          - projT w (fun j => ((LRZgens v b j : ℤ) : ℝ)) :=
    map_sub (projT w) _ _
  rw [hcast, h0] at hlin
  exact (eq_of_sub_eq_zero hlin.symm)

/-- **B7 dream lemma. Label: FALSE as literally stated (v1.1 AND the repaired v1.2 candidate),
found 2026-09-26 sessions 3 and 4.**
MSS's Theorem 3.1 / Prop 3.3-3.4 content: the image of `Z_v` under the projection `T = projT w`
along a short vector `w` (B5/B6) is, up to a translate `t0 : Fin 5 → ℝ`, exactly the zonotope
`Z_{v'}` for `v' = vprime v a b` at the extremal pair `(a,b)`.

**DEFINITION VERSIONED v1.1, 2026-09-26 (I10).** v1.0 took `w` as a free parameter with only
`hwnz`/`hwgcd` hypotheses, unconnected to `a b` — the orchestrator-flagged gap. v1.1 replaces `w`
by the concrete `LRZgens v a - LRZgens v b` (no longer a free variable; `hwnz`/`hwgcd` dropped,
since `projT_merge_eq` above needs neither), and threads `extremalPair`'s actual witness
conditions as hypotheses `haz`/`hbz` on an explicit `z` (the point `extremalPair` ranks), so `a b`
are (INTENDED to be) constrained to be an extremal pair for SOME `z`, not arbitrary indices.

**FALSIFIED, set-level, 2026-09-26 session 3 (Rule 3; full derivation `b7_notes.md` §4).**
`haz`/`hbz` are in fact satisfied by `z := v` for EVERY choice of `a b` (all ratios `z_i/v_i`
become `1`, so both hypotheses hold as equalities unconditionally) — the side condition does not
actually pin `(a,b)` to a genuine extremal pair, contrary to the docstring's intent. Exploiting
this, a genericity-free, translate-invariant necessary condition (exact-rational Minkowski
zonotope volume, `vol(Z(v_1..v_6)) = Σ_{|S|=5} |det (v_i)_{i∈S}|`, sanity-checked against the
classical "5 unit vectors + diagonal ⇒ volume 6" instance) was computed on both sides of the
claimed equality for 5 concrete `(v,a,b)` triples satisfying the stated hypotheses via `z := v`.
**All 5 volumes mismatch, by ratios with no common pattern** (22 vs 16, 120 vs 339, 556 vs 232,
5458 vs 391, 551558 vs 13630) — a volume mismatch is an unconditional obstruction to set equality
up to translate, independent of any generator-correspondence assumption.

**REPAIR ATTEMPT AND SECOND FALSIFICATION, 2026-09-26 session 4 (Rule 3, I10 v1.2 candidate,
NOT committed to the Lean statement below).** Per the task's step 1, the two repair options from
the session-3 diagnosis (require `z` genuinely non-degenerate; equivalently hard-code `a b` as
`extremalPair`'s own witnesses) are the SAME repair in substance: both force `a` to be a true
argmax and `b` a true argmin of `z i / v i` for a `z` that is NOT a scalar multiple of `v`
(`∃ i j, z i * v j ≠ z j * v i`, matching `bridge31`'s own `hz` hypothesis in `EightMSS.lean`).
(development file, not part of this archive) was extended (`extremal_pair`, `is_nondegenerate`)
to compute genuine, non-degenerate extremal pairs by exact `Fraction` argmax/argmin (not `z:=v`)
and re-run `volume_test` on them. Ground covered: 6 concrete `(v,z)` instances, `z` explicitly
checked non-proportional to `v` in each, spanning small/uniform, reversed-order, "spike", and
random-looking `v` (case1: `v=(1,1,1,1,1,1,2)`, `z=(1,2,1,1,1,1,1)` → extremal `a=1,b=6`, through
case6: `v=(2,3,5,7,11,13,17)`, spike `z=(1,1,1,1,1,1,100)` → extremal `a=6,b=5`).
**Result: all 6 volumes mismatch again** (22 vs 10, 542 vs 243, 552 vs 24, 7224 vs 1687, 83029 vs
30743, 228434 vs 102143), with no common ratio (2.2, 2.23, 23, 4.28, 2.7, 2.24 — ruling out even
a missing global scalar-normalization fix). **Conclusion: constraining `(a,b)` to a genuine
extremal pair does NOT rescue the claim.** The falsity is not (only) in the vacuous `haz`/`hbz`
side condition; it is in the projection/merge construction itself (the candidate generator set
`{2·T(u_a)} ∪ {T(u_i) : i ≠ a,b}`, or the implicit assumption that the MSS zonotope equality is a
literal Lean `Set` translate rather than something involving an additional linear identification
this file's `phiAux`/`projT` basis convention does not currently supply). **I18 kill criterion
fired a second time**, now for the repair-by-genuine-extremal-pair strategy specifically (not
merely for the vacuous-hypothesis instance already killed in session 3). Autopsy: spec was
"replace `haz`/`hbz` with a non-degeneracy condition on `z`, forcing genuine argmax/argmin `a,b`";
killed by the same volume-mismatch method, now controlling for the exact defect it was meant to
fix; salvage is the extended harness (`extremal_pair`/`is_nondegenerate` in `phiaux_check.py`),
reusable for any future v1.2+ candidate. **The Lean statement below is therefore left unchanged
from v1.1** (bumping to a v1.2 hypothesis change would misrepresent the finding as a fix, when
session 4 shows it is not one); it remains `sorry`, label FALSE-as-typed / repair-not-found, and
is not attempted further this session per Rule 3 / I18 discipline.

**What remains true and unaffected:** `projT_merge_eq` above (`T(u_a) = T(u_b)`, PROVED
unconditionally) does not depend on `haz`/`hbz` at all and is not touched by this finding. The
earlier session's separate falsification (Section 3, `b7_notes.md`) of the per-generator
correspondence strategy is also unaffected and remains a valid, independent dead end for that
specific (stronger) strategy. -/
theorem projT_image_eq_LRZ6 (v z : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1)
    (a b : Fin 7)
    (haz : ∀ i, (z i : ℚ) / v i ≤ (z a : ℚ) / v a)
    (hbz : ∀ i, (z b : ℚ) / v b ≤ (z i : ℚ) / v i) :
    ∃ t0 : Fin 5 → ℝ,
      (fun x : Fin 6 → ℝ => projT (LRZgens v a - LRZgens v b) x) '' LRZ v =
        (fun x : Fin 5 → ℝ => x + t0) '' LRZ6 (LRSpectrumFull.EightMSS.vprime v a b) := by
  sorry

/-- **B8 (Lemma 3.6 pullback), STATEMENT ONLY (CONJECTURE, `sorry`), pinned per the task's
fallback instruction.** MSS's Lemma 3.6: given the 6-runner induction hypothesis at threshold
`1/7` applied to `vprime v a b`, and B7's projected-zonotope identification, a lonely time for
`vprime v a b` at gap `≥ 1/7` pulls back to a lonely time for `v` at gap `≥ 1/8`, with NO numeric
margin loss (see `bridge31_notes.md` §2: `1/(n+1) → 1/(n+2)` is exact here, the constants `1/7`
and `1/8` match `(n-1)/(n+1)` at `n=7` and its induction step exactly). This is stated directly in
the B3 zonotope-membership language (`B3_iff`) rather than MSS's `K_v`/successive-minima language,
since `B3_iff` is already VERIFIED in this file and is the bridge this project's downstream
`bridge31` actually needs; the `lambda1`/B5 successive-minimum apparatus is used only implicitly
through the `(3.7)`-style density hypothesis `hdense`, kept abstract here (as an existence
hypothesis on a lattice point of the projected zonotope) rather than re-derived, since B5 already
supplies the point-count bound this hypothesis packages. NOT attempted: the proof (the two-case
triangle-inequality construction of `bridge31_notes.md` §2, itself dependent on B7 closing
first — B7 is a hypothesis here via `hB7`, not re-proved). -/
theorem bridge31_pullback (v z : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1)
    (a b : Fin 7)
    (haz : ∀ i, (z i : ℚ) / v i ≤ (z a : ℚ) / v a)
    (hbz : ∀ i, (z b : ℚ) / v b ≤ (z i : ℚ) / v i)
    (hB7 : ∃ t0 : Fin 5 → ℝ,
      (fun x : Fin 6 → ℝ => projT (LRZgens v a - LRZgens v b) x) '' LRZ v =
        (fun x : Fin 5 → ℝ => x + t0) '' LRZ6 (LRSpectrumFull.EightMSS.vprime v a b))
    (hdense : ∃ z' : Fin 5 → ℤ,
      (fun j => (((z' j : ℝ) - (1 / 7 : ℝ) *
          (∑ i, LRZgens6 (LRSpectrumFull.EightMSS.vprime v a b) i j : ℝ)) / (1 - 2 * (1 / 7 : ℝ))))
        ∈ LRZ6 (LRSpectrumFull.EightMSS.vprime v a b)) :
    ∃ w : Fin 6 → ℤ,
      (fun j => (((w j : ℝ) - (1 / 8 : ℝ) * (zonoCenterZ v j : ℝ)) / (1 - 2 * (1 / 8 : ℝ))))
        ∈ LRZ v := by
  sorry

end LRSpectrumFull.EightZonotope
