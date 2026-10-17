/-
# E6: Barajas-Serra (2008, arXiv:0710.4495) reproved from scratch

Formalized independently from the paper text ((development file, not part of this archive), pdftotext of
the arXiv PDF), NOT from any existing Lean formalization. See
(development file, not part of this archive) for the full paper-to-project translation and the scope
decision (we bypass the paper's `chi_r`/`liminf` chromatic-number machinery entirely: Lemma 2 and
Corollary 3, as actually used, construct an EXPLICIT rational witness `t = lambda / N`, which is
already the real-valued statement this project wants; no discrete-chromatic-number layer is
needed).

Scope this session (E6-1, E6-2 only, per the assessed 12-20 session plan in
(development file, not part of this archive), "2026-09-26 E6 assessed"):

* E6-1: Lemma 2 (Prime Filtering) and Corollary 3, general and prime-agnostic.
* E6-2: Section 3's two easy cases, `|D| = 2` (3 runners) and `|D| = 4` (5 runners).

Rule 3 (falsify before proving): (development file, not part of this archive) checked, with exact integer
arithmetic:
  - eq. (3)'s valuation-shift mechanics: 27000 random trials across p in {3,5,7}, 0 failures.
  - Lemma 2's conclusion (a multiplier lambda exists whenever the level-sum hypothesis holds):
    344 hypothesis-respecting random instances (small p, small |D|), 0 failures, brute-force
    search over Z_N used as ground truth.
  - Negative controls (hypothesis deliberately violated): 3 instances exhibited, correctly NOT
    claimed to fail (Lemma 2 makes no claim when the hypothesis is violated; brute force still
    found witnesses in those small cases by luck, which is consistent, not a counterexample).

Rule 0 labels used throughout this file: every `theorem` here is either fully proved (no `sorry`,
label PROVED pending the adversarial review below, upgraded to VERIFIED once `lake build` is
clean with only standard axioms) or explicitly marked `sorry` and labeled CONJECTURE/STATEMENT
ONLY in its docstring. No result in this file claims a stronger label than its proof state.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import LRSpectrumFull.NearestInteger
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.BarajasSerra

open LRSpectrumFull

/-! ## Dictionary objects (Section 2 of the paper), pinned per Rule 5 -/

/-- `nu_p(x)`, the `p`-adic valuation of a positive natural number, eq. before Lemma 2.
We reuse Mathlib's `padicValNat`; this `def` exists only to fix notation matching the paper. -/
noncomputable def nu (p x : ℕ) : ℕ := padicValNat p x

/-- `r_p(x)`, the leading nonzero base-`p` digit of `x` (paper, Section 2, just before Lemma 2). -/
noncomputable def rp (p x : ℕ) : ℕ := (x / p ^ nu p x) % p

/-- `q(x)`, the index of the `(N/p)`-arc containing the residue of `x` mod `N = p^(m+1)`
(paper, Section 2, definition of `q = q_{p,m}`). -/
def qarc (p m N x : ℕ) : ℕ := ((x % N) / p ^ m) % p

/-- The `p`-level sets `D_p(i) = {d in D : nu_p(d) = i}` (paper, Section 2). -/
noncomputable def Dlevel (p : ℕ) (D : Finset ℕ) (i : ℕ) : Finset ℕ :=
  D.filter (fun d => nu p d = i)

/-- `Lambda_{j,p}` for `j < m`: the multiplier family `{1 + p^(m-j) k : 0 <= k < p}`
(paper, Section 2, just before eq. (2)). -/
def Lam (j m p : ℕ) : Finset ℕ :=
  (Finset.range p).image (fun k => 1 + p ^ (m - j) * k)

/-- `Lambda_{m,p} = {1, ..., p-1}` (paper, Section 2).
**Definition v1.1 (session 3, fixed from v1.0).** The original `v1.0` definition,
`(Finset.range p).image (fun k => k + 1) |>.erase 0`, evaluates to `{1, ..., p}` (the `erase 0`
was a no-op, since `0` is never in the image): it wrongly INCLUDED `p` itself, which is not a
unit mod `p` at all. No completed (`sorry`-free) theorem in this file cited `LamTop` under `v1.0`
(only `primeFiltering`/`primeFilteringCor3`, both still `sorry` at the time of this fix), so no
re-certification is needed per Rule 10; this is a same-session same-`sorry` correction, not a
mid-proof mutation. -/
def LamTop (p : ℕ) : Finset ℕ := (Finset.range (p - 1)).image (fun k => k + 1)

theorem LamTop_card (p : ℕ) : (LamTop p).card = p - 1 := by
  unfold LamTop
  rw [Finset.card_image_of_injective _ (add_left_injective 1), Finset.card_range]

theorem mem_LamTop (p k : ℕ) : k ∈ LamTop p ↔ 1 ≤ k ∧ k ≤ p - 1 := by
  unfold LamTop
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩

/-! ## Digit-arithmetic foundation (E6, session 2)

Falsify-checked (Rule 3) in (development file, not part of this archive), `check_eq3`: 27000 random trials
across `p in {3,5,7}`, `m in {1,2,3}`, 0 failures, before any of this was written in Lean.
-/

/-- `qarc` is unchanged by adding a multiple of the modulus `N`. Trivial periodicity fact,
proved first since everything below reduces to it. -/
theorem qarc_periodic (p m N x c : ℕ) :
    qarc p m N (x + N * c) = qarc p m N x := by
  unfold qarc
  rw [Nat.add_mul_mod_self_left]

/-- Core digit-shift identity: adding `p^m * e` (`e < p`) to `x` shifts exactly the top
(`m`-th) base-`p` digit of `x mod p^(m+1)` by `e`, wrapping mod `p`, with no effect on lower
digits and no leakage above the top digit (since `N = p^(m+1)` has no room for a digit `m+1`).
This is the arithmetic engine behind eq. (3) of the paper. -/
theorem qarc_add_topmul (p m : ℕ) (hp : 0 < p) (x e : ℕ) (he : e < p) :
    qarc p m (p ^ (m + 1)) (x + p ^ m * e) = (qarc p m (p ^ (m + 1)) x + e) % p := by
  unfold qarc
  have hpm : 0 < p ^ m := pow_pos hp m
  have hNpm : p ^ (m + 1) = p ^ m * p := pow_succ p m
  set N := p ^ (m + 1) with hN
  have he' : p ^ m * e < N := by rw [hNpm]; exact (Nat.mul_lt_mul_left hpm).mpr he
  have hstep1 : (x + p ^ m * e) % N = (x % N + p ^ m * e) % N := by
    conv_lhs => rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt he']
  rw [hstep1]
  have hdr : x % N = p ^ m * (x % N / p ^ m) + x % N % p ^ m := (Nat.div_add_mod (x % N) (p ^ m)).symm
  set d := x % N / p ^ m with hd
  set r0 := x % N % p ^ m with hr0
  have hx0lt : x % N < N := Nat.mod_lt x (by positivity)
  have hr0lt : r0 < p ^ m := Nat.mod_lt _ hpm
  have hdlt : d < p := by
    rw [hd]
    rw [Nat.div_lt_iff_lt_mul hpm]
    rw [mul_comm]
    rw [← hNpm]
    exact hx0lt
  set A := (d + e) % p with hA
  set c := (d + e) / p with hc
  have hde : d + e = p * c + A := by rw [hc, hA]; exact (Nat.div_add_mod (d + e) p).symm
  have hAltp : A < p := Nat.mod_lt _ hp
  have key : x % N + p ^ m * e = (p ^ m * A + r0) + N * c := by
    have h1 : x % N + p ^ m * e = p ^ m * (d + e) + r0 := by
      conv_lhs => rw [hdr]
      ring
    rw [h1, hde]
    have h2 : p ^ m * (p * c + A) = p ^ m * A + p ^ m * p * c := by ring
    rw [h2, hNpm]; ring
  have hAlt : p ^ m * A + r0 < N := by
    have hA1 : A + 1 ≤ p := hAltp
    have h1 : p ^ m * A + p ^ m ≤ p ^ m * p := by
      have : p ^ m * (A + 1) ≤ p ^ m * p := Nat.mul_le_mul_left _ hA1
      calc p ^ m * A + p ^ m = p ^ m * (A + 1) := by ring
        _ ≤ p ^ m * p := this
    have h2 : p ^ m * A + r0 < p ^ m * A + p ^ m := by omega
    rw [hNpm]
    omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hAlt]
  have hdiv : (p ^ m * A + r0) / p ^ m = A := by
    rw [Nat.add_comm, Nat.add_mul_div_left r0 A hpm]
    simp [Nat.div_eq_of_lt hr0lt]
  rw [hdiv, Nat.mod_eq_of_lt hAltp, Nat.mod_eq_of_lt hdlt]

/-! ## Carry lemma (E6, session 6: paper's eq. (5), Section 3, `|D| = 4` hard case)

Falsify-checked (Rule 3) in (development file, not part of this archive):
  - `check_carry_lemma`: fully general `x, y : ℕ` (not just multiples of a common `d`), random
    `p in {3,5,7}`, `m in {0,..,3}`, 50000 trials, 0 failures. This is the atomic carry fact
    (adding ANY two numbers in base `p`, the carry into a given digit position is always `0` or
    `1`) applied at digit position `m`, isolated from the `j*d`/`d` instance the paper actually
    uses, and strictly more general than what the theorem below needs.
  - `check_carry_lemma_jd`: the specialized `p = 5`, `x = j*d`, `y = d` instance plus the
    cumulative bound `q(j*d) = (j*q(d) + c_j) % p`, `0 <= c_j <= j-1`, 40047 trials
    (`d % 5 != 0` filtered), 0 failures.
Both before any of this was written in Lean.
-/

/-- **Carry lemma, general form.** Adding any two naturals `x, y`, the top (`m`-th) base-`p`
digit of the sum is the sum of the two top digits plus a carry-in from the lower digits, that
carry always being `0` or `1` (standard fact about base-`p` addition: at any digit position, the
carry-out of a digit-by-digit add is bounded by the number of summands minus one). This is the
atomic fact behind the paper's eq. (5) (`q((j+1)d) ⊂ q(jd) + q(d) + {0,1}`); the theorem below
specializes it to `x = j*d`, `y = d`. -/
theorem qarc_add_carry (p m : ℕ) (hp : 0 < p) (x y : ℕ) :
    ∃ c, c < 2 ∧
      qarc p m (p ^ (m + 1)) (x + y)
        = (qarc p m (p ^ (m + 1)) x + qarc p m (p ^ (m + 1)) y + c) % p := by
  set N := p ^ (m + 1) with hN
  have hpm : 0 < p ^ m := pow_pos hp m
  have hNpm : N = p ^ m * p := by rw [hN, pow_succ]
  have hNpos : 0 < N := by rw [hN]; positivity
  have hxymod : (x + y) % N = (x % N + y % N) % N := Nat.add_mod x y N
  set a := x % N with ha
  set b := y % N with hb
  have haltN : a < N := Nat.mod_lt _ hNpos
  have hbltN : b < N := Nat.mod_lt _ hNpos
  -- digit decompositions of a, b
  set qa := a / p ^ m with hqa
  set ra := a % p ^ m with hra
  set qb := b / p ^ m with hqb
  set rb := b % p ^ m with hrb
  have hadecomp : a = p ^ m * qa + ra := (Nat.div_add_mod a (p ^ m)).symm
  have hbdecomp : b = p ^ m * qb + rb := (Nat.div_add_mod b (p ^ m)).symm
  have hralt : ra < p ^ m := Nat.mod_lt _ hpm
  have hrblt : rb < p ^ m := Nat.mod_lt _ hpm
  have hqalt : qa < p := by
    have : qa < N / p ^ m := by
      rw [hqa]; exact Nat.div_lt_div_of_lt_of_dvd (Dvd.intro p hNpm.symm) haltN
    rwa [hNpm, Nat.mul_div_cancel_left p hpm] at this
  have hqblt : qb < p := by
    have : qb < N / p ^ m := by
      rw [hqb]; exact Nat.div_lt_div_of_lt_of_dvd (Dvd.intro p hNpm.symm) hbltN
    rwa [hNpm, Nat.mul_div_cancel_left p hpm] at this
  have hqaeq : qarc p m N x = qa := by
    unfold qarc; rw [← ha, ← hqa, Nat.mod_eq_of_lt hqalt]
  have hqbeq : qarc p m N y = qb := by
    unfold qarc; rw [← hb, ← hqb, Nat.mod_eq_of_lt hqblt]
  -- low-digit carry: ra + rb = p^m * carryLow + r', carryLow < 2
  set carryLow := (ra + rb) / p ^ m with hcl
  set r' := (ra + rb) % p ^ m with hr'
  have hlowsum : ra + rb = p ^ m * carryLow + r' := (Nat.div_add_mod (ra + rb) (p ^ m)).symm
  have hrltlt : r' < p ^ m := Nat.mod_lt _ hpm
  have hcllt : carryLow < 2 := by
    rw [hcl, Nat.div_lt_iff_lt_mul hpm]
    omega
  -- top-digit carry: qa + qb + carryLow = p * carryTop + digit, digit < p
  set S := qa + qb + carryLow with hS
  set digit := S % p with hdig
  set carryTop := S / p with hct
  have hSdecomp : S = p * carryTop + digit := (Nat.div_add_mod S p).symm
  have hdiglt : digit < p := Nat.mod_lt _ hp
  have habsum : a + b = N * carryTop + (p ^ m * digit + r') := by
    have h1 : a + b = p ^ m * S + r' := by
      rw [hadecomp, hbdecomp]; rw [show p ^ m * qa + ra + (p ^ m * qb + rb)
        = p ^ m * (qa + qb) + (ra + rb) by ring, hlowsum]
      rw [hS]; ring
    rw [h1, hSdecomp]
    have h2 : p ^ m * (p * carryTop + digit) = N * carryTop + p ^ m * digit := by
      rw [hNpm]; ring
    rw [h2]; ring
  have hrem_lt : p ^ m * digit + r' < N := by
    have h1 : p ^ m * digit + p ^ m ≤ p ^ m * p := by
      have : p ^ m * (digit + 1) ≤ p ^ m * p := Nat.mul_le_mul_left _ (by omega)
      calc p ^ m * digit + p ^ m = p ^ m * (digit + 1) := by ring
        _ ≤ p ^ m * p := this
    have h2 : p ^ m * digit + r' < p ^ m * digit + p ^ m := by omega
    rw [hNpm]; omega
  have habmod : (a + b) % N = p ^ m * digit + r' := by
    rw [habsum, Nat.add_comm (N * carryTop), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
  refine ⟨carryLow, hcllt, ?_⟩
  have hqxy : qarc p m N (x + y) = digit := by
    unfold qarc
    rw [hxymod, habmod]
    have hdivd : (p ^ m * digit + r') / p ^ m = digit := by
      rw [Nat.add_comm, Nat.add_mul_div_left r' digit hpm]
      simp [Nat.div_eq_of_lt hrltlt]
    rw [hdivd, Nat.mod_eq_of_lt hdiglt]
  rw [hqxy, hqaeq, hqbeq, hdig, hS]

/-- **Cumulative small-integer carry bound (paper's eq. (5), second inclusion).** For `j >= 1`,
multiplying `d` by the literal small integer `j` shifts `qarc d` by exactly `j` times itself, up
to a carry `c` bounded by `j - 1` (not just `0`/`1`, since carries accumulate across the `j - 1`
addition steps `d, 2d, ..., jd`). This is distinct from `qarc_mul_lam_eq`/`qarc_mul_lam_gt`, which
handle unit multipliers `1 + p^(m-r)*k`, not literal small `j`. -/
theorem qarc_mul_smallint_carry (p m : ℕ) (hp : 0 < p) (d j : ℕ) (hj : 1 ≤ j) :
    ∃ c, c ≤ j - 1 ∧
      qarc p m (p ^ (m + 1)) (j * d)
        = (j * qarc p m (p ^ (m + 1)) d + c) % p := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      have hqlt : qarc p m (p ^ (m + 1)) d < p := by unfold qarc; exact Nat.mod_lt _ hp
      exact ⟨0, by omega, by simp [Nat.mod_eq_of_lt hqlt]⟩
    · obtain ⟨c, hcle, heq⟩ := ih hj0
      obtain ⟨c2, hc2lt, heq2⟩ := qarc_add_carry p m hp (j * d) d
      have hjd1 : (j + 1) * d = j * d + d := by ring
      refine ⟨c + c2, by omega, ?_⟩
      rw [hjd1, heq2]
      have hmod1 : Nat.ModEq p (j * qarc p m (p ^ (m + 1)) d + c) (qarc p m (p ^ (m + 1)) (j * d)) := by
        unfold Nat.ModEq
        rw [Nat.mod_eq_of_lt (heq ▸ Nat.mod_lt _ hp : qarc p m (p ^ (m + 1)) (j * d) < p)]
        exact heq.symm
      have hmod2 : Nat.ModEq p
          (j * qarc p m (p ^ (m + 1)) d + c + qarc p m (p ^ (m + 1)) d + c2)
          (qarc p m (p ^ (m + 1)) (j * d) + qarc p m (p ^ (m + 1)) d + c2) :=
        (hmod1.add_right (qarc p m (p ^ (m + 1)) d)).add_right c2
      have hgoal : Nat.ModEq p
          ((j + 1) * qarc p m (p ^ (m + 1)) d + (c + c2))
          (qarc p m (p ^ (m + 1)) (j * d) + qarc p m (p ^ (m + 1)) d + c2) := by
        have heq3 : (j + 1) * qarc p m (p ^ (m + 1)) d + (c + c2)
            = j * qarc p m (p ^ (m + 1)) d + c + qarc p m (p ^ (m + 1)) d + c2 := by ring
        rw [heq3]; exact hmod2
      exact hgoal.symm

/-- eq. (3), first case: multiplying by `lambda = 1 + p^(m-j)*k` (`j < m`) does not move the
top digit `qarc` of `x` at all when `nu_p(x) > j`, because the correction term is then
divisible by the full modulus `p^(m+1)`. -/
theorem qarc_mul_lam_gt (p j m : ℕ) (hjm : j ≤ m) (k x : ℕ) (hvx : j < nu p x) :
    qarc p m (p ^ (m + 1)) ((1 + p ^ (m - j) * k) * x) = qarc p m (p ^ (m + 1)) x := by
  set i := nu p x with hidef
  have hi : p ^ i ∣ x := by rw [hidef]; unfold nu; exact pow_padicValNat_dvd
  obtain ⟨w, hw⟩ := hi
  have hval : (1 + p ^ (m - j) * k) * x
      = x + p ^ (m + 1) * (k * w * p ^ (i - j - 1)) := by
    have h1 : (1 + p ^ (m - j) * k) * x = x + p ^ (m - j) * k * x := by ring
    rw [h1, hw]
    have hexp : m - j + i = (m + 1) + (i - j - 1) := by omega
    have h2 : p ^ (m - j) * k * (p ^ i * w)
        = p ^ (m - j + i) * (k * w) := by rw [pow_add]; ring
    rw [h2, hexp, pow_add]; ring
  rw [hval]
  exact qarc_periodic p m (p ^ (m + 1)) x _

/-- eq. (3), second case: multiplying by `lambda = 1 + p^(m-j)*k` (`j < m`) shifts the top
digit `qarc` of `x` by exactly `k * r_p(x)` (mod `p`) when `nu_p(x) = j`. This, together with
`qarc_mul_lam_gt`, is the full eq. (3) mechanics falsify-checked in `falsify.py`. -/
theorem qarc_mul_lam_eq (p j m : ℕ) (hp : p.Prime) (hjm : j ≤ m) (k : ℕ) (hk : k < p)
    (x : ℕ) (hvx : nu p x = j) :
    qarc p m (p ^ (m + 1)) ((1 + p ^ (m - j) * k) * x)
      = (qarc p m (p ^ (m + 1)) x + k * rp p x) % p := by
  set i := nu p x with hidef
  have hi : p ^ i ∣ x := by rw [hidef]; unfold nu; exact pow_padicValNat_dvd
  obtain ⟨z, hz⟩ := hi
  -- `hvx` reads `i = j` after `set` folded `nu p x` to `i`; rewrite `hz` to use `j` directly,
  -- BEFORE ever using it to rewrite `x` (avoids re-creating a `nu p x` subterm out of `x`'s own
  -- expansion, which was the exact bug in the first (broken) attempt at this lemma).
  rw [hvx] at hz
  have hz0 : rp p x = z % p := by
    unfold rp
    rw [show nu p x = j from hidef ▸ hvx, hz, Nat.mul_div_cancel_left z (pow_pos hp.pos j)]
  have hval : (1 + p ^ (m - j) * k) * x = x + p ^ m * (k * z) := by
    have h1 : (1 + p ^ (m - j) * k) * x = x + p ^ (m - j) * k * x := by ring
    rw [h1, hz]
    have hexp : p ^ (m - j) * p ^ j = p ^ m := by rw [← pow_add]; congr 1; omega
    have h2 : p ^ (m - j) * k * (p ^ j * z) = p ^ m * (k * z) := by
      calc p ^ (m - j) * k * (p ^ j * z) = (p ^ (m - j) * p ^ j) * (k * z) := by ring
        _ = p ^ m * (k * z) := by rw [hexp]
    rw [h2]
  rw [hval]
  set e := (k * z) % p with he
  have hsplit : x + p ^ m * (k * z) = (x + p ^ m * e) + (p ^ (m + 1)) * (k * z / p) := by
    have hcz : k * z = p * (k * z / p) + e := (Nat.div_add_mod (k * z) p).symm
    have h3 : p ^ m * (p * (k * z / p) + e) = p ^ m * e + p ^ (m + 1) * (k * z / p) := by
      rw [pow_succ]; ring
    calc x + p ^ m * (k * z) = x + p ^ m * (p * (k * z / p) + e) := by rw [← hcz]
      _ = (x + p ^ m * e) + p ^ (m + 1) * (k * z / p) := by rw [h3]; ring
  rw [hsplit, qarc_periodic, qarc_add_topmul p m hp.pos x e (Nat.mod_lt _ hp.pos)]
  have hemod : e = (k * rp p x) % p := by
    rw [he, hz0, Nat.mul_mod, Nat.mod_eq_of_lt hk]
  have hfin : Nat.ModEq p e (k * rp p x) := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt (he ▸ Nat.mod_lt (k * z) hp.pos : e < p)]
    exact hemod
  exact Nat.ModEq.add_left _ hfin

/-- eq. (2): multiplying by a unit `lam` (coprime to `p`) does not change the `p`-adic
valuation. Needed to reduce `nu_p(lam * d)` back to `nu_p(d)` when composing several
`Lam j m p`-multipliers across levels in Lemma 2's induction (each factor is itself coprime to
`p`, so any partial product is too). -/
theorem nu_mul_coprime (p lam x : ℕ) [Fact p.Prime] (hlam : Nat.Coprime lam p)
    (hlam0 : lam ≠ 0) (hx0 : x ≠ 0) :
    nu p (lam * x) = nu p x := by
  unfold nu
  rw [padicValNat.mul hlam0 hx0]
  have hp : p.Prime := (inferInstance : Fact p.Prime).out
  have hndvd : ¬ p ∣ lam := hp.coprime_iff_not_dvd.mp hlam.symm
  have : padicValNat p lam = 0 := padicValNat.eq_zero_of_not_dvd hndvd
  omega

/-- `rp p x` (the leading nonzero base-`p` digit) is genuinely coprime to `p` for `x ≠ 0`: this
is what makes it "leading nonzero" (not just "some digit"), and is exactly what makes the
per-level shift `k ↦ (a + k * rp p x) % p` a bijection below (`injOn_shift_scale`), which is the
engine of the union-bound / pigeonhole step in `primeFiltering`. -/
theorem rp_coprime (p x : ℕ) (hp : p.Prime) (hx : x ≠ 0) : Nat.Coprime (rp p x) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set i := nu p x with hidef
  have hdvd : p ^ i ∣ x := by rw [hidef]; unfold nu; exact pow_padicValNat_dvd
  obtain ⟨w, hw⟩ := hdvd
  have hndvd : ¬ p ∣ w := by
    intro hpw
    obtain ⟨w', hw'⟩ := hpw
    have hcontra : p ^ (padicValNat p x + 1) ∣ x := by
      refine ⟨w', ?_⟩
      rw [show padicValNat p x = i from hidef, hw, hw', pow_succ]; ring
    exact pow_succ_padicValNat_not_dvd hx hcontra
  have hrpw : rp p x = w % p := by
    unfold rp
    rw [show nu p x = i from hidef, hw, Nat.mul_div_cancel_left w (pow_pos hp.pos i)]
  rw [hrpw]
  have hcw : Nat.Coprime w p := ((hp.coprime_iff_not_dvd).mpr hndvd).symm
  have hgcd : Nat.gcd p w = Nat.gcd (w % p) p := Nat.gcd_rec p w
  unfold Nat.Coprime at hcw ⊢
  rw [Nat.gcd_comm] at hcw
  rwa [hgcd] at hcw

/-- **VERIFIED, no `sorry` (session 12). The `r5`-WLOG reflection lemma requested for the
`|As| = 2` minority-element route (session 11 autopsy, item 1).** For `d` at level `0`
(`nu p d = 0`, i.e. `p ∤ d`) inside `p ^ k` (`k > 0`), the leading digit `rp` of the complement
`p ^ k - d` is the "digit complement" `p - rp p d`, NOT the `qarc_reflect` involution
`(p - 1) - (·)`: these are genuinely different maps (`qarc_reflect` reflects a digit `< p`
through `(p-1)/2`-ish, landing back in `{0, ..., p-1}`; here `rp` values live in `{1, ..., p-1}`
since `rp_coprime` forces `rp p d ≠ 0` at level `0`, and the complement `p - rp p d` also lands in
`{1, ..., p-1}`, matching the paper's `r5(N-d) = 5 - r5(d)` exactly, not `qarc`'s `4 - (·)`).
Proved directly from `rp`'s definition (`x / p ^ (nu p x) % p`) via `padicValNat.eq_zero_of_not_dvd`
on both `d` and `p ^ k - d` (level `0` is preserved by complementation, since `p ∣ p^k` and
`p ∤ d` forces `p ∤ (p^k - d)`, otherwise `p ∣ d` by `Nat.dvd_sub'` applied to the double
complement), then a `Nat.ModEq`/divisibility argument pinning `(p^k - d) % p` to `p - d % p`
using only `0 < d % p < p` and `p ∣ p^k` — no `m`/`N`/`qarc_reflect` machinery needed, confirming
the task's expectation that this is simpler than the full `qarc_reflect` identity. Falsify-checked
first (Rule 3, (development file, not part of this archive), `check_rp_reflect`, 100000 random trials,
`p ∈ {3,5,7}`, `k ∈ {1,..,5}`, `d` coprime to `p`, `0 < d < p^k`: 0 fails). -/
theorem rp_reflect (p k d : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hdpos : 0 < d) (hdlt : d < p ^ k) (hd : ¬ p ∣ d) :
    rp p (p ^ k - d) = p - rp p d := by
  have hp0 : 0 < p := hp.pos
  have hnud : nu p d = 0 := padicValNat.eq_zero_of_not_dvd hd
  have hrpd : rp p d = d % p := by unfold rp; rw [hnud]; simp
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hdle : d ≤ p ^ k := le_of_lt hdlt
  have hdndvd : ¬ p ∣ (p ^ k - d) := by
    intro hcon
    exact hd ((Nat.dvd_sub_iff_right hdle hpk).mp hcon)
  have hnud' : nu p (p ^ k - d) = 0 := padicValNat.eq_zero_of_not_dvd hdndvd
  have hrpd' : rp p (p ^ k - d) = (p ^ k - d) % p := by unfold rp; rw [hnud']; simp
  rw [hrpd', hrpd]
  -- Now a pure mod-`p` computation: `p ∣ p^k`, `0 < d % p < p`, `d ≤ p^k`, conclude
  -- `(p^k - d) % p = p - d % p`.
  have hdmodpos : 0 < d % p := Nat.pos_of_ne_zero (fun h0 => hd ((Nat.dvd_iff_mod_eq_zero).mpr h0))
  have hdmodlt : d % p < p := Nat.mod_lt _ hp0
  set r := (p ^ k - d) % p with hrdef
  have hrlt : r < p := Nat.mod_lt _ hp0
  have hsum : (p ^ k - d) + d = p ^ k := Nat.sub_add_cancel hdle
  have hmod0 : (p ^ k) % p = 0 := (Nat.dvd_iff_mod_eq_zero).mp hpk
  have key : (r + d % p) % p = 0 := by
    have h1 : ((p ^ k - d) + d) % p = ((p ^ k - d) % p + d % p) % p := Nat.add_mod _ _ _
    rw [hsum, hmod0, ← hrdef] at h1
    omega
  have hdvdsum : p ∣ (r + d % p) := (Nat.dvd_iff_mod_eq_zero).mpr key
  obtain ⟨c, hc⟩ := hdvdsum
  have hbound2 : r + d % p < 2 * p := by omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso; rw [h0, mul_zero] at hc; omega
    · exact h0
  have hclt2 : c < 2 := by
    by_contra hcon
    push_neg at hcon
    have : p * 2 ≤ p * c := Nat.mul_le_mul_left p hcon
    omega
  have hc1 : c = 1 := by omega
  rw [hc1, mul_one] at hc
  omega

/-- The per-level shift-and-scale map `k ↦ (a + k * c) % p` is injective on `Finset.range p`
when `c` is coprime to `p`. This is the abstract bijection behind eq. (3)'s "shifts the top digit
by `k * r_p(x)`": composing it with the union bound below (`exists_good_k`) is exactly the
pigeonhole step the paper's Lemma 2 induction needs at every level, general and top alike. -/
theorem injOn_shift_scale (p a c : ℕ) (hp : p.Prime) (hc : Nat.Coprime c p) :
    Set.InjOn (fun k => (a + k * c) % p) (Finset.range p) := by
  intro k1 hk1 k2 hk2 heq
  simp only [Finset.coe_range, Set.mem_Iio] at hk1 hk2
  simp only at heq
  have hmod : (a + k1 * c) ≡ (a + k2 * c) [MOD p] := heq
  have hmod2 : k1 * c ≡ k2 * c [MOD p] := (Nat.ModEq.add_left_cancel' a) hmod
  have hmod3 : k1 ≡ k2 [MOD p] := Nat.ModEq.cancel_right_of_coprime (by rwa [Nat.gcd_comm]) hmod2
  have : k1 % p = k2 % p := hmod3
  rwa [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hk2] at this

/-- **Generic union-bound / pigeonhole lemma.** If, for each `d` in a level `D'`, the "bad"
values of `k` (those landing `res d k` in the forbidden set `F d`) are counted injectively (so
there are at most `(F d).card` of them), and the total forbidden budget is strictly less than the
size of the search space `K`, then some `k ∈ K` is simultaneously good for every `d`. This is the
Finset-bookkeeping step flagged in the previous session's autopsy: `Finset.card_biUnion_le` to
bound the total bad set, then extract a good `k` from a nonempty complement (Rule 6: no ordering
assumption on `D'`, no assumption `K` is `Finset.range p` specifically). -/
theorem exists_good_k (K D' : Finset ℕ) (F : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ)
    (hinj : ∀ d ∈ D', Set.InjOn (res d) K)
    (hbound : (∑ d ∈ D', (F d).card) < K.card) :
    ∃ k ∈ K, ∀ d ∈ D', res d k ∉ F d := by
  classical
  set Bad : ℕ → Finset ℕ := fun d => K.filter (fun k => res d k ∈ F d) with hBaddef
  have hBadsub : ∀ d, Bad d ⊆ K := fun d => Finset.filter_subset _ _
  have hcard : ∀ d ∈ D', (Bad d).card ≤ (F d).card := by
    intro d hd
    have hsub : (Bad d).image (res d) ⊆ F d := by
      intro y hy
      simp only [Finset.mem_image, hBaddef, Finset.mem_filter] at hy
      obtain ⟨k, ⟨_, hk2⟩, hk3⟩ := hy
      rwa [← hk3]
    have hinjd : Set.InjOn (res d) (Bad d) := (hinj d hd).mono (hBadsub d)
    calc (Bad d).card = ((Bad d).image (res d)).card :=
          (Finset.card_image_of_injOn hinjd).symm
      _ ≤ (F d).card := Finset.card_le_card hsub
  have hunion : (D'.biUnion Bad).card ≤ ∑ d ∈ D', (Bad d).card := Finset.card_biUnion_le
  have hunion2 : (D'.biUnion Bad).card ≤ ∑ d ∈ D', (F d).card :=
    le_trans hunion (Finset.sum_le_sum hcard)
  have hlt : (D'.biUnion Bad).card < K.card := lt_of_le_of_lt hunion2 hbound
  have hsubK : D'.biUnion Bad ⊆ K := by
    intro k hk
    simp only [Finset.mem_biUnion] at hk
    obtain ⟨d, _, hk2⟩ := hk
    exact hBadsub d hk2
  have hne : (K \ D'.biUnion Bad).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsubK]
    omega
  obtain ⟨k, hk⟩ := hne
  rw [Finset.mem_sdiff] at hk
  refine ⟨k, hk.1, ?_⟩
  intro d hd hcontra
  apply hk.2
  simp only [Finset.mem_biUnion]
  exact ⟨d, hd, by simp [hBaddef, hk.1, hcontra]⟩

/-! ## Lemma 2 (Prime Filtering) and Corollary 3

**Session 3 status.** `primeFiltering` (Lemma 2) is now VERIFIED: zero `sorry` in its closure
(`qarc_periodic`, `qarc_add_topmul`, `qarc_mul_lam_gt`, `qarc_mul_lam_eq`, `nu_mul_coprime`,
`rp_coprime`, `injOn_shift_scale`, `exists_good_k`, `LamTop_coprime`, `primeFiltering_top`,
`primeFiltering_step`, `primeFiltering_aux`), `lake build` clean, standard axioms only (pasted
literally in the session's final report). The induction is assembled as `primeFiltering_aux`,
recursion on `t : ℕ` counting UP from `0` (levels processed from the top down), invariant at `t`:
"there is a coprime multiplier `lam` with `qarc p m N (lam*d) ∉ F d` for every `d ∈ D` at level
`nu p d ≥ m - t`". `t = 0` is the base case (`primeFiltering_top`, top level `m` alone, via
`LamTop p` and the top-level instance of eq. (3)); `t → t+1` is `primeFiltering_step` (extends by
one more level down via `Lam (m-t-1) m p`, eq. (3)'s two cases, and the generic union-bound
pigeonhole lemma `exists_good_k`); `t = m` gives `primeFiltering` itself. Two same-session,
same-`sorry` corrections were needed along the way (Rule 10, logged, no re-certification owed
since nothing `sorry`-free cited either before this fix): `LamTop` `v1.0` wrongly included `p`
itself (`{1,...,p}` instead of `{1,...,p-1}`, `erase 0` was a no-op) — fixed to `v1.1`; and
`qarc_mul_lam_gt`/`qarc_mul_lam_eq`'s hypothesis was relaxed from `j < m` to `j ≤ m` (the proofs
never actually used strictness, and the top level needs the `j = m` instance).

`primeFilteringCor3` remains `sorry`: see its updated docstring for the precise remaining content
(the general form needs a genuine hypothesis at levels `≥ i0`, not the vacuous placeholder the
statement carried until now; a specialized `i0 = m` case — the only one this session's downstream
targets need — is additionally provable "automatically" via a digit argument not yet formalized).
-/

/-- Any element of `LamTop p` is automatically coprime to `p` (a prime cannot have a nonzero
divisor strictly below itself). Small fact used to discharge the `Coprime` obligation at the top
level of the induction below. -/
theorem LamTop_coprime (p : ℕ) (hp : p.Prime) (lam : ℕ) (hlam : lam ∈ LamTop p) :
    Nat.Coprime lam p := by
  rw [mem_LamTop] at hlam
  have hndvd : ¬ p ∣ lam := by
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hndvd)

/-- Base case (top level `j = m`) of the descending induction: a coprime multiplier handling
level `m` alone, extracted from the top-level budget `htop` via the generic pigeonhole lemma
`exists_good_k` with search space `LamTop p` (size `p - 1`, matching `htop`'s `p - 2` bound with
one to spare). -/
theorem primeFiltering_top (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (F : ℕ → Finset ℕ) (m N : ℕ)
    (hN : N = p ^ (m + 1)) (hposD : ∀ d ∈ Dlevel p D m, 0 < d)
    (htop : (∑ d ∈ Dlevel p D m, (F d).card) ≤ p - 2) :
    ∃ lam : ℕ, lam ∈ LamTop p ∧ ∀ d ∈ Dlevel p D m, qarc p m N (lam * d) ∉ F d := by
  subst hN
  have hplt2 : 2 ≤ p := hp.two_le
  set K := Finset.range (p - 1) with hKdef
  have hbound : (∑ d ∈ Dlevel p D m, (F d).card) < K.card := by
    rw [hKdef, Finset.card_range]; omega
  have hinj : ∀ d ∈ Dlevel p D m,
      Set.InjOn (fun k => (qarc p m (p ^ (m + 1)) d + k * rp p d) % p) K := by
    intro d hd
    have hd0 : d ≠ 0 := (hposD d hd).ne'
    have hcop : Nat.Coprime (rp p d) p := rp_coprime p d hp hd0
    exact (injOn_shift_scale p (qarc p m (p ^ (m + 1)) d) (rp p d) hp hcop).mono
      (by intro x hx; simp only [hKdef, Finset.coe_range, Set.mem_Iio] at hx ⊢; omega)
  obtain ⟨k, hk, hgood⟩ := exists_good_k K (Dlevel p D m) F
    (fun d k => (qarc p m (p ^ (m + 1)) d + k * rp p d) % p) hinj hbound
  have hklt : k < p - 1 := by rwa [hKdef, Finset.mem_range] at hk
  refine ⟨k + 1, ?_, ?_⟩
  · rw [mem_LamTop]; omega
  · intro d hd
    have hlevel : nu p d = m := (Finset.mem_filter.mp hd).2
    have heq : qarc p m (p ^ (m + 1)) ((1 + p ^ (m - m) * k) * d) = (qarc p m (p ^ (m + 1)) d + k * rp p d) % p :=
      qarc_mul_lam_eq p m m hp le_rfl k (by omega) d hlevel
    have hval : (1 + p ^ (m - m) * k) = k + 1 := by
      rw [Nat.sub_self, pow_zero, one_mul]; ring
    rw [hval] at heq
    rw [heq]
    exact hgood d hd

/-- Single inductive step: extends a coprime multiplier `lam0` valid for all levels `≥ r`
(`0 < r ≤ m`) to one valid for all levels `≥ r - 1`, using the level budget `hlevels` at
`j = r - 1` (which is `< m` since `r ≤ m`). This is the general (non-top) case of eq. (3),
`qarc_mul_lam_gt`/`qarc_mul_lam_eq`, combined via `exists_good_k` on search space `Finset.range p`
(the parameter `k` indexing `Lam j m p` directly, size `p`, matching `hlevels`'s `p - 1` bound). -/
theorem primeFiltering_step (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d)
    (F : ℕ → Finset ℕ) (m N : ℕ) (hN : N = p ^ (m + 1)) (r : ℕ) (hr : 0 < r) (hrm : r ≤ m)
    (hlevels : (∑ d ∈ Dlevel p D (r - 1), (F d).card) ≤ p - 1)
    (lam0 : ℕ) (hlam0ne : lam0 ≠ 0) (hlam0cop : Nat.Coprime lam0 p)
    (hlam0 : ∀ d ∈ D, r ≤ nu p d → qarc p m N (lam0 * d) ∉ F d) :
    ∃ lam : ℕ, lam ≠ 0 ∧ Nat.Coprime lam p ∧
      ∀ d ∈ D, r - 1 ≤ nu p d → qarc p m N (lam * d) ∉ F d := by
  subst hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hppos := hp.pos
  set j := r - 1 with hjdef
  have hjm : j < m := by omega
  set K := Finset.range p with hKdef
  have hbound : (∑ d ∈ Dlevel p D j, (F d).card) < K.card := by
    rw [hKdef, Finset.card_range]; omega
  have hinj : ∀ d ∈ Dlevel p D j,
      Set.InjOn (fun k => (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p) K := by
    intro d hd
    have hdpos : 0 < d := hpos d (Finset.mem_filter.mp hd).1
    have hcop : Nat.Coprime (rp p (lam0 * d)) p :=
      rp_coprime p (lam0 * d) hp (Nat.mul_ne_zero hlam0ne hdpos.ne')
    exact injOn_shift_scale p _ _ hp hcop
  obtain ⟨k, hk, hgood⟩ := exists_good_k K (Dlevel p D j) F
    (fun d k => (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p) hinj hbound
  have hklt : k < p := by rwa [hKdef, Finset.mem_range] at hk
  have hdvdp : p ∣ p ^ (m - j) := dvd_pow_self p (show m - j ≠ 0 by omega)
  obtain ⟨w, hw⟩ := hdvdp
  have hcopfactor : Nat.Coprime (1 + p ^ (m - j) * k) p := by
    have hdvd2 : p ∣ p ^ (m - j) * k := by rw [hw]; exact ⟨w * k, by ring⟩
    have hndvd : ¬ p ∣ (1 + p ^ (m - j) * k) := by
      intro hc
      have hp1 : p ∣ (1 : ℕ) :=
        (Nat.dvd_add_right hdvd2).mp (by rwa [Nat.add_comm] at hc)
      have := Nat.le_of_dvd (by norm_num) hp1
      have := hp.two_le
      omega
    exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hndvd)
  refine ⟨(1 + p ^ (m - j) * k) * lam0, ?_,
      Nat.coprime_mul_iff_left.mpr ⟨hcopfactor, hlam0cop⟩, ?_⟩
  · exact Nat.mul_ne_zero (by omega) hlam0ne
  · intro d hd hnud
    rcases lt_or_ge j (nu p d) with hgt | hle
    · have hnu : nu p (lam0 * d) = nu p d :=
        nu_mul_coprime p lam0 d hlam0cop hlam0ne (hpos d hd).ne'
      have hval : qarc p m (p ^ (m + 1)) (((1 + p ^ (m - j) * k) * lam0) * d) = qarc p m (p ^ (m + 1)) (lam0 * d) := by
        rw [mul_assoc]
        exact qarc_mul_lam_gt p j m (le_of_lt hjm) k (lam0 * d) (hnu ▸ hgt)
      rw [hval]
      exact hlam0 d hd (by omega)
    · have hlevel : nu p d = j := by omega
      have hnu : nu p (lam0 * d) = j :=
        (nu_mul_coprime p lam0 d hlam0cop hlam0ne (hpos d hd).ne').trans hlevel
      have hval : qarc p m (p ^ (m + 1)) (((1 + p ^ (m - j) * k) * lam0) * d)
          = (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p := by
        rw [mul_assoc]
        exact qarc_mul_lam_eq p j m hp (le_of_lt hjm) k hklt (lam0 * d) hnu
      rw [hval]
      exact hgood d (Finset.mem_filter.mpr ⟨hd, hlevel⟩)

/-- Descending-induction assembly, recursion variable `t` counting UP from `0` (levels processed
from the top), per session instructions ("`Nat.le_induction`/strong recursion on `m - r`
increasing, rather than literally descending on `r`, to avoid `Nat` subtraction pitfalls"). At
`t` the invariant covers all levels `≥ m - t`; `t = 0` is `primeFiltering_top`, `t = m` gives
`primeFiltering` itself (level `≥ 0` = all of `D`). -/
theorem primeFiltering_aux (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hDne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 < d) (F : ℕ → Finset ℕ) (m : ℕ) (hm : m = D.sup (nu p)) (N : ℕ)
    (hN : N = p ^ (m + 1)) (hlevels : ∀ j < m, (∑ d ∈ Dlevel p D j, (F d).card) ≤ p - 1)
    (htop : (∑ d ∈ Dlevel p D m, (F d).card) ≤ p - 2) :
    ∀ t ≤ m, ∃ lam : ℕ, lam ≠ 0 ∧ Nat.Coprime lam p ∧
      ∀ d ∈ D, m - t ≤ nu p d → qarc p m N (lam * d) ∉ F d := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨lam, hlamtop, hgood⟩ := primeFiltering_top p hp D F m N hN
      (fun d hd => hpos d (Finset.mem_filter.mp hd).1) htop
    refine ⟨lam, by rw [mem_LamTop] at hlamtop; omega, LamTop_coprime p hp lam hlamtop, ?_⟩
    intro d hd hnud
    simp only [Nat.sub_zero] at hnud
    have hdle : nu p d ≤ m := hm ▸ Finset.le_sup hd
    have hlevel : nu p d = m := le_antisymm hdle hnud
    exact hgood d (Finset.mem_filter.mpr ⟨hd, hlevel⟩)
  | succ t ih =>
    intro htm1
    have htm : t ≤ m := by omega
    obtain ⟨lam0, hlam0ne, hlam0cop, hlam0⟩ := ih htm
    obtain ⟨lam, hlamne, hlamcop, hgood⟩ := primeFiltering_step p hp D hpos F m N hN (m - t)
      (by omega) (by omega)
      (by
        have : m - t - 1 = m - (t + 1) := by omega
        rw [this]; exact hlevels (m - (t + 1)) (by omega))
      lam0 hlam0ne hlam0cop hlam0
    refine ⟨lam, hlamne, hlamcop, ?_⟩
    intro d hd hnud
    have heq : m - t - 1 = m - (t + 1) := by omega
    rw [heq] at hgood
    exact hgood d hd hnud

/-- **Lemma 2 (Prime Filtering), statement only, `sorry`.**
Given a prime `p`, a finite set `D` of positive naturals, `m = max_{d in D} nu_p(d)`,
`N = p^(m+1)`, and a forbidden set `F d subset Fin p` for each `d in D` (represented as
`Finset ℕ`, values understood mod `p`), if the forbidden sets are small enough level-by-level
(sum `<= p-1` below the top level, sum `<= p-2` at the top level `m`), then there is a multiplier
`lambda`, coprime to `p`, such that `q(lambda*d) not in F d` for every `d in D`. -/
theorem primeFiltering (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hDne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 < d) (F : ℕ → Finset ℕ)
    (m : ℕ) (hm : m = D.sup (nu p)) (N : ℕ) (hN : N = p ^ (m + 1))
    (hlevels : ∀ j < m, (∑ d ∈ Dlevel p D j, (F d).card) ≤ p - 1)
    (htop : (∑ d ∈ Dlevel p D m, (F d).card) ≤ p - 2) :
    ∃ lam : ℕ, Nat.Coprime lam p ∧ ∀ d ∈ D, qarc p m N (lam * d) ∉ F d := by
  obtain ⟨lam, hlamne, hlamcop, hgood⟩ :=
    primeFiltering_aux p hp D hDne hpos F m hm N hN hlevels htop m le_rfl
  refine ⟨lam, hlamcop, ?_⟩
  intro d hd
  exact hgood d hd (by omega)

/-! ## Digit-to-real bridge (E6, session 4)

Falsify-checked (Rule 3) in (development file, not part of this archive), `check_bridge`: 36000 random
trials across `p in {3,5,7}`, `m in {0,1,2,3}`, 0 failures, for both the MID and TOP formulas
below, before any of this was written in Lean.
-/

/-- `qarc` is literally the top base-`p` digit of `d mod N` (the outer `% p` in its definition
is redundant, since `(d mod N)/p^m < p` already): this is the identity that lets us reason about
`d mod N` and `N - d mod N` directly in terms of `qarc`. -/
theorem qarc_eq_div (p m N d : ℕ) (hp : 0 < p) (hN : N = p ^ (m + 1)) :
    qarc p m N d = (d % N) / p ^ m := by
  unfold qarc
  have hlt : d % N < N := Nat.mod_lt _ (by rw [hN]; positivity)
  have h1 : (d % N) / p ^ m < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp m), mul_comm]
    calc d % N < N := hlt
      _ = p ^ m * p := by rw [hN, pow_succ]
  exact Nat.mod_eq_of_lt h1

/-! ## Digit reflection identity (E6, session 11)

Session 9's autopsy (see `barajasSerra_card4_hard`'s docstring, session 9 block) found by
falsification that the sign-flip `d ↦ N - d` needed for the `|As| = 3` WLOG normalization realizes
the digit-level involution `x ↦ (p - 1) - x`, NOT the naively-guessed `x ↦ -x mod p` (session 8's
claim, which is FALSE: `check_reflection_transport` in (development file, not part of this archive) fails it
on every one of 81127 trials with `nu_p(d) = 0`, `p = 5`, `m ∈ {1,...,4}` random, re-confirmed this
session with a fresh independent 81127-trial run, still 0 failures for `x ↦ (p-1)-x` and 81127/81127
failures for `x ↦ -x mod p`). This was flagged as "not yet stated as a Lean lemma"; it is formalized
below and is VERIFIED (see build log), not merely re-confirmed by falsification.
-/

/-- **Digit reflection identity.** For `d` not divisible by `p` (`nu_p d = 0`, matching the
`|As|` elements' shared `nu_5 = 0` in the `|D| = 4` hard case) and any level `m ≥ 1`, the top
`p`-adic digit of the complement `N - d` (for `0 < d < N`, `N = p^(m+1)`) is the reflection
`(p - 1) - qarc p m N d` of `d`'s own top digit. Falsify-checked (Rule 3) BEFORE this proof was
written: (development file, not part of this archive), `check_reflection_transport`, candidate
`x ↦ (p-1)-x`, 81127 trials, 0 failures. Rule 6 adversarial review: the hypothesis `0 < m` is
load-bearing, not cosmetic — at `m = 0` (so `N = p`), every `d` with `0 < d < p` trivially has
`nu_p d = 0` but the "lower digit" `rem = d % p^m = d % 1 = 0` always, which is exactly the
degenerate case the proof's `hremne` step rules out; the statement is FALSE at `m = 0` (e.g.
`p = 5, d = 1`: `qarc 5 0 5 (5-1) = 4`, `(p-1) - qarc 5 0 5 1 = 4 - 1 = 3 ≠ 4`), so `hm : 0 < m` is
correctly required, not a lazy hypothesis. The proof needs no `sorry`, no `native_decide`, and no
new axioms beyond Mathlib's standard ones (see build log). -/
theorem qarc_reflect (p m N d : ℕ) (hp : p.Prime) (hm : 0 < m) (hN : N = p ^ (m + 1))
    (hdpos : 0 < d) (hdlt : d < N) (hd : ¬ p ∣ d) :
    qarc p m N (N - d) = (p - 1) - qarc p m N d := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hApos : 0 < p ^ m := pow_pos hp0 m
  have hNeq : N = p ^ m * p := by rw [hN, pow_succ]
  have hqd : qarc p m N d = d / p ^ m := by
    have h := qarc_eq_div p m N d hp0 hN
    rwa [Nat.mod_eq_of_lt hdlt] at h
  have hNdlt : N - d < N := by omega
  have hqNd : qarc p m N (N - d) = (N - d) / p ^ m := by
    have h := qarc_eq_div p m N (N - d) hp0 hN
    rwa [Nat.mod_eq_of_lt hNdlt] at h
  obtain ⟨q, rem, hdecomp, hremlt⟩ : ∃ q rem, d = p ^ m * q + rem ∧ rem < p ^ m :=
    ⟨d / p ^ m, d % p ^ m, (Nat.div_add_mod d (p ^ m)).symm, Nat.mod_lt _ hApos⟩
  have hqeq : d / p ^ m = q := by
    rw [hdecomp, show p ^ m * q + rem = rem + p ^ m * q from by ring,
      Nat.add_mul_div_left _ _ hApos, Nat.div_eq_of_lt hremlt, zero_add]
  rw [hqeq] at hqd
  have hqltp : q < p := by
    by_contra hcon
    push_neg at hcon
    have hle : p ^ m * p ≤ p ^ m * q := Nat.mul_le_mul_left _ hcon
    omega
  have hremne : rem ≠ 0 := by
    intro hrem0
    apply hd
    have hAdvd : p ^ m ∣ d := ⟨q, by rw [hdecomp, hrem0, add_zero]⟩
    have hpdvdA : p ∣ p ^ m := dvd_pow_self p (by omega)
    exact hpdvdA.trans hAdvd
  have hlow : p ^ m * ((p - 1) - q) ≤ N - d := by
    have h1 : p ^ m * ((p - 1) - q) + p ^ m * q = p ^ m * (p - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h2 : p ^ m * (p - 1) + p ^ m = N := by
      have h3 : p ^ m * (p - 1) + p ^ m * 1 = p ^ m * p := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [mul_one] at h3; omega
    omega
  have hhigh : N - d < p ^ m * ((p - 1) - q) + p ^ m := by
    have h1 : p ^ m * ((p - 1) - q) + p ^ m * q = p ^ m * (p - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h2 : p ^ m * (p - 1) + p ^ m = N := by
      have h3 : p ^ m * (p - 1) + p ^ m * 1 = p ^ m * p := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [mul_one] at h3; omega
    omega
  rw [hqNd, hqd]
  rw [mul_comm] at hlow hhigh
  have hhigh' : N - d < (p - 1 - q + 1) * p ^ m := by
    rw [add_mul, one_mul]; exact hhigh
  exact (Nat.div_eq_of_lt_le hlow hhigh')

/-- Generic bridge from a modular "far from both `0` and `Q`" bound to a real `nearestIntDist`
bound at the rational point `a / Q`. Contrapositive of `nearestIntDist_div_lt_iff`. -/
theorem nearestIntDist_ge_of_min (a : ℤ) (Q : ℕ) (hQ : 0 < Q) (δ : ℝ)
    (h : δ * (Q : ℝ) ≤ min (((a % (Q : ℤ) : ℤ) : ℝ)) ((Q : ℝ) - ((a % (Q : ℤ) : ℤ) : ℝ))) :
    δ ≤ nearestIntDist ((a : ℝ) / (Q : ℝ)) := by
  rw [← not_lt]
  intro hc
  rw [nearestIntDist_div_lt_iff a Q hQ δ] at hc
  linarith

/-- **Bridge lemma, mid-level case.** If `qarc p m N d` avoids both `0` and `p - 1` (the forbidden
set `F d = {0, p-1}` of Corollary 3), then `d`'s residue mod `N` is at distance `>= p^m = N/p`
from both `0` and `N`, hence `nearestIntDist (d/N) >= 1/p`. This is the mid-level half of the
digit-to-real bridge (paper, Corollary 3, general levels `< i0`); the erosion from lower digits
(`rem < p^m`) is exactly why BOTH endpoints `0` and `p-1` must be excluded here, not just `0`. -/
theorem qarc_bridge_mid (p m N d : ℕ) (hp : p.Prime) (hN : N = p ^ (m + 1))
    (h0 : qarc p m N d ≠ 0) (h1 : qarc p m N d ≠ p - 1) :
    (1 / (p : ℝ)) ≤ nearestIntDist ((d : ℝ) / (N : ℝ)) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hpm : 0 < p ^ m := pow_pos hp0 m
  have hqeq : qarc p m N d = (d % N) / p ^ m := qarc_eq_div p m N d hp0 hN
  set q := (d % N) / p ^ m with hqdef
  set rem := (d % N) % p ^ m with hremdef
  have hdecomp : d % N = p ^ m * q + rem := (Nat.div_add_mod (d % N) (p ^ m)).symm
  have hremlt : rem < p ^ m := Nat.mod_lt _ hpm
  have hqltp : q < p := by
    have : qarc p m N d < p := by unfold qarc; exact Nat.mod_lt _ hp0
    rwa [hqeq] at this
  rw [hqeq] at h0 h1
  have hq1 : 1 ≤ q := by omega
  have hqp2 : q + 1 ≤ p - 1 := by omega
  -- key inequality: d % N + p^m ≤ N, giving both p^m ≤ d%N and p^m ≤ N - d%N
  have e1 : p ^ m * (q + 1) ≤ p ^ m * (p - 1) := Nat.mul_le_mul_left _ hqp2
  have e2 : p ^ m * (q + 1) = p ^ m * q + p ^ m := by ring
  have e3 : p ^ m * (p - 1) + p ^ m = p ^ m * p := by
    have hpe : (p - 1) + 1 = p := by omega
    calc p ^ m * (p - 1) + p ^ m = p ^ m * ((p - 1) + 1) := by ring
      _ = p ^ m * p := by rw [hpe]
  have hkey : d % N + p ^ m ≤ N := by
    rw [hdecomp, hN, pow_succ]
    omega
  have e0 : p ^ m ≤ p ^ m * q := by
    calc p ^ m = p ^ m * 1 := (mul_one _).symm
      _ ≤ p ^ m * q := Nat.mul_le_mul_left _ hq1
  have hle1 : p ^ m ≤ d % N := by
    calc p ^ m ≤ p ^ m * q := e0
      _ ≤ p ^ m * q + rem := Nat.le_add_right _ _
      _ = d % N := hdecomp.symm
  have hNlt : d % N < N := Nat.mod_lt _ (by rw [hN]; positivity)
  have hle2 : p ^ m ≤ N - d % N := Nat.le_sub_of_add_le' hkey
  have hbridge : (1 / (p : ℝ)) * (N : ℝ) ≤
      min (((d : ℤ) % (N : ℤ) : ℝ)) ((N : ℝ) - (((d : ℤ) % (N : ℤ) : ℤ) : ℝ)) := by
    have hcast : ((d : ℤ) % (N : ℤ) : ℤ) = ((d % N : ℕ) : ℤ) := (Int.natCast_mod d N).symm
    rw [hcast]
    have hNp : (1 / (p : ℝ)) * (N : ℝ) = (p ^ m : ℝ) := by
      rw [hN, pow_succ]; push_cast; field_simp
    rw [hNp, le_min_iff]
    constructor
    · exact_mod_cast hle1
    · have hcast2 : ((N - d % N : ℕ) : ℝ) = (N : ℝ) - (d % N : ℝ) := by
        exact_mod_cast Nat.cast_sub (le_of_lt hNlt)
      have hgoal : (p ^ m : ℝ) ≤ (N : ℝ) - ((d % N : ℕ) : ℝ) := by
        rw [← hcast2]; exact_mod_cast hle2
      exact_mod_cast hgoal
  have hNpos : 0 < N := by rw [hN]; positivity
  have := nearestIntDist_ge_of_min (d : ℤ) N hNpos (1 / (p : ℝ)) hbridge
  simpa using this

/-- The top digit `qarc` of `d` is automatically nonzero at `d`'s own level (`nu_p d = m`): no
`F`-exclusion needed. This is the "digit argument" flagged in the session-3 docstring: `nu_p d = m`
forces `d mod N` to be an EXACT multiple of `p^m` (no lower digits, `rem = 0`), and the leading
digit of that exact multiple is `rp p d`, which is coprime to `p` (hence nonzero) since `d ≠ 0`. -/
theorem qarc_top_ne_zero (p m N d : ℕ) (hp : p.Prime) (hN : N = p ^ (m + 1)) (hd : d ≠ 0)
    (hlevel : nu p d = m) : qarc p m N d ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hdvd : p ^ m ∣ d := by rw [← hlevel]; unfold nu; exact pow_padicValNat_dvd
  obtain ⟨w, hw⟩ := hdvd
  have hndvd : ¬ p ∣ w := by
    intro hpw
    obtain ⟨w', hw'⟩ := hpw
    have hcontra : p ^ (m + 1) ∣ d := ⟨w', by rw [hw, hw', pow_succ]; ring⟩
    exact pow_succ_padicValNat_not_dvd hd (hlevel ▸ hcontra)
  have hqeq : qarc p m N d = w % p := by
    rw [qarc_eq_div p m N d hp0 hN, hw, hN, pow_succ, Nat.mul_mod_mul_left,
      Nat.mul_div_cancel_left _ (pow_pos hp0 m)]
  rw [hqeq]
  intro hcontra
  exact hndvd (Nat.dvd_of_mod_eq_zero hcontra)

/-- **Bridge lemma, top-level case.** If `nu_p d = m` (`d` sits exactly at the top level), then
`nearestIntDist (d/N) >= 1/p` automatically, with no hypothesis on `F d` at all: since `d mod N`
is then an exact multiple of `p^m` (`rem = 0`), there is no erosion from lower digits, so a single
nonzero digit (`qarc_top_ne_zero`) already suffices — unlike the mid-level case, which needs both
endpoints excluded. -/
theorem qarc_bridge_top (p m N d : ℕ) (hp : p.Prime) (hN : N = p ^ (m + 1)) (hd : d ≠ 0)
    (hlevel : nu p d = m) : (1 / (p : ℝ)) ≤ nearestIntDist ((d : ℝ) / (N : ℝ)) := by
  have hp0 : 0 < p := hp.pos
  have h0 : qarc p m N d ≠ 0 := qarc_top_ne_zero p m N d hp hN hd hlevel
  have hqltp : qarc p m N d < p := by unfold qarc; exact Nat.mod_lt _ hp0
  rcases eq_or_ne (qarc p m N d) (p - 1) with h1 | h1
  · -- q = p - 1: still fine, since rem = 0 exactly (no erosion), redo the min bound directly
    have hdvd : p ^ m ∣ d := by rw [← hlevel]; unfold nu; exact pow_padicValNat_dvd
    obtain ⟨w, hw⟩ := hdvd
    have hqeq : qarc p m N d = (d % N) / p ^ m := qarc_eq_div p m N d hp0 hN
    have hrem0 : (d % N) % p ^ m = 0 := by
      rw [hw, hN, pow_succ, Nat.mul_mod_mul_left]
      exact Nat.mul_mod_right _ _
    have hdecomp : d % N = qarc p m N d * p ^ m := by
      rw [hqeq]
      calc d % N = p ^ m * (d % N / p ^ m) + d % N % p ^ m :=
            (Nat.div_add_mod (d % N) (p ^ m)).symm
        _ = p ^ m * (d % N / p ^ m) := by rw [hrem0]; ring
        _ = (d % N / p ^ m) * p ^ m := by ring
    have hNlt : d % N < N := Nat.mod_lt _ (by rw [hN]; positivity)
    have hle1 : p ^ m ≤ d % N := by
      rw [hdecomp]
      have h1le : 1 ≤ qarc p m N d := by omega
      calc p ^ m = 1 * p ^ m := (one_mul _).symm
        _ ≤ qarc p m N d * p ^ m := Nat.mul_le_mul_right _ h1le
    have hle2 : p ^ m ≤ N - d % N := by
      rw [hdecomp]
      have hNval : N = p ^ m * p := by rw [hN, pow_succ]
      have hstep : qarc p m N d * p ^ m + p ^ m ≤ N := by
        calc qarc p m N d * p ^ m + p ^ m = (qarc p m N d + 1) * p ^ m := by ring
          _ ≤ p * p ^ m := Nat.mul_le_mul_right _ (by omega)
          _ = p ^ m * p := by ring
          _ = N := hNval.symm
      exact Nat.le_sub_of_add_le' hstep
    have hbridge : (1 / (p : ℝ)) * (N : ℝ) ≤
        min (((d : ℤ) % (N : ℤ) : ℝ)) ((N : ℝ) - (((d : ℤ) % (N : ℤ) : ℤ) : ℝ)) := by
      have hcast : ((d : ℤ) % (N : ℤ) : ℤ) = ((d % N : ℕ) : ℤ) := (Int.natCast_mod d N).symm
      rw [hcast]
      have hNp : (1 / (p : ℝ)) * (N : ℝ) = (p ^ m : ℝ) := by
        rw [hN, pow_succ]; push_cast; field_simp
      rw [hNp, le_min_iff]
      refine ⟨by exact_mod_cast hle1, ?_⟩
      have hcast2 : ((N - d % N : ℕ) : ℝ) = (N : ℝ) - (d % N : ℝ) := by
        exact_mod_cast Nat.cast_sub (le_of_lt hNlt)
      have hgoal : (p ^ m : ℝ) ≤ (N : ℝ) - ((d % N : ℕ) : ℝ) := by
        rw [← hcast2]; exact_mod_cast hle2
      exact_mod_cast hgoal
    have hNpos : 0 < N := by rw [hN]; positivity
    have := nearestIntDist_ge_of_min (d : ℤ) N hNpos (1 / (p : ℝ)) hbridge
    simpa using this
  · exact qarc_bridge_mid p m N d hp hN h0 h1

/-- **`primeFilteringCor3Top`, specialization of Corollary 3 to `i0 = m` (VERIFIED, no `sorry`).**
The case actually needed by `diffValuation3_case`/`barajasSerra_card2`. No `htoplevels` hypothesis
is needed at all in this specialization: the top level's bound is automatic
(`qarc_bridge_top`, invariant under multiplication by any `p`-coprime `lam` via `nu_mul_coprime`),
unlike the general `i0 < m` case in `primeFilteringCor3` below (still `sorry`, session-3/4 autopsy:
the general hypothesis shape connecting a bound on `d` itself to one on `lam * d` was never pinned
down, and is not needed by this session's actual targets). -/
theorem primeFilteringCor3Top (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hDne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 < d) (m : ℕ) (hm : m = D.sup (nu p))
    (hcard : ∀ j < m, (Dlevel p D j).card ≤ (p - 1) / 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / (p : ℝ)) ≤ nearestIntDist (t * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N := p ^ (m + 1) with hN
  set F : ℕ → Finset ℕ := fun d => if nu p d = m then (∅ : Finset ℕ) else ({0, p - 1} : Finset ℕ)
    with hFdef
  have hlevels : ∀ j < m, (∑ d ∈ Dlevel p D j, (F d).card) ≤ p - 1 := by
    intro j hj
    have hFval : ∀ d ∈ Dlevel p D j, F d = ({0, p - 1} : Finset ℕ) := by
      intro d hd
      have hlv : nu p d = j := (Finset.mem_filter.mp hd).2
      simp only [hFdef]
      rw [if_neg (by omega)]
    have hcardF : ∀ d ∈ Dlevel p D j, (F d).card ≤ 2 := by
      intro d hd
      rw [hFval d hd]
      exact (Finset.card_insert_le _ _).trans (by simp)
    calc (∑ d ∈ Dlevel p D j, (F d).card) ≤ ∑ d ∈ Dlevel p D j, 2 :=
          Finset.sum_le_sum hcardF
      _ = 2 * (Dlevel p D j).card := by rw [Finset.sum_const]; ring
      _ ≤ 2 * ((p - 1) / 2) := by
          have := hcard j hj
          omega
      _ ≤ p - 1 := by omega
  have htop : (∑ d ∈ Dlevel p D m, (F d).card) ≤ p - 2 := by
    have hFval : ∀ d ∈ Dlevel p D m, F d = (∅ : Finset ℕ) := by
      intro d hd
      have hlv : nu p d = m := (Finset.mem_filter.mp hd).2
      simp only [hFdef]
      rw [if_pos hlv]
    have : (∑ d ∈ Dlevel p D m, (F d).card) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [hFval d hd]; simp
    rw [this]
    omega
  obtain ⟨lam, hlamcop, hgood⟩ := primeFiltering p hp D hDne hpos F m hm N hN hlevels htop
  have hlamne : lam ≠ 0 := by
    rintro rfl
    have hgcd : Nat.gcd 0 p = 1 := hlamcop
    rw [Nat.gcd_zero_left] at hgcd
    have hp2 := hp.two_le
    omega
  have hlamR : (0:ℝ) < (lam:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hlamne
  have hNposR : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by rw [hN]; exact pow_pos hp.pos _
    exact_mod_cast this
  refine ⟨(lam : ℝ) / (N : ℝ), div_pos hlamR hNposR, ?_⟩
  intro d hd
  have hgd := hgood d hd
  have hdpos := hpos d hd
  have hlevel_choice := em (nu p d = m)
  rcases hlevel_choice with hlev | hlev
  · have hnu : nu p (lam * d) = m := by
      have := nu_mul_coprime p lam d hlamcop hlamne hdpos.ne'
      rw [hlev] at this; exact this
    have hbound := qarc_bridge_top p m N (lam * d) hp hN (Nat.mul_ne_zero hlamne hdpos.ne') hnu
    have heq : ((lam : ℝ) / (N : ℝ)) * (d : ℝ) = ((lam * d : ℕ) : ℝ) / (N : ℝ) := by
      push_cast; ring
    rw [heq]; exact hbound
  · have hFd : F d = ({0, p - 1} : Finset ℕ) := by simp only [hFdef]; rw [if_neg hlev]
    rw [hFd] at hgd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hgd
    have hbound := qarc_bridge_mid p m N (lam * d) hp hN hgd.1 hgd.2
    have heq : ((lam : ℝ) / (N : ℝ)) * (d : ℝ) = ((lam * d : ℕ) : ℝ) / (N : ℝ) := by
      push_cast; ring
    rw [heq]; exact hbound

/-- **Corollary 3, statement only, `sorry` (depends on `primeFiltering`).**
Specializes Lemma 2 to `F d = {0, p-1}` for `d` below level `i0`. **Session 3 correction (Rule 6
adversarial review):** the `v1.0` hypothesis `htoplevels_auto` was VACUOUS (`... → True`), which
made the whole statement provable by nonsense and hid the real content; per the paper's actual
Corollary 3 (`bs2008.txt`, Section 2) `|d|_N >= N/p` for levels `>= i0` is a genuine HYPOTHESIS in
general (only automatic in the special case `i0 = m`, via a digit argument: `nu_p d = m` forces
`d mod N` to be an exact nonzero multiple of `p^m`, hence at distance `>= p^m = N/p` from both `0`
and `N`, with no lower digits to erode that bound — unlike the general mid-level case, where lower
digits are exactly why `F d = {0, p-1}` must exclude BOTH endpoints, not just `{0}`). `v1.1` below
states the general hypothesis honestly, matching the paper; a `primeFilteringCor3Top` (`i0 = m`
only, sufficient for E6-2's targets: `diffValuation3_case`/`barajasSerra_card2`) discharging that
hypothesis automatically was NOT completed this session (Rule 2/18 autopsy in the final report):
it needs (a) the digit-to-`nearestIntDist` bridge lemma connecting `qarc` bounds to the real
inequality (not yet written), applied twice (once for the excluded-both-endpoints mid-level case,
once for the top-level exact-multiple case), and (b) the `F`-indicator gluing argument itself.
Neither is mathematically hard given the foundation already VERIFIED above, but both are unwritten
Lean, so the honest label stays `sorry`/CONJECTURE-for-this-project, not "almost done" (Rule 0). -/
theorem primeFilteringCor3 (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hDne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 < d) (i0 m : ℕ) (hm : m = D.sup (nu p)) (hi0 : i0 ≤ m)
    (htoplevels : ∀ i, i0 ≤ i → ∀ d ∈ Dlevel p D i,
      (1 / (p : ℝ)) ≤ nearestIntDist ((d : ℝ) / (p ^ (m + 1) : ℝ)))
    (hcard : ∀ j < i0, (Dlevel p D j).card ≤ (p - 1) / 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / (p : ℝ)) ≤ nearestIntDist (t * d) := by
  sorry

/-! ## Section 3, easy case `|D| = 2` (3 runners = 2 speeds)

Falls into sub-cases: (a) both elements coprime to `3` — proved here directly, completely
independently of Lemma 2/Corollary 3, since it needs neither (the paper mentions this case only
degenerates to a one-line argument); (b) different `3`-adic valuations, and (c) equal `3`-adic
valuations (`x = 3^k x'`, `y = 3^k y'` both coprime to `3`) — both closed session 4, via
`primeFilteringCor3Top`/`coprime3_case` respectively (`diffValuation3_case`,
`sameValuation3_case`). `barajasSerra_card2_general`/`barajasSerra_card2` combine all cases; no
`sorry` remains in this section.
-/

/-- **PROVED, no `sorry`.** If `3` does not divide either of two positive integers `x y`, then
`t = 1/3` is a real witness making BOTH nearest-integer distances `>= 1/3`: this is the "both
coprime to 3" branch of the paper's `|D| = 2` case (Section 3, first paragraph), and needs
neither Lemma 2 nor Corollary 3 (the paper's own remark: "either... relatively prime with 3...").
Adversarial review (Rule 6): quantifiers are `∀ x y : ℤ`, no hidden dependence; edge case `x` or
`y` negative is handled since we only use `x % 3` (`Int.emod`, always in `[0,3)` regardless of
sign, via `Int.emod_nonneg`/`Int.emod_lt_of_pos`); no division by zero; the case split covers all
three residues and rules out the impossible one (`0`) by hypothesis. -/
theorem coprime3_case (x y : ℤ) (hx : ¬ (3 : ℤ) ∣ x) (hy : ¬ (3 : ℤ) ∣ y) :
    (1 / 3 : ℝ) ≤ nearestIntDist ((1 / 3 : ℝ) * x) ∧
    (1 / 3 : ℝ) ≤ nearestIntDist ((1 / 3 : ℝ) * y) := by
  have key : ∀ z : ℤ, ¬ (3 : ℤ) ∣ z → (1 / 3 : ℝ) ≤ nearestIntDist ((1 / 3 : ℝ) * z) := by
    intro z hz
    have h0 : (0:ℤ) ≤ z % 3 := Int.emod_nonneg z (by norm_num)
    have h1 : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
    have hdiv : z = 3 * (z / 3) + z % 3 := (Int.ediv_add_emod z 3).symm ▸ by ring
    have htri : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
    have hz0 : z % 3 ≠ 0 := by
      intro h
      apply hz
      exact Int.dvd_of_emod_eq_zero h
    have heq : (1 / 3 : ℝ) * z = ((z % 3 : ℤ) : ℝ) / 3 + (z / 3 : ℤ) := by
      have hcast : (z : ℝ) = 3 * ((z / 3 : ℤ) : ℝ) + ((z % 3 : ℤ) : ℝ) := by
        exact_mod_cast hdiv
      linarith [hcast]
    rw [heq, nearestIntDist_add_int]
    rcases htri with h | h | h
    · exact absurd h hz0
    · rw [h]
      have : nearestIntDist ((1:ℤ) / 3 : ℝ) = 1 / 3 := by
        have heval : ((1:ℤ):ℝ) / 3 = (1:ℝ) / 3 := by push_cast; ring
        rw [heval]
        unfold nearestIntDist
        rw [Int.fract_eq_self.mpr (by norm_num) ]
        norm_num
      simpa using this.ge
    · rw [h]
      have : nearestIntDist ((2:ℤ) / 3 : ℝ) = 1 / 3 := by
        have heval : ((2:ℤ):ℝ) / 3 = (2:ℝ) / 3 := by push_cast; ring
        rw [heval]
        unfold nearestIntDist
        rw [Int.fract_eq_self.mpr (by norm_num)]
        norm_num
      simpa using this.ge
  exact ⟨key x hx, key y hy⟩

/-- **PROVED, no `sorry` (session 4).** The paper's remaining `|D| = 2` branch: `x, y` with
different `3`-adic valuations. Closed via `primeFilteringCor3Top` (`p = 3`, `D = {x,y}`): the
level-cardinality hypothesis is trivial (`(3-1)/2 = 1`, and a level below the max can contain at
most one of `x,y` since their valuations differ). -/
theorem diffValuation3_case (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hdiff : nu 3 x ≠ nu 3 y) :
    ∃ t : ℝ, 0 < t ∧ (1 / 3 : ℝ) ≤ nearestIntDist (t * x) ∧
      (1 / 3 : ℝ) ≤ nearestIntDist (t * y) := by
  have hxy : x ≠ y := by rintro rfl; exact hdiff rfl
  set D : Finset ℕ := {x, y} with hDdef
  have hDne : D.Nonempty := ⟨x, by simp [hDdef]⟩
  have hposD : ∀ d ∈ D, 0 < d := by
    intro d hd
    simp only [hDdef, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hx
    · exact hy
  set m := D.sup (nu 3) with hm
  have hcard : ∀ j < m, (Dlevel 3 D j).card ≤ (3 - 1) / 2 := by
    intro j hj
    have hle1 : (Dlevel 3 D j).card ≤ 1 := by
      by_contra hc
      push_neg at hc
      have hsub : Dlevel 3 D j ⊆ D := Finset.filter_subset _ _
      have hcardD : D.card ≤ 2 := by
        rw [hDdef]; exact (Finset.card_insert_le _ _).trans (by simp)
      have heqD : Dlevel 3 D j = D := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hxin : x ∈ Dlevel 3 D j := by rw [heqD]; simp [hDdef]
      have hyin : y ∈ Dlevel 3 D j := by rw [heqD]; simp [hDdef]
      have hxlv : nu 3 x = j := (Finset.mem_filter.mp hxin).2
      have hylv : nu 3 y = j := (Finset.mem_filter.mp hyin).2
      exact hdiff (hxlv.trans hylv.symm)
    omega
  obtain ⟨t, ht0, hgood⟩ :=
    primeFilteringCor3Top 3 (by decide) D hDne hposD m hm hcard
  exact ⟨t, ht0, hgood x (by simp [hDdef]), hgood y (by simp [hDdef])⟩

/-- **PROVED, no `sorry` (session 4).** The equal-`3`-adic-valuation branch, complementing
`diffValuation3_case`: reduces `x = 3^k x'`, `y = 3^k y'` (`k` the common valuation) to
`coprime3_case` on the coprime-to-`3` quotients `x', y'`, reusing `rp`/`rp_coprime` (already
VERIFIED above) to extract "coprime to 3" from "leading digit at the top of its own valuation". -/
theorem sameValuation3_case (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hsame : nu 3 x = nu 3 y) :
    ∃ t : ℝ, 0 < t ∧ (1 / 3 : ℝ) ≤ nearestIntDist (t * x) ∧
      (1 / 3 : ℝ) ≤ nearestIntDist (t * y) := by
  have h3 : Nat.Prime 3 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨h3⟩
  set k := nu 3 x with hk
  have hdvdx : (3:ℕ) ^ k ∣ x := by rw [hk]; exact pow_padicValNat_dvd
  have hdvdy : (3:ℕ) ^ k ∣ y := by rw [hsame]; exact pow_padicValNat_dvd
  obtain ⟨x', hx'eq⟩ := hdvdx
  obtain ⟨y', hy'eq⟩ := hdvdy
  have h3kpos : 0 < (3:ℕ) ^ k := pow_pos (by norm_num) k
  have hx'pos : 0 < x' := by
    rcases Nat.eq_zero_or_pos x' with h | h
    · exfalso; rw [h, mul_zero] at hx'eq; omega
    · exact h
  have hy'pos : 0 < y' := by
    rcases Nat.eq_zero_or_pos y' with h | h
    · exfalso; rw [h, mul_zero] at hy'eq; omega
    · exact h
  have hxdiv : x / 3 ^ k = x' := by rw [hx'eq]; exact Nat.mul_div_cancel_left x' h3kpos
  have hydiv : y / 3 ^ k = y' := by rw [hy'eq]; exact Nat.mul_div_cancel_left y' h3kpos
  have hrpx : rp 3 x = x' % 3 := by unfold rp; rw [← hk, hxdiv]
  have hrpy : rp 3 y = y' % 3 := by unfold rp; rw [← hsame, hydiv]
  have hcopx : Nat.Coprime (x' % 3) 3 := hrpx ▸ rp_coprime 3 x h3 hx.ne'
  have hcopy : Nat.Coprime (y' % 3) 3 := hrpy ▸ rp_coprime 3 y h3 hy.ne'
  have hx'cop : ¬ (3:ℕ) ∣ x' := by
    intro hdvd
    have h0 : x' % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    rw [h0] at hcopx
    norm_num [Nat.Coprime, Nat.gcd_zero_left] at hcopx
  have hy'cop : ¬ (3:ℕ) ∣ y' := by
    intro hdvd
    have h0 : y' % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    rw [h0] at hcopy
    norm_num [Nat.Coprime, Nat.gcd_zero_left] at hcopy
  obtain ⟨hb0, hb1⟩ := coprime3_case (x' : ℤ) (y' : ℤ)
    (by exact_mod_cast hx'cop) (by exact_mod_cast hy'cop)
  refine ⟨1 / (3 ^ (k + 1) : ℝ), by positivity, ?_, ?_⟩
  · have hxcast : (x : ℝ) = (3:ℝ) ^ k * (x' : ℝ) := by exact_mod_cast hx'eq
    have heqx : (1 / (3 ^ (k + 1) : ℝ)) * (x : ℝ) = (1 / 3 : ℝ) * (x' : ℝ) := by
      rw [hxcast, pow_succ]
      have h3k0 : (3:ℝ) ^ k ≠ 0 := by positivity
      field_simp
    rw [heqx]
    exact_mod_cast hb0
  · have hycast : (y : ℝ) = (3:ℝ) ^ k * (y' : ℝ) := by exact_mod_cast hy'eq
    have heqy : (1 / (3 ^ (k + 1) : ℝ)) * (y : ℝ) = (1 / 3 : ℝ) * (y' : ℝ) := by
      rw [hycast, pow_succ]
      have h3k0 : (3:ℝ) ^ k ≠ 0 := by positivity
      field_simp
    rw [heqy]
    exact_mod_cast hb1

/-- Helper: bridges the `ℕ`-valued `diffValuation3_case`/`sameValuation3_case` witnesses (stated
for `x y : ℕ`) back to the `ℤ`-valued runner speeds `u : Fin 2 → ℤ` used by `ML`, via
`Int.toNat`/`Int.toNat_of_nonneg` and the divisibility-to-valuation translations
`padicValNat_dvd_iff_le`/`padicValNat.eq_zero_of_not_dvd`. -/
theorem barajasSerra_card2_general (u : Fin 2 → ℤ) (hpos : ∀ i, 0 < u i) :
    (1 / 3 : ℝ) ≤ ML u := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  set x : ℕ := (u 0).toNat with hxdef
  set y : ℕ := (u 1).toNat with hydef
  have hx0 : 0 < x := Int.pos_iff_toNat_pos.mp (hpos 0)
  have hy0 : 0 < y := Int.pos_iff_toNat_pos.mp (hpos 1)
  have hxcast : (x : ℤ) = u 0 := Int.toNat_of_nonneg (hpos 0).le
  have hycast : (y : ℤ) = u 1 := Int.toNat_of_nonneg (hpos 1).le
  have key : ∃ t : ℝ, 0 < t ∧ (1/3:ℝ) ≤ nearestIntDist (t * x) ∧ (1/3:ℝ) ≤ nearestIntDist (t * y) := by
    by_cases hd : nu 3 x = nu 3 y
    · exact sameValuation3_case x y hx0 hy0 hd
    · exact diffValuation3_case x y hx0 hy0 hd
  obtain ⟨t, ht0, hbx, hby⟩ := key
  have hle : (1 / 3 : ℝ) ≤ gap u t := by
    apply le_gap
    intro i
    match i with
    | 0 => rw [← hxcast]; simpa [mul_comm] using hbx
    | 1 => rw [← hycast]; simpa [mul_comm] using hby
  calc (1/3:ℝ) ≤ gap u t := hle
    _ ≤ ML u := le_csSup (bddAbove_range_gap u) ⟨t, rfl⟩

theorem barajasSerra_card2 (u : Fin 2 → ℤ) (hpos : ∀ i, 0 < u i) :
    (1 / 3 : ℝ) ≤ ML u := by
  by_cases h0 : (3:ℤ) ∣ u 0
  · by_cases h1 : (3:ℤ) ∣ u 1
    · exact barajasSerra_card2_general u hpos
    · exact barajasSerra_card2_general u hpos
  · by_cases h1 : (3:ℤ) ∣ u 1
    · exact barajasSerra_card2_general u hpos
    · obtain ⟨hb0, hb1⟩ := coprime3_case (u 0) (u 1) h0 h1
      have hle : (1 / 3 : ℝ) ≤ gap u (1/3) := by
        apply le_gap
        intro i
        fin_cases i
        · simpa [mul_comm] using hb0
        · simpa [mul_comm] using hb1
      calc (1/3:ℝ) ≤ gap u (1/3) := hle
        _ ≤ ML u := le_csSup (bddAbove_range_gap u) ⟨(1/3:ℝ), rfl⟩

/-! ## Section 3, `|D| = 4` (5 runners), session 5 (E6, session 5)

Paper argument (`bs2008.txt`, Section 3, second half; full derivation in
(development file, not part of this archive), "Session 5 addendum"): `p = 5`, `m = max nu_5(D)`,
`D5(i) := Dlevel 5 D i`. `D5(0)` and `D5(m)` are nonempty (needs `gcd(D) = 1` for `D5(0)`,
automatic for `D5(m)` by definition of `m`). Dichotomy on `|D5(j)|` for `j < m` (worked by hand,
(development file, not part of this archive)): either (a) `|D5(j)| ≤ 2` for every `j < m`, or (b)
`|D5(0)| = 3`, `|D5(m)| = 1`, and `D5(j) = ∅` for every other `j`. `|D| = 4` and both endpoint
levels nonempty force this; no third case.

Case (a) is **VERIFIED below** (`barajasSerra_card4_easy`): it is *exactly* the hypothesis shape
of the already-VERIFIED `primeFilteringCor3Top` with `p = 5` (`(p-1)/2 = 2`), so it needs no new
mathematical content, only the substitution.

Case (b) is the paper's `ℓ(A)` argument (eqs. (4)-(6)) and is **NOT formalized this session**
(I18 autopsy, `barajasSerra_card4_hard` below, `sorry`). See that theorem's docstring for the
precise blocking point and the falsification evidence (Rule 3, `check_D4_ellA` in
(development file, not part of this archive): 200000 trials, 0 failures, so the underlying claim is
HEURISTIC, not FALSE, and the blocker is formalization effort, not correctness). -/

/-- **VERIFIED, no `sorry`.** `|D| = 4` case (a): every non-top level has at most 2 elements.
Direct substitution into the already-VERIFIED `primeFilteringCor3Top` (`p = 5`, `(p-1)/2 = 2`).
No new mathematics; this is glue only. -/
theorem barajasSerra_card4_easy (D : Finset ℕ) (hDne : D.Nonempty) (hpos : ∀ d ∈ D, 0 < d)
    (m : ℕ) (hm : m = D.sup (nu 5)) (hcard : ∀ j < m, (Dlevel 5 D j).card ≤ 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 5 : ℝ) ≤ nearestIntDist (t * d) := by
  apply primeFilteringCor3Top 5 (by decide) D hDne hpos m hm
  intro j hj
  have := hcard j hj
  omega

/-- **VERIFIED, no `sorry` (session 9).** WLOG rotation-normalization lemma for the `|As|=3`
branch of `barajasSerra_card4_hard`. If three pairwise-distinct residues mod `5` are "hard"
(no rotation packs them into a length-`3` window `{0,1,2}` — this is the intended formalization
of "`ℓ({q(d1),q(d2),q(d3)}) ≥ 4`" / "eq. (6) fails at `j=1`" in the paper's language, though the
connection to the actual `qarc`-valued instance from `Dlevel 5 D 0` is NOT made in this lemma; see
the docstring on `barajasSerra_card4_hard` below for what remains), then SOME rotation `k` sends them exactly onto the
canonical triple `{0,2,3}`. Proved by exhaustive case split (`interval_cases` down to `125`
concrete numeral triples, each closed by `omega` on the distinctness hypotheses or `decide` on the
resulting finite membership/subset facts) — this is route (a) from the docstring on `barajasSerra_card4_hard` below, decided in
favor of route (a) over the reflection route (b) after `check_reflection_transport` falsified
session 8's specific reflection proposal (Rule 3). Independently cross-checked via an isomorphic
`Fin 5`-valued statement closed by a single top-level `decide` after `revert`
((development file, not part of this archive), not part of this file, kept as a private sanity artifact). -/
theorem card4_hard_rotation_normalize
    (r1 r2 r3 : ℕ) (h1 : r1 < 5) (h2 : r2 < 5) (h3 : r3 < 5)
    (hne12 : r1 ≠ r2) (hne13 : r1 ≠ r3) (hne23 : r2 ≠ r3)
    (hhard : ¬ ∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) ⊆
      ({0, 1, 2} : Finset ℕ)) :
    ∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) = ({0, 2, 3} : Finset ℕ) := by
  interval_cases r1 <;> interval_cases r2 <;> interval_cases r3 <;>
    first
      | (exfalso; omega)
      | (exfalso; apply hhard; decide)
      | decide


/-- **VERIFIED, no `sorry` (session 10). Resolves item (i) of the session-9 open-prerequisite
list: pairwise-distinctness of the three top digits is NOT always true for `|As| = 3`, and does
NOT need separate case-chase handling — it reduces to an EASIER case, one rotation away from
`{0,1,2}` with no further multiplication step at all.**

Rule 3 falsify-check (exhaustive, not random, since the state space is tiny): for every subset of
`Finset.range 5` of size `≤ 2` (all `C(5,1) + C(5,2) = 15` of them), the minimal cyclic window
length is `≤ 3`; 0 failures ((development file, not part of this archive) companion check run inline this
session, not saved as a separate script since it is a one-off 15-case exhaustive scan, reported
here literally: `trials=15 fails=0`). This is the reason non-distinct top digits are easier, not
harder: a 2-or-fewer-element set of residues mod `5` always fits inside SOME length-`3` window
`{k,k+1,k+2}` before any `j`-multiplication (eq. (5)) is even needed — unlike the genuinely
`ℓ = 4` "hard" orbit (`card4_hard_rotation_normalize` below), which needs the full eq.-(5)/(6)
chase.

This subsumes and generalizes `card4_hard_rotation_normalize`'s hypothesis space: together, the
two lemmas below (`card4_window_dichotomy`) partition ALL `125` triples `(r1,r2,r3) ∈ (range 5)^3`
into "fits a window after one rotation, no further work" (this lemma's branch, includes every
non-pairwise-distinct triple AND the `5` pairwise-distinct-but-`ℓ=3`-easy triples) vs. "genuinely
the `ℓ = 4` hard orbit" (needs `card4_hard_rotation_normalize`'s canonical-triple route). -/
theorem card4_window_easy (r1 r2 r3 : ℕ) (h1 : r1 < 5) (h2 : r2 < 5) (h3 : r3 < 5)
    (hnd : r1 = r2 ∨ r1 = r3 ∨ r2 = r3) :
    ∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) ⊆ ({0, 1, 2} : Finset ℕ) := by
  interval_cases r1 <;> interval_cases r2 <;> interval_cases r3 <;>
    first
      | (exfalso; omega)
      | decide

/-- **VERIFIED, no `sorry` (session 10).** Full dichotomy over all `125` triples of residues mod
`5`, combining `card4_window_easy` (non-distinct or `ℓ ≤ 3` distinct) with
`card4_hard_rotation_normalize` (the genuine `ℓ = 4` hard orbit) into a single case-complete
statement usable directly by the case chase. Closes item (i) completely: no triple of top digits
is ever left unhandled by one of the two branches. -/
theorem card4_window_dichotomy (r1 r2 r3 : ℕ) (h1 : r1 < 5) (h2 : r2 < 5) (h3 : r3 < 5) :
    (∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) ⊆ ({0, 1, 2} : Finset ℕ)) ∨
    (r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧
      ∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) = ({0, 2, 3} : Finset ℕ)) := by
  by_cases hnd : r1 = r2 ∨ r1 = r3 ∨ r2 = r3
  · exact Or.inl (card4_window_easy r1 r2 r3 h1 h2 h3 hnd)
  · push_neg at hnd
    obtain ⟨hne12, hne13, hne23⟩ := hnd
    by_cases hhard : ∃ k < 5, ({(r1 + k) % 5, (r2 + k) % 5, (r3 + k) % 5} : Finset ℕ) ⊆
        ({0, 1, 2} : Finset ℕ)
    · exact Or.inl hhard
    · exact Or.inr ⟨hne12, hne13, hne23,
        card4_hard_rotation_normalize r1 r2 r3 h1 h2 h3 hne12 hne13 hne23 hhard⟩

/-- **VERIFIED, no `sorry` (session 10). Resolves item (ii): the rotation-to-multiplication
bridge.** If three elements `d1, d2, d3` all sit at level `0` (`nu p d_i = 0`) and share the SAME
leading digit `rp p d_i = s` (a unit mod `p`, since each `d_i ≠ 0`), then the abstract rotation
`k` produced by `card4_window_dichotomy`/`card4_hard_rotation_normalize` is REALIZED by the
concrete unit multiplier `1 + p^m * k ∈ Lam 0 m p` (paper's `λ_k ∈ Λ_{0,p}`, eq. (4)): multiplying
each `d_i` by this single multiplier shifts every one of their top digits by exactly `k * s`
simultaneously (uniformly, since `s` does not depend on `i`) — this is a direct instantiation of
the already-VERIFIED `qarc_mul_lam_eq` at `j = 0`, not new arithmetic content. The common-`s`
hypothesis is exactly what makes a SINGLE `k` shift all three at once (session 9's docstring
already isolated this fact by hand; this lemma is its Lean realization). -/
theorem card4_rotation_is_multiplication (p m k s : ℕ) (hp : p.Prime) (hk : k < p)
    (d1 d2 d3 : ℕ) (hv1 : nu p d1 = 0) (hv2 : nu p d2 = 0) (hv3 : nu p d3 = 0)
    (hs1 : rp p d1 = s) (hs2 : rp p d2 = s) (hs3 : rp p d3 = s) :
    qarc p m (p ^ (m + 1)) ((1 + p ^ m * k) * d1) = (qarc p m (p ^ (m + 1)) d1 + k * s) % p ∧
    qarc p m (p ^ (m + 1)) ((1 + p ^ m * k) * d2) = (qarc p m (p ^ (m + 1)) d2 + k * s) % p ∧
    qarc p m (p ^ (m + 1)) ((1 + p ^ m * k) * d3) = (qarc p m (p ^ (m + 1)) d3 + k * s) % p := by
  have hm0 : m - 0 = m := by omega
  refine ⟨?_, ?_, ?_⟩
  · have := qarc_mul_lam_eq p 0 m hp (by omega) k hk d1 hv1
    rwa [hm0, hs1] at this
  · have := qarc_mul_lam_eq p 0 m hp (by omega) k hk d2 hv2
    rwa [hm0, hs2] at this
  · have := qarc_mul_lam_eq p 0 m hp (by omega) k hk d3 hv3
    rwa [hm0, hs3] at this

/-- **VERIFIED, no `sorry` (session 12). The `|As| = 2` minority-element counting argument**
(task item 2; paper `bs2008.txt` lines 233-238, `|As|=2` branch of the `ℓ(A)` case chase). Purely
a finite residue-mod-`5` fact, isolated exactly as `check_case_as2_minority` in
(development file, not part of this archive) isolates it (Rule 3, 500000 trials + negative control, 0
fails): given a popular shift `s ∈ {1,2}` for which some `k` keeps BOTH `q1, q2` (the two
majority-element top digits after the winning `j`-multiplication, already pinned into `{1,2}` by
the upstream case chase) out of the forbidden set `{0,4}`, and given the minority element's own
shift rate `other` is `r5(d3) = 2s` or `-2s mod 5` (never `= s`, since `d3 ∉ As` is exactly what
"minority" means, paper line 234) — some SUCH `k` also keeps `d3`'s residue `qd3` out of `{0,4}`.
Encoded as one existential (`∃ k`, all three conditions at once) rather than the paper's
two-step "good-for-`{1,2}`, then good-for-`3`" phrasing; the two are equivalent since a `k`
satisfying all three trivially lies in the `{1,2}`-good set. Closed by exhaustive case split:
`s ∈ {1,2}` (`2`), `other ∈ {2s,-2s} mod 5` (`2`), `q1,q2 ∈ {1,2}` (`4`), `qd3 < 5` (`5`) — `80`
concrete leaves, each decided by `decide` over the bounded existential `∃ k < 5`, same decidable
pattern as `card4_hard_rotation_normalize` above. Rule 6 review: quantifier order is `∀`
hypothesis instance `∃ k`, matching how the case chase consumes it (a single `k` must work for
all three elements). Edge case `other = s` (majority and minority accidentally coincide) is
excluded by hypothesis, not silently assumed: the negative control in `falsify.py` confirms the
claim is FALSE without it (nonzero fails), so this hypothesis is genuinely load-bearing, not
decorative. **Scope note (Rule 16 honesty): this lemma is one isolated finite fact inside the
larger `|As|=2` branch, not the branch itself.** It does NOT establish that `q1, q2 ∈ {1,2}` are
actually achieved after multiplication by the winning `j` (that is separate case-chase content,
itself resting on the still-`sorry` `ℓ(A)`/window machinery), nor does it wire the result back
into `Dlevel`/`primeFiltering` bookkeeping. See `barajasSerra_card4_hard`'s docstring below for
the full remaining gap list; this lemma closes exactly the sub-claim `check_case_as2_minority`
checks, no more. -/
theorem case_as2_minority (s other q1 q2 qd3 : ℕ)
    (hs : s = 1 ∨ s = 2)
    (hother : other = (2 * s) % 5 ∨ other = (5 - (2 * s) % 5) % 5)
    (hq1 : q1 = 1 ∨ q1 = 2) (hq2 : q2 = 1 ∨ q2 = 2) (hqd3 : qd3 < 5) :
    ∃ k < 5, ((q1 + k * s) % 5 ≠ 0 ∧ (q1 + k * s) % 5 ≠ 4) ∧
      ((q2 + k * s) % 5 ≠ 0 ∧ (q2 + k * s) % 5 ≠ 4) ∧
      ((qd3 + k * other) % 5 ≠ 0 ∧ (qd3 + k * other) % 5 ≠ 4) := by
  rcases hs with rfl | rfl <;> rcases hother with rfl | rfl <;>
    rcases hq1 with rfl | rfl <;> rcases hq2 with rfl | rfl <;>
    interval_cases qd3 <;> decide

/- **HISTORICAL (sessions 5-12). Session 13: `barajasSerra_card4_hard` was MOVED to
`LRSpectrumFull/BarajasSerraCard4.lean` and is proved there (no `sorry`), by a different route:
a kernel-`decide`d finite table over the relaxed carry model (`BarajasSerraCard4Table.combo`),
which needs neither the sign-flip WLOG nor the popular-class case chase described below.
The text below is the pre-session-13 autopsy, kept for the record.** Original header: `sorry`
(STATEMENT ONLY, semantics pinned; CONJECTURE-for-this-project, I18 autopsy,
updated session 6).**
`|D| = 4` case (b): `|D5(0)| = 3`, `|D5(m)| = 1`, all other levels empty. This is the paper's
`ℓ(A)` argument (eqs. (4)-(6)): writing `A = D5(0) = {d1,d2,d3}` and `q(d) := qarc 5 m N d`, the
paper shows some multiplier `lam ∈ Lam 0 m 5` composed with some `j ∈ {1,2,3,4}` (`Lam m 0 5`
acting on `A` via the direct-integer-multiplication trick of eq. (5), NOT a unit-multiplier
substitution) sends `q(j * lam * A)` into `Z5 \ {0,4}` simultaneously for all three elements,
while eq. (2)/`nu_mul_coprime`-style invariance keeps the single top-level element's own bound
intact. Combined with `primeFiltering`'s per-level budget this gives the result.

**Session 5 autopsy (superseded by session 6 below, kept for the record):** the blocking gap was
identified as a lemma not present anywhere in the file: an eq.-(5) analogue giving
`qarc p m N (j * d)` in terms of `qarc p m N d` and a CARRY bounded by `{0,...,j-1}`.

**Session 6 progress (item (1) of the session-5 three-item list CLOSED, VERIFIED):**
`qarc_add_carry` (general two-summand carry fact, any `x, y : ℕ`, carry `< 2`) and
`qarc_mul_smallint_carry` (the `j*d`-specific cumulative form, carry `≤ j - 1`) are now proved,
`sorry`-free, above this theorem. Falsify-checked in isolation first (Rule 3,
(development file, not part of this archive)): `check_carry_lemma` (fully general `x,y`, 50000 trials,
`p ∈ {3,5,7}`, 0 failures) and `check_carry_lemma_jd` (the `p=5`, `j ∈ {2,3,4}` specialization
plus the cumulative bound, 40047 trials, 0 failures), both before the Lean proof was written.

**I18 autopsy, session 6 (remaining gap, genuinely stuck point, NOT "almost done" per Rule 0):**
item (1) (the carry lemma) is done; items (2) and (3) of the session-5 plan are NOT done this
session. The blocking content in (2) is larger than the "small, `≤ 6` sub-cases" estimate in the
session-5 docstring suggested: the paper's own proof (`bs2008.txt`, lines 219-236) is not a single
finite decidable check over the `q(d_i)` residues alone. It is a two-branch case split on the
"most popular class" `|As|` (`|As| = 3` vs `|As| = {d1,d2}` with the third handled by a residue
disjointness argument), and within each branch a chain of THREE steps (`j = 1, 2, 3`) where, at
each step, the assumption "eq. (6) fails" pins down the EXACT value of `q(j*d_i)` for specific
`i` (not just membership in the generic `qarc_mul_smallint_carry` range), which then must be fed
back into the addition decomposition (`qarc_add_carry` applied again to `j*d_i, d_i`) to get a
TIGHTER inclusion for `q((j+1)*d_i)` than the generic cumulative bound gives. Formalizing this
needs, concretely: (i) a Lean statement of `ℓ(A)`, the "smallest length-`k` arithmetic-progression
window in `Z_5` containing a finite set of residues" (not present anywhere in this file or
`MaxLoneliness.lean`); (ii) the eq.-(4) unit-shift step (`qarc_mul_lam_eq` already covers this,
just needs the `j = 0`-level instantiation with `Lam 0 m 5`, not yet wired to this argument); (iii)
the exact case-chase above, which is a genuine nested `rcases`/`omega` tree (`2` carry-outcomes at
each of `3` steps, `2` branches on `|As|`, so on the order of `2^3 x 2 = 16` leaf cases minimum,
each needing the tightened, not generic, carry fact) — this is real proof content, not glue, and
was not attempted this session (Rule 2: time was spent on (1), the identified crux, and on
verifying it cleanly rather than starting (2) under time pressure and risking an unsound case
split). Falsify-checked as a black-box existence claim (Rule 3, unchanged from session 5):
`check_D4_ellA`, 200000 trials, 0 failures, so the overall target remains HEURISTIC, not FALSE.
Honest remaining work: (2) the `ℓ(A)`-argument case chase (fresh estimate: 2-4h, revised up from
the session-5 "small" estimate now that the exact-value tracking requirement is visible), then
(3) glue via `primeFiltering` (genuinely small, matching `barajasSerra_card4_easy`'s pattern).
Left as `sorry`.

**Session 8 (this session): re-derivation of the WLOG normalization, still NOT formalized,
new genuine blocking point identified BEFORE the case chase even starts.** Re-read
`bs2008.txt` Section 3 end-to-end again (lines ~150-236 of the pdftotext). Confirmed session 7's
finding (the exact-value, not just class-membership, tracking of `q(j*d)` through
`qarc_add_carry` reapplied at each step) by hand-verifying the paper's own arithmetic:
- `|As|=3` branch, normalized `q(d1,d2,d3)=(0,2,3)`: eq.(5) with `j=1` gives ranges
  `q(2d1)∈{0,1}, q(2d2)∈{0,4}, q(2d3)∈{1,2}` (8 combos). Directly enumerating `ℓ` (window size)
  for all 8 combos: exactly the 2 combos with `q(2d2)=4 ∧ q(2d3)=2` have `ℓ=4>3` (fail); the other
  6 have `ℓ≤3` (hold) — `q(2d1)` stays genuinely ambiguous (`∈{0,1}`) in the failing combos, matching
  the paper's claim verbatim. Then at `j=2→3`, using the PINNED `q(2d2)=4,q(2d3)=2` (not the loose
  cumulative range) plus the still-ambiguous `q(2d1)∈{0,1}` reproduces the paper's
  `q(3d1)⊂{0,1,2}, q(3d2)⊂{1,2}, q(3d3)⊂{0,1}` exactly, and all three ranges sit inside the common
  window `{0,1,2}` so `ℓ≤3` unconditionally at `j=3` — no further case split needed there. This
  hand-check is itself evidence (Rule 3-style, on top of `check_D4_ellA`) that the paper's argument
  is correct as literally written, PROVIDED the WLOG step below is valid.

**The actually-missing piece (not previously isolated): the WLOG normalization
`q(d1)=0, q(d2)=2, q(d3)=3` for the `|As|=3` branch is a nontrivial claim in its own right, not a
free relabeling.** Working it out from scratch (this was NOT spelled out in the paper beyond "up to
multiplication by `λk`"): since all three elements of `As` share `nu_5 = 0` and the same residue
class `s`, `r5(d) = s` for every `d ∈ As`, so a single `λk` shifts `q(d1), q(d2), q(d3)`
UNIFORMLY (all by `+k*s`, i.e. a rotation of `ℤ/5`). One can use this rotation freedom to send
`q(d1)` to `0`, but the two remaining differences `q(d2)-q(d1)` and `q(d3)-q(d1)` are then FIXED,
real invariants of the instance, not further reducible by `λk`. (6) failing at `j=1` forces
`ℓ({q(d1),q(d2),q(d3)}) ≥ 4`, and a direct count over all `Finset.range 5`-triples shows this
happens (after rotating one point to `0`) for exactly 3 of the 6 possible unordered pairs
`{a,b} ⊂ {1,2,3,4}` for the other two points: `{1,3}, {2,3}, {2,4}` (each giving cyclic gap
pattern `(0,1,1)` up to rotation, vs. the other 3 pairs `{1,2},{1,4},{3,4}` giving pattern
`(0,0,2)` or `(2,0,0)`, both `ℓ=3`, i.e. NOT the hard case). All three hard pairs are related by a
further RELABELING of which element is called `d2` vs. `d3` together with which residue is called
`s` (i.e. by the dihedral symmetry of `ℤ/5`, not by `λk` alone): e.g. `{2,3}` is literally the
paper's case; `{1,3}` and `{2,4}` are its images under swapping `d2 ↔ d3` composed with the
reflection `x ↦ -x` on the AMBIENT modulus (available because `q` and `ℓ` are computed relative
to `d1`'s own realized value, and the whole configuration can be reflected as a set without
touching any individual `d`, since reflection commutes with the digit arithmetic covered by
`qarc_add_carry`/`qarc_mul_smallint_carry`, both proved for general `x,y : ℕ`, no sign assumption
baked in — this still needs to be checked rigorously in the `ℕ`/`qarc` formalization, since `qarc`
as defined has no notion of "negation"; the paper's real-number/`ℤ` picture and this file's
`ℕ`-valued `qarc` may not transport the reflection symmetry for free). **This is the actual new
blocking point, upstream of the case chase itself**: a small lemma stating "if `ℓ` fails at `j=1`
for a normalized `|As|=3` triple, then, after possibly swapping the labels `d2,d3` and choosing
`λk` appropriately, `(q(d1),q(d2),q(d3)) = (0,2,3)`" is not yet stated or proved, and its proof
needs either (a) a case-exhaustive check over all `Finset.range 5 ×ˢ Finset.range 5 ×ˢ Finset.range 5`
triples with `decide`, which is cheap computationally but still needs the surrounding
quantifier structure (existential `λk`, existential relabeling) wired up correctly, or (b) the
reflection-symmetry route sketched above, made rigorous. Neither was attempted in Lean this
session (Rule 2: this session's budget went to re-deriving and hand-verifying the arithmetic
above by hand/on paper first, per Rule 6, before writing anything, given session 7's exact
failure mode was skipping this verification). **I18 autopsy: kill criterion for this session is
time — the normalization lemma alone is comparable in size to what session 7 estimated for the
whole case chase, so attempting the full case chase in the time remaining risks exactly session
7's mistake (a plausible-looking but false shortcut) at even higher stakes.** Given this is now
session 6, 7, AND 8 all failing to close this specific sub-goal (Rule 16, last-mile check): this
sub-goal should be escalated to a dedicated, longer, more heavily-scoped session (or split into
two sessions, one for the normalization lemma alone with its own falsify-check, one for the case
chase given the normalization as a hypothesis) rather than attempted a 4th time under the same
budget shape. The `|D|=2` case (`barajasSerra_card2`) remains fully VERIFIED and is real, standing
progress on E6 regardless of this branch's status.

**Session 9 (this session): the reflection question from session 8 is RESOLVED, and the answer
is a correction, not a confirmation — reflection is not needed at all, and the whole `|As|=3`
hard class collapses to ONE rotation-orbit, not three.**

Task for this session (narrow scope, WLOG normalization lemma only, no case chase): determine
whether session 8's proposed reflection `x ↦ -x` on `ℤ/5` is (a) free at the level of
`nearestIntDist` alone, (b) genuinely realizable at the `qarc` digit level via some transform of
the `d_i`, or (c) unnecessary because a cruder symmetry already suffices.

**Step 1 (Rule 3 falsify-check, (development file, not part of this archive),
`check_reflection_transport`, 40455 trials, `nu_5(d) = 0`, `m ∈ {1,..,4}` random): `x ↦ -x mod p`
(session 8's proposed reflection) is FALSE, 40455/40455 fails.** The actual digit-level identity
(0 fails) is `qarc p m N (N - d) = (p - 1) - qarc p m N d`, i.e. reflection through `(p-1)/2`-ish
(`x ↦ 4 - x` for `p = 5`), NOT reflection through `0` (`x ↦ -x mod p` fixes `0`, swaps `1 ↔ 4`,
`2 ↔ 3`; `x ↦ 4-x` fixes `2`, swaps `0 ↔ 4`, `1 ↔ 3`). These are different involutions of `ℤ/5`.
Session 8's proposed transport claim is **FALSE as stated** (Rule 0 label on that specific claim).
The `j`-multiplication compatibility check (`qarc(N - j·d)` vs `qarc(j·(N-d))`, same 40455 trials)
holds with 0 fails, confirming the mod-`N` residue arithmetic itself is fine — the failure is
specifically in which involution of `ℤ/5` the natural-number complement `d ↦ N-d` realizes. Also:
answering the task's own sub-question directly — no, `nearestIntDist(x) = nearestIntDist(-x)`
does NOT give the needed reduction "for free", because it is a fact about the FINAL numeric bound
for a single already-fixed witness `t`, not a mechanism for constructing the witness `t` for a
second (reflected) residue configuration from the witness for the first: the case-chase step that
would need to transport is upstream of `qarc_bridge_mid`/`nearestIntDist` entirely (it operates on
`qarc(j·d_i)` values via `qarc_add_carry`), so a symmetry of the final inequality is the wrong
level, exactly as flagged as the open risk in session 8.

**Step 2 (decisive, makes step 1's reflection question moot): exhaustive check (no randomness;
`check_full_orbit_exhaustive`, all `C(5,3) = 10` unordered triples of distinct residues mod 5,
cross-checked independently in Lean by `decide`, see `card4_hard_rotation_normalize` below) shows
rotation ALONE (no reflection, no relabeling — relabeling was never actually a separate operation
here, since `As` is a `Finset`, i.e. an unordered set, so "which element is called `d2` vs `d3`"
carries no mathematical content in the first place) already acts on the 10 triples in exactly 2
orbits: the "easy" orbit (`ℓ = 3`, 5 members, e.g. `{0,1,2}`) and the "hard" orbit (`ℓ = 4`, 5
members: `{0,1,3},{0,2,3},{0,2,4},{1,2,4},{1,3,4}`). Both orbits are `ℓ`-homogeneous. So EVERY
hard `|As|=3` instance rotates to the SAME canonical representative `{0,2,3}` — not merely 3-of-6
pairs needing an extra symmetry, as session 8 estimated, but all 5 hard triples reachable by
rotation from `{0,2,3}` alone. Session 8's "3 hard pairs related by reflection" framing was itself
imprecise: those 3 pairs (`{1,3},{2,3},{2,4}`, describing `q(d2)-q(d1),q(d3)-q(d1)` after fixing
`q(d1)=0`) are already a full rotation orbit under the S_3-relabel+rotation action, as verified by
`check_reflection_pair_orbit` (orbit of `(0,2,3)` under relabel+rotate = exactly
`{{1,3},{2,3},{2,4}}`, matching the hard set with no reflection added).

**Step 3 (Rule 6 adversarial review, done before committing the Lean lemma below):** quantifier
order is `∀` fixed hard triple `∃` rotation `k`, the only order that makes the WLOG usable
downstream. Edge case checked: the lemma requires the three residues PAIRWISE DISTINCT as an
explicit hypothesis — this is NOT proved here (it is a separate fact about `Dlevel 5 D 0`'s three
elements' top-level digits that must be established, or handled as its own case, before this
lemma applies; left as an open prerequisite, flagged honestly, not assumed away). No circularity:
the lemma is a leaf decidable fact with no dependency on the rest of this file's machinery.
Cross-checked by two independent computations (Python exhaustive/brute-force in `falsify.py` and
Lean's `decide` kernel check on an isomorphic `Fin 5` formulation, (development file, not part of this archive),
both agreeing) — satisfies Rule 3's "falsify before proving" for this specific finite claim.

**Route decided: (a) case-exhaustive `decide`, not (b) reflection machinery.** Reflection route
is dead (step 1); no new `qarc`-negation machinery is needed or attempted. The normalization lemma
below is `sorry`-free, VERIFIED (see build log). **What remains for the (separate, later) case
chase session:** (i) establish the three top-level digits of `Dlevel 5 D 0`'s elements are
pairwise distinct (or handle the repeat case separately) — genuinely NOT done, open; (ii) wire
`Lam 0 m 5`'s unit multiplier to realize the rotation `k` found here via `qarc_mul_lam_eq`
(mentioned but not instantiated this session); (iii) the `j = 1,2,3` case chase itself, now against
a SINGLE canonical triple `{0,2,3}` rather than 3-6 cases, which shrinks session 8's `2^3×2 = 16`
leaf-case estimate roughly in proportion (no longer multiplied by 3 or 6 hard/total configurations,
just the one canonical one) — still not attempted, still real proof content, still `2-4h` per
session 8's estimate for that part alone. Left as `sorry`. -/
end LRSpectrumFull.BarajasSerra
