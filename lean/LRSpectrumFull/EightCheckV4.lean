/-
# Kernel certificate checker v4 for the eight-runner Lemma 7 search (atom E7c)

Replays, with `Nat` bit operations only, a search-tree certificate that no ratio-min representative
7-tuple is bad (`k = 7`, `q = 8p`, window `[1, W]`, `W = 4p`).  Soundness statements are in
`EightCheckSound.lean`; this file only defines the checker.  Nothing here is a claim about the
lonely runner conjecture.

Representations.
* Speeds `v ≤ W` live in SPREAD form (bit `16 v`), so per-speed counters are 16-bit fields.
* Window positions `j` live in COMPACT form (bit `j`).
* Tables are functions (in the certificate modules: balanced trees of row constants, so a row lookup
  costs `log W` small unfoldings instead of a shift of the whole table).
  `cov v` = compact mask of the `j` covered by `v`; `covby j` = spread mask of the admissible `v`
  covering `j`; `adm`, `even`, `m8` = spread masks of admissible / even admissible / admissible
  multiples of 8; `ones` = spread mask of all `v ≤ W`.

Certificate: a stream of 16-bit fields read by a cursor (chunked, see `rd`).  Node records:
* `0 j` branch on the uncovered `j`, then child records, each `1 c n (w x)^n <subtree>`: take the
  coverer `c`, exclude the earlier ones, remove the `n` speeds `w` justified by witnesses `x`
  (ratio-min filter, see `filtOK`); closed by `0` (every coverer used) or by `2 <bound leaf>`
  (REST: a bound leaf on the same state with the used coverers removed).
* `1` no slot left, something uncovered.  `2 j` `j` uncovered with no available coverer.
* `3 t n v_1 .. v_n`: uniform bound with exception set `T = {v_i}` (strictly increasing) and
  threshold `t`: every available speed outside `T` covers at most `t` uncovered positions, every
  `v ∈ T` covers at least `t`, and `∑_T cnt + (r - n) t < |U|`.
* `4` all covered; the parity side condition leaves no completion.
* `7 i` delegated leaf (only in `checkRootH`): the state must equal `H i`.
* `5 s (j + 1024 y)^s t n v_1 .. v_n`: weighted bound, weights `y_j ≥ 1` on `s` strictly increasing
  uncovered `j`, loads `L_v = ∑ y_j [v covers j]` computed exactly, `Y = ∑ y_j ≤ 32767`; then the
  same `T`/`t` test on `L` against `Y`.

State carried down the tree: `sz` (chosen so far), `ev` (evens chosen), `avail` (spread),
`unc` (compact), `cu` (spread counters, field `v` = `|cov v ∩ unc|`, updated incrementally),
`nu = |unc|`, `d` (the ratio-min parameter).
-/

namespace LRSpectrumFull.EightV4

structure Ctx where
  p : Nat
  W : Nat
  cov : Nat → Nat
  covby : Nat → Nat
  adm : Nat
  even : Nat
  m8 : Nat
  ones : Nat
  /-- `cntF u acc = acc + ∑_{j ∈ u} covby j` (per-speed counters); in the certificate modules either
  `cntL covby 1024` or a walk down a balanced tree of masks that skips empty ranges -/
  cntF : Nat → Nat → Nat

/-- `a < b` through the accelerated `Nat.ble` (`Nat.blt` unfolds through `HAdd` / `OfNat` instances) -/
def ltN (a b : Nat) : Bool := Nat.ble (Nat.add a (nat_lit 1)) b

/-- field `pos` (16 bits) of the certificate, stored in chunks of 2048 fields: `C i` is chunk `i`.
(A single `Nat` certificate costs a shift of the whole certificate per read, and the kernel's whnf
cache keeps every shifted copy.) -/
def rd (C : Nat → Nat) (pos : Nat) : Nat :=
  Nat.land (Nat.shiftRight (C (Nat.shiftRight pos (nat_lit 11))) (Nat.mul (nat_lit 16) (Nat.land pos (nat_lit 2047)))) (nat_lit 65535)
/-- 16-bit field `v` of a spread vector -/
def fld (x v : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) v)) (nat_lit 65535)
def bitC (x j : Nat) : Bool := !Nat.beq (Nat.land (Nat.shiftRight x j) (nat_lit 1)) (nat_lit 0)
def bitS (x v : Nat) : Bool := !Nat.beq (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) v)) (nat_lit 1)) (nat_lit 0)
/-- `x` with the bits of `m` cleared -/
def clr (x m : Nat) : Nat := Nat.xor x (Nat.land x m)
def sbit (v : Nat) : Nat := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) v)
/-- `lgk k b 0 = log2 b` for a power of two `b < 2^(2^k)`, by binary search.  `Nat.log2` is NOT
kernel-accelerated in Lean 4.30 (measured: 13 ms per call at 652 bits, 0.7 s at 5000 bits). -/
def lgk : Nat → Nat → Nat → Nat
  | 0, _, i => i
  | k + 1, b, i =>
    let c := Nat.shiftRight b (Nat.shiftLeft (nat_lit 1) k)
    bif Nat.beq c (nat_lit 0) then lgk k b i else lgk k c (Nat.add i (Nat.shiftLeft (nat_lit 1) k))
/-- index of the lowest set bit of a compact mask below `2^1024` (`x ≠ 0`) -/
def lowC (x : Nat) : Nat := lgk (nat_lit 10) (Nat.xor x (Nat.land x (Nat.sub x (nat_lit 1)))) (nat_lit 0)
/-- index of the lowest set bit of a spread mask below `2^16384` (`x ≠ 0`) -/
def lowS (x : Nat) : Nat := lgk (nat_lit 14) (Nat.xor x (Nat.land x (Nat.sub x (nat_lit 1)))) (nat_lit 0)
/-- distance of `y` to the nearest multiple of `q` -/
def nrm (q y : Nat) : Nat :=
  let r := Nat.mod y q
  bif Nat.ble r (Nat.sub q r) then r else Nat.sub q r

/-- popcount of a compact mask (fuel bounds the count) -/
def pcl : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, u, acc => bif Nat.beq u (nat_lit 0) then acc else pcl f (Nat.land u (Nat.sub u (nat_lit 1))) (Nat.succ acc)

/-- `acc + ∑_{j ∈ u} cb j` by a lowest-bit loop (fuel bounds `|u|`); one admissible `cntF` -/
def cntL (cb : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, u, acc => bif Nat.beq u (nat_lit 0) then acc else
      let j := lowC u
      cntL cb f (Nat.xor u (Nat.shiftLeft (nat_lit 1) j)) (Nat.add acc (cb j))

/-- `acc + ∑_{j ∈ u} cb' (2^j)` by a lowest-bit loop, the row table `cb'` keyed by the isolated bit
`2^j` itself (no bit index is computed); the default `cntF` of the certificate modules -/
def cntB (cb' : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, u, acc => bif Nat.beq u (nat_lit 0) then acc else
      let b := Nat.xor u (Nat.land u (Nat.sub u (nat_lit 1)))
      cntB cb' f (Nat.xor u b) (Nat.add acc (cb' b))

/-- popcount of a spread mask: field `W` of `x * ones` -/
def spc (X : Ctx) (x : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul x X.ones) (Nat.mul (nat_lit 16) X.W)) (nat_lit 65535)

/-- every field of `L` selected by the spread mask `M` is at most `t` (fields of `L` below 2^15) -/
def allLe (X : Ctx) (L M t : Nat) : Bool :=
  ltN t (nat_lit 32768) &&
  Nat.beq (Nat.land (Nat.add L (Nat.mul (Nat.sub (nat_lit 32767) t) X.ones)) (Nat.shiftLeft M (nat_lit 15))) (nat_lit 0)

/-- read the exception set `T`: `n` strictly increasing speeds, each with `L_v ≥ t`; returns
`(∑_T L, M \ T, cursor)` -/
def readT (C : Nat → Nat) (L t : Nat) : Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | 0, _, s, M, pos => some (s, M, pos)
  | n + 1, pv, s, M, pos =>
    let v := rd C pos
    let lv := fld L v
    bif ltN pv v && Nat.ble t lv then readT C L t n v (Nat.add s lv) (clr M (sbit v)) (Nat.succ pos)
    else none

/-- the `t n T` tail of a bound leaf on loads `L` (fields < 2^15) against the bound `B`, over the
available mask `av` with `r` slots -/
def tailOK (X : Ctx) (C : Nat → Nat) (L B av r pos : Nat) : Option Nat :=
  let t := rd C pos
  let n := rd C (Nat.succ pos)
  bif Nat.ble n r then
    match readT C L t n (nat_lit 0) (nat_lit 0) av (Nat.add pos (nat_lit 2)) with
    | none => none
    | some (s, M, pos') =>
      bif allLe X L M t && ltN (Nat.add s (Nat.mul (Nat.sub r n) t)) B then some pos' else none
  else none

/-- read `s` weight pairs `(j, y)`, one field each (`j` = low 10 bits, `y` = high 6 bits), `j`
strictly increasing in `unc`, `y ≥ 1`; returns `(L, Y, cursor)` -/
def readW (X : Ctx) (C : Nat → Nat) (unc : Nat) : Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | 0, _, L, Y, pos => some (L, Y, pos)
  | n + 1, pj, L, Y, pos =>
    let f := rd C pos
    let j := Nat.land f (nat_lit 1023)
    let y := Nat.shiftRight f (nat_lit 10)
    bif ltN pj j && bitC unc j && Nat.ble (nat_lit 1) y then
      readW X C unc n j (Nat.add L (Nat.mul y (X.covby j))) (Nat.add Y y) (Nat.succ pos)
    else none

/-- a bound leaf (tag 3 or 5) at cursor `pos` on `(unc, cu, nu)` over `av` with `r` slots -/
def boundLeaf (X : Ctx) (C : Nat → Nat) (unc cu nu av r pos : Nat) : Option Nat :=
  let tag := rd C pos
  bif Nat.beq tag (nat_lit 3) then tailOK X C cu nu av r (Nat.succ pos)
  else bif Nat.beq tag (nat_lit 5) then
    match readW X C unc (rd C (Nat.succ pos)) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.add pos (nat_lit 2)) with
    | none => none
    | some (L, Y, pos') => bif ltN Y (nat_lit 32768) then tailOK X C L Y av r pos' else none
  else none

/-- the ratio-min filter: remove `n` speeds `w`, each with a witness `1 ≤ x < d` that
`|w / c| < d` (`c` a unit, `w` a multiple of 8, `‖x c‖ = w`) or `|c / w| < d` (`c` a multiple of
8, `w` a unit, `‖x w‖ = c`) -/
def filt (X : Ctx) (C : Nat → Nat) (c d : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, av, pos => some (av, pos)
  | n + 1, av, pos =>
    let w := rd C pos
    let x := rd C (Nat.succ pos)
    let q := Nat.mul (nat_lit 8) X.p
    bif Nat.ble (nat_lit 1) x && ltN x d &&
        ((Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 1) && Nat.beq (Nat.mod w (nat_lit 8)) (nat_lit 0) && Nat.beq (nrm q (Nat.mul x c)) w) ||
         (Nat.beq (Nat.mod c (nat_lit 8)) (nat_lit 0) && Nat.beq (Nat.mod w (nat_lit 2)) (nat_lit 1) && Nat.beq (nrm q (Nat.mul x w)) c))
    then filt X C c d n (clr av (sbit w)) (Nat.add pos (nat_lit 2)) else none

/-- no completion respects the parity cap (as in v2) -/
def noCompl (ev lim ae ao r : Nat) : Nat → Bool
  | 0 => !(Nat.ble ev lim) || ltN ao r
  | e + 1 => (!(Nat.ble (ev + (e + (nat_lit 1))) lim) || ltN ae (e + (nat_lit 1)) || ltN ao (r - (e + (nat_lit 1)))) &&
      noCompl ev lim ae ao r e

/-- the child records of a branch node.  `g sz ev avail unc cu nu pos` checks one subtree.
`m` = coverers of the branch position not yet used, `avr` = raw avail minus used coverers,
`aer` = effective avail minus used coverers -/
def kids (X : Ctx) (C : Nat → Nat) (g : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Nat)
    (sz ev unc cu nu d r : Nat) : Nat → Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | f + 1, m, avr, aer, pos =>
    let mk := rd C pos
    bif Nat.beq mk (nat_lit 0) then (bif Nat.beq m (nat_lit 0) then some (Nat.succ pos) else none)
    else bif Nat.beq mk (nat_lit 2) then boundLeaf X C unc cu nu aer r (Nat.succ pos)
    else bif Nat.beq mk (nat_lit 1) then
      let c := rd C (Nat.succ pos)
      let b := sbit c
      bif bitS m c then
        let avr' := clr avr b
        match filt X C c d (rd C (Nat.add pos (nat_lit 2))) avr' (Nat.add pos (nat_lit 3)) with
        | none => none
        | some (avc, pos3) =>
          let cc := X.cov c
          let ev' := bif Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0) then Nat.succ ev else ev
          match g (Nat.succ sz) ev' avc (clr unc cc)
              (Nat.sub cu (X.cntF (Nat.land unc cc) (nat_lit 0))) (Nat.sub nu (fld cu c)) pos3 with
          | none => none
          | some pos4 => kids X C g sz ev unc cu nu d r f (clr m b) avr' (clr aer b) pos4
      else none
    else none

/-- replay one subtree -/
def go (X : Ctx) (C : Nat → Nat) (H : Nat → Nat × Nat × Nat × Nat × Nat) (d : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _, _, _, _, _ => none
  | f + 1, sz, ev, avail, unc, cu, nu, pos =>
    let r := Nat.sub (nat_lit 7) sz
    let av' := bif Nat.ble (nat_lit 5) ev then clr avail X.even else avail
    let tag := rd C pos
    bif Nat.beq tag (nat_lit 0) then
      let j := rd C (Nat.succ pos)
      bif ltN sz (nat_lit 7) && bitC unc j then
        kids X C (go X C H d f) sz ev unc cu nu d r (nat_lit 1024) (Nat.land (X.covby j) av') avail av'
          (Nat.add pos (nat_lit 2))
      else none
    else bif Nat.beq tag (nat_lit 1) then
      bif Nat.beq r (nat_lit 0) && !Nat.beq unc (nat_lit 0) then some (Nat.succ pos) else none
    else bif Nat.beq tag (nat_lit 2) then
      let j := rd C (Nat.succ pos)
      bif bitC unc j && Nat.beq (Nat.land (X.covby j) av') (nat_lit 0) then some (Nat.add pos (nat_lit 2)) else none
    else bif Nat.beq tag (nat_lit 4) then
      let ae := spc X (Nat.land av' X.even)
      let ao := Nat.sub (spc X av') ae
      bif Nat.beq unc (nat_lit 0) && Nat.ble sz (nat_lit 7) && noCompl ev (nat_lit 5) ae ao r r then some (Nat.succ pos) else none
    else bif Nat.beq tag (nat_lit 7) then
      match H (rd C (Nat.succ pos)) with
      | (d', sz', ev', av'', unc') =>
        bif Nat.beq d' d && Nat.beq sz' sz && Nat.beq ev' ev && Nat.beq av'' avail && Nat.beq unc' unc
        then some (Nat.add pos (nat_lit 2)) else none
    else bif Nat.ble sz (nat_lit 7) then boundLeaf X C unc cu nu av' r pos
    else none

/-- no delegation: the `sz` component `99` never matches a real state -/
def noH : Nat → Nat × Nat × Nat × Nat × Nat :=
  fun _ => (nat_lit 0, nat_lit 99, nat_lit 0, nat_lit 0, nat_lit 0)

/-- sanity conditions on the context under which the replay is meaningful -/
def ctxOK (X : Ctx) : Bool := ltN (nat_lit 0) X.p && Nat.beq X.W (Nat.mul (nat_lit 4) X.p) && ltN X.W (nat_lit 1024)

/-- check one subtree from an explicit state (counters recomputed from `unc`; `avail` must be a
sub-mask of `adm`, which the parity leaf needs) -/
def checkState (X : Ctx) (d sz ev avail unc : Nat) (C : Nat → Nat) : Bool :=
  ctxOK X && ltN unc (Nat.shiftLeft (nat_lit 1) (Nat.succ X.W)) && !bitC unc (nat_lit 0) &&
  Nat.beq (clr avail X.adm) (nat_lit 0) &&
  match go X C noH d (nat_lit 9) sz ev avail unc (X.cntF unc (nat_lit 0)) (pcl (nat_lit 1024) unc (nat_lit 0)) (nat_lit 0) with
  | some _ => true
  | none => false

/-- the root: `S = {1}`, then one child per available multiple of 8, `e`, in increasing order;
child `e` has `S = {1, e}`, `d = e`, the smaller multiples of 8 excluded, and the units `w` with
`|e / w| < e` removed (witnessed) -/
def rootKids (X : Ctx) (C : Nat → Nat) (H : Nat → Nat × Nat × Nat × Nat × Nat) (unc1 cu1 nu1 : Nat) : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | f + 1, m, run, pos =>
    bif Nat.beq m (nat_lit 0) then some pos else
    let b := lowS m
    let e := Nat.shiftRight b (nat_lit 4)
    let run' := clr run (Nat.shiftLeft (nat_lit 1) b)
    match filt X C e e (rd C pos) run' (Nat.succ pos) with
    | none => none
    | some (av, pos1) =>
      let ce := X.cov e
      match go X C H e (nat_lit 9) (nat_lit 2) (nat_lit 1) av (clr unc1 ce) (Nat.sub cu1 (X.cntF (Nat.land unc1 ce) (nat_lit 0)))
          (Nat.sub nu1 (fld cu1 e)) pos1 with
      | none => none
      | some pos2 => rootKids X C H unc1 cu1 nu1 f (clr m (Nat.shiftLeft (nat_lit 1) b)) run' pos2

/-- the whole certificate -/
def checkRoot (X : Ctx) (C : Nat → Nat) : Bool :=
  let av1 := clr X.adm (sbit (nat_lit 1))
  let unc1 := clr (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ X.W)) (nat_lit 2)) (X.cov (nat_lit 1))
  let cu1 := X.cntF unc1 (nat_lit 0)
  ctxOK X &&
  match rootKids X C noH unc1 cu1 (pcl (nat_lit 1024) unc1 (nat_lit 0)) (nat_lit 1024) (Nat.land av1 X.m8) av1 (nat_lit 0) with
  | some _ => true
  | none => false

/-- the whole certificate with DELEGATED leaves: a record `7 i` closes the current state if it equals
`H i = (d, sz, ev, avail, unc)`; each `H i` is then discharged by a separate `checkState` theorem -/
def checkRootH (X : Ctx) (C : Nat → Nat) (H : Nat → Nat × Nat × Nat × Nat × Nat) : Bool :=
  let av1 := clr X.adm (sbit (nat_lit 1))
  let unc1 := clr (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ X.W)) (nat_lit 2)) (X.cov (nat_lit 1))
  let cu1 := X.cntF unc1 (nat_lit 0)
  ctxOK X &&
  match rootKids X C H unc1 cu1 (pcl (nat_lit 1024) unc1 (nat_lit 0)) (nat_lit 1024) (Nat.land av1 X.m8) av1 (nat_lit 0) with
  | some _ => true
  | none => false

end LRSpectrumFull.EightV4
