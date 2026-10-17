/-
# The computational core for four runners

Rosenfeld's chain (arXiv:2509.14111) for `k` velocities is: for each prime `p` passing the Lemma 7
check, `p` divides the product of the speeds of any counterexample; if the product of the passing
primes exceeds the Corollary 3 bound, there is no counterexample.

For `k = 3` the chain is small.  The Corollary 3 bound is `[C(4,2)^2/3]^3 = 1728`, and the primes
`7, 11, 13, 17` all pass, with product `17017 > 1728`.  The largest window is `M = 34`.

This file supplies the decidable core: `lemma7Check k p` is `true` exactly when no valid `k`-tuple
in the window covers it.  The side condition is tested in the DIVISIBILITY-COUNT form proved
equivalent in `GcdSideCondition.lean`, which is what makes it cheap: the naive form is a gcd over
every `(k-1)`-subset of every tuple, whereas here it is one count per prime factor of `k+1`.

For `k = 3` the modulus is `q = 4p`, whose only prime factor besides `p` is `2`, and multiples of `p`
are excluded separately.  So the side condition is exactly: AT MOST ONE of the three velocities is
even.

The threshold is `1/(k+1)`, matching Lemma 6.  Note that the cover relation printed before Lemma 7
in the paper reads `1/(k-1)`; that is a typo, since Lemma 7 is stated as an equivalent reformulation
of Lemma 6.
-/

import Mathlib

namespace LRSpectrumFull

/-- `v` covers `j` at modulus `q = (k+1)*p`: the distance of `j*v/q` to the integers is below
`1/(k+1)`. -/
def coversAt (k p j v : ℕ) : Bool :=
  let q := (k + 1) * p
  let r := j * v % q
  (k + 1) * min r (q - r) < q

/-- the admissible velocities: `[1, ⌊q/2⌋]` with the multiples of `p` removed -/
def admissible (k p : ℕ) : List ℕ :=
  (List.range (((k + 1) * p) / 2 + 1)).filter (fun v => 1 ≤ v && v % p != 0)

/-- the side condition, in the divisibility-count form of `gcd_side_condition_iff`: for every prime
`ℓ` dividing `k+1`, at most `k-2` of the velocities are divisible by `ℓ` -/
def sideOK (k : ℕ) (V : List ℕ) : Bool :=
  ((List.range (k + 2)).filter (fun l => 2 ≤ l && (k + 1) % l == 0 && Nat.Prime l)).all
    (fun l => (V.filter (fun v => v % l == 0)).length ≤ k - 2)

/-- `V` covers the whole window -/
def coversWindow (k p : ℕ) (V : List ℕ) : Bool :=
  ((List.range (((k + 1) * p) / 2 + 1)).filter (fun j => 1 ≤ j)).all
    (fun j => V.any (fun v => coversAt k p j v))

/-- all `k`-element subsets of the admissible set.  `sublistsLen` enumerates these directly; the
full powerset would be `2^32` lists at `p = 17`. -/
def tuples (k p : ℕ) : List (List ℕ) :=
  (admissible k p).sublistsLen k

/-- **The Lemma 7 check**: no valid `k`-tuple covers the window. -/
def lemma7Check (k p : ℕ) : Bool :=
  (tuples k p).all (fun V => !(sideOK k V && coversWindow k p V))

-- The four primes the chain needs are checked in `LRCFourRunners.lean`; this file holds only
-- the definitions, so that the expensive evaluation is isolated from the build of the core.

end LRSpectrumFull
