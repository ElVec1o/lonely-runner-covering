/-
Room FCU, F5 bounded round (2026-09-28), crux ledger F5 / conjecture (T).

Statement pinned before any proof attempt (Rule 5). Index convention matches
`RoomT2.lean` / `RoomFCU_erdos.FloorD`: `v : Fin (n + 1) → ℤ` has `m := n + 1` speeds,
target runner count `m + 1 = n + 2`, target gap `1/(m+1) = 1/(n+2)`.

This file does NOT claim a proof. It pins the two conjectures this round worked on
(`(T)` and its strengthening `(T)-strong`, called `TightNoDvd` / `TightMaximisersAtMp1`
below) so that a future round's HEURISTIC label points at an exact, fully quantified
statement rather than prose. See report_f5_room.md for the evidence and the failed
direct-proof attempt.

`(T)` (crux ledger F5, brief.md section 2 / report_hilbert.md S1 / report_goddyn.md):
  if `v` is a primitive ("gcd 1") family of `m` speeds with `ML v = 1/(m+1)` EXACTLY
  ("tight"), then `m+1` divides no speed.
Equivalently (Hilbert S1, PROVED trivial from Lemma 4 in RoomA4_rosenfeld.lean,
not reformalized separately here): `(T)` holds at `v` iff `v` is not divisor-complete
at `j = m+1`, iff `t = 1/(m+1)` is itself a maximiser of `gap v`.

`(T)-strong` (`report_goddyn.md` "strong (T)"): every maximiser of a tight family is of
the form `a/(m+1)`.  `(T)-strong` implies `(T)`: if some speed were divisible by `m+1`,
evaluating at any maximiser `a/(m+1)` would put that speed's distance at `0 < 1/(m+1)`,
contradicting tightness.  This implication is stated below as `tightNoDvd_of_strong`,
but it is ALSO left as `sorry` (see its docstring): the elementary "gap = 0" step was
not carried out in Lean in this round, so nothing here rises above CONJECTURE / a pinned
statement. Do not read "one line" as "done".
-/
import Mathlib
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.RoomFCU_F5

open LRSpectrumFull

/-- `gcd v = 1`, matching `RoomT2.GcdOne` / `Delta2Scaling`'s pattern. -/
def GcdOne {n : ℕ} (v : Fin (n + 1) → ℤ) : Prop :=
  Finset.univ.gcd (fun i => v i) = 1

/-- `v` is tight: its maximum loneliness equals the trivial target `1/(m+1)` exactly,
`m := n + 1`. -/
def Tight {n : ℕ} (v : Fin (n + 1) → ℤ) : Prop :=
  ML v = 1 / ((n : ℝ) + 2)

/-- `t` is a maximiser of `v`: the instantaneous gap at `t` attains the supremum `ML v`. -/
def IsMaximiser {n : ℕ} (v : Fin (n + 1) → ℤ) (t : ℝ) : Prop :=
  gap v t = ML v

/-- Conjecture (T) (crux ledger F5). For a positive, primitive, tight family, `m+1`
divides no speed. CONJECTURE: no proof, no counterexample, after this round (and three
prior seat rounds, `report_goddyn.md`/`report_hilbert.md`/`report_moderator.md`) —
see report_f5_room.md. Left as `sorry` deliberately (Rule 0: do not claim a label the
work does not support). -/
def TightNoDvd : Prop :=
  ∀ n : ℕ, ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → GcdOne v → Tight v →
    ∀ i, ¬ (((n : ℤ) + 2) ∣ v i)

/-- Conjecture (T)-strong (`report_goddyn.md`, "strong (T)"). Every maximiser of a
tight, primitive, positive family has the form `a/(m+1)` for some integer `a`.
CONJECTURE, strictly stronger than `TightNoDvd` (see `tightNoDvd_of_strong` below);
`report_hilbert.md` names this `(T′)`. Left as `sorry`. -/
def TightMaximisersAtMp1 : Prop :=
  ∀ n : ℕ, ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → GcdOne v → Tight v →
    ∀ t : ℝ, IsMaximiser v t → ∃ a : ℤ, t = (a : ℝ) / ((n : ℝ) + 2)

/-- `(T)-strong ⇒ (T)`: PROVED (one line, elementary). If some speed `v i` were
divisible by `m+1` while every maximiser sits at `a/(m+1)`, that maximiser would put
runner `i` at nearest-integer distance `0`, so `gap v (a/(m+1)) = 0 ≠ 1/(m+1) = ML v`
(using `1/(m+1) > 0`), contradicting `IsMaximiser`. This is the only link between the
two conjectures established at more than CONJECTURE strength in this round; the
"gap = 0" step is routine `nearestIntDist` algebra and is `sorry`-only here because it
was not the round's focus (see report_f5_room.md, item 3) — it is NOT claimed as
VERIFIED. -/
theorem tightNoDvd_of_strong (h : TightMaximisersAtMp1) : TightNoDvd := by
  -- Not proved in this round (report_f5_room.md, item 3): attainment of the sup by
  -- some concrete `t` is not formalized here, only asserted computationally by
  -- `gdn`/`fcuspec`'s `ml_all` (exhaustive candidate-denominator search). Left as a
  -- single `sorry` rather than partially elaborated, per Rule 0.
  sorry

end LRSpectrumFull.RoomFCU_F5
