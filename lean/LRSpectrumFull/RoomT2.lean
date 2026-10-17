/-
Room FCU, T2 sub-round (2026-09-28).

Statement pinned before any proof attempt (Rule 5).  Convention matches `RoomFCU_erdos.FloorD`:
`v : Fin (n + 1) → ℤ` has `n + 1 =: m` speeds, target runner count `n + 2 = m + 1`.

T2 (as issued, report_moderator.md 2026-09-24, section 7 item 3 / atom table):
  For all m ≥ 3 and positive integer `v` with `gcd(v) = 1` and some `(m + 1) ∣ v i`
  (equivalently `(n + 2) ∣ v i` in this file's index), `ML v ≥ 2 / (2 m + 1)`.

The brief's atom-table label is "floor 2/(2m+1) on D", where `D` is the divisor-complete
sub-class of `RoomFCU_erdos.FloorD`.  The ranking entry (section 7 item 3) and the original
2026-09-24/28 hunts (`t2hunt/out`, `out2`) test the WEAKER hypothesis set below (gcd 1 plus
the single divisibility condition `(m+1) ∣ v_i`, no full divisor-completeness).

CORRECTED 2026-09-28 (later same day): that search's mutation step could and did wander
outside `D` between checkpoints (only 2 of its 5 seed families, `E_m` and `F(m,j)`, are
divisor-complete by construction; its accept/reject mutation had no divisor-completeness
filter). So "`T2Weak` holds, hence `T2OnD` holds" is a valid logical inference
(`t2OnD_of_t2Weak` below), but the earlier claim that the *falsification data itself*
exhaustively covered `D` was not established — the search's bulk of evaluations were not
restricted to `D`, only its rediscovered champion happened to be. This has now been fixed
and re-run properly: `t2hunt`'s `rundc` mode adds an explicit `is_dc` filter to both seeding
and mutation, so every accepted state during the search is genuinely divisor-complete. Result
(`t2hunt/out_dc/`, m = 12..20, ~265M evaluations, ≥180s/m): zero violations, and the
minimiser found at every `m` is again the `E_m` family `[1,…,m−1, m(m+1)]` — the same
champion the unrestricted search found, now confirmed within a search that cannot leave `D`.
This is real, if still HEURISTIC-level (Rule 3), confirming evidence specifically for
`T2OnD`, not merely inherited from `T2Weak`.

CORRECTION 2026-10-01 (RoomT3 round, (development file, not part of this archive)): the `rundc` search seeded only `E_m`
and `F(m,j)`, so the statement above that `E_m` is the minimiser found 'at every m' is a seeding artifact,
not evidence that `E_m` is extremal in `D`. Exact enumeration inside boxes shows divisor-complete gcd-1
families with smaller `ML` than `E_m` for m = 3..10 (for example `[1,3,4]`, `ML = 2/7 = 2/(2m+1)`, so T2OnD
holds with equality at m = 3 inside `D`) and a tie at m = 14. The no-violation evidence for T2OnD therefore
rests on the exhaustive boxes (m <= 10) plus annealing whose coverage is limited; treat it as weaker than
stated in the paragraph above.

Status after this round: CONJECTURE, unchanged (no proof either way). See report_t2_room.md
for the exhaustion sweep (I2) and the reason `ML_ge_of_escape` (RoomFCU_compress.lean) does
not close it.
-/
import Mathlib
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.RoomT2

open LRSpectrumFull

/-- `gcd v = 1` via `Finset.gcd`, matching `Delta2Scaling`'s pattern. -/
def GcdOne {n : ℕ} (v : Fin (n + 1) → ℤ) : Prop :=
  Finset.univ.gcd (fun i => v i) = 1

/-- T2, weak-hypothesis form (the form actually hunted): gcd 1 plus a single divisor
condition `(n + 2) ∣ v i` for some `i`, WITHOUT the full divisor-complete requirement on `D`.
This is what `t2hunt/` tests and what `report_moderator.md` ranks; it is a stronger claim
than the `D`-restricted T2 (more hypotheses would only make the conclusion easier), so
refuting it here does not by itself refute the `D`-restricted crux-relevant statement, and
proving it here would prove the `D`-restricted one for free. -/
def T2Weak : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → GcdOne v →
    (∃ i, ((n + 2 : ℕ) : ℤ) ∣ v i) → 2 / (2 * (n : ℝ) + 3) ≤ ML v

/-- T2 restricted to the divisor-complete class `D` of `RoomFCU_erdos.FloorD`
(every `j ∈ [2, n+2]` divides some speed).  This is the form named in the brief's atom
table ("floor 2/(2m+1) on D") and in `FloorCruxU`'s hypothesis (DC). -/
def T2OnD : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin (n + 1) → ℤ, (∀ i, 0 < v i) → GcdOne v →
    (∀ j : ℕ, 2 ≤ j → j ≤ n + 2 → ∃ i, (j : ℤ) ∣ v i) →
    (∃ i, ((n + 2 : ℕ) : ℤ) ∣ v i) → 2 / (2 * (n : ℝ) + 3) ≤ ML v

/-- `T2Weak` is the stronger statement: it has fewer hypotheses (no divisor-completeness)
for the same conclusion, so it implies the `D`-restricted form directly. -/
theorem t2OnD_of_t2Weak (h : T2Weak) : T2OnD := by
  intro n hn v hv hg _ hdvd
  exact h n hn v hv hg hdvd

/-- T2Weak, unproved.  CONJECTURE per Rule 0: supported only by falsification data
(`t2hunt/`, 314M+ evaluations m = 14..20 plus this round's m = 22, 24 extension, viol = 0)
and by the equality cases m = 3..7 and m = 12 recorded in the moderator report.  No proof,
partial or otherwise, is claimed. -/
theorem t2Weak : T2Weak := by
  sorry

end LRSpectrumFull.RoomT2
