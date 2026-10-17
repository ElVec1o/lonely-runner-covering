import E8Stage.P31.Asm
import E8Stage.P37.Asm
import E8Stage.P43.Asm
import E8Stage.P47.Asm
import E8Stage.P53.Asm
import E8Stage.P59.Asm
import E8Stage.P61.Asm
import E8Stage.P67.Asm
import E8Stage.P71.Asm
import E8Stage.P73.Asm
import E8Stage.P79.Asm
import E8Stage.P83.Asm
import E8Stage.P89.Asm
import E8Stage.P97.Asm
import E8Stage.P101.Asm
import E8Stage.P103.Asm
import E8Stage.P107.Asm
import E8Stage.P109.Asm
import E8Stage.P113.Asm
import E8Stage.P127.Asm
import E8Stage.P131.Asm
import E8Stage.P137.Asm
import E8Stage.P139.Asm
import E8Stage.P149.Asm
import E8Stage.P151.Asm
import E8Stage.P157.Asm
import E8Stage.P163.Asm
import LRSpectrumFull.EightE5
import LRSpectrumFull.BarajasSerraLRC6Plan

/-!
# Eight runners with the 27 per-prime checks proved in-environment (no compacted axioms)

NOT part of the default `lake build` and not imported by any module of the package: it needs the
staged oleans `E8Stage/P<p>/Asm.olean` (and their imports) produced by
`code/eight/stage/run_campaign.sh`-style runs with `KEEP=1`, which live in
`code/eight/stage/work/olean`, outside the lake package. Build it only with
`bash code/eight/stage/assemble_real.sh` (raw `lean` + `LEAN_PATH`), never with `lake build`.

Each `LRSpectrumFull.EightV4.Cert<p>.lemma7Check_seven_p<p> : lemma7Check 7 p = true` is a
`decide +kernel` proof staged by `run_prime.sh`. `hchk_all_real` is the same case split as
`EightCert27.hchk_all` but uses these real theorems. `EightE5` (imported for `eight_runners_of`)
transitively imports `EightCert27`, so its 27 axioms are present in the environment, but
`eight_runners_of` takes the per-prime checks as a hypothesis and does not use them:
`#print axioms eight_runners_unconditional_real` must list only propext, Classical.choice,
Quot.sound. Label: VERIFIED only if that output is obtained; otherwise no claim.
-/

namespace LRSpectrumFull.EightRunnersReal
open LRSpectrumFull
open LRSpectrumFull.EightPlan

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem hchk_all_real : ∀ p ∈ rosenfeldS, lemma7Check 7 p = true := by
  intro p hp
  simp only [rosenfeldS, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [LRSpectrumFull.EightV4.Cert31.lemma7Check_seven_p31,
    LRSpectrumFull.EightV4.Cert37.lemma7Check_seven_p37,
    LRSpectrumFull.EightV4.Cert43.lemma7Check_seven_p43,
    LRSpectrumFull.EightV4.Cert47.lemma7Check_seven_p47,
    LRSpectrumFull.EightV4.Cert53.lemma7Check_seven_p53,
    LRSpectrumFull.EightV4.Cert59.lemma7Check_seven_p59,
    LRSpectrumFull.EightV4.Cert61.lemma7Check_seven_p61,
    LRSpectrumFull.EightV4.Cert67.lemma7Check_seven_p67,
    LRSpectrumFull.EightV4.Cert71.lemma7Check_seven_p71,
    LRSpectrumFull.EightV4.Cert73.lemma7Check_seven_p73,
    LRSpectrumFull.EightV4.Cert79.lemma7Check_seven_p79,
    LRSpectrumFull.EightV4.Cert83.lemma7Check_seven_p83,
    LRSpectrumFull.EightV4.Cert89.lemma7Check_seven_p89,
    LRSpectrumFull.EightV4.Cert97.lemma7Check_seven_p97,
    LRSpectrumFull.EightV4.Cert101.lemma7Check_seven_p101,
    LRSpectrumFull.EightV4.Cert103.lemma7Check_seven_p103,
    LRSpectrumFull.EightV4.Cert107.lemma7Check_seven_p107,
    LRSpectrumFull.EightV4.Cert109.lemma7Check_seven_p109,
    LRSpectrumFull.EightV4.Cert113.lemma7Check_seven_p113,
    LRSpectrumFull.EightV4.Cert127.lemma7Check_seven_p127,
    LRSpectrumFull.EightV4.Cert131.lemma7Check_seven_p131,
    LRSpectrumFull.EightV4.Cert137.lemma7Check_seven_p137,
    LRSpectrumFull.EightV4.Cert139.lemma7Check_seven_p139,
    LRSpectrumFull.EightV4.Cert149.lemma7Check_seven_p149,
    LRSpectrumFull.EightV4.Cert151.lemma7Check_seven_p151,
    LRSpectrumFull.EightV4.Cert157.lemma7Check_seven_p157,
    LRSpectrumFull.EightV4.Cert163.lemma7Check_seven_p163]

/-- LRC for eight runners, per-prime checks from the staged kernel proofs. -/
theorem eight_runners_unconditional_real (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
  EightE5.eight_runners_of BarajasSerra.LRC6_barajasSerra hchk_all_real v hv

end LRSpectrumFull.EightRunnersReal
