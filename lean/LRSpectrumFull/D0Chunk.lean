/-
# D0 certificate: chunk checker (Task B probe)

A record is `(v; k1; k2; k3)` = 16 integers.  `recOK` is a `Bool` that checks `0 < v i` and `D0cert`;
`chunkOK L = L.all recOK`.  `chunkOK_sound`: if `chunkOK L = true` then `S4` holds for every speed vector
in `L`.  Data modules close `chunkOK data = true` by `decide +kernel` (kernel evaluation only: the proof term is
`of_decide_eq_true (Eq.refl true)` checked by the kernel; no `native_decide`, no new axiom).
-/
import LRSpectrumFull.D0Bridge

namespace LRSpectrumFull
namespace D0

structure Rec where
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  b0 : ℤ
  b1 : ℤ
  b2 : ℤ
  b3 : ℤ
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ

def Rec.vv (r : Rec) : Fin 4 → ℤ := ![r.v0, r.v1, r.v2, r.v3]
def Rec.ka (r : Rec) : Fin 4 → ℤ := ![r.a0, r.a1, r.a2, r.a3]
def Rec.kb (r : Rec) : Fin 4 → ℤ := ![r.b0, r.b1, r.b2, r.b3]
def Rec.kc (r : Rec) : Fin 4 → ℤ := ![r.c0, r.c1, r.c2, r.c3]
/-- the natural-number speed vector of a record -/
def Rec.vn (r : Rec) : Fin 4 → ℕ := ![r.v0.toNat, r.v1.toNat, r.v2.toNat, r.v3.toNat]

def recOK (r : Rec) : Bool :=
  decide (0 < r.v0 ∧ 0 < r.v1 ∧ 0 < r.v2 ∧ 0 < r.v3) && decide (D0cert r.vv r.ka r.kb r.kc)

def chunkOK (L : List Rec) : Bool := L.all recOK

theorem recOK_sound (r : Rec) (h : recOK r = true) : S4 r.vn := by
  simp only [recOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨p0, p1, p2, p3⟩, hc⟩ := h
  have hv : (fun i => ((r.vn i : ℕ) : ℤ)) = r.vv := by
    funext i
    fin_cases i <;> simp [Rec.vn, Rec.vv, p0.le, p1.le, p2.le, p3.le]
  have hpos : ∀ i, 0 < r.vn i := by
    intro i
    fin_cases i <;> simp [Rec.vn] <;> omega
  refine d0_sound_nat r.vn hpos r.ka r.kb r.kc ?_
  rw [hv]; exact hc

theorem chunkOK_sound (L : List Rec) (h : chunkOK L = true) : ∀ r ∈ L, S4 r.vn := by
  intro r hr
  exact recOK_sound r (List.all_eq_true.mp h r hr)

end D0
end LRSpectrumFull
