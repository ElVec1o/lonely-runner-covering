/-
# D0 certificate: fast scalar chunk checker

`recOK3` is the checker measured to be about 3 times cheaper in the kernel than `recOK` of `D0Chunk`:
no `Fin 4 → ℤ` vectors (no `Matrix.vecCons` evaluation), all six inequalities in `ℕ` via `Int.natAbs`
and `Int.toNat` (kernel-accelerated `Nat` arithmetic), determinant by an explicit 16-scalar expansion.
`recOK3_sound : recOK3 r = true → S4 r.vn` (chain `recOK3 → recOK2 → recOK` of `D0Chunk`).
-/
import LRSpectrumFull.D0Chunk

namespace LRSpectrumFull
namespace D0

def det4s (m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33 : ℤ) : ℤ :=
  m00 * det3 m11 m12 m13 m21 m22 m23 m31 m32 m33
  - m01 * det3 m10 m12 m13 m20 m22 m23 m30 m32 m33
  + m02 * det3 m10 m11 m13 m20 m21 m23 m30 m31 m33
  - m03 * det3 m10 m11 m12 m20 m21 m22 m30 m31 m32

def sg (vi vj ai aj bi bj ci cj : ℤ) : ℤ :=
  |aj * vi - ai * vj| + |bj * vi - bi * vj| + |cj * vi - ci * vj|

def sgn (vi vj ai aj bi bj ci cj : ℤ) : ℕ :=
  (aj * vi - ai * vj).natAbs + (bj * vi - bi * vj).natAbs + (cj * vi - ci * vj).natAbs

/-- intermediate: scalar checker with `ℤ` inequalities -/
def recOK2 (r : Rec) : Bool :=
  decide (0 < r.v0 ∧ 0 < r.v1 ∧ 0 < r.v2 ∧ 0 < r.v3 ∧
    det4s r.v0 r.a0 r.b0 r.c0 r.v1 r.a1 r.b1 r.c1 r.v2 r.a2 r.b2 r.c2 r.v3 r.a3 r.b3 r.c3 ≠ 0 ∧
    5 * sg r.v0 r.v1 r.a0 r.a1 r.b0 r.b1 r.c0 r.c1 ≤ 3 * (r.v0 + r.v1) ∧
    5 * sg r.v0 r.v2 r.a0 r.a2 r.b0 r.b2 r.c0 r.c2 ≤ 3 * (r.v0 + r.v2) ∧
    5 * sg r.v0 r.v3 r.a0 r.a3 r.b0 r.b3 r.c0 r.c3 ≤ 3 * (r.v0 + r.v3) ∧
    5 * sg r.v1 r.v2 r.a1 r.a2 r.b1 r.b2 r.c1 r.c2 ≤ 3 * (r.v1 + r.v2) ∧
    5 * sg r.v1 r.v3 r.a1 r.a3 r.b1 r.b3 r.c1 r.c3 ≤ 3 * (r.v1 + r.v3) ∧
    5 * sg r.v2 r.v3 r.a2 r.a3 r.b2 r.b3 r.c2 r.c3 ≤ 3 * (r.v2 + r.v3))

/-- the checker used by the fast probes -/
def recOK3 (r : Rec) : Bool :=
  decide (0 < r.v0 ∧ 0 < r.v1 ∧ 0 < r.v2 ∧ 0 < r.v3 ∧
    det4s r.v0 r.a0 r.b0 r.c0 r.v1 r.a1 r.b1 r.c1 r.v2 r.a2 r.b2 r.c2 r.v3 r.a3 r.b3 r.c3 ≠ 0 ∧
    5 * sgn r.v0 r.v1 r.a0 r.a1 r.b0 r.b1 r.c0 r.c1 ≤ 3 * (r.v0.toNat + r.v1.toNat) ∧
    5 * sgn r.v0 r.v2 r.a0 r.a2 r.b0 r.b2 r.c0 r.c2 ≤ 3 * (r.v0.toNat + r.v2.toNat) ∧
    5 * sgn r.v0 r.v3 r.a0 r.a3 r.b0 r.b3 r.c0 r.c3 ≤ 3 * (r.v0.toNat + r.v3.toNat) ∧
    5 * sgn r.v1 r.v2 r.a1 r.a2 r.b1 r.b2 r.c1 r.c2 ≤ 3 * (r.v1.toNat + r.v2.toNat) ∧
    5 * sgn r.v1 r.v3 r.a1 r.a3 r.b1 r.b3 r.c1 r.c3 ≤ 3 * (r.v1.toNat + r.v3.toNat) ∧
    5 * sgn r.v2 r.v3 r.a2 r.a3 r.b2 r.b3 r.c2 r.c3 ≤ 3 * (r.v2.toNat + r.v3.toNat))

theorem sg_eq (vi vj ai aj bi bj ci cj : ℤ) :
    sg vi vj ai aj bi bj ci cj = (sgn vi vj ai aj bi bj ci cj : ℤ) := by
  simp only [sg, sgn, Int.abs_eq_natAbs]; push_cast; rfl

theorem recOK2_imp (r : Rec) (h : recOK2 r = true) : recOK r = true := by
  simp only [recOK2, recOK, Bool.and_eq_true, decide_eq_true_eq] at *
  obtain ⟨p0, p1, p2, p3, hd, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨⟨p0, p1, p2, p3⟩, hd, h1, h2, h3, h4, h5, h6⟩

theorem recOK3_imp (r : Rec) (h : recOK3 r = true) : recOK2 r = true := by
  simp only [recOK2, recOK3, decide_eq_true_eq] at *
  obtain ⟨p0, p1, p2, p3, hd, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨p0, p1, p2, p3, hd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [sg_eq] <;> omega

theorem recOK3_sound (r : Rec) (h : recOK3 r = true) : S4 r.vn :=
  recOK_sound r (recOK2_imp r (recOK3_imp r h))

def chunkOK3 (L : List Rec) : Bool := L.all recOK3

theorem chunkOK3_sound (L : List Rec) (h : chunkOK3 L = true) : ∀ r ∈ L, S4 r.vn := by
  intro r hr
  exact recOK3_sound r (List.all_eq_true.mp h r hr)

end D0
end LRSpectrumFull
