/-
# Time cover: the finite covering check (natural-number bitmasks, kernel-evaluable) and its soundness

Boxes are triples `(w₁, w₂, w₃)` (arc offsets of three coordinates).  For a coordinate offset `w`, the piece
`p < M2` lies in the closed arc iff `(p + w) % M2 ≤ L2`.  `maskAt` is the bitmask (bit `k` = `k`-th box) of the
boxes whose arc contains piece `p`.  `tab` lists the masks for all pieces `p < M2`; `dedup` removes consecutive
repeats (a mask list is constant on runs).  `coverB` checks, for every triple of masks `m₁ m₂ m₃` occurring in the
three deduplicated tables, that `m₁ &&& m₂ &&& m₃ ≠ 0`, where the middle level is deduplicated again after
masking with `m₁`.  `cover_sound`: if `coverB = true` then every triple of pieces `(p₁,p₂,p₃)` lies in a common
box, with the same box index in all three coordinates.
-/
import Mathlib

namespace LRSpectrumFull
namespace TC

/-- bit `k` is set iff piece `p` lies in the arc of the `k`-th box -/
def maskAt {B : Type} (M2 L2 : ℕ) (f : B → ℕ) (p : ℕ) : List B → ℕ
  | [] => 0
  | b :: bs => (if (p + f b) % M2 ≤ L2 then 1 else 0) + 2 * maskAt M2 L2 f p bs

theorem maskAt_testBit {B : Type} (M2 L2 : ℕ) (f : B → ℕ) (p : ℕ) :
    ∀ (bs : List B) (k : ℕ), (maskAt M2 L2 f p bs).testBit k = true →
      ∃ hk : k < bs.length, (p + f (bs[k])) % M2 ≤ L2 := by
  intro bs
  induction bs with
  | nil => intro k hk; simp [maskAt] at hk
  | cons b bs ih =>
    intro k hk
    have hm : maskAt M2 L2 f p (b :: bs)
        = (if (p + f b) % M2 ≤ L2 then 1 else 0) + 2 * maskAt M2 L2 f p bs := rfl
    rw [hm] at hk
    cases k with
    | zero =>
      rw [Nat.testBit_zero] at hk
      by_cases hc : (p + f b) % M2 ≤ L2
      · exact ⟨by simp, by simpa using hc⟩
      · rw [if_neg hc] at hk
        simp at hk
    | succ k =>
      rw [Nat.testBit_succ] at hk
      have hdiv : ((if (p + f b) % M2 ≤ L2 then 1 else 0) + 2 * maskAt M2 L2 f p bs) / 2
          = maskAt M2 L2 f p bs := by
        split_ifs <;> omega
      rw [hdiv] at hk
      obtain ⟨hlt, hh⟩ := ih k hk
      exact ⟨by simp; omega, by simpa using hh⟩

/-- `dd prev xs`: `xs` with consecutive repeats (and a leading repeat of `prev`) removed -/
def dd : ℕ → List ℕ → List ℕ
  | _, [] => []
  | prev, x :: xs => if x = prev then dd prev xs else x :: dd x xs

def dedup : List ℕ → List ℕ
  | [] => []
  | x :: xs => x :: dd x xs

theorem mem_dd (prev : ℕ) : ∀ (xs : List ℕ) (x : ℕ), x ∈ xs → x = prev ∨ x ∈ dd prev xs := by
  intro xs
  induction xs generalizing prev with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
    intro x hx
    unfold dd
    by_cases hy : y = prev
    · rw [if_pos hy]
      rcases List.mem_cons.mp hx with h | h
      · left; rw [h, hy]
      · exact ih prev x h
    · rw [if_neg hy]
      rcases List.mem_cons.mp hx with h | h
      · right; rw [h]; exact List.mem_cons_self
      · rcases ih y x h with h' | h'
        · right; rw [h']; exact List.mem_cons_self
        · right; exact List.mem_cons_of_mem _ h'

theorem mem_dedup {L : List ℕ} {x : ℕ} (h : x ∈ L) : x ∈ dedup L := by
  cases L with
  | nil => simp at h
  | cons z zs =>
    unfold dedup
    rcases List.mem_cons.mp h with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · rcases mem_dd z zs x h1 with h2 | h2
      · rw [h2]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h2

def chk1 (s : ℕ) (D3 : List ℕ) : Bool := D3.all fun x => (s &&& x) != 0

def chk2 (x1 : ℕ) (D2 D3 : List ℕ) : Bool :=
  (dedup (D2.map fun y => x1 &&& y)).all fun s => chk1 s D3

def chk3 (D1 D2 D3 : List ℕ) : Bool := D1.all fun x1 => chk2 x1 D2 D3

theorem chk3_sound {D1 D2 D3 : List ℕ} (h : chk3 D1 D2 D3 = true) :
    ∀ m1 ∈ D1, ∀ m2 ∈ D2, ∀ m3 ∈ D3, ((m1 &&& m2) &&& m3) ≠ 0 := by
  intro m1 h1 m2 h2 m3 h3
  unfold chk3 at h
  have h' := List.all_eq_true.mp h m1 h1
  unfold chk2 at h'
  have hm : (m1 &&& m2) ∈ dedup (D2.map fun y => m1 &&& y) :=
    mem_dedup (List.mem_map.mpr ⟨m2, h2, rfl⟩)
  have h'' := List.all_eq_true.mp h' _ hm
  unfold chk1 at h''
  have := List.all_eq_true.mp h'' m3 h3
  simpa using this

theorem exists_testBit {n : ℕ} (h : n ≠ 0) : ∃ k, n.testBit k = true := by
  by_contra hcon
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have h2 : n.testBit i ≠ true := fun h' => hcon ⟨i, h'⟩
  simp only [ne_eq, Bool.not_eq_true] at h2
  simp [h2]

def tab {B : Type} (M2 L2 : ℕ) (f : B → ℕ) (bs : List B) : List ℕ :=
  (List.range M2).map fun p => maskAt M2 L2 f p bs

def coverB (M2 L2 : ℕ) (bs : List (ℕ × ℕ × ℕ)) : Bool :=
  chk3 (dedup (tab M2 L2 (fun b => b.1) bs)) (dedup (tab M2 L2 (fun b => b.2.1) bs))
    (dedup (tab M2 L2 (fun b => b.2.2) bs))

theorem mem_tab {B : Type} {M2 L2 : ℕ} (f : B → ℕ) (bs : List B) {p : ℕ} (hp : p < M2) :
    maskAt M2 L2 f p bs ∈ dedup (tab M2 L2 f bs) :=
  mem_dedup (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩)

theorem cover_sound {M2 L2 : ℕ} {bs : List (ℕ × ℕ × ℕ)} (h : coverB M2 L2 bs = true)
    {p1 p2 p3 : ℕ} (h1 : p1 < M2) (h2 : p2 < M2) (h3 : p3 < M2) :
    ∃ k, ∃ hk : k < bs.length,
      (p1 + (bs[k]).1) % M2 ≤ L2 ∧ (p2 + (bs[k]).2.1) % M2 ≤ L2 ∧
        (p3 + (bs[k]).2.2) % M2 ≤ L2 := by
  have h' : chk3 (dedup (tab M2 L2 (fun b => b.1) bs)) (dedup (tab M2 L2 (fun b => b.2.1) bs))
      (dedup (tab M2 L2 (fun b => b.2.2) bs)) = true := h
  have hne := chk3_sound h' _ (mem_tab (L2 := L2) (fun b => b.1) bs h1) _
    (mem_tab (L2 := L2) (fun b => b.2.1) bs h2) _ (mem_tab (L2 := L2) (fun b => b.2.2) bs h3)
  obtain ⟨k, hk⟩ := exists_testBit hne
  rw [Nat.testBit_and, Nat.testBit_and] at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
  obtain ⟨hlt, c1⟩ := maskAt_testBit M2 L2 (fun b => b.1) p1 bs k hk1
  obtain ⟨_, c2⟩ := maskAt_testBit M2 L2 (fun b => b.2.1) p2 bs k hk2
  obtain ⟨_, c3⟩ := maskAt_testBit M2 L2 (fun b => b.2.2) p3 bs k hk3
  exact ⟨k, hlt, c1, c2, c3⟩

end TC
end LRSpectrumFull
