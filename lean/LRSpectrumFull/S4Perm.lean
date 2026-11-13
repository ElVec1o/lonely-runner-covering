/-
# S4 range: permutation plumbing

`S4q a b c d` is `S4 ![a,b,c,d]`.  `sel i a b c d` picks the `i`-th of the four numbers (`i : ℕ`, anything
`≥ 3` gives `d`).  `anyPerm L f a b c d` tests `f` on the speeds rearranged by every index quadruple in `L`.
`anyPerm_sound`: if every quadruple of `L` is a permutation of `{0,1,2,3}` (`IsPerm`, decided once per list)
and `f` is sound for a vector of four positive pairwise distinct speeds, then `anyPerm L f a b c d = true`
implies `S4q a b c d` for four positive pairwise distinct speeds.  Invariance of `S4` under permuting the
speeds together with their phases is `S4_of_cover`.
-/
import LRSpectrumFull.D0Bridge

namespace LRSpectrumFull
namespace D0

/-- `S4` for four listed speeds -/
def S4q (a b c d : ℕ) : Prop := S4 ![a, b, c, d]

/-- the `i`-th of four numbers -/
def sel (i a b c d : ℕ) : ℕ := if i = 0 then a else if i = 1 then b else if i = 2 then c else d

abbrev Perm4 := ℕ × ℕ × ℕ × ℕ

/-- the four components are distinct and below 4 -/
def IsPerm (p : Perm4) : Prop :=
  p.1 < 4 ∧ p.2.1 < 4 ∧ p.2.2.1 < 4 ∧ p.2.2.2 < 4 ∧
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2

instance (p : Perm4) : Decidable (IsPerm p) := by unfold IsPerm; infer_instance

def anyPerm (L : List Perm4) (f : ℕ → ℕ → ℕ → ℕ → Bool) (a b c d : ℕ) : Bool :=
  L.any fun p => f (sel p.1 a b c d) (sel p.2.1 a b c d) (sel p.2.2.1 a b c d) (sel p.2.2.2 a b c d)

/-- `S4` is invariant under rearranging speeds (with their phases), for an injective speed vector. -/
theorem S4_of_cover {v w : Fin 4 → ℕ} (hv : Function.Injective v)
    (h1 : ∀ r, ∃ s, w r = v s) (h2 : ∀ j, ∃ r, w r = v j) (h : S4 w) : S4 v := by
  intro φ
  choose s hs using h1
  obtain ⟨t, ht⟩ := h (fun r => φ (s r))
  refine ⟨t, fun j => ?_⟩
  obtain ⟨r, hr⟩ := h2 j
  have hsr : s r = j := hv (by rw [← hs r, hr])
  have h3 := ht r
  have h4 : GoodR (v (s r)) (φ (s r)) t := by rw [← hs r]; exact h3
  rw [hsr] at h4
  exact h4

theorem sel_lt {i : ℕ} (a b c d : ℕ) : ∃ s : Fin 4, sel i a b c d = ![a, b, c, d] s := by
  unfold sel
  split_ifs
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem sel_ne {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    sel i a b c d ≠ sel j a b c d := by
  unfold sel
  split_ifs <;> omega

theorem sel_pos {i a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < sel i a b c d := by
  unfold sel
  split_ifs <;> assumption

theorem vec_get (a b c d : ℕ) (j : Fin 4) : ∃ i : ℕ, i < 4 ∧ ![a, b, c, d] j = sel i a b c d := by
  fin_cases j
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩

theorem vec_inj {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

theorem vec_pos {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ∀ i, 0 < (![a, b, c, d] : Fin 4 → ℕ) i := by
  intro i
  fin_cases i <;> simpa

/-- a sound test `f` on four positive pairwise distinct speeds, run over rearrangements `L` of the speeds -/
theorem anyPerm_sound (L : List Perm4) (hL : ∀ p ∈ L, IsPerm p) (f : ℕ → ℕ → ℕ → ℕ → Bool)
    (hf : ∀ x y u w : ℕ, 0 < x → 0 < y → 0 < u → 0 < w → x ≠ y → x ≠ u → x ≠ w → y ≠ u → y ≠ w →
      u ≠ w → f x y u w = true → S4q x y u w)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : anyPerm L f a b c d = true) : S4q a b c d := by
  unfold anyPerm at h
  rw [List.any_eq_true] at h
  obtain ⟨p, hp, hfp⟩ := h
  obtain ⟨p0, p1, p2, p3, n01, n02, n03, n12, n13, n23⟩ := hL p hp
  have key := hf _ _ _ _ (sel_pos ha hb hc hd) (sel_pos ha hb hc hd) (sel_pos ha hb hc hd)
    (sel_pos ha hb hc hd)
    (sel_ne p0 p1 n01 hab hac had hbc hbd hcd) (sel_ne p0 p2 n02 hab hac had hbc hbd hcd)
    (sel_ne p0 p3 n03 hab hac had hbc hbd hcd) (sel_ne p1 p2 n12 hab hac had hbc hbd hcd)
    (sel_ne p1 p3 n13 hab hac had hbc hbd hcd) (sel_ne p2 p3 n23 hab hac had hbc hbd hcd) hfp
  unfold S4q at key ⊢
  refine S4_of_cover (vec_inj hab hac had hbc hbd hcd) ?_ ?_ key
  · intro r
    fin_cases r
    · exact sel_lt a b c d
    · exact sel_lt a b c d
    · exact sel_lt a b c d
    · exact sel_lt a b c d
  · intro j
    obtain ⟨i, hi, hij⟩ := vec_get a b c d j
    have hcov : i = p.1 ∨ i = p.2.1 ∨ i = p.2.2.1 ∨ i = p.2.2.2 := by omega
    rcases hcov with h0 | h0 | h0 | h0
    · exact ⟨0, by rw [hij, h0]; rfl⟩
    · exact ⟨1, by rw [hij, h0]; rfl⟩
    · exact ⟨2, by rw [hij, h0]; rfl⟩
    · exact ⟨3, by rw [hij, h0]; rfl⟩

end D0
end LRSpectrumFull
