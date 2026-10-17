/-
# E6 session 13: finite table for the `|D| = 4` hard case (core only, no Mathlib)

Relaxed digit model of the paper's eqs. (4)-(5), p = 5. For a level-0 element `d` put `a = q(d)`,
`r = d mod 5`, and let `c1 c2 c3 ∈ {0,1}` be the carries with `q(2d) = q(d)+q(d)+c1`,
`q(3d) = q(2d)+q(d)+c2`, `q(4d) = q(3d)+q(d)+c3` (mod 5). The multiplier `(1 + 5^m k) * j`
(`1 ≤ j ≤ 4`, `k < 5`) sends `q(d)` to `q(j d) + k * (j r mod 5)` (mod 5). `good` says the result
avoids the forbidden arcs `{0, 4}`.

`combo`: for ANY three elements of this relaxed model (carries free, `r` free in `1..4`, no
popular-class or sign normalization) some common `(j, k)` is good for all three. Checked
exhaustively (all 160^3 triples) by kernel `decide` over the 80 distinct good-set bitmasks. The
same exhaustive check was run first in Rust ((development file, not part of this archive): 0 bad
triples out of 4096000), Rule 3.
-/

namespace LRSpectrumFull.BarajasSerra.Card4Table

/-- Model of `q(j d) mod 5` from `a = q(d)` and the three carries. -/
def qj (a c1 c2 c3 j : Nat) : Nat :=
  match j with
  | 1 => a
  | 2 => (a + a + c1) % 5
  | 3 => ((a + a + c1) % 5 + a + c2) % 5
  | _ => (((a + a + c1) % 5 + a + c2) % 5 + a + c3) % 5

/-- The multiplier `(1 + 5^m k) * j` puts `d` outside the arcs `{0, 4}`. -/
def good (a r c1 c2 c3 j k : Nat) : Bool :=
  ((qj a c1 c2 c3 j + k * ((j * r) % 5)) % 5 != 0) &&
  ((qj a c1 c2 c3 j + k * ((j * r) % 5)) % 5 != 4)

/-- Bitmask of good `(j, k)`, bit `5 (j - 1) + k`. -/
def mask (a r c1 c2 c3 : Nat) : Nat :=
  (List.range 20).foldl
    (fun acc b => if good a r c1 c2 c3 (b / 5 + 1) (b % 5) then acc + 2 ^ b else acc) 0

def tab : List Nat := [241340, 241372, 243054, 251603, 252281, 252345, 256377, 256732, 368077, 375413, 375605, 380730, 386294, 386518, 389590, 389941, 433978, 434074, 440555, 445686, 446266, 451830, 452054, 455477, 470439, 472787, 472915, 480697, 480979, 481657, 481721, 486108, 634556, 634588, 636270, 636604, 644462, 644942, 645799, 649593, 696122, 696218, 702699, 703386, 707830, 714637, 717035, 717419, 728693, 736154, 740813, 741261, 747115, 747405, 749803, 750187, 831315, 833212, 841070, 841550, 842407, 842574, 846247, 846503, 859597, 859765, 866933, 867125, 871885, 872333, 878187, 881110, 929191, 929619, 931539, 931667, 939449, 940878, 944551, 944807]
def ch0 : List Nat := [241340, 241372, 243054, 251603, 252281, 252345, 256377, 256732, 368077, 375413]
def ch1 : List Nat := [375605, 380730, 386294, 386518, 389590, 389941, 433978, 434074, 440555, 445686]
def ch2 : List Nat := [446266, 451830, 452054, 455477, 470439, 472787, 472915, 480697, 480979, 481657]
def ch3 : List Nat := [481721, 486108, 634556, 634588, 636270, 636604, 644462, 644942, 645799, 649593]
def ch4 : List Nat := [696122, 696218, 702699, 703386, 707830, 714637, 717035, 717419, 728693, 736154]
def ch5 : List Nat := [740813, 741261, 747115, 747405, 749803, 750187, 831315, 833212, 841070, 841550]
def ch6 : List Nat := [842407, 842574, 846247, 846503, 859597, 859765, 866933, 867125, 871885, 872333]
def ch7 : List Nat := [878187, 881110, 929191, 929619, 931539, 931667, 939449, 940878, 944551, 944807]
theorem tab_eq : tab = ch0 ++ ch1 ++ ch2 ++ ch3 ++ ch4 ++ ch5 ++ ch6 ++ ch7 := by decide +kernel

theorem tri0 : (ch0.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri1 : (ch1.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri2 : (ch2.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri3 : (ch3.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri4 : (ch4.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri5 : (ch5.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri6 : (ch6.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tri7 : (ch7.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true := by
  decide +kernel

theorem tab_lt : (tab.all fun x => decide (x < 2 ^ 20)) = true := by decide +kernel

theorem mask_mem_all : ((List.range 5).all fun a => (List.range 5).all fun r =>
    (List.range 2).all fun c1 => (List.range 2).all fun c2 => (List.range 2).all fun c3 =>
    r == 0 || (tab.contains (mask a r c1 c2 c3))) = true := by decide +kernel

theorem mask_bit_all : ((List.range 5).all fun a => (List.range 5).all fun r =>
    (List.range 2).all fun c1 => (List.range 2).all fun c2 => (List.range 2).all fun c3 =>
    (List.range 20).all fun b =>
      (mask a r c1 c2 c3).testBit b == good a r c1 c2 c3 (b / 5 + 1) (b % 5)) = true := by
  decide +kernel

theorem mask_mem (a : Nat) (ha : a < 5) (r : Nat) (hr : r < 5) (c1 : Nat) (h1 : c1 < 2)
    (c2 : Nat) (h2 : c2 < 2) (c3 : Nat) (h3 : c3 < 2) (hr0 : 0 < r) :
    mask a r c1 c2 c3 ∈ tab := by
  have := mask_mem_all
  simp only [List.all_eq_true, List.mem_range] at this
  have h := this a ha r hr c1 h1 c2 h2 c3 h3
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with h | h
  · omega
  · exact h

theorem mask_bit (a : Nat) (ha : a < 5) (r : Nat) (hr : r < 5) (c1 : Nat) (h1 : c1 < 2)
    (c2 : Nat) (h2 : c2 < 2) (c3 : Nat) (h3 : c3 < 2) (b : Nat) (hb : b < 20) :
    (mask a r c1 c2 c3).testBit b = good a r c1 c2 c3 (b / 5 + 1) (b % 5) := by
  have := mask_bit_all
  simp only [List.all_eq_true, List.mem_range] at this
  have h := this a ha r hr c1 h1 c2 h2 c3 h3 b hb
  simpa using h

theorem triple (x y z : Nat) (hx : x ∈ tab) (hy : y ∈ tab) (hz : z ∈ tab) : (x &&& y &&& z) ≠ 0 := by
  have hall : ∀ x ∈ tab, ∀ y ∈ tab, ∀ z ∈ tab, (x &&& y &&& z) ≠ 0 := by
    intro x hx
    rw [tab_eq] at hx
    simp only [List.mem_append] at hx
    have key : ∀ l : List Nat,
        (l.all fun x => tab.all fun y => tab.all fun z => (x &&& y &&& z) != 0) = true →
        x ∈ l → ∀ y ∈ tab, ∀ z ∈ tab, (x &&& y &&& z) ≠ 0 := by
      intro l hl hxl y hy z hz
      simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hl
      exact hl x hxl y hy z hz
    rcases hx with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact key _ tri0 h
    · exact key _ tri1 h
    · exact key _ tri2 h
    · exact key _ tri3 h
    · exact key _ tri4 h
    · exact key _ tri5 h
    · exact key _ tri6 h
    · exact key _ tri7 h
  exact hall x hx y hy z hz

/-- **VERIFIED target (kernel `decide`, no `native_decide`).** Any three elements of the relaxed
digit model share a good multiplier `(j, k)`, `1 ≤ j ≤ 4`, `k < 5`. -/
theorem combo (a1 r1 c11 c12 c13 a2 r2 c21 c22 c23 a3 r3 c31 c32 c33 : Nat)
    (ha1 : a1 < 5) (hr1 : r1 < 5) (hr1' : 0 < r1) (h11 : c11 < 2) (h12 : c12 < 2) (h13 : c13 < 2)
    (ha2 : a2 < 5) (hr2 : r2 < 5) (hr2' : 0 < r2) (h21 : c21 < 2) (h22 : c22 < 2) (h23 : c23 < 2)
    (ha3 : a3 < 5) (hr3 : r3 < 5) (hr3' : 0 < r3) (h31 : c31 < 2) (h32 : c32 < 2) (h33 : c33 < 2) :
    ∃ j k, 1 ≤ j ∧ j ≤ 4 ∧ k < 5 ∧ good a1 r1 c11 c12 c13 j k = true ∧
      good a2 r2 c21 c22 c23 j k = true ∧ good a3 r3 c31 c32 c33 j k = true := by
  have m1 := mask_mem a1 ha1 r1 hr1 c11 h11 c12 h12 c13 h13 hr1'
  have m2 := mask_mem a2 ha2 r2 hr2 c21 h21 c22 h22 c23 h23 hr2'
  have m3 := mask_mem a3 ha3 r3 hr3 c31 h31 c32 h32 c33 h33 hr3'
  obtain ⟨b, hb⟩ := Nat.exists_testBit_of_ne_zero (triple _ _ _ m1 m2 m3)
  simp only [Nat.testBit_and, Bool.and_eq_true] at hb
  obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
  have hlt : ∀ x ∈ tab, x < 2 ^ 20 := by
    have := tab_lt
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this
  have hb20 : b < 20 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have h1 : mask a1 r1 c11 c12 c13 < 2 ^ b :=
      Nat.lt_of_lt_of_le (hlt _ m1) (Nat.pow_le_pow_right (by decide) hge)
    rw [Nat.testBit_lt_two_pow h1] at hb1
    exact Bool.false_ne_true hb1
  refine ⟨b / 5 + 1, b % 5, by omega, by omega, Nat.mod_lt _ (by decide), ?_, ?_, ?_⟩
  · rw [← mask_bit a1 ha1 r1 hr1 c11 h11 c12 h12 c13 h13 b hb20]; exact hb1
  · rw [← mask_bit a2 ha2 r2 hr2 c21 h21 c22 h22 c23 h23 b hb20]; exact hb2
  · rw [← mask_bit a3 ha3 r3 hr3 c31 h31 c32 h32 c33 h33 b hb20]; exact hb3

end LRSpectrumFull.BarajasSerra.Card4Table
