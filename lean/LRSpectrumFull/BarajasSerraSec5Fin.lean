/-
# E6 session 20: finite core of Barajas-Serra Section 5 (`|A| = 4`), core only (no Mathlib)

Model of a level-0 element `x` under the multipliers `(1 + 7^m k) j`, `1 ≤ j ≤ 5`: `a = q(x)`,
`f = (x mod 7^m) / 7^m`; then `q(j x) = j a + ⌊j f⌋ (mod 7)`. The carry vector `(⌊j f⌋)_{j ≤ 5}` is
one of the 10 rows of `CT` (Farey fractions of order 5). This is sharper than the paper's eq. (9)
(`q((j+1)x) ∈ q(jx) + q(x) + {0,1}`): with (9) alone the claim (12) of Case 3 is FALSE in the model
(28 pair configurations, `e6s20/sec5.rs`), while (12) holds exactly (m = 2, 3, `e6s20/sec5c.rs`) and
in the Farey model (`e6s20/sec5f.rs`).

`F1`, `F2`, `F3`: some `j ≤ 4` (resp. `≤ 5`) puts the class-`s` `q`-values in an arc of length
`5`, `4`, `2` (four, three, two elements; first `a` normalized to 0). `Z1`, `Z2`, `Z3`: an arc plus
the other classes (ratios `2`, `4`) admit a `Λ_0` shift `k`. Rust mirror: `e6s20/sec5d.rs`
(0 failures; negative control: `Z3` with ratios `(4,4)` fails 84 times).
-/

namespace LRSpectrumFull.BarajasSerra.Sec5Fin

def CT : List (List Nat) := [[0,0,0,0,0],[0,0,0,0,1],[0,0,0,1,1],[0,0,1,1,1],[0,0,1,1,2],
  [0,1,1,2,2],[0,1,1,2,3],[0,1,2,2,3],[0,1,2,3,3],[0,1,2,3,4]]

/-- carry `⌊j f⌋` in Farey row `p`. -/
def cf (p j : Nat) : Nat := (CT.getD p []).getD (j - 1) 0

/-- model value of `q(j x)`. -/
def qm (a p j : Nat) : Nat := (j * a + cf p j) % 7

def arcB (len t : Nat) (vs : List Nat) : Bool := vs.all (fun v => decide ((v + 7 - t) % 7 < len))

def hasArc (len : Nat) (vs : List Nat) : Bool := (List.range 7).any (fun t => arcB len t vs)

def gd (v : Nat) : Bool := v % 7 != 0 && v % 7 != 6

theorem cf_one : (List.range 10).all (fun p => cf p 1 == 0) = true := by decide

theorem farey_pick : (List.range 2).all (fun c2 => (List.range 3).all (fun c3 => (List.range 4).all
    (fun c4 => (List.range 5).all (fun c5 => !(CT.contains [0, c2, c3, c4, c5]) || (List.range 10).any
      (fun p => cf p 2 == c2 && cf p 3 == c3 && cf p 4 == c4 && cf p 5 == c5))))) = true := by decide

/-- representatives of the Farey rows for `j ≤ 4` (rows agreeing on `⌊2f⌋, ⌊3f⌋, ⌊4f⌋`). -/
def rep4 (p : Nat) : Nat := [0, 0, 2, 3, 3, 5, 5, 7, 8, 8].getD p 0

theorem rep4_spec : (List.range 10).all (fun p => [0, 2, 3, 5, 7, 8].contains (rep4 p) &&
    (List.range 5).all (fun j => cf p j == cf (rep4 p) j)) = true := by decide

/-- the 24 codes `a = a2 + 7 a3 + 49 a4` with `{0,a2,a3,a4}` in no arc of length 5. -/
def bad24 : List Nat := [75, 87, 124, 131, 132, 136, 137, 144, 159, 166, 183, 184, 215, 216, 233, 240, 255, 262, 263, 267, 268, 275, 312, 324]

theorem F1a : (List.range 343).all (fun a => hasArc 5 [0, a % 7, a / 7 % 7, a / 49] || bad24.contains a) = true := by
  decide +kernel

def inner1 (a : Nat) : Bool := [0, 2, 3, 5, 7, 8].all (fun p1 => [0, 2, 3, 5, 7, 8].all (fun p2 =>
  [0, 2, 3, 5, 7, 8].all (fun p3 => [0, 2, 3, 5, 7, 8].all (fun p4 => (List.range 4).any (fun j =>
    hasArc 5 [qm 0 p1 (j + 1), qm (a % 7) p2 (j + 1), qm (a / 7 % 7) p3 (j + 1), qm (a / 49) p4 (j + 1)])))))

theorem F1b0 : [75, 87, 124, 131, 132, 136].all inner1 = true := by decide +kernel
theorem F1b1 : [137, 144, 159, 166, 183, 184].all inner1 = true := by decide +kernel
theorem F1b2 : [215, 216, 233, 240, 255, 262].all inner1 = true := by decide +kernel
theorem F1b3 : [263, 267, 268, 275, 312, 324].all inner1 = true := by decide +kernel

theorem F1b : bad24.all inner1 = true := by
  rw [show bad24 = [75, 87, 124, 131, 132, 136] ++ [137, 144, 159, 166, 183, 184] ++
    [215, 216, 233, 240, 255, 262] ++ [263, 267, 268, 275, 312, 324] from rfl, List.all_append,
    List.all_append, List.all_append, F1b0, F1b1, F1b2, F1b3]; rfl

/-- F2: three elements of one class (Farey representatives, `j ≤ 4`). -/
theorem F2 : (List.range 49).all (fun a => [0, 2, 3, 5, 7, 8].all (fun p1 => [0, 2, 3, 5, 7, 8].all
    (fun p2 => [0, 2, 3, 5, 7, 8].all (fun p3 => (List.range 4).any (fun j => hasArc 4
      [qm 0 p1 (j + 1), qm (a % 7) p2 (j + 1), qm (a / 7) p3 (j + 1)]))))) = true := by decide +kernel

/-- F3: two elements of one class (needs `j = 5`). -/
theorem F3 : (List.range 7).all (fun a => (List.range 100).all (fun pc => (List.range 5).any
    (fun j => hasArc 2 [qm 0 (pc % 10) (j + 1), qm a (pc / 10) (j + 1)]))) = true := by decide +kernel

/-- Z1: an arc of length 5, one class, `J = j r(x1) ≠ 0`. -/
theorem Z1 : (List.range 7).all (fun t => (List.range 7).all (fun J => J == 0 ||
    (List.range 7).any (fun k => (List.range 7).all (fun u =>
      !(decide ((u + 7 - t) % 7 < 5)) || gd (u + k * J))))) = true := by decide +kernel

/-- Z2: an arc of length 4 plus one element of ratio 2 or 4. -/
theorem Z2 : (List.range 7).all (fun t => (List.range 7).all (fun w => (List.range 7).all (fun J =>
    J == 0 || [2, 4].all (fun r => (List.range 7).any (fun k => (List.range 7).all (fun u =>
      !(decide ((u + 7 - t) % 7 < 4)) || gd (u + k * J)) && gd (w + k * (r * J % 7))))))) = true := by
  decide +kernel

/-- Z3: an arc of length 2 plus two elements with ratios `(2,2)`, `(2,4)` or `(4,2)`. -/
theorem Z3 : (List.range 7).all (fun t => (List.range 7).all (fun w1 => (List.range 7).all (fun w2 =>
    (List.range 7).all (fun J => J == 0 || [(2, 2), (2, 4), (4, 2)].all (fun rr =>
      (List.range 7).any (fun k => (List.range 7).all (fun u =>
        !(decide ((u + 7 - t) % 7 < 2)) || gd (u + k * J)) && gd (w1 + k * (rr.1 * J % 7)) &&
          gd (w2 + k * (rr.2 * J % 7)))))))) = true := by decide +kernel

theorem shift0 : (List.range 7).all (fun a => (List.range 7).all (fun r => r == 0 ||
    (List.range 7).any (fun c => (a + c * r) % 7 == 0))) = true := by decide

end LRSpectrumFull.BarajasSerra.Sec5Fin
