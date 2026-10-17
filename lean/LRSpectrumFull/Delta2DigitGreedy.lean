/-
# The digit-greedy witness slices

Systematizing the digit mechanics of the verified `five_runners` (Barajas–Serra Prime Filtering)
into uniform-in-`k` witness theorems.

* `floor_of_not_dvd_le` — the widened non-resonant slice: if **some** `2 ≤ q ≤ k+2` divides no
  velocity, `t = 1/q` clears the floor.  (The previously verified slice was `q = k+2` only;
  empirically this widening covers 86–92% of the Riesz-failing hard core.)

* `floor_of_two_level` — the carry-free rung of the digit greedy: `p` prime, `3 ≤ p ≤ k+2`,
  `1 ≤ L`; every velocity is a unit mod `p` or `p^L` times a unit; if at most `(p−1)/2` are
  units, some digit `c` makes `t = (c·p^L + 1)/p^{L+1}` a witness.  High runners are
  automatically safe; each unit runner forbids exactly two values of `c` (its target digit is an
  invertible-affine function of `c`), so a good digit exists by counting.  This is the mechanism
  by which Prime-Filtering beats resonance, verified uniformly in `k`.

The full multi-level greedy (all non-maximal `p`-levels of size `≤ (p−1)/2`, digits chosen
bottom-up against carries) is the same mechanism iterated; its statement is in the paper as a
PROVED-candidate with this file as the formalized base rung (a 23,698-instance falsification
sweep found zero failures of criterion or construction).
-/
import LRSpectrumFull.Delta2Connect

namespace LRSpectrumFull

/-- **Widened non-resonant slice.**  If some modulus `2 ≤ q ≤ k+2` divides no velocity, then
`t = 1/q` witnesses the floor. -/
theorem floor_of_not_dvd_le {k : ℕ} (q : ℕ) (hq2 : 2 ≤ q) (hqk : q ≤ k + 2)
    (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (h : ∀ i, ¬ (q ∣ (v i).toNat)) : 1 / ((k : ℝ) + 2) ≤ ML v := by
  refine cube_floor_of_witness v hv 1 q (by omega) (fun i => ?_)
  have hr : (v i).toNat * 1 % q ≠ 0 := by
    rw [mul_one]; exact fun h0 => h i (Nat.dvd_of_mod_eq_zero h0)
  have hlt : (v i).toNat * 1 % q < q := Nat.mod_lt _ (by omega)
  have h1 : 1 ≤ min ((v i).toNat * 1 % q) (q - (v i).toNat * 1 % q) := by omega
  calc q ≤ (k + 2) * 1 := by omega
    _ ≤ (k + 2) * min ((v i).toNat * 1 % q) (q - (v i).toNat * 1 % q) :=
        Nat.mul_le_mul_left _ h1

set_option maxHeartbeats 1600000 in
/-- **The carry-free two-level greedy.**  `p` prime, `3 ≤ p ≤ k+2`, `1 ≤ L`.  If every velocity
is either a unit mod `p` or exactly `p^L` times a unit, and at most `(p−1)/2` are units, then
some digit `c < p` makes `t = (c·p^L + 1)/p^{L+1}` a witness for the floor. -/
theorem floor_of_two_level {k : ℕ} (p L : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpk : p ≤ k + 2) (hL : 1 ≤ L) (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hsplit : ∀ i, ¬ (p ∣ (v i).toNat) ∨
      (p ^ L ∣ (v i).toNat ∧ ¬ (p ∣ (v i).toNat / p ^ L)))
    (hcount : 2 * (Finset.univ.filter (fun i => ¬ (p ∣ (v i).toNat))).card ≤ p - 1) :
    1 / ((k : ℝ) + 2) ≤ ML v := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp0.ne'⟩
  set P : ℕ := p ^ L with hPdef
  have hP0 : 0 < P := pow_pos hp0 L
  set low : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => ¬ (p ∣ (v i).toNat)) with hlow
  -- forbidden digits: for each unit runner, the two `c` putting its target digit at `0` or `p−1`
  set forb : Finset (ZMod p) := low.biUnion (fun i =>
    {(-((((v i).toNat / P : ℕ) : ZMod p))) * (((v i).toNat : ZMod p))⁻¹,
     (-1 - (((v i).toNat / P : ℕ) : ZMod p)) * (((v i).toNat : ZMod p))⁻¹}) with hforb
  have hcard2 : forb.card ≤ 2 * low.card := by
    calc forb.card
        ≤ ∑ i ∈ low, ({(-((((v i).toNat / P : ℕ) : ZMod p))) * (((v i).toNat : ZMod p))⁻¹,
            (-1 - (((v i).toNat / P : ℕ) : ZMod p)) * (((v i).toNat : ZMod p))⁻¹} :
            Finset (ZMod p)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ low, 2 := Finset.sum_le_sum (fun i _ =>
          (Finset.card_insert_le _ _).trans (by simp))
      _ = 2 * low.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hex : ∃ c : ZMod p, c ∉ forb := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ forb := fun c _ => hall c
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  obtain ⟨c, hc⟩ := hex
  set a : ℕ := c.val * P + 1 with hadef
  set W : ℕ := P * p with hWdef
  have hW0 : 0 < W := Nat.mul_pos hP0 hp0
  have hqW : p ^ (L + 1) = W := by rw [hWdef, hPdef, pow_succ]
  have h2PW : 2 * P ≤ W := by
    have := Nat.mul_le_mul_left P (show 2 ≤ p by omega)
    calc 2 * P = P * 2 := by ring
      _ ≤ P * p := this
      _ = W := hWdef.symm
  -- the shared finish: a residue block in `[P, W − P]` forces the witness inequality
  have hfin : ∀ n y : ℕ, n * a % W = y → P ≤ y → y + P ≤ W →
      W ≤ (k + 2) * min (n * a % W) (W - n * a % W) := by
    intro n y hy h1 h2
    rw [hy]
    have hm : P ≤ min y (W - y) := le_min h1 (by omega)
    calc W = P * p := hWdef
      _ ≤ P * (k + 2) := Nat.mul_le_mul_left _ hpk
      _ = (k + 2) * P := by ring
      _ ≤ (k + 2) * min y (W - y) := Nat.mul_le_mul_left _ hm
  have hq0 : 0 < p ^ (L + 1) := pow_pos hp0 _
  refine cube_floor_of_witness v hv a (p ^ (L + 1)) hq0 (fun i => ?_)
  rw [hqW]
  rcases hsplit i with hunit | ⟨hdvd, hsdvd⟩
  · -- unit runner
    set n : ℕ := (v i).toNat with hndef
    have hnz : ((n : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      exact hunit ((CharP.cast_eq_zero_iff (ZMod p) p n).mp h0)
    have hiLow : i ∈ low := by
      rw [hlow]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hunit⟩
    set δ : ZMod p := (((n / P : ℕ) : ZMod p)) with hδdef
    set D : ℕ := n * c.val + n / P with hDdef
    have hDcast : ((D : ℕ) : ZMod p) = (n : ZMod p) * c + δ := by
      rw [hDdef, hδdef]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
    -- the chosen digit avoids 0
    have hD0 : ((D : ℕ) : ZMod p) ≠ 0 := by
      rw [hDcast]
      intro h0
      apply hc
      rw [hforb]
      refine Finset.mem_biUnion.mpr ⟨i, hiLow, ?_⟩
      have h1 : (n : ZMod p) * c = -δ := by linear_combination h0
      have h2 : (n : ZMod p) * ((-δ) * ((n : ZMod p))⁻¹) = -δ := by
        field_simp
      have : c = (-δ) * ((n : ZMod p))⁻¹ := mul_left_cancel₀ hnz (h1.trans h2.symm)
      rw [this, hδdef, hndef]
      exact Finset.mem_insert_self _ _
    -- and avoids p−1
    have hDm1 : ((D : ℕ) : ZMod p) ≠ -1 := by
      rw [hDcast]
      intro h0
      apply hc
      rw [hforb]
      refine Finset.mem_biUnion.mpr ⟨i, hiLow, ?_⟩
      have h1 : (n : ZMod p) * c = -1 - δ := by linear_combination h0
      have h2 : (n : ZMod p) * ((-1 - δ) * ((n : ZMod p))⁻¹) = -1 - δ := by
        field_simp
      have : c = (-1 - δ) * ((n : ZMod p))⁻¹ := mul_left_cancel₀ hnz (h1.trans h2.symm)
      rw [this, hδdef, hndef]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hDp : D % p < p := Nat.mod_lt _ hp0
    have hd1 : 1 ≤ D % p := by
      rcases Nat.eq_zero_or_pos (D % p) with h0 | h1
      · exfalso
        apply hD0
        rw [← ZMod.natCast_mod D p, h0, Nat.cast_zero]
      · exact h1
    have hd2 : D % p ≤ p - 2 := by
      by_contra hgt
      push_neg at hgt
      have heq : D % p = p - 1 := by omega
      apply hDm1
      rw [← ZMod.natCast_mod D p, heq]
      have h1p : 1 ≤ p := by omega
      rw [Nat.cast_sub h1p, ZMod.natCast_self, Nat.cast_one, zero_sub]
    -- block decomposition of n·a mod W
    have hna : n * a = P * D + n % P := by
      have hdm : P * (n / P) + n % P = n := Nat.div_add_mod n P
      calc n * a = n * (c.val * P + 1) := by rw [hadef]
        _ = P * (n * c.val) + n := by ring
        _ = P * (n * c.val) + (P * (n / P) + n % P) := by rw [hdm]
        _ = P * (n * c.val + n / P) + n % P := by ring
        _ = P * D + n % P := by rw [hDdef]
    have hy : n * a % W = P * (D % p) + n % P := by
      have hDd : p * (D / p) + D % p = D := Nat.div_add_mod D p
      have hsplit2 : n * a = W * (D / p) + (P * (D % p) + n % P) := by
        calc n * a = P * D + n % P := hna
          _ = P * (p * (D / p) + D % p) + n % P := by rw [hDd]
          _ = (P * p) * (D / p) + (P * (D % p) + n % P) := by ring
          _ = W * (D / p) + (P * (D % p) + n % P) := by rw [hWdef]
      have hrP : n % P < P := Nat.mod_lt _ hP0
      have hAZ : P * (D % p) ≤ P * (p - 2) := Nat.mul_le_mul_left _ hd2
      have hZW : P * (p - 2) + 2 * P = W := by
        have hpp : p - 2 + 2 = p := by omega
        calc P * (p - 2) + 2 * P = P * ((p - 2) + 2) := by ring
          _ = P * p := by rw [hpp]
          _ = W := hWdef.symm
      have hlt : P * (D % p) + n % P < W := by omega
      rw [hsplit2, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hyP : P ≤ P * (D % p) + n % P := by
      have := Nat.mul_le_mul_left P hd1
      omega
    have hyW : (P * (D % p) + n % P) + P ≤ W := by
      have hAZ : P * (D % p) ≤ P * (p - 2) := Nat.mul_le_mul_left _ hd2
      have hZW : P * (p - 2) + 2 * P = W := by
        have hpp : p - 2 + 2 = p := by omega
        calc P * (p - 2) + 2 * P = P * ((p - 2) + 2) := by ring
          _ = P * p := by rw [hpp]
          _ = W := hWdef.symm
      have hrP : n % P < P := Nat.mod_lt _ hP0
      omega
    exact hfin n _ hy hyP hyW
  · -- high runner: (v i).toNat = P · s with p ∤ s
    set n : ℕ := (v i).toNat with hndef
    have hn0 : 0 < n := by
      have := hv i
      rw [hndef]
      omega
    obtain ⟨s, hs⟩ := hdvd
    have hsP : n / P = s := by rw [hs, Nat.mul_div_cancel_left s hP0]
    have hps : ¬ p ∣ s := by rw [hsP] at hsdvd; exact hsdvd
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h1
      · exfalso; rw [h0, mul_zero] at hs; omega
      · exact h1
    have hd1 : 1 ≤ s % p := by
      rcases Nat.eq_zero_or_pos (s % p) with h0 | h1
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hps
      · exact h1
    have hdp : s % p < p := Nat.mod_lt _ hp0
    -- p ∣ P (since L ≥ 1), so the c-term dies mod W
    have hpP : p ∣ P := by rw [hPdef]; exact dvd_pow_self p (by omega : L ≠ 0)
    obtain ⟨E, hE⟩ := hpP
    have hy : n * a % W = P * (s % p) := by
      have hsd : p * (s / p) + s % p = s := Nat.div_add_mod s p
      have hsplit2 : n * a = W * (s * c.val * E + s / p) + P * (s % p) := by
        calc n * a = (P * s) * (c.val * P + 1) := by rw [hs, hadef]
          _ = s * c.val * (P * P) + P * s := by ring
          _ = s * c.val * (P * (p * E)) + P * s := by rw [← hE]
          _ = s * c.val * (P * (p * E)) + P * (p * (s / p) + s % p) := by rw [hsd]
          _ = (P * p) * (s * c.val * E + s / p) + P * (s % p) := by ring
          _ = W * (s * c.val * E + s / p) + P * (s % p) := by rw [hWdef]
      have hAZ : P * (s % p) ≤ P * (p - 1) := Nat.mul_le_mul_left _ (by omega)
      have hZW : P * (p - 1) + P = W := by
        have hpp : p - 1 + 1 = p := by omega
        calc P * (p - 1) + P = P * ((p - 1) + 1) := by ring
          _ = P * p := by rw [hpp]
          _ = W := hWdef.symm
      have hlt : P * (s % p) < W := by omega
      rw [hsplit2, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hyP : P ≤ P * (s % p) := by
      have := Nat.mul_le_mul_left P hd1
      omega
    have hyW : P * (s % p) + P ≤ W := by
      have hAZ : P * (s % p) ≤ P * (p - 1) := Nat.mul_le_mul_left _ (by omega)
      have hZW : P * (p - 1) + P = W := by
        have hpp : p - 1 + 1 = p := by omega
        calc P * (p - 1) + P = P * ((p - 1) + 1) := by ring
          _ = P * p := by rw [hpp]
          _ = W := hWdef.symm
      omega
    exact hfin n _ hy hyP hyW

end LRSpectrumFull
