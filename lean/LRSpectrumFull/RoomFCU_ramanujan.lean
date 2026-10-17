import Mathlib

/-!
# ROOM FCU, exact-forms seat: an explicit lonely time for the family F(m, j)

For `m ≥ 1`, `(m + 1) / 2 < j ≤ m` and `gcd (j, m + 1) = 1`, the family

  `F(m, j) = ([1, m] \ {j}) ∪ {j (m + 1)}`     (m speeds)

has, with `D = m j + m + 1` and `s` any integer with `j ∣ s (m + 1 - j) + 1`, the time
`t = (s D + 1) / (j D)` at which every speed `x` satisfies `‖x t‖ ≥ (m + 1) / D`.
Everything is stated on exact integer residues: `r = x (s D + 1) mod (j D)` and the claim is
`j (m + 1) ≤ r` and `r + j (m + 1) ≤ j D`, i.e. `min (r, jD - r) ≥ j (m + 1)`.

Consequences: `ML(F(m,j)) ≥ (m+1)/(mj+m+1) > 1/(m+1)`; in the project's witness syntax
(`q ≤ (m+1) * min (x p % q) (q - x p % q)`) the pair `p = sD+1`, `q = jD` is a witness.
The matching upper bound `ML = (m+1)/(mj+m+1)` is computed (all 499 cases m ≤ 56), not proved here.
-/

namespace LRSpectrumFull.RoomFCURamanujan

/-- The residue of `x (s D + 1)` modulo `j D`, for `x < D`. -/
lemma mod_eq (j D x s : ℕ) (hj : 0 < j) (hx : x < D) :
    x * (s * D + 1) % (j * D) = (x * s % j) * D + x := by
  have hρ : x * s % j < j := Nat.mod_lt _ hj
  have hdecomp : x * (s * D + 1) = ((x * s % j) * D + x) + (x * s / j) * (j * D) := by
    have h := Nat.div_add_mod (x * s) j
    calc x * (s * D + 1) = (x * s) * D + x := by ring
      _ = (j * (x * s / j) + x * s % j) * D + x := by rw [h]
      _ = ((x * s % j) * D + x) + (x * s / j) * (j * D) := by ring
  rw [hdecomp, Nat.add_mul_mod_self_right]
  apply Nat.mod_eq_of_lt
  have h1 : (x * s % j + 1) * D ≤ j * D := Nat.mul_le_mul_right D hρ
  nlinarith

/-- `j ∣ a + 1` and `a % j` pin `a % j = j - 1`. -/
lemma mod_of_dvd_succ (a j : ℕ) (hj : 0 < j) (h : j ∣ a + 1) : a % j + 1 = j := by
  have hlt : a % j < j := Nat.mod_lt _ hj
  have hd : j ∣ a % j + 1 := by
    have h2 := Nat.div_add_mod a j
    have : a + 1 = j * (a / j) + (a % j + 1) := by omega
    rw [this] at h
    exact (Nat.dvd_add_right (dvd_mul_right j _)).mp h
  have hle : j ≤ a % j + 1 := Nat.le_of_dvd (by omega) hd
  omega

/-- Speeds `x ∈ [1, m]`, `x ≠ j`. -/
theorem famF_small (m j s x : ℕ) (hj : m + 1 < 2 * j) (hjm : j ≤ m)
    (hs : j ∣ s * (m + 1 - j) + 1) (hx1 : 1 ≤ x) (hxm : x ≤ m) (hxj : x ≠ j) :
    j * (m + 1) ≤ x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) ∧
      x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) + j * (m + 1)
        ≤ j * (m * j + m + 1) := by
  have hj0 : 0 < j := by omega
  have hxD : x < m * j + m + 1 := by nlinarith
  rw [mod_eq j (m * j + m + 1) x s hj0 hxD]
  set D := m * j + m + 1 with hD
  set c := m + 1 - j with hc
  have hρlt : x * s % j < j := Nat.mod_lt _ hj0
  -- s is a unit mod j
  have hcop : Nat.Coprime j s := by
    have hg1 : Nat.gcd j s ∣ s * c + 1 := (Nat.gcd_dvd_left j s).trans hs
    have hg2 : Nat.gcd j s ∣ s * c := (Nat.gcd_dvd_right j s).trans (dvd_mul_right s c)
    exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hg2).mp hg1)
  -- ρ ≠ 0
  have hρ0 : x * s % j ≠ 0 := by
    intro h0
    have hdv : j ∣ x * s := Nat.dvd_of_mod_eq_zero h0
    have hjx : j ∣ x := hcop.dvd_of_dvd_mul_right hdv
    obtain ⟨e, rfl⟩ := hjx
    rcases e with _ | _ | e
    · omega
    · simp at hxj
    · nlinarith
  have hρ1 : 1 ≤ x * s % j := Nat.one_le_iff_ne_zero.mpr hρ0
  have hlow : j * (m + 1) ≤ x * s % j * D + x := by
    have : 1 * D ≤ (x * s % j) * D := Nat.mul_le_mul_right D hρ1
    nlinarith
  refine ⟨hlow, ?_⟩
  by_cases htop : x * s % j + 1 = j
  · -- ρ = j - 1: then x ≡ c (mod j), forcing x = c = m + 1 - j
    have hxs : j ∣ x * s + 1 := by
      have h2 := Nat.div_add_mod (x * s) j
      have : x * s + 1 = j * (x * s / j + 1) := by
        have : x * s + 1 = j * (x * s / j) + (x * s % j + 1) := by omega
        rw [this, htop]; ring
      rw [this]; exact dvd_mul_right _ _
    have hcs : j ∣ c * s + 1 := by rw [mul_comm c s]; exact hs
    have hxc : x = c := by
      rcases le_total c x with hle | hle
      · have hd : j ∣ (x - c) * s := by
          rw [Nat.sub_mul]
          have := Nat.dvd_sub hxs hcs
          have e : x * s + 1 - (c * s + 1) = x * s - c * s := by omega
          rwa [e] at this
        have hd' : j ∣ x - c := hcop.dvd_of_dvd_mul_right hd
        have : x - c = 0 := Nat.eq_zero_of_dvd_of_lt hd' (by omega)
        omega
      · have hd : j ∣ (c - x) * s := by
          rw [Nat.sub_mul]
          have := Nat.dvd_sub hcs hxs
          have e : c * s + 1 - (x * s + 1) = c * s - x * s := by omega
          rwa [e] at this
        have hd' : j ∣ c - x := hcop.dvd_of_dvd_mul_right hd
        have : c - x = 0 := Nat.eq_zero_of_dvd_of_lt hd' (by omega)
        omega
    have hρeq : x * s % j = j - 1 := by omega
    rw [hρeq, hxc]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hcj : c = m - j' := by omega
    rw [hcj]
    have hmj : j' ≤ m := by omega
    simp only [Nat.add_sub_cancel]
    zify [hmj]
    rw [hD]; push_cast; nlinarith
  · -- ρ ≤ j - 2
    have hρ2 : x * s % j + 2 ≤ j := by omega
    have h1 : (x * s % j + 2) * D ≤ j * D := Nat.mul_le_mul_right D hρ2
    nlinarith

/-- The inserted speed `j (m + 1)`. -/
theorem famF_big (m j s : ℕ) (hj : m + 1 < 2 * j) (hjm : j ≤ m) :
    j * (m + 1) * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) = j * (m + 1) ∧
      j * (m + 1) + j * (m + 1) ≤ j * (m * j + m + 1) := by
  have hj2 : 2 ≤ j := by omega
  have hm1 : 1 ≤ m := by omega
  have hmj : m + 1 ≤ m * j := by nlinarith
  refine ⟨?_, ?_⟩
  · have e : j * (m + 1) * (s * (m * j + m + 1) + 1)
        = j * (m + 1) + ((m + 1) * s) * (j * (m * j + m + 1)) := by ring
    rw [e, Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt
    have : m + 1 < m * j + m + 1 := by omega
    exact Nat.mul_lt_mul_of_pos_left this (by omega)
  · nlinarith

/-- Existence of `s` under `gcd (j, m + 1) = 1`. -/
theorem exists_s (m j : ℕ) (hj2 : 2 ≤ j) (hjm : j ≤ m + 1) (hcop : Nat.Coprime j (m + 1)) :
    ∃ s, j ∣ s * (m + 1 - j) + 1 := by
  have hc : Nat.Coprime (m + 1 - j) j :=
    (Nat.coprime_sub_self_left hjm).mpr hcop.symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc (by omega)
  refine ⟨(j - 1) * u, ?_⟩
  have h2 := Nat.div_add_mod ((m + 1 - j) * u) j
  rw [hu] at h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨j' * ((m + 1 - (j' + 1)) * u / (j' + 1)) + 1, ?_⟩
  simp only [Nat.add_sub_cancel]
  generalize (m + 1 - (j' + 1)) * u / (j' + 1) = Q at h2
  have e : j' * u * (m + 1 - (j' + 1)) = j' * ((m + 1 - (j' + 1)) * u) := by ring
  rw [e, ← h2]; ring

/-- The family `F(m, j)` as a finset of speeds. -/
def famF (m j : ℕ) : Finset ℕ := ((Finset.Icc 1 m).erase j) ∪ {j * (m + 1)}

/-- Main statement: at `t = (sD+1)/(jD)` every speed of `F(m,j)` is at distance at least
`(m+1)/D` from the integers, stated as `j(m+1) ≤ r ≤ jD - j(m+1)` on the exact residue `r`. -/
theorem famF_lonely (m j : ℕ) (hj : m + 1 < 2 * j) (hjm : j ≤ m)
    (hcop : Nat.Coprime j (m + 1)) :
    ∃ s, ∀ x ∈ famF m j,
      j * (m + 1) ≤ x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) ∧
      x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1)) + j * (m + 1)
        ≤ j * (m * j + m + 1) := by
  obtain ⟨s, hs⟩ := exists_s m j (by omega) (by omega) hcop
  refine ⟨s, fun x hx => ?_⟩
  simp only [famF, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc,
    Finset.mem_singleton] at hx
  rcases hx with ⟨hxj, hx1, hxm⟩ | rfl
  · exact famF_small m j s x hj hjm hs hx1 hxm hxj
  · obtain ⟨h1, h2⟩ := famF_big m j s hj hjm
    rw [h1]; exact ⟨le_refl _, h2⟩

/-- Project witness syntax (target gap `1/(m+1)`; `m = k+1` speeds, so `k + 2 = m + 1`):
`q ≤ (m+1) * min (x p % q) (q - x p % q)` for every speed, with `q = jD > 0`. -/
theorem famF_witness (m j : ℕ) (hj : m + 1 < 2 * j) (hjm : j ≤ m)
    (hcop : Nat.Coprime j (m + 1)) :
    ∃ p q : ℕ, 0 < q ∧ ∀ x ∈ famF m j,
      q ≤ (m + 1) * min (x * p % q) (q - x * p % q) := by
  obtain ⟨s, hs⟩ := famF_lonely m j hj hjm hcop
  refine ⟨s * (m * j + m + 1) + 1, j * (m * j + m + 1), Nat.mul_pos (by omega) (by omega), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hs x hx
  set r := x * (s * (m * j + m + 1) + 1) % (j * (m * j + m + 1))
  have hmin : j * (m + 1) ≤ min r (j * (m * j + m + 1) - r) := le_min h1 (by omega)
  have hkey : j * (m * j + m + 1) ≤ (m + 1) * (j * (m + 1)) := by nlinarith
  calc j * (m * j + m + 1) ≤ (m + 1) * (j * (m + 1)) := hkey
    _ ≤ (m + 1) * min r (j * (m * j + m + 1) - r) := Nat.mul_le_mul_left _ hmin

end LRSpectrumFull.RoomFCURamanujan
