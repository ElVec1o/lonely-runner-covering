import LRSpectrumFull.BarajasSerraSec6_5

/-!
# E6 session 19: Barajas-Serra Section 6.6 (`|A1| = 2`, `|A2| = 2`, `|A4| = 1`), case (a), `m ≥ 2`

`A1 = {d1, d2}` (class `ρ`), `A2 = {d3, d4}` (class `2ρ`), `A4 = {d5}` (class `4ρ`), all level 0.
Conclusion: a multiplier prime to 7 keeping all five off `q ∈ {0, 6}` (`sec66`), real form with a top
speed (`sec66_witness`).

Route (paper 6.6 with the session-16 corrections). `e12 = d1 - d2`, `e34 = d3 - d4` (residues); after
renaming `d3 ↔ d4`, `r(e34) / r(e12) ∈ {1, 2, 4}`.
* Target (15): `q(e12), q(e34) ∈ {0, 6}` by a unit (`twoq`), then Lemma 5 at `(2, 2, 1)` (`z66_15`):
  one of them zero; different levels (Lemma 2 twice: `target6` on the higher, `0` on the lower);
  same level, same `r` (`f = e12 - e34`, `q(f) = 6`, `q(e34) = 0`); same level `< m`, ratio 2 or 4
  (Lemma 9 (ii), `j = 2`, both values, `l9two_key`).
* same level `m`, `r(e12) = 2 r(e34)` (paper (a)): rescale `e12 = 2N/7`, `e34 = N/7`; bad pairs (16);
  Lemma 7 on `(d2, d4)` with `X = {4,5,6}` unless `e(d2,d4) ∈ {5N/7, 6N/7}`; then `e~(d2,d4) ∈ {z, z-1}`
  and Lemma 7 on `(d5, d2)` with `X = {2,4}` (`z = 5`) or `{4,6}` (`z = 6`). These sets have no two
  consecutive elements, so Lemma 7 always applies: the paper's last sub-case (`nu(e25) = m`, the
  argument with `7 d5`) is not needed.
* same level `m`, `r(e34) = 2 r(e12)` (paper (b)): rescale `e12 = N/7`, `e34 = 2N/7`; Lemma 7 on
  `(d2, d4)` with `X = {2,4}` (session-16 correction; the paper's `{2,4,6}` has `l = 5`).
Falsified first: `e6s19/lean19.rs` (`sub`): 6.6 conclusion m = 2, all class-1 2-multisets, class-2
2-multisets, class-4 singletons mod N: 73530625 configurations, 0 failures (negative control
`Lambda_0` only: 9983358 failures); `e6s19/z66.rs`: the finite facts `z66_15`, `zA`, `zA5`, `zA6`,
`zB` 0 failures, bad lists equal to (16) and the session-16 list for (b), controls fire.
-/

namespace LRSpectrumFull.BarajasSerra.Sec6

open LRSpectrumFull.BarajasSerra LRSpectrumFull.BarajasSerra.G

/-- the class data of 6.6. -/
def Cls66 (d1 d2 d3 d4 d5 : ℕ) : Prop :=
  ¬ 7 ∣ d1 ∧ ¬ 7 ∣ d2 ∧ ¬ 7 ∣ d3 ∧ ¬ 7 ∣ d4 ∧ ¬ 7 ∣ d5 ∧ R d2 = R d1 ∧ R d3 = 2 * R d1 ∧
    R d4 = 2 * R d1 ∧ R d5 = 4 * R d1

theorem Cls66.swap34 {d1 d2 d3 d4 d5 : ℕ} (h : Cls66 d1 d2 d3 d4 d5) : Cls66 d1 d2 d4 d3 d5 := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  exact ⟨a, b, d, c, e, f, i, g, j⟩

theorem finish66 (m : ℕ) (hm : 1 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (hc : Cls66 d1 d2 d3 d4 d5) (μ : ℕ)
    (hμ : Nat.Coprime μ 7) (K : ZMod 7) (k1 : ok7 ((qq m (μ * d1) : ZMod 7) + K))
    (k2 : ok7 ((qq m (μ * d2) : ZMod 7) + K)) (k3 : ok7 ((qq m (μ * d3) : ZMod 7) + 2 * K))
    (k4 : ok7 ((qq m (μ * d4) : ZMod 7) + 2 * K)) (k5 : ok7 ((qq m (μ * d5) : ZMod 7) + 4 * K)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩ := hc
  have nz : ∀ x, ¬ 7 ∣ x → x ≠ 0 := fun x hx h => by rw [h] at hx; exact hx (dvd_zero 7)
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; norm_num at hμ
  have hρ : R (μ * d1) ≠ 0 := R_ne_zero (Nat.mul_ne_zero hμ0 (nz _ h1))
  obtain ⟨lam, hcop, hall⟩ := finish_list m hm μ hμ _ hρ
    ([(d1, 1), (d2, 1), (d3, 2), (d4, 2), (d5, 4)])
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨h1, by ring⟩
      · exact ⟨h2, by rw [R_mul_unit hμ (nz _ h2), R_mul_unit hμ (nz _ h1), r2]; ring⟩
      · exact ⟨h3, by rw [R_mul_unit hμ (nz _ h3), R_mul_unit hμ (nz _ h1), r3]; ring⟩
      · exact ⟨h4, by rw [R_mul_unit hμ (nz _ h4), R_mul_unit hμ (nz _ h1), r4]; ring⟩
      · exact ⟨h5, by rw [R_mul_unit hμ (nz _ h5), R_mul_unit hμ (nz _ h1), r5]; ring⟩) K
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · simpa using k1
      · simpa using k2
      · exact k3
      · exact k4
      · exact k5)
  refine ⟨lam, hcop, ?_⟩
  intro x hx
  rcases mem_list5 hx with rfl | rfl | rfl | rfl | rfl
  · exact hall (x, 1) (by simp)
  · exact hall (x, 1) (by simp)
  · exact hall (x, 2) (by simp)
  · exact hall (x, 2) (by simp)
  · exact hall (x, 4) (by simp)

/-! ## finite facts (checked first in `e6s19/z66.rs`) -/

theorem z66_15 : ∀ a o1 b o2 c : ZMod 7, (o1 = 6 ∨ o1 = 0 ∨ o1 = 1) → (o2 = 6 ∨ o2 = 0 ∨ o2 = 1) →
    ∃ K, ok7 (a + K) ∧ ok7 (a + o1 + K) ∧ ok7 (b + 2 * K) ∧ ok7 (b + o2 + 2 * K) ∧ ok7 (c + 4 * K) := by
  decide +kernel

theorem zA66 : ∀ q2 q4 q5 : ZMod 7, 2 * q2 - q4 ∉ ({4, 5, 6} : Finset (ZMod 7)) →
    ∃ K, ok7 (q2 + K) ∧ ok7 (q2 + 2 + K) ∧ ok7 (q4 + 2 * K) ∧ ok7 (q4 + 1 + 2 * K) ∧ ok7 (q5 + 4 * K) := by
  decide +kernel

theorem zA5_66 : ∀ q2 q4 q5 : ZMod 7, (2 * q2 - q4 = 5 ∨ 2 * q2 - q4 = 4) →
    2 * q5 - q2 ∉ ({2, 4} : Finset (ZMod 7)) →
    ∃ K, ok7 (q2 + K) ∧ ok7 (q2 + 2 + K) ∧ ok7 (q4 + 2 * K) ∧ ok7 (q4 + 1 + 2 * K) ∧ ok7 (q5 + 4 * K) := by
  decide +kernel

theorem zA6_66 : ∀ q2 q4 q5 : ZMod 7, (2 * q2 - q4 = 6 ∨ 2 * q2 - q4 = 5) →
    2 * q5 - q2 ∉ ({4, 6} : Finset (ZMod 7)) →
    ∃ K, ok7 (q2 + K) ∧ ok7 (q2 + 2 + K) ∧ ok7 (q4 + 2 * K) ∧ ok7 (q4 + 1 + 2 * K) ∧ ok7 (q5 + 4 * K) := by
  decide +kernel

theorem zB66 : ∀ q2 q4 q5 : ZMod 7, 2 * q2 - q4 ∉ ({2, 4} : Finset (ZMod 7)) →
    ∃ K, ok7 (q2 + K) ∧ ok7 (q2 + 1 + K) ∧ ok7 (q4 + 2 * K) ∧ ok7 (q4 + 2 + 2 * K) ∧ ok7 (q5 + 4 * K) := by
  decide +kernel

theorem ell456 : Z7.ell {4, 5, 6} ≤ 4 := by decide
theorem ell24 : Z7.ell {2, 4} ≤ 4 := by decide
theorem z7_456 : ∀ z : ZMod 7, z ∈ ({4, 5, 6} : Finset (ZMod 7)) → z - 1 ∈ ({4, 5, 6} : Finset (ZMod 7)) →
    z = 5 ∨ z = 6 := by decide
theorem z7_nc24 : ∀ z : ZMod 7, ¬ (z ∈ ({2, 4} : Finset (ZMod 7)) ∧ z - 1 ∈ ({2, 4} : Finset (ZMod 7))) := by
  decide
theorem z7_nc46 : ∀ z : ZMod 7, ¬ (z ∈ ({4, 6} : Finset (ZMod 7)) ∧ z - 1 ∈ ({4, 6} : Finset (ZMod 7))) := by
  decide
theorem z7_ratio : ∀ a b : ZMod 7, a ≠ 0 → b ≠ 0 →
    (b = a ∨ b = 2 * a ∨ a = 2 * b) ∨ (-b = a ∨ -b = 2 * a ∨ a = 2 * -b) := by decide
theorem z7_eight' (x : ZMod 7) : 2 * (4 * x) = x := z7_eight x

/-! ## Lemma 2 in the forms used here -/

/-- any nonzero residue can be sent to `q = 6` by a unit. -/
theorem target6 (m e : ℕ) (he0 : e ≠ 0) (hlt : e < 7 ^ (m + 1)) :
    ∃ lam, Nat.Coprime lam 7 ∧ qq m (lam * e) = 6 := by
  have hle := nu_le_m he0 hlt
  rcases lt_or_eq_of_le hle with hl | heq
  · obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 e) (m := m) (x := e) (t := 6)
      (by norm_num) hle rfl he0 (by norm_num)
    have hmem : 1 + 7 ^ (m - nu 7 e) * k ∈ Lam (nu 7 e) m 7 :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact ⟨_, (coprime_of_modEq_one (by norm_num) (Lam_modEq_seven hl hmem)).1, hkq⟩
  · obtain ⟨w, hw0, hw7, hw⟩ := top_form he0 hlt heq
    obtain ⟨l, hlmem, hlw⟩ := exists_top_inv hw0 hw7
    have hcop := LamTop_coprime 7 (by norm_num) l hlmem
    refine ⟨6 * l, Nat.Coprime.mul_left (by norm_num) hcop, ?_⟩
    have h1 : 6 * l * e ≡ 0 + 7 ^ m * 6 [MOD 7 ^ (m + 1)] := by
      rw [mul_assoc, zero_add, mul_comm (7 ^ m) 6]; exact (top_mul hw hlw).mul_left 6
    have h2 := qq_of_top1 h1
    have h3 : qq m 0 = 0 := by simp [qq, qarc]
    rw [h3] at h2
    exact nat_cast_zmod7_eq_of_lt (qq_lt m _) (by norm_num) (by rw [h2]; simp)

/-- below the top, `q = 0` by a factor of `Lam j`. -/
theorem target0 (m x : ℕ) (hx0 : x ≠ 0) (hlt : nu 7 x < m) :
    ∃ lam ∈ Lam (nu 7 x) m 7, qq m (lam * x) = 0 := by
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := nu 7 x) (m := m) (x := x) (t := 0)
    (by norm_num) hlt.le rfl hx0 (by norm_num)
  exact ⟨_, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, hkq⟩

theorem qq_zero' (m lam : ℕ) : qq m (lam * 0) = 0 := by simp [qq, qarc]

theorem nz_of_cop {l : ℕ} (h : Nat.Coprime l 7) : l ≠ 0 := fun h0 => by rw [h0] at h; norm_num at h

/-- two residues, the second strictly higher (or `0`): `q(lam e_hi) = 6`, `q(lam e_lo) = 0`. -/
theorem two_levels (m : ℕ) (x y a b : ℕ) (hlo0 : E m x y ≠ 0)
    (hhi : E m a b = 0 ∨ (E m a b ≠ 0 ∧ nu 7 (E m x y) < nu 7 (E m a b))) :
    ∃ lam, Nat.Coprime lam 7 ∧ (qq m (lam * E m x y) = 0 ∨ qq m (lam * E m x y) = 6) ∧
      (qq m (lam * E m a b) = 0 ∨ qq m (lam * E m a b) = 6) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases hhi with h0 | ⟨h0, hlt⟩
  · obtain ⟨lam, hc, hq⟩ := target6 m _ hlo0 (E_lt m x y)
    exact ⟨lam, hc, Or.inr hq, Or.inl (by rw [h0]; exact qq_zero' m lam)⟩
  · obtain ⟨l1, hc1, hq1⟩ := target6 m _ h0 (E_lt m a b)
    have hle := nu_le_m h0 (E_lt m a b)
    have hn : nu 7 (l1 * E m x y) = nu 7 (E m x y) := nu_mul_coprime 7 l1 _ hc1 (nz_of_cop hc1) hlo0
    obtain ⟨l2, hl2, hq2⟩ := target0 m (l1 * E m x y) (Nat.mul_ne_zero (nz_of_cop hc1) hlo0) (by omega)
    rw [hn] at hl2
    have hl27 := Lam_modEq_seven (by omega) hl2
    have hc2 := (coprime_of_modEq_one (by norm_num) hl27).1
    refine ⟨l2 * l1, Nat.Coprime.mul_left hc2 hc1, Or.inl (by rw [mul_assoc]; exact hq2), Or.inr ?_⟩
    have hfix : qq m (l2 * (l1 * E m a b)) = qq m (l1 * E m a b) := by
      unfold qq
      apply qarc_mul_fix (v := nu 7 (E m x y) + 1) (by omega)
      · rw [show m + 1 - (nu 7 (E m x y) + 1) = m - nu 7 (E m x y) by omega]; exact Lam_modEq_one hl2
      · exact Dvd.dvd.mul_left ((pow_dvd_pow 7 (by omega)).trans (pow_nu_dvd 7 _)) _
    rw [mul_assoc, hfix, hq1]

/-- **Lemma 9 (ii), `j = 2`, both values**: `q(lam x), q(lam y) ∈ {0, 6}`. -/
theorem l9two_key (m h x y : ℕ) (hhm : h < m) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : nu 7 x = h)
    (hy : nu 7 y = h) (hr : rp 7 y = 2 * rp 7 x % 7) :
    ∃ lam, Nat.Coprime lam 7 ∧ (qq m (lam * x) = 0 ∨ qq m (lam * x) = 6) ∧
      (qq m (lam * y) = 0 ∨ qq m (lam * y) = 6) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN := N_pos m
  set e := dsub (7 ^ (m + 1)) (2 * x) y with he
  have hdvd : 7 ^ (h + 1) ∣ e := dvd_dsub_two hhm.le hx hy hr
  obtain ⟨lam1, _, hc1, hne1, _, hstep⟩ :=
    step_top_or_zero m (h + 1) e (by omega) (dsub_lt _ _ _ hN) hdvd
  have hnx1 : nu 7 (lam1 * x) = h := (nu_mul_coprime 7 lam1 x hc1 hne1 hx0).trans hx
  have hny1 : nu 7 (lam1 * y) = h := (nu_mul_coprime 7 lam1 y hc1 hne1 hy0).trans hy
  have hx10 : lam1 * x ≠ 0 := Nat.mul_ne_zero hne1 hx0
  have hr1 : rp 7 (lam1 * y) = 2 * rp 7 (lam1 * x) % 7 := by
    rw [rp_mul_unit (not_dvd_of_coprime hc1) hy0, rp_mul_unit (not_dvd_of_coprime hc1) hx0, hr]
    have a := (Nat.mod_modEq (2 * rp 7 x) 7).mul_left lam1
    unfold Nat.ModEq at a
    rw [show lam1 * (2 * rp 7 x) = 2 * (lam1 * rp 7 x) by ring] at a
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = if (2 * qq m (lam1 * x) + 14 - qq m (lam1 * y)) % 7 = 6 then 6 else 0 :=
    ⟨_, rfl⟩
  have htlt : t < 7 := by rw [ht]; split_ifs <;> norm_num
  obtain ⟨k, hk, hkq⟩ := exists_lam_target (p := 7) (h := h) (m := m) (x := lam1 * x) (t := t)
    (by norm_num) hhm.le hnx1 hx10 htlt
  have hmem : 1 + 7 ^ (m - h) * k ∈ Lam h m 7 :=
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  set lam2 := 1 + 7 ^ (m - h) * k with hlam2
  obtain ⟨hc2, _⟩ := coprime_of_modEq_one (by norm_num) (Lam_modEq_seven hhm hmem)
  have hqx : qq m (lam2 * (lam1 * x)) = (qq m (lam1 * x) + k * rp 7 (lam1 * x)) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk _ hnx1
  have hqy : qq m (lam2 * (lam1 * y)) = (qq m (lam1 * y) + k * rp 7 (lam1 * y)) % 7 :=
    qarc_mul_lam_eq 7 h m (by norm_num) hhm.le k hk _ hny1
  have hK : (k * rp 7 (lam1 * y)) % 7 = (2 * ((k * rp 7 (lam1 * x)) % 7)) % 7 := by
    have := ((show rp 7 (lam1 * y) ≡ 2 * rp 7 (lam1 * x) [MOD 7] by
      rw [hr1]; exact Nat.mod_modEq _ _).mul_left k)
    unfold Nat.ModEq at this
    rw [show k * (2 * rp 7 (lam1 * x)) = 2 * (k * rp 7 (lam1 * x)) by ring] at this; omega
  have hxt : qq m (lam2 * (lam1 * x)) = t := hkq
  have h2x : 2 * (lam2 * (lam1 * x)) ≡ lam2 * (lam1 * y) + lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast; push_cast; rw [he, dsub_cast _ _ _ hN]; push_cast; ring
  obtain ⟨cd, hcd, hdouble⟩ := qq_double_nat m (lam2 * (lam1 * x))
  set Zd := dsub (7 ^ (m + 1)) (lam2 * (lam1 * y)) (lam2 * (lam1 * x)) with hZd
  have hyz : lam2 * (lam1 * y) ≡ lam2 * (lam1 * x) + Zd [MOD 7 ^ (m + 1)] :=
    modEq_add_dsub _ _ _ hN
  have hxz : lam2 * (lam1 * x) ≡ Zd + lam2 * (lam1 * e) [MOD 7 ^ (m + 1)] := by
    apply modEq_of_cast
    have a1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2x
    have a2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hyz
    push_cast at a1 a2 ⊢
    linear_combination a1 + a2
  obtain ⟨cz, hcz, hqz⟩ := qq_add_nat hyz
  have hmu : lam2 ≡ 1 [MOD 7 ^ (m + 1 - (h + 1))] := by
    rw [show m + 1 - (h + 1) = m - h by omega]; exact Lam_modEq_one hmem
  have hX := qq_lt m (lam1 * x); have hY := qq_lt m (lam1 * y)
  have hZ := qq_lt m Zd
  have hqx' : qq m (lam2 * (lam1 * x)) = (qq m (lam1 * x) + (k * rp 7 (lam1 * x)) % 7) % 7 := by
    rw [hqx, Nat.add_mod_mod]
  have hqy' : qq m (lam2 * (lam1 * y)) = (qq m (lam1 * y) + 2 * ((k * rp 7 (lam1 * x)) % 7)) % 7 := by
    rw [hqy, ← Nat.add_mod_mod, hK, Nat.add_mod_mod]
  have hKx : (k * rp 7 (lam1 * x)) % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have key : (qq m (lam2 * (lam1 * x)) = 0 ∨ qq m (lam2 * (lam1 * x)) = 6) ∧
      (qq m (lam2 * (lam1 * y)) = 0 ∨ qq m (lam2 * (lam1 * y)) = 6) ∧ (qq m Zd = 0 ∨ qq m Zd = 6) := by
    rcases hstep lam2 hmu with hz0 | htop
    · obtain ⟨c, hc, hqa⟩ := qq_add_nat h2x
      obtain ⟨c4, hc4, hqb⟩ := qq_add_nat hxz
      rw [hz0] at hqa hqb
      exact arith9_key _ _ _ _ _ _ _ cd c c4 cz t hX hY hKx hZ hcd hc hc4 hcz hqx' hqy' hdouble ht
        hxt hqz (Or.inl ⟨hqa, hqb⟩)
    · have hqa := qq_top_nat (h2x.trans (Nat.ModEq.add_left _ htop))
      have hqb := qq_top_nat (hxz.trans (Nat.ModEq.add_left _ htop))
      exact arith9_key _ _ _ _ _ _ _ cd 0 0 cz t hX hY hKx hZ hcd (by norm_num) (by norm_num) hcz
        hqx' hqy' hdouble ht hxt hqz (Or.inr ⟨hqa, hqb⟩)
  obtain ⟨kX, kY, -⟩ := key
  exact ⟨lam2 * lam1, Nat.Coprime.mul_left hc2 hc1, by rw [mul_assoc]; exact kX, by rw [mul_assoc]; exact kY⟩

/-! ## (15) -/

theorem finish15 (m : ℕ) (hm : 1 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (hc : Cls66 d1 d2 d3 d4 d5) (lam : ℕ)
    (hl : Nat.Coprime lam 7) (h12 : qq m (lam * E m d1 d2) = 0 ∨ qq m (lam * E m d1 d2) = 6)
    (h34 : qq m (lam * E m d3 d4) = 0 ∨ qq m (lam * E m d3 d4) = 6) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨c1, hc1, p1⟩ := pair_off m lam d1 d2
  obtain ⟨c2, hc2, p2⟩ := pair_off m lam d3 d4
  obtain ⟨K, k2, k1, k4, k3, k5⟩ := z66_15 (qq m (lam * d2)) _ (qq m (lam * d4)) _ (qq m (lam * d5))
    (oset_w3 _ _ hc1 h12) (oset_w3 _ _ hc2 h34)
  apply finish66 m hm d1 d2 d3 d4 d5 hc lam hl K _ k2 _ k4 k5
  · exact ok7_congr k1 (by rw [p1]; ring)
  · exact ok7_congr k3 (by rw [p2]; ring)

/-- all cases with target (15). -/
theorem twoq (m : ℕ) (x y a b : ℕ)
    (h : E m x y = 0 ∨ E m a b = 0 ∨ nu 7 (E m x y) ≠ nu 7 (E m a b) ∨
      (R (E m a b) = R (E m x y)) ∨
      (nu 7 (E m x y) < m ∧ (R (E m a b) = 2 * R (E m x y) ∨ R (E m x y) = 2 * R (E m a b)))) :
    ∃ lam, Nat.Coprime lam 7 ∧ (qq m (lam * E m x y) = 0 ∨ qq m (lam * E m x y) = 6) ∧
      (qq m (lam * E m a b) = 0 ∨ qq m (lam * E m a b) = 6) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hx0 : E m x y = 0
  · by_cases ha0 : E m a b = 0
    · exact ⟨1, by norm_num, Or.inl (by rw [hx0]; exact qq_zero' m 1), Or.inl (by rw [ha0]; exact qq_zero' m 1)⟩
    · obtain ⟨lam, hc, hq⟩ := target6 m _ ha0 (E_lt m a b)
      exact ⟨lam, hc, Or.inl (by rw [hx0]; exact qq_zero' m lam), Or.inr hq⟩
  by_cases ha0 : E m a b = 0
  · exact two_levels m x y a b hx0 (Or.inl ha0)
  by_cases hne : nu 7 (E m x y) ≠ nu 7 (E m a b)
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact two_levels m x y a b hx0 (Or.inr ⟨ha0, hlt⟩)
    · obtain ⟨lam, hc, p, q⟩ := two_levels m a b x y ha0 (Or.inr ⟨hx0, hgt⟩)
      exact ⟨lam, hc, q, p⟩
  push Not at hne
  set j := nu 7 (E m x y) with hj
  rcases h with h | h | h | hR | ⟨hjm, h2 | h4⟩
  · exact absurd h hx0
  · exact absurd h ha0
  · exact absurd hne h
  · -- same level, same residue: f = e12 - e34
    have hle := nu_le_m hx0 (E_lt m x y)
    set f := E m (E m x y) (E m a b) with hf
    have hmod : E m x y ≡ E m a b + f [MOD 7 ^ (m + 1)] := E_modEq m _ _
    by_cases hf0 : f = 0
    · obtain ⟨lam, hc, hq⟩ := target6 m _ ha0 (E_lt m a b)
      have heq := qq_eq_of_E0 hf0 lam
      exact ⟨lam, hc, Or.inr (by rw [heq, hq]), Or.inr hq⟩
    have hdvd : 7 ^ (j + 1) ∣ f := by
      apply dvd_dsub_one hle rfl hne.symm
      apply nat_cast_zmod7_eq_of_lt (rp_lt _) (rp_lt _); exact hR.symm
    have hfnu : j + 1 ≤ nu 7 f := by
      have := (padicValNat_dvd_iff_le (p := 7) hf0).mp hdvd; unfold nu; omega
    have hfle := nu_le_m hf0 (E_lt m _ _)
    obtain ⟨l1, hc1, hq1⟩ := target6 m f hf0 (E_lt m _ _)
    have hn : nu 7 (l1 * E m a b) = j := (nu_mul_coprime 7 l1 _ hc1 (nz_of_cop hc1) ha0).trans hne.symm
    obtain ⟨l2, hl2, hq2⟩ := target0 m (l1 * E m a b) (Nat.mul_ne_zero (nz_of_cop hc1) ha0) (by omega)
    rw [hn] at hl2
    have hl27 := Lam_modEq_seven (by omega) hl2
    have hc2 := (coprime_of_modEq_one (by norm_num) hl27).1
    have hfix : qq m (l2 * (l1 * f)) = qq m (l1 * f) := by
      unfold qq
      apply qarc_mul_fix (v := j + 1) (by omega)
      · rw [show m + 1 - (j + 1) = m - j by omega]; exact Lam_modEq_one hl2
      · exact Dvd.dvd.mul_left hdvd _
    refine ⟨l2 * l1, Nat.Coprime.mul_left hc2 hc1, ?_, Or.inl (by rw [mul_assoc]; exact hq2)⟩
    have hm2 : l2 * l1 * E m x y ≡ l2 * (l1 * E m a b) + l2 * (l1 * f) [MOD 7 ^ (m + 1)] := by
      have := hmod.mul_left (l2 * l1); rw [mul_add] at this
      simpa only [mul_assoc] using this
    obtain ⟨c, hc, hq⟩ := qq_add_nat hm2
    rw [hq2, hfix, hq1] at hq
    omega
  · exact l9two_key m j (E m x y) (E m a b) hjm hx0 ha0 rfl hne.symm (rp_of_R h2)
  · obtain ⟨lam, hc, p, q⟩ := l9two_key m j (E m a b) (E m x y) hjm ha0 hx0 hne.symm rfl (rp_of_R h4)
    exact ⟨lam, hc, q, p⟩

/-! ## top level, ratio 2 or 4 -/

/-- `2P - Q ≡ zN/7` and a multiplier `≡ 1 mod 7`: `e~ = 2 q(P) - q(Q) ∈ {z, z - 1}`. -/
theorem et_of_top (m P Q z lam : ℕ) (hr : rp 7 Q = 2 * rp 7 P % 7) (hz : ediff m P Q = 7 ^ m * z)
    (hl : lam ≡ 1 [MOD 7]) :
    2 * (qq m (lam * P) : ZMod 7) - qq m (lam * Q) = z ∨
      2 * (qq m (lam * P) : ZMod 7) - qq m (lam * Q) = z - 1 := by
  have hb : 2 * P ≡ Q + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
    have := modEq_add_dsub (7 ^ (m + 1)) (2 * P) Q (N_pos m)
    rwa [← (ediff_branch1 m P Q hr).1, hz] at this
  have h2 : 2 * (lam * P) ≡ lam * Q + 7 ^ m * z [MOD 7 ^ (m + 1)] := by
    rw [show 2 * (lam * P) = lam * (2 * P) by ring]; exact top_keep hl hb
  have A := qq_of_top1 h2
  obtain ⟨c, hc, hd⟩ := qq_double_nat m (lam * P)
  have B : (qq m (2 * (lam * P)) : ZMod 7) = 2 * (qq m (lam * P) : ZMod 7) + c := by
    rw [hd, ZMod.natCast_mod]; push_cast; ring
  interval_cases c
  · left; linear_combination B.symm.trans A
  · right; linear_combination B.symm.trans A

/-- common rescale: `e12 ≡ n1 N/7`, `e34 ≡ n3 N/7` after `μ`. -/
theorem rescale66 (m : ℕ) (d1 d2 d3 d4 : ℕ) (h12 : E m d1 d2 ≠ 0 ∧ nu 7 (E m d1 d2) = m)
    (h34 : E m d3 d4 ≠ 0 ∧ nu 7 (E m d3 d4) = m) (w : ZMod 7) (hw0 : w ≠ 0) (a1 a3 : ℕ) (ha1 : a1 < 7)
    (ha3 : a3 < 7) (hr1 : R (E m d1 d2) = (a1 : ZMod 7) * w) (hr3 : R (E m d3 d4) = (a3 : ZMod 7) * w) :
    ∃ μ, Nat.Coprime μ 7 ∧ μ * d1 ≡ μ * d2 + 7 ^ m * a1 [MOD 7 ^ (m + 1)] ∧
      μ * d3 ≡ μ * d4 + 7 ^ m * a3 [MOD 7 ^ (m + 1)] := by
  obtain ⟨n1, -, hm1, hR1⟩ := off_of_top m d1 d2 h12.1 h12.2
  obtain ⟨n3, -, hm3, hR3⟩ := off_of_top m d3 d4 h34.1 h34.2
  obtain ⟨u, hu⟩ := z7_solve w 1 hw0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact absurd hu (by decide)
  have hμu : ((u.val : ℕ) : ZMod 7) = u := ZMod.natCast_zmod_val u
  refine ⟨u.val, coprime_of_zmod_ne_zero hu0, scale_top hm1 ha1 ?_, scale_top hm3 ha3 ?_⟩
  · push_cast; rw [hμu, hR1, hr1]; linear_combination (a1 : ZMod 7) * hu
  · push_cast; rw [hμu, hR3, hr3]; linear_combination (a3 : ZMod 7) * hu

/-- paper (a): `r(e12) = 2 r(e34)`, both at the top. -/
theorem top_a66 (m : ℕ) (hm : 2 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (hc : Cls66 d1 d2 d3 d4 d5)
    (h12 : E m d1 d2 ≠ 0 ∧ nu 7 (E m d1 d2) = m) (h34 : E m d3 d4 ≠ 0 ∧ nu 7 (E m d3 d4) = m)
    (hR : R (E m d1 d2) = 2 * R (E m d3 d4)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨μ, hμ, hm1, hm3⟩ := rescale66 m d1 d2 d3 d4 h12 h34 _ (R_ne_zero h34.1) 2 1 (by norm_num)
    (by norm_num) (by rw [hR]; push_cast; ring) (by push_cast; ring)
  obtain ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩ := hc
  have nz : ∀ x, ¬ 7 ∣ x → x ≠ 0 := fun x hx h => by rw [h] at hx; exact hx (dvd_zero 7)
  have hμ0 := nz_of_cop hμ
  have hr24 : rp 7 (μ * d4) = 2 * rp 7 (μ * d2) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ (nz _ h4), R_mul_unit hμ (nz _ h2), r4, r2]; ring
  have hr52 : rp 7 (μ * d2) = 2 * rp 7 (μ * d5) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ (nz _ h5), R_mul_unit hμ (nz _ h2), r5, r2]
    linear_combination (μ : ZMod 7) * (z7_eight (R d1)).symm
  have fin : ∀ lam, lam ≡ 1 [MOD 7] → ∀ K : ZMod 7,
      ok7 ((qq m (lam * (μ * d2)) : ZMod 7) + K) → ok7 ((qq m (lam * (μ * d2)) : ZMod 7) + 2 + K) →
      ok7 ((qq m (lam * (μ * d4)) : ZMod 7) + 2 * K) → ok7 ((qq m (lam * (μ * d4)) : ZMod 7) + 1 + 2 * K) →
      ok7 ((qq m (lam * (μ * d5)) : ZMod 7) + 4 * K) →
      ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
    intro lam hl K k2 k1 k4 k3 k5
    have hlc := (coprime_of_modEq_one (by norm_num) hl).1
    have e1 := qq_top_eq hm1 lam hl
    have e3 := qq_top_eq hm3 lam hl
    have r : ∀ x, lam * (μ * x) = lam * μ * x := fun x => by ring
    rw [r] at e1 e3 k1 k2 k3 k4 k5
    rw [r] at e1 e3
    apply finish66 m (by omega) d1 d2 d3 d4 d5 ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩ (lam * μ)
      (Nat.Coprime.mul_left hlc hμ) K (ok7_congr k1 (by rw [e1]; push_cast; ring)) k2
      (ok7_congr k3 (by rw [e3]; push_cast; ring)) k4 k5
  by_cases hz56 : ediff m (μ * d2) (μ * d4) = 7 ^ m * 5 ∨ ediff m (μ * d2) (μ * d4) = 7 ^ m * 6
  · -- steer `e~(d2, d5)` (as `e~(d5, d2)` of eq. (13)) away from `{2,4}` or `{4,6}`
    have steer5 : ∀ X : Finset (ZMod 7), Z7.ell X ≤ 4 → (∀ z : ZMod 7, ¬ (z ∈ X ∧ z - 1 ∈ X)) →
        ∃ lam, lam ≡ 1 [MOD 7] ∧ 2 * (qq m (lam * (μ * d5)) : ZMod 7) - qq m (lam * (μ * d2)) ∉ X := by
      intro X hX hnc
      obtain ⟨lam, hl, hX'⟩ := steer m hm (μ * d5) (μ * d2) (not_dvd_mul hμ h5) (not_dvd_mul hμ h2)
        hr52 X hX (fun z _ _ => hnc _)
      rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 (nz _ h5)) (Nat.mul_ne_zero hμ0 (nz _ h2)) hr52] at hX'
      exact ⟨lam, hl, hX'⟩
    rcases hz56 with h5z | h6z
    · obtain ⟨lam, hl, hX⟩ := steer5 {2, 4} ell24 z7_nc24
      have ha := et_of_top m (μ * d2) (μ * d4) 5 lam hr24 h5z hl
      obtain ⟨K, k2, k1, k4, k3, k5⟩ := zA5_66 (qq m (lam * (μ * d2))) (qq m (lam * (μ * d4)))
        (qq m (lam * (μ * d5))) (by rcases ha with h | h <;> [left; right] <;> rw [h] <;> decide) hX
      exact fin lam hl K k2 k1 k4 k3 k5
    · have ell46 : Z7.ell {4, 6} ≤ 4 := by decide
      obtain ⟨lam, hl, hX⟩ := steer5 {4, 6} ell46 z7_nc46
      have ha := et_of_top m (μ * d2) (μ * d4) 6 lam hr24 h6z hl
      obtain ⟨K, k2, k1, k4, k3, k5⟩ := zA6_66 (qq m (lam * (μ * d2))) (qq m (lam * (μ * d4)))
        (qq m (lam * (μ * d5))) (by rcases ha with h | h <;> [left; right] <;> rw [h] <;> decide) hX
      exact fin lam hl K k2 k1 k4 k3 k5
  · have hz : ∀ z, z < 7 → ediff m (μ * d2) (μ * d4) = 7 ^ m * z →
        ¬ ((z : ZMod 7) ∈ ({4, 5, 6} : Finset (ZMod 7)) ∧ (z : ZMod 7) - 1 ∈ ({4, 5, 6} : Finset (ZMod 7))) := by
      intro z hz7 hze hmem
      rcases z7_456 _ hmem.1 hmem.2 with h | h
      · have : z = 5 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h]; rfl)
        exact hz56 (Or.inl (by rw [hze, this]))
      · have : z = 6 := nat_cast_zmod7_eq_of_lt hz7 (by norm_num) (by rw [h]; rfl)
        exact hz56 (Or.inr (by rw [hze, this]))
    obtain ⟨lam, hl, hX⟩ := steer m hm (μ * d2) (μ * d4) (not_dvd_mul hμ h2) (not_dvd_mul hμ h4) hr24
      {4, 5, 6} ell456 hz
    rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 (nz _ h2)) (Nat.mul_ne_zero hμ0 (nz _ h4)) hr24] at hX
    obtain ⟨K, k2, k1, k4, k3, k5⟩ := zA66 (qq m (lam * (μ * d2))) (qq m (lam * (μ * d4)))
      (qq m (lam * (μ * d5))) hX
    exact fin lam hl K k2 k1 k4 k3 k5

/-- paper (b): `r(e34) = 2 r(e12)`, both at the top. -/
theorem top_b66 (m : ℕ) (hm : 2 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (hc : Cls66 d1 d2 d3 d4 d5)
    (h12 : E m d1 d2 ≠ 0 ∧ nu 7 (E m d1 d2) = m) (h34 : E m d3 d4 ≠ 0 ∧ nu 7 (E m d3 d4) = m)
    (hR : R (E m d3 d4) = 2 * R (E m d1 d2)) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  obtain ⟨μ, hμ, hm1, hm3⟩ := rescale66 m d1 d2 d3 d4 h12 h34 _ (R_ne_zero h12.1) 1 2 (by norm_num)
    (by norm_num) (by push_cast; ring) (by rw [hR]; push_cast; ring)
  obtain ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩ := hc
  have nz : ∀ x, ¬ 7 ∣ x → x ≠ 0 := fun x hx h => by rw [h] at hx; exact hx (dvd_zero 7)
  have hμ0 := nz_of_cop hμ
  have hr24 : rp 7 (μ * d4) = 2 * rp 7 (μ * d2) % 7 := by
    apply rp_of_R; rw [R_mul_unit hμ (nz _ h4), R_mul_unit hμ (nz _ h2), r4, r2]; ring
  obtain ⟨lam, hl, hX⟩ := steer m hm (μ * d2) (μ * d4) (not_dvd_mul hμ h2) (not_dvd_mul hμ h4) hr24
    {2, 4} ell24 (fun z _ _ => z7_nc24 _)
  rw [etilde_b1 m lam _ _ hl (Nat.mul_ne_zero hμ0 (nz _ h2)) (Nat.mul_ne_zero hμ0 (nz _ h4)) hr24] at hX
  obtain ⟨K, k2, k1, k4, k3, k5⟩ := zB66 (qq m (lam * (μ * d2))) (qq m (lam * (μ * d4)))
    (qq m (lam * (μ * d5))) hX
  have hlc := (coprime_of_modEq_one (by norm_num) hl).1
  have e1 := qq_top_eq hm1 lam hl
  have e3 := qq_top_eq hm3 lam hl
  have r : ∀ x, lam * (μ * x) = lam * μ * x := fun x => by ring
  rw [r] at e1 e3 k1 k2 k3 k4 k5
  rw [r] at e1 e3
  apply finish66 m (by omega) d1 d2 d3 d4 d5 ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩ (lam * μ)
    (Nat.Coprime.mul_left hlc hμ) K (ok7_congr k1 (by rw [e1]; push_cast; ring)) k2
    (ok7_congr k3 (by rw [e3]; push_cast; ring)) k4 k5

/-! ## assembling 6.6 -/

/-- 6.6 with the orientation `r(e34) / r(e12) ∈ {1, 2, 4}` when both are nonzero at one level. -/
theorem core66 (m : ℕ) (hm : 2 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (hc : Cls66 d1 d2 d3 d4 d5)
    (hor : E m d1 d2 ≠ 0 → E m d3 d4 ≠ 0 → nu 7 (E m d1 d2) = nu 7 (E m d3 d4) →
      (R (E m d3 d4) = R (E m d1 d2) ∨ R (E m d3 d4) = 2 * R (E m d1 d2) ∨
        R (E m d1 d2) = 2 * R (E m d3 d4))) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  by_cases hsame : E m d1 d2 ≠ 0 ∧ E m d3 d4 ≠ 0 ∧ nu 7 (E m d1 d2) = nu 7 (E m d3 d4)
  · obtain ⟨h0, h0', hj⟩ := hsame
    have hle := nu_le_m h0 (E_lt m _ _)
    rcases hor h0 h0' hj with h1 | h2 | h4
    · obtain ⟨lam, hl, p, q⟩ := twoq m d1 d2 d3 d4 (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      exact finish15 m (by omega) d1 d2 d3 d4 d5 hc lam hl p q
    · rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨lam, hl, p, q⟩ := twoq m d1 d2 d3 d4 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hlt, Or.inl h2⟩))))
        exact finish15 m (by omega) d1 d2 d3 d4 d5 hc lam hl p q
      · exact top_b66 m hm d1 d2 d3 d4 d5 hc ⟨h0, heq⟩ ⟨h0', hj ▸ heq⟩ h2
    · rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨lam, hl, p, q⟩ := twoq m d1 d2 d3 d4 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hlt, Or.inr h4⟩))))
        exact finish15 m (by omega) d1 d2 d3 d4 d5 hc lam hl p q
      · exact top_a66 m hm d1 d2 d3 d4 d5 hc ⟨h0, heq⟩ ⟨h0', hj ▸ heq⟩ h4
  · have h : E m d1 d2 = 0 ∨ E m d3 d4 = 0 ∨ nu 7 (E m d1 d2) ≠ nu 7 (E m d3 d4) := by tauto
    obtain ⟨lam, hl, p, q⟩ := twoq m d1 d2 d3 d4 (by rcases h with h | h | h <;> simp [h])
    exact finish15 m (by omega) d1 d2 d3 d4 d5 hc lam hl p q

/-- **Section 6.6** (`|A1| = |A2| = 2`, `|A4| = 1`, `m ≥ 2`). -/
theorem sec66 (m : ℕ) (hm : 2 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (h1 : ¬ 7 ∣ d1) (h2 : ¬ 7 ∣ d2)
    (h3 : ¬ 7 ∣ d3) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (r2 : R d2 = R d1) (r3 : R d3 = 2 * R d1)
    (r4 : R d4 = 2 * R d1) (r5 : R d5 = 4 * R d1) :
    ∃ lam, Nat.Coprime lam 7 ∧ ∀ x ∈ [d1, d2, d3, d4, d5], qq m (lam * x) ≠ 0 ∧ qq m (lam * x) ≠ 6 := by
  have hc : Cls66 d1 d2 d3 d4 d5 := ⟨h1, h2, h3, h4, h5, r2, r3, r4, r5⟩
  by_cases hsame : E m d1 d2 ≠ 0 ∧ E m d3 d4 ≠ 0 ∧ nu 7 (E m d1 d2) = nu 7 (E m d3 d4)
  · obtain ⟨h0, h0', hj⟩ := hsame
    rcases z7_ratio _ _ (R_ne_zero h0) (R_ne_zero h0') with hp | hn
    · exact core66 m hm d1 d2 d3 d4 d5 hc (fun _ _ _ => hp)
    · obtain ⟨hne', hnu', hR'⟩ := swap_rule m d3 d4 h0'
      obtain ⟨lam, hl, hall⟩ := core66 m hm d1 d2 d4 d3 d5 hc.swap34 (fun _ _ _ => by rw [hR']; exact hn)
      refine ⟨lam, hl, fun x hx => hall x ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢; tauto
  · exact core66 m hm d1 d2 d3 d4 d5 hc (fun a b c => absurd ⟨a, b, c⟩ hsame)

/-- **Section 6.6, real form** with one top speed. -/
theorem sec66_witness (m : ℕ) (hm : 2 ≤ m) (d1 d2 d3 d4 d5 : ℕ) (h1 : ¬ 7 ∣ d1) (h2 : ¬ 7 ∣ d2)
    (h3 : ¬ 7 ∣ d3) (h4 : ¬ 7 ∣ d4) (h5 : ¬ 7 ∣ d5) (r2 : R d2 = R d1) (r3 : R d3 = 2 * R d1)
    (r4 : R d4 = 2 * R d1) (r5 : R d5 = 4 * R d1) (d6 : ℕ) (h6 : d6 ≠ 0) (h6m : nu 7 d6 = m) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ [d1, d2, d3, d4, d5, d6], (1 : ℝ) / 7 ≤ nearestIntDist (t * x) := by
  obtain ⟨lam, hc, hall⟩ := sec66 m hm d1 d2 d3 d4 d5 h1 h2 h3 h4 h5 r2 r3 r4 r5
  obtain ⟨t, ht, hw⟩ := witness_of_lam m lam hc [d1, d2, d3, d4, d5] [d6] hall
    (by intro x hx; simp at hx; subst hx; exact ⟨h6, h6m⟩)
  exact ⟨t, ht, fun x hx => hw x (by simpa using hx)⟩

end LRSpectrumFull.BarajasSerra.Sec6
