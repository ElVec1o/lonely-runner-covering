import LRSpectrumFull.BarajasSerra
import Mathlib.Data.ZMod.Basic

/-!
# E6 session 16: groundwork G1 and G2 for Barajas-Serra Section 6

* G2 (multiplier bookkeeping): a multiplier `lam ≡ 1 [MOD p^(m+1-v)]` (for instance any product of
  elements of `Lam j m p` with `j < v`) fixes `q` at every level `>= v`, fixes `nu` and `r`, and
  fixes `q` of any difference whose residue is divisible by `p^v`. A factor `1 + p^(m-j) k` times
  such a multiplier with `v = j` shifts level `j` by `k r(x)`.
* G1 (Lemma 2 with slack): prime filtering for a set whose nonzero residues all lie at levels
  `< v <= m`, with elements `≡ 0 (mod N)` allowed (their `q` is `0` for every multiplier); the
  multiplier returned is `≡ 1 [MOD p^(m+1-v)]`, so by G2 it disturbs nothing at levels `>= v`.
  Also the version with a top level (`nu <= m`, not `= m`), zero residues allowed.

Falsified first in Rust: (development file, not part of this archive) (180000 random instances each for
G1 and G2, p in {3,5,7}, m in 1..3, 0 failures).
-/

namespace LRSpectrumFull.BarajasSerra.G

open LRSpectrumFull.BarajasSerra

/-! ## G2 -/

theorem Lam_modEq_one {p j m lam : ℕ} (h : lam ∈ Lam j m p) : lam ≡ 1 [MOD p ^ (m - j)] := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
  simp [Nat.ModEq, Nat.add_mul_mod_self_left]

theorem modEq_one_mul {a b M : ℕ} (ha : a ≡ 1 [MOD M]) (hb : b ≡ 1 [MOD M]) : a * b ≡ 1 [MOD M] := by
  simpa using ha.mul hb

theorem modEq_one_mono {p a s t : ℕ} (h : a ≡ 1 [MOD p ^ s]) (hts : t ≤ s) : a ≡ 1 [MOD p ^ t] := by
  exact Nat.ModEq.of_dvd (pow_dvd_pow p hts) h

theorem mul_modEq_self_of_dvd {p m v lam x : ℕ} (hv : v ≤ m + 1) (hlam : lam ≡ 1 [MOD p ^ (m + 1 - v)])
    (hx : p ^ v ∣ x) : lam * x ≡ x [MOD p ^ (m + 1)] := by
  obtain ⟨w, rfl⟩ := hx
  have h1 : lam * p ^ v ≡ 1 * p ^ v [MOD p ^ (m + 1 - v) * p ^ v] := hlam.mul_right' (p ^ v)
  have hpow : p ^ (m + 1 - v) * p ^ v = p ^ (m + 1) := by rw [← pow_add]; congr 1; omega
  rw [hpow, one_mul] at h1
  have h2 := h1.mul_right w
  rw [← mul_assoc]
  exact h2

theorem qarc_congr {p m N a b : ℕ} (h : a ≡ b [MOD N]) : qarc p m N a = qarc p m N b := by
  unfold qarc; rw [show a % N = b % N from h]

theorem qarc_mul_fix {p m v lam x : ℕ} (hv : v ≤ m + 1) (hlam : lam ≡ 1 [MOD p ^ (m + 1 - v)])
    (hx : p ^ v ∣ x) : qarc p m (p ^ (m + 1)) (lam * x) = qarc p m (p ^ (m + 1)) x := by
  exact qarc_congr (mul_modEq_self_of_dvd hv hlam hx)

theorem pow_nu_dvd (p x : ℕ) : p ^ nu p x ∣ x := by
  unfold nu; exact pow_padicValNat_dvd

theorem qarc_mul_fix_nu {p m v lam x : ℕ} (hv : v ≤ m + 1) (hlam : lam ≡ 1 [MOD p ^ (m + 1 - v)])
    (hx : v ≤ nu p x) : qarc p m (p ^ (m + 1)) (lam * x) = qarc p m (p ^ (m + 1)) x := by
  exact qarc_mul_fix hv hlam ((pow_dvd_pow p hx).trans (pow_nu_dvd p x))

theorem qarc_mul_lam_eq_prod {p j m k lamB x : ℕ} (hp : p.Prime) (hjm : j ≤ m) (hk : k < p)
    (hB : lamB ≡ 1 [MOD p ^ (m + 1 - j)]) (hx : nu p x = j) :
    qarc p m (p ^ (m + 1)) ((1 + p ^ (m - j) * k) * lamB * x)
      = (qarc p m (p ^ (m + 1)) x + k * rp p x) % p := by
  have h1 : lamB * x ≡ x [MOD p ^ (m + 1)] :=
    mul_modEq_self_of_dvd (by omega) hB (hx ▸ pow_nu_dvd p x)
  have h2 : (1 + p ^ (m - j) * k) * lamB * x ≡ (1 + p ^ (m - j) * k) * x [MOD p ^ (m + 1)] := by
    rw [mul_assoc]; exact h1.mul_left _
  rw [qarc_congr h2]
  exact qarc_mul_lam_eq p j m hp hjm k hk x hx

theorem coprime_of_modEq_one {p lam : ℕ} (hp : p.Prime) (hlam : lam ≡ 1 [MOD p]) :
    Nat.Coprime lam p ∧ lam ≠ 0 := by
  have h1 : lam % p = 1 := by
    have := hlam; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt hp.one_lt
  refine ⟨?_, ?_⟩
  · have hndvd : ¬ p ∣ lam := by
      intro hd; rw [Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff dvd_rfl |>.mpr hd) (Nat.mod_lt _ hp.pos)] at h1
      exact absurd h1 (by norm_num)
    exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hndvd)
  · rintro rfl; simp at h1

theorem nu_mul_of_modEq_one {p lam x : ℕ} (hp : p.Prime) (hlam : lam ≡ 1 [MOD p]) (hx : x ≠ 0) :
    nu p (lam * x) = nu p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hc, h0⟩ := coprime_of_modEq_one hp hlam
  exact nu_mul_coprime p lam x hc h0 hx

theorem rp_mul_of_modEq_one {p lam x : ℕ} (hp : p.Prime) (hlam : lam ≡ 1 [MOD p]) (hx : x ≠ 0) :
    rp p (lam * x) = rp p x := by
  have hl1 : lam % p = 1 := by
    have := hlam; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt hp.one_lt
  unfold rp
  rw [nu_mul_of_modEq_one hp hlam hx, Nat.mul_div_assoc lam (pow_nu_dvd p x), Nat.mul_mod, hl1,
    one_mul, Nat.mod_mod]

/-- The residue of `x - y` modulo `N`, as a natural number in `[0, N)`. -/
def dsub (N x y : ℕ) : ℕ := (x % N + (N - y % N)) % N

theorem dsub_cast (N x y : ℕ) (hN : 0 < N) : ((dsub N x y : ℕ) : ZMod N) = (x : ZMod N) - y := by
  unfold dsub
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod,
    Nat.cast_sub (le_of_lt (Nat.mod_lt _ hN)), ZMod.natCast_mod, ZMod.natCast_self]
  ring

theorem dsub_mul (N lam x y : ℕ) (hN : 0 < N) : dsub N (lam * x) (lam * y) ≡ lam * dsub N x y [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [dsub_cast N _ _ hN, dsub_cast N _ _ hN]
  push_cast; ring

theorem qarc_dsub_fix {p m v lam x y : ℕ} (hv : v ≤ m + 1) (hlam : lam ≡ 1 [MOD p ^ (m + 1 - v)])
    (hp : 0 < p) (hxy : p ^ v ∣ dsub (p ^ (m + 1)) x y) :
    qarc p m (p ^ (m + 1)) (dsub (p ^ (m + 1)) (lam * x) (lam * y))
      = qarc p m (p ^ (m + 1)) (dsub (p ^ (m + 1)) x y) := by
  have hN : 0 < p ^ (m + 1) := pow_pos hp _
  apply qarc_congr
  exact (dsub_mul _ lam x y hN).trans (mul_modEq_self_of_dvd hv hlam hxy)

/-- Single-element steering (the most frequent use of Lemma 2 in Section 6): a level-`h` element
(`h <= m`) can be sent to any prescribed `q`-value by one factor of `Lam h m p`. -/
theorem exists_lam_target {p h m x t : ℕ} (hp : p.Prime) (hhm : h ≤ m) (hx : nu p x = h)
    (hx0 : x ≠ 0) (ht : t < p) :
    ∃ k < p, qarc p m (p ^ (m + 1)) ((1 + p ^ (m - h) * k) * x) = t := by
  have hcop : Nat.Coprime (rp p x) p := rp_coprime p x hp hx0
  have hinj := injOn_shift_scale p (qarc p m (p ^ (m + 1)) x) (rp p x) hp hcop
  set f := fun k => (qarc p m (p ^ (m + 1)) x + k * rp p x) % p with hf
  have hsub : (Finset.range p).image f ⊆ Finset.range p := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  have hcard : (Finset.range p).card ≤ ((Finset.range p).image f).card := by
    rw [Finset.card_image_of_injOn hinj]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have htm : t ∈ (Finset.range p).image f := by rw [heq]; exact Finset.mem_range.mpr ht
  obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp htm
  refine ⟨k, Finset.mem_range.mp hk, ?_⟩
  rw [qarc_mul_lam_eq p h m hp hhm k (Finset.mem_range.mp hk) x hx]
  exact hkt

/-! ## G1 -/

theorem below_aux (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d)
    (F : ℕ → Finset ℕ) (m v : ℕ) (hv : v ≤ m) (hlow : ∀ d ∈ D, nu p d < v)
    (hlevels : ∀ j < v, (∑ d ∈ Dlevel p D j, (F d).card) ≤ p - 1) :
    ∀ t ≤ v, ∃ lam : ℕ, lam ≡ 1 [MOD p ^ (m + 1 - v)] ∧
      ∀ d ∈ D, v - t ≤ nu p d → qarc p m (p ^ (m + 1)) (lam * d) ∉ F d := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, Nat.ModEq.refl 1, ?_⟩
    intro d hd h
    have := hlow d hd
    omega
  | succ t ih =>
    intro htv
    obtain ⟨lam0, hlam0c, hlam0⟩ := ih (by omega)
    have hlam0p : lam0 ≡ 1 [MOD p] := by
      simpa using modEq_one_mono hlam0c (show 1 ≤ m + 1 - v by omega)
    obtain ⟨hlam0cop, hlam0ne⟩ := coprime_of_modEq_one hp hlam0p
    set j := v - (t + 1) with hjdef
    have hjm : j < m := by omega
    set K := Finset.range p with hKdef
    have hbound : (∑ d ∈ Dlevel p D j, (F d).card) < K.card := by
      rw [hKdef, Finset.card_range]; have := hlevels j (by omega); have := hp.two_le; omega
    have hinj : ∀ d ∈ Dlevel p D j,
        Set.InjOn (fun k => (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p) K := by
      intro d hd
      have hdpos : 0 < d := hpos d (Finset.mem_filter.mp hd).1
      have hcop : Nat.Coprime (rp p (lam0 * d)) p :=
        rp_coprime p (lam0 * d) hp (Nat.mul_ne_zero hlam0ne hdpos.ne')
      exact injOn_shift_scale p _ _ hp hcop
    obtain ⟨k, hk, hgood⟩ := exists_good_k K (Dlevel p D j) F
      (fun d k => (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p) hinj hbound
    have hklt : k < p := by rwa [hKdef, Finset.mem_range] at hk
    refine ⟨(1 + p ^ (m - j) * k) * lam0, ?_, ?_⟩
    · apply modEq_one_mul _ hlam0c
      apply modEq_one_mono _ (show m + 1 - v ≤ m - j by omega)
      exact Lam_modEq_one (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    · intro d hd hnud
      rcases lt_or_ge j (nu p d) with hgt | hle
      · have hnu : nu p (lam0 * d) = nu p d :=
          nu_mul_coprime p lam0 d hlam0cop hlam0ne (hpos d hd).ne'
        have hval : qarc p m (p ^ (m + 1)) (((1 + p ^ (m - j) * k) * lam0) * d)
            = qarc p m (p ^ (m + 1)) (lam0 * d) := by
          rw [mul_assoc]
          exact qarc_mul_lam_gt p j m (le_of_lt hjm) k (lam0 * d) (hnu ▸ hgt)
        rw [hval]
        exact hlam0 d hd (by omega)
      · have hlevel : nu p d = j := by omega
        have hnu : nu p (lam0 * d) = j :=
          (nu_mul_coprime p lam0 d hlam0cop hlam0ne (hpos d hd).ne').trans hlevel
        have hval : qarc p m (p ^ (m + 1)) (((1 + p ^ (m - j) * k) * lam0) * d)
            = (qarc p m (p ^ (m + 1)) (lam0 * d) + k * rp p (lam0 * d)) % p := by
          rw [mul_assoc]
          exact qarc_mul_lam_eq p j m hp (le_of_lt hjm) k hklt (lam0 * d) hnu
        rw [hval]
        exact hgood d (Finset.mem_filter.mpr ⟨hd, hlevel⟩)

theorem qarc_of_mod_zero {p m N d lam : ℕ} (hd : d % N = 0) : qarc p m N (lam * d) = 0 := by
  unfold qarc; rw [Nat.mul_mod, hd]; simp

theorem primeFilteringBelow (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (F : ℕ → Finset ℕ) (m N : ℕ)
    (hN : N = p ^ (m + 1)) (v : ℕ) (hv : v ≤ m)
    (hlow : ∀ d ∈ D, d % N ≠ 0 → nu p d < v)
    (hlevels : ∀ j < v, (∑ d ∈ Dlevel p (D.filter (fun d => d % N ≠ 0)) j, (F d).card) ≤ p - 1)
    (hzero : ∀ d ∈ D, d % N = 0 → 0 ∉ F d) :
    ∃ lam : ℕ, lam ≡ 1 [MOD p ^ (m + 1 - v)] ∧ ∀ d ∈ D, qarc p m N (lam * d) ∉ F d := by
  subst hN
  obtain ⟨lam, hlc, hlam⟩ := below_aux p hp (D.filter (fun d => d % p ^ (m + 1) ≠ 0))
    (by
      intro d hd
      have := (Finset.mem_filter.mp hd).2
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at this
      · exact h)
    F m v hv (fun d hd => hlow d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2)
    hlevels v le_rfl
  refine ⟨lam, hlc, ?_⟩
  intro d hd
  by_cases hz : d % p ^ (m + 1) = 0
  · rw [qarc_of_mod_zero hz]; exact hzero d hd hz
  · exact hlam d (Finset.mem_filter.mpr ⟨hd, hz⟩) (by omega)

theorem slack_aux (p : ℕ) (hp : p.Prime) (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d) (F : ℕ → Finset ℕ) (m : ℕ) (hle : ∀ d ∈ D, nu p d ≤ m) (N : ℕ)
    (hN : N = p ^ (m + 1)) (hlevels : ∀ j < m, (∑ d ∈ Dlevel p D j, (F d).card) ≤ p - 1)
    (htop : (∑ d ∈ Dlevel p D m, (F d).card) ≤ p - 2) :
    ∀ t ≤ m, ∃ lam : ℕ, lam ≠ 0 ∧ Nat.Coprime lam p ∧
      ∀ d ∈ D, m - t ≤ nu p d → qarc p m N (lam * d) ∉ F d := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨lam, hlamtop, hgood⟩ := primeFiltering_top p hp D F m N hN
      (fun d hd => hpos d (Finset.mem_filter.mp hd).1) htop
    refine ⟨lam, by rw [mem_LamTop] at hlamtop; omega, LamTop_coprime p hp lam hlamtop, ?_⟩
    intro d hd hnud
    simp only [Nat.sub_zero] at hnud
    have hlevel : nu p d = m := le_antisymm (hle d hd) hnud
    exact hgood d (Finset.mem_filter.mpr ⟨hd, hlevel⟩)
  | succ t ih =>
    intro htm1
    obtain ⟨lam0, hlam0ne, hlam0cop, hlam0⟩ := ih (by omega)
    obtain ⟨lam, hlamne, hlamcop, hgood⟩ := primeFiltering_step p hp D hpos F m N hN (m - t)
      (by omega) (by omega)
      (by
        have : m - t - 1 = m - (t + 1) := by omega
        rw [this]; exact hlevels (m - (t + 1)) (by omega))
      lam0 hlam0ne hlam0cop hlam0
    refine ⟨lam, hlamne, hlamcop, ?_⟩
    intro d hd hnud
    have heq : m - t - 1 = m - (t + 1) := by omega
    rw [heq] at hgood
    exact hgood d hd hnud

theorem primeFilteringSlack (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (F : ℕ → Finset ℕ) (m N : ℕ)
    (hN : N = p ^ (m + 1))
    (hlevels : ∀ j < m, (∑ d ∈ Dlevel p (D.filter (fun d => d % N ≠ 0)) j, (F d).card) ≤ p - 1)
    (htop : (∑ d ∈ Dlevel p (D.filter (fun d => d % N ≠ 0)) m, (F d).card) ≤ p - 2)
    (hzero : ∀ d ∈ D, d % N = 0 → 0 ∉ F d) :
    ∃ lam : ℕ, Nat.Coprime lam p ∧ ∀ d ∈ D, qarc p m N (lam * d) ∉ F d := by
  have hposD : ∀ d ∈ D.filter (fun d => d % N ≠ 0), 0 < d := by
    intro d hd
    have := (Finset.mem_filter.mp hd).2
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at this
    · exact h
  have hleD : ∀ d ∈ D.filter (fun d => d % N ≠ 0), nu p d ≤ m := by
    intro d hd
    have hz := (Finset.mem_filter.mp hd).2
    by_contra hc
    apply hz
    rw [hN]
    exact Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff dvd_rfl |>.mpr
      ((pow_dvd_pow p (show m + 1 ≤ nu p d by omega)).trans (pow_nu_dvd p d)))
      (Nat.mod_lt _ (pow_pos hp.pos _))
  obtain ⟨lam, _, hlamcop, hlam⟩ := slack_aux p hp _ hposD F m hleD N hN hlevels htop m le_rfl
  refine ⟨lam, hlamcop, ?_⟩
  intro d hd
  by_cases hz : d % N = 0
  · rw [qarc_of_mod_zero hz]; exact hzero d hd hz
  · exact hlam d (Finset.mem_filter.mpr ⟨hd, hz⟩) (by omega)

end LRSpectrumFull.BarajasSerra.G
