/-
# Continuity of `nearestIntDist` (step A1.1 toward `WallLemma`)

`nearestIntDist x` is the distance from `x` to the nearest integer, i.e. the `infDist`
from `x` to `ℤ ⊆ ℝ`. Since `infDist` to a fixed set is `1`-Lipschitz, `nearestIntDist` is
continuous — the first ingredient for "the 2-parameter loneliness `mgap` attains its sup
on the compact torus". NO `sorry`, NO `native_decide`.
-/
import LRSpectrumFull.Subtorus
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace LRSpectrumFull

open Metric

/-- `nearestIntDist x` is the `infDist` from `x` to the integers. -/
theorem nearestIntDist_eq_infDist (x : ℝ) :
    nearestIntDist x = infDist x (Set.range (Int.cast : ℤ → ℝ)) := by
  refine le_antisymm ?_ ?_
  · -- `nid x ≤ |x - n|` for every integer `n`, hence `nid x ≤ infDist`.
    refine le_infDist (Set.range_nonempty _) |>.mpr ?_
    rintro y ⟨n, rfl⟩
    rw [Real.dist_eq]
    exact nearestIntDist_le_dist x n
  · -- `infDist ≤ fract x` and `infDist ≤ 1 - fract x`, hence `≤ min = nid`.
    unfold nearestIntDist
    have hfloor : (⌊x⌋ : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨⌊x⌋, rfl⟩
    have hceil : ((⌊x⌋ + 1 : ℤ) : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨⌊x⌋ + 1, rfl⟩
    have hf0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x < 1 := Int.fract_lt_one x
    have hfr : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
    refine le_min ?_ ?_
    · have h : infDist x (Set.range (Int.cast : ℤ → ℝ)) ≤ dist x (⌊x⌋ : ℝ) :=
        infDist_le_dist_of_mem hfloor
      rwa [Real.dist_eq, ← hfr, abs_of_nonneg hf0] at h
    · have h : infDist x (Set.range (Int.cast : ℤ → ℝ)) ≤ dist x ((⌊x⌋ + 1 : ℤ) : ℝ) :=
        infDist_le_dist_of_mem hceil
      rw [Real.dist_eq] at h
      have he : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = Int.fract x - 1 := by
        rw [hfr]; push_cast; ring
      rw [he, abs_of_nonpos (by linarith)] at h
      linarith

/-- **`nearestIntDist` is continuous.** -/
theorem continuous_nearestIntDist : Continuous nearestIntDist := by
  have : nearestIntDist = fun x => infDist x (Set.range (Int.cast : ℤ → ℝ)) :=
    funext nearestIntDist_eq_infDist
  rw [this]
  exact continuous_infDist_pt _

/-- The `inf'` of finitely many continuous real-valued functions is continuous. -/
theorem continuous_finset_inf' {ι β : Type*} [TopologicalSpace β] {s : Finset ι}
    (hs : s.Nonempty) {f : ι → β → ℝ} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => s.inf' hs (fun i => f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i
  | cons i s hi hsne ih =>
    have hcont : Continuous (fun x => f i x ⊓ s.inf' hsne (fun j => f j x)) := (hf i).min ih
    convert hcont using 2 with x
    exact Finset.inf'_cons hsne (fun j => f j x)

variable {k r : ℕ}

/-- The `i`-th runner's instantaneous loneliness at time `τ`. `mgap v τ = inf'ᵢ runner v i τ`
holds by definition. -/
noncomputable def runner (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) (τ : Fin r → ℝ) : ℝ :=
  nearestIntDist (∑ l, (v i l : ℝ) * τ l)

theorem mgap_eq_inf'_runner (v : Fin (k + 1) → Fin r → ℤ) (τ : Fin r → ℝ) :
    mgap v τ = Finset.univ.inf' Finset.univ_nonempty (fun i => runner v i τ) := rfl

/-- Each runner is continuous in `τ`. -/
theorem continuous_runner (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1)) :
    Continuous (runner v i) := by
  refine continuous_nearestIntDist.comp ?_
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (continuous_apply j)

/-- Perturbing `τ` by `s • w` is affine inside the runner. -/
theorem runner_perturb (v : Fin (k + 1) → Fin r → ℤ) (i : Fin (k + 1))
    (τ w : Fin r → ℝ) (s : ℝ) :
    runner v i (fun l => τ l + s * w l)
      = nearestIntDist ((∑ l, (v i l : ℝ) * τ l) + s * (∑ l, (v i l : ℝ) * w l)) := by
  unfold runner
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- **`mgap M` is continuous** in the time parameter `τ` (the 2-parameter loneliness is a
continuous function on the torus). -/
theorem continuous_mgap (v : Fin (k + 1) → Fin r → ℤ) : Continuous (mgap v) := by
  rw [show mgap v = fun τ => Finset.univ.inf' Finset.univ_nonempty (fun i => runner v i τ) from rfl]
  exact continuous_finset_inf' Finset.univ_nonempty (continuous_runner v)

/-- **`mgap` is `ℤʳ`-periodic.** Shifting the time `τ` by an integer vector leaves the
2-parameter loneliness unchanged (each runner moves by an integer number of laps). -/
theorem mgap_add_intCast (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) (n : Fin r → ℤ) :
    mgap v (fun j => t j + (n j : ℝ)) = mgap v t := by
  unfold mgap
  congr 1
  funext i
  have hsum : (∑ j, (v i j : ℝ) * (t j + (n j : ℝ)))
      = (∑ j, (v i j : ℝ) * t j) + ((∑ j, v i j * n j : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, nearestIntDist_add_int]

/-- Any time is `mgap`-equivalent to its fractional part (which lies in `[0,1)ʳ`). -/
theorem mgap_fract (v : Fin (k + 1) → Fin r → ℤ) (t : Fin r → ℝ) :
    mgap v (fun j => Int.fract (t j)) = mgap v t := by
  have h := mgap_add_intCast v (fun j => Int.fract (t j)) (fun j => ⌊t j⌋)
  have he : (fun j => Int.fract (t j) + ((⌊t j⌋ : ℤ) : ℝ)) = t := by
    funext j
    have hf : Int.fract (t j) = t j - ((⌊t j⌋ : ℤ) : ℝ) := rfl
    rw [hf]; ring
  rw [he] at h
  exact h.symm

/-- **A1 (attainment).** The 2-parameter loneliness `mgap v` attains a GLOBAL maximum:
there is a time `τ` with `mgap v s ≤ mgap v τ` for every `s`. (Continuity + `ℤʳ`-periodicity
reduce the sup over `ℝʳ` to a max over the compact box `[0,1]ʳ`.) -/
theorem exists_mgap_max (v : Fin (k + 1) → Fin r → ℤ) :
    ∃ τ : Fin r → ℝ, ∀ s, mgap v s ≤ mgap v τ := by
  have hcompact : IsCompact (Set.Icc (0 : Fin r → ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0 : Fin r → ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  obtain ⟨τ, _hτmem, hτmax⟩ :=
    hcompact.exists_isMaxOn hne (continuous_mgap v).continuousOn
  refine ⟨τ, fun s => ?_⟩
  have hfr : (fun j => Int.fract (s j)) ∈ Set.Icc (0 : Fin r → ℝ) 1 := by
    refine Set.mem_Icc.mpr ⟨fun j => ?_, fun j => ?_⟩
    · simpa using Int.fract_nonneg (s j)
    · simpa using (Int.fract_lt_one (s j)).le
  calc mgap v s = mgap v (fun j => Int.fract (s j)) := (mgap_fract v s).symm
    _ ≤ mgap v τ := hτmax hfr

/-- **The wall condition (A2 ingredient).** Two reals with equal nearest-integer distance
have equal fractional parts, or complementary ones — i.e. they coincide mod 1 up to sign.
(At the loneliness optimum, two *active* runners satisfy this, putting the optimum on a
wall `{x_i = ±x_j}`.) -/
theorem nearestIntDist_eq_imp (a b : ℝ) (h : nearestIntDist a = nearestIntDist b) :
    Int.fract a = Int.fract b ∨ Int.fract a + Int.fract b = 1 := by
  unfold nearestIntDist at h
  have hfa0 : (0 : ℝ) ≤ Int.fract a := Int.fract_nonneg a
  have hfa1 : Int.fract a < 1 := Int.fract_lt_one a
  have hfb0 : (0 : ℝ) ≤ Int.fract b := Int.fract_nonneg b
  have hfb1 : Int.fract b < 1 := Int.fract_lt_one b
  rcases le_total (Int.fract a) (1 / 2) with ha | ha <;>
    rcases le_total (Int.fract b) (1 / 2) with hb | hb
  · rw [min_eq_left (by linarith), min_eq_left (by linarith)] at h; left; exact h
  · rw [min_eq_left (by linarith), min_eq_right (by linarith)] at h; right; linarith
  · rw [min_eq_right (by linarith), min_eq_left (by linarith)] at h; right; linarith
  · rw [min_eq_right (by linarith), min_eq_right (by linarith)] at h; left; linarith

/-- Adding a small real to `x` shifts its fractional part by that amount (no wraparound). -/
theorem fract_add_small (x δ : ℝ) (h0 : 0 ≤ Int.fract x + δ) (h1 : Int.fract x + δ < 1) :
    Int.fract (x + δ) = Int.fract x + δ := by
  have hx : x + δ = (Int.fract x + δ) + ((⌊x⌋ : ℤ) : ℝ) := by
    have : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := rfl
    rw [this]; ring
  rw [hx, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- **A2a ingredient: `nearestIntDist` has no local maximum below `1/2`.** If `nid x < 1/2`,
then arbitrarily close to `x` there is a `y` with strictly larger `nid`. (At the loneliness
optimum this forces ≥ 2 *active* runners: a lone active runner could be perturbed up.) -/
theorem nid_exists_gt (x ε : ℝ) (hε : 0 < ε) (h : nearestIntDist x < 1 / 2) :
    ∃ y, |y - x| < ε ∧ nearestIntDist x < nearestIntDist y := by
  have hf0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  rcases le_total (Int.fract x) (1 / 2) with hle | hle
  · -- fract x ≤ 1/2; nid x = fract x < 1/2.  Move right.
    have hlt : Int.fract x < 1 / 2 := by
      unfold nearestIntDist at h; rwa [min_eq_left (by linarith)] at h
    obtain ⟨δ, hδ0, hδε, hδh⟩ : ∃ δ, 0 < δ ∧ δ < ε ∧ Int.fract x + δ < 1 / 2 := by
      refine ⟨min (ε / 2) ((1 / 2 - Int.fract x) / 2), lt_min (by linarith) (by linarith),
        (min_le_left _ _).trans_lt (by linarith), ?_⟩
      have := min_le_right (ε / 2) ((1 / 2 - Int.fract x) / 2); linarith
    refine ⟨x + δ, ?_, ?_⟩
    · rw [add_sub_cancel_left, abs_of_pos hδ0]; exact hδε
    · have hfr : Int.fract (x + δ) = Int.fract x + δ :=
        fract_add_small x δ (by linarith) (by linarith)
      unfold nearestIntDist
      rw [min_eq_left (by linarith), hfr, min_eq_left (by linarith)]
      linarith
  · -- fract x ≥ 1/2; nid x = 1 - fract x.  Move left.
    have hlt : 1 / 2 < Int.fract x := by
      unfold nearestIntDist at h; rw [min_eq_right (by linarith)] at h; linarith
    obtain ⟨δ, hδ0, hδε, hδh⟩ : ∃ δ, 0 < δ ∧ δ < ε ∧ 1 / 2 < Int.fract x - δ := by
      refine ⟨min (ε / 2) ((Int.fract x - 1 / 2) / 2), lt_min (by linarith) (by linarith),
        (min_le_left _ _).trans_lt (by linarith), ?_⟩
      have := min_le_right (ε / 2) ((Int.fract x - 1 / 2) / 2); linarith
    refine ⟨x - δ, ?_, ?_⟩
    · rw [show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ0]; exact hδε
    · have hfr : Int.fract (x - δ) = Int.fract x - δ := by
        have := fract_add_small x (-δ) (by linarith) (by linarith); simpa using this
      unfold nearestIntDist
      rw [min_eq_right (by linarith), hfr, min_eq_right (by linarith)]
      linarith

/-- **A2a: ≥ 2 active runners at the optimum.** At a global maximizer `τ` with positive
loneliness, at least two runners achieve the minimum. (If only one runner `i₀` were active,
perturbing `τ` along a direction with `row_{i₀}·w = 1` raises `runner i₀` — `nid` has no
local max below `1/2` — while the others stay above the level by continuity, raising `mgap`
and contradicting maximality.) -/
theorem exists_two_active (v : Fin 4 → Fin 2 → ℤ) (τ : Fin 2 → ℝ)
    (hmax : ∀ s, mgap v s ≤ mgap v τ) (hpos : 0 < mgap v τ) :
    ∃ i j, i ≠ j ∧ runner v i τ = mgap v τ ∧ runner v j τ = mgap v τ := by
  by_contra hcon
  push_neg at hcon
  set c := mgap v τ with hc
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty) (fun i => runner v i τ)
  have hci₀ : runner v i₀ τ = c := by rw [hc, mgap_eq_inf'_runner]; exact hi₀.symm
  have hother : ∀ kk, kk ≠ i₀ → c < runner v kk τ := by
    intro kk hkk
    refine lt_of_le_of_ne ?_ (fun heq => ?_)
    · rw [hc, mgap_eq_inf'_runner]; exact Finset.inf'_le _ (Finset.mem_univ kk)
    · exact hcon i₀ kk (fun h => hkk h.symm) (hci₀.trans hc) (heq.symm.trans hc)
  -- `c < 1/2`
  have hclt : c < 1 / 2 := by
    obtain ⟨kk, hkk⟩ := exists_ne i₀
    exact lt_of_lt_of_le (hother kk hkk) (by unfold runner; exact nearestIntDist_le_half _)
  -- the active runner is a nonzero row
  have hnid0 : nearestIntDist (0 : ℝ) = 0 := by simpa using nearestIntDist_intCast 0
  have hrow : ∃ l₀, v i₀ l₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hz : (∑ l, (v i₀ l : ℝ) * τ l) = 0 :=
      Finset.sum_eq_zero (fun l _ => by rw [hall l]; simp)
    have : runner v i₀ τ = 0 := by unfold runner; rw [hz, hnid0]
    rw [hci₀] at this; linarith
  obtain ⟨l₀, hl₀⟩ := hrow
  -- direction `w = row_{i₀} / ‖row_{i₀}‖²`, so `row_{i₀}·w = 1`
  set N : ℝ := ∑ m, (v i₀ m : ℝ) ^ 2 with hN
  have hN0 : 0 < N := by
    rw [hN]
    refine Finset.sum_pos' (fun m _ => sq_nonneg _) ⟨l₀, Finset.mem_univ l₀, ?_⟩
    have : (v i₀ l₀ : ℝ) ≠ 0 := by exact_mod_cast hl₀
    positivity
  set w : Fin 2 → ℝ := fun l => (v i₀ l : ℝ) / N with hwdef
  have hNne : N ≠ 0 := ne_of_gt hN0
  have hrw1 : (∑ l, (v i₀ l : ℝ) * w l) = 1 := by
    have hsum : (∑ l, (v i₀ l : ℝ) * ((v i₀ l : ℝ) / N)) = (∑ l, (v i₀ l : ℝ) ^ 2) / N := by
      rw [eq_div_iff hNne, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _; field_simp
    rw [hwdef, hsum, ← hN, div_self hNne]
  -- the second-best runner level stays above `c` near `τ`
  set M : (Fin 2 → ℝ) → ℝ := fun σ =>
    (Finset.univ.erase i₀).inf'
      ⟨(exists_ne i₀).choose, Finset.mem_erase.mpr ⟨(exists_ne i₀).choose_spec, Finset.mem_univ _⟩⟩
      (fun k => runner v k σ) with hMdef
  have hMcont : Continuous M := continuous_finset_inf' _ (continuous_runner v)
  have hMτ : c < M τ := by
    rw [hMdef, Finset.lt_inf'_iff]; intro b hb; exact hother b (Finset.mem_erase.mp hb).1
  have hscont : Continuous (fun s : ℝ => M (fun l => τ l + s * w l)) :=
    hMcont.comp (continuous_pi (fun l => continuous_const.add (continuous_id.mul continuous_const)))
  have hf0 : c < (fun s : ℝ => M (fun l => τ l + s * w l)) 0 := by
    simp only [zero_mul, add_zero]; exact hMτ
  have hev : ∀ᶠ s in nhds (0 : ℝ), c < M (fun l => τ l + s * w l) :=
    hscont.continuousAt.eventually (eventually_gt_nhds hf0)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  -- raise the active runner
  have hnidlt : nearestIntDist (∑ l, (v i₀ l : ℝ) * τ l) < 1 / 2 := by
    have : runner v i₀ τ < 1 / 2 := by rw [hci₀]; exact hclt
    unfold runner at this; exact this
  obtain ⟨y, hyδ, hygt⟩ := nid_exists_gt (∑ l, (v i₀ l : ℝ) * τ l) δ hδ hnidlt
  set s := y - (∑ l, (v i₀ l : ℝ) * τ l) with hs
  -- `mgap` at the perturbed time exceeds `c`
  have hgap : c < mgap v (fun l => τ l + s * w l) := by
    rw [mgap_eq_inf'_runner, Finset.lt_inf'_iff]
    intro b _
    rcases eq_or_ne b i₀ with rfl | hb
    · have key : runner v b (fun l => τ l + s * w l) = nearestIntDist y := by
        rw [runner_perturb, hrw1, mul_one]; congr 1; rw [hs]; ring
      rw [key]
      calc c = runner v b τ := hci₀.symm
        _ = nearestIntDist (∑ l, (v b l : ℝ) * τ l) := rfl
        _ < nearestIntDist y := hygt
    · have hMgt : c < M (fun l => τ l + s * w l) :=
        hball (by rw [Real.dist_eq, sub_zero]; exact hyδ)
      refine lt_of_lt_of_le hMgt ?_
      rw [hMdef]; exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  have hle := hmax (fun l => τ l + s * w l)
  linarith [hgap, hle]

/-- **A1, packaged.** There is a time `τ` attaining the max-loneliness `mML v` and which is
a global maximizer of `mgap v`. -/
theorem exists_mgap_max_eq_mML (v : Fin (k + 1) → Fin r → ℤ) :
    ∃ τ : Fin r → ℝ, mgap v τ = mML v ∧ ∀ s, mgap v s ≤ mgap v τ := by
  obtain ⟨τ, hτ⟩ := exists_mgap_max v
  refine ⟨τ, ?_, hτ⟩
  refine le_antisymm (le_csSup (bddAbove_range_mgap v) ⟨τ, rfl⟩)
    (csSup_le (Set.range_nonempty _) ?_)
  rintro y ⟨s, rfl⟩; exact hτ s

/-- **A1 ⟹ the maximizer is lonely.** If `mD v < 1/4`, the global maximizer `τ` has every
runner `> 1/4` from an integer (`mgap v τ > 1/4`). This is the input to the wall argument
(A2): a strict interior optimum of the min-of-tents is impossible. -/
theorem exists_mgap_gt_quarter (v : Fin (k + 1) → Fin r → ℤ) (h : mD v < 1 / 4) :
    ∃ τ : Fin r → ℝ, (1 / 4 : ℝ) < mgap v τ ∧ ∀ s, mgap v s ≤ mgap v τ := by
  obtain ⟨τ, heq, hmax⟩ := exists_mgap_max_eq_mML v
  refine ⟨τ, ?_, hmax⟩
  have : (1 / 4 : ℝ) < mML v := by unfold mD at h; linarith
  rwa [heq]

end LRSpectrumFull
