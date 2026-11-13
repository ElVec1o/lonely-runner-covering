/-
# D0 certificate: bridge to the project's natural-number shape

`S4 v` is the statement used by `R5_core` / `P3` / `T`: for natural speeds `v : Fin 4 → ℕ` and every real
phase vector there is a time with `GoodR (v i) (φ i) t` for all `i` (`GoodR` = `1/5 ≤ tpDist (v t + φ)`).
`d0_sound_nat` gives `S4 v` from a certificate for the integer cast of `v`.  Uses `0 < v i` only.
-/
import LRSpectrumFull.D0Sound
import LRSpectrumFull.RFiveBase

namespace LRSpectrumFull
namespace D0

/-- the four-runner statement for natural speeds, in the shape of `R5_core`, `P3`, `T` -/
def S4 (v : Fin 4 → ℕ) : Prop := ∀ φ : Fin 4 → ℝ, ∃ t : ℝ, ∀ i, GoodR (v i) (φ i) t

theorem d0_sound_nat (v : Fin 4 → ℕ) (hpos : ∀ i, 0 < v i) (k1 k2 k3 : Fin 4 → ℤ)
    (h : D0cert (fun i => (v i : ℤ)) k1 k2 k3) : S4 v := by
  intro φ
  obtain ⟨t, ht⟩ := d0_sound (fun i => (v i : ℤ)) k1 k2 k3 (fun i => by show (0 : ℤ) < (v i : ℤ); exact_mod_cast hpos i) h φ
  exact ⟨t, fun i => by simpa [GoodR] using ht i⟩

end D0
end LRSpectrumFull
