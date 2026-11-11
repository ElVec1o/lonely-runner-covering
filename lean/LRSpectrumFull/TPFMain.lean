/-
# TP'(3), Case F: every triple `a < b < c ≤ 15` with gcd 1 and every phases (mod 4)

Assembled from the 26 verified chunk lemmas of `TPFData` and the generic `triple_spec`.
-/
import LRSpectrumFull.TPFData

namespace LRSpectrumFull
namespace TPF

set_option maxRecDepth 100000 in
theorem chunks_ok : ∀ ch ∈ chunks, ch.all tripleOK = true := by
  intro ch hch
  simp only [chunks, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chunk0_ok
  · exact chunk1_ok
  · exact chunk2_ok
  · exact chunk3_ok
  · exact chunk4_ok
  · exact chunk5_ok
  · exact chunk6_ok
  · exact chunk7_ok
  · exact chunk8_ok
  · exact chunk9_ok
  · exact chunk10_ok
  · exact chunk11_ok
  · exact chunk12_ok
  · exact chunk13_ok
  · exact chunk14_ok
  · exact chunk15_ok
  · exact chunk16_ok
  · exact chunk17_ok
  · exact chunk18_ok
  · exact chunk19_ok
  · exact chunk20_ok
  · exact chunk21_ok
  · exact chunk22_ok
  · exact chunk23_ok
  · exact chunk24_ok
  · exact chunk25_ok

def keyCheck : Bool :=
  (List.range 16).all fun a => (List.range 16).all fun b => (List.range 16).all fun c =>
    !(decide (0 < a ∧ a < b ∧ b < c ∧ Nat.gcd (Nat.gcd a b) c = 1)) ||
      chunks.flatten.any fun x => x.1 == (a : Int) && x.2.1 == (b : Int) && x.2.2.1 == (c : Int)

set_option maxRecDepth 100000 in
theorem keyCheck_true : keyCheck = true := by decide +kernel

theorem keys_complete : ∀ a < 16, ∀ b < 16, ∀ c < 16, 0 < a → a < b → b < c →
    Nat.gcd (Nat.gcd a b) c = 1 →
    ∃ x ∈ chunks.flatten, x.1 = (a : Int) ∧ x.2.1 = (b : Int) ∧ x.2.2.1 = (c : Int) := by
  intro a ha b hb c hc h0 h1 h2 h3
  have := keyCheck_true
  unfold keyCheck at this
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  have h := this a ha b hb c hc
  rcases h with h | ⟨x, hx, ⟨e1, e2⟩, e3⟩
  · exact absurd ⟨h0, h1, h2, h3⟩ h
  · exact ⟨x, hx, e1, e2, e3⟩

theorem caseF (a b c : Nat) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 15)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (sa sb sc : Int) :
    ∃ t : ℝ, 1 / 4 ≤ tpDist ((a : ℝ) * t + (sa : ℝ) / 4) ∧
      1 / 4 ≤ tpDist ((b : ℝ) * t + (sb : ℝ) / 4) ∧ 1 / 4 ≤ tpDist ((c : ℝ) * t + (sc : ℝ) / 4) := by
  obtain ⟨⟨x1, x2, x3, tbl⟩, hx, h1, h2, h3⟩ := keys_complete a (by omega) b (by omega) c (by omega) ha hab hbc hg
  obtain ⟨ch, hch, hxch⟩ := List.mem_flatten.mp hx
  have hall := chunks_ok ch hch
  have hok : tripleOK (x1, x2, x3, tbl) = true := by
    rw [List.all_eq_true] at hall; exact hall _ hxch
  simp only at h1 h2 h3
  rw [h1, h2, h3] at hok
  have := triple_spec _ _ _ tbl hok sa sb sc
  simpa using this

end TPF
end LRSpectrumFull
