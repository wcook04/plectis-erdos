import ErdosProblems.Erdos269.R12.OcticWindowBand
import Mathlib.Analysis.SpecificLimits.Normed

/-! Complete octic escape statement, including the hypotheses for both named
caps and the automatic zero-cap case. The irrationality target stays open. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open Filter PaperR7 PaperR11 PaperR12
open scoped Topology

def shortPaperCap (B a : ℕ) : ℕ := 90 * B * (a + 1) ^ 2

theorem quadratic_cap_div_eight_pow_tendsto (C : ℕ) :
    Tendsto (fun a : ℕ => ((C * (a + 1) ^ 2 : ℕ) : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (8 : ℝ) ^ n)
      atTop (𝓝 0) := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hmul := hshift.const_mul ((C : ℝ) * 8)
  convert hmul using 1
  · funext a
    dsimp
    push_cast
    rw [pow_add]
    field_simp
    <;> ring
  · simp

theorem long_cap_le_shortPaperCap (B a : ℕ) : longPaperCap B a ≤ shortPaperCap B a := by
  apply (longPaperCap_le_three_squareR11 B a).trans
  exact Nat.mul_le_mul_right ((a + 1) ^ 2)
    (Nat.mul_le_mul_right B (by decide : 3 ≤ 90))

theorem long_cap_div_eight_pow_tendsto (B : ℕ) :
    Tendsto (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (quadratic_cap_div_eight_pow_tendsto (3 * B))
    (Eventually.of_forall fun a => ?_) (Eventually.of_forall fun a => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast longPaperCap_le_three_squareR11 B a

theorem short_cap_div_eight_pow_tendsto (B : ℕ) :
    Tendsto (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := quadratic_cap_div_eight_pow_tendsto (90 * B)

/-- All clauses of the current long-paper octic escape equivalence. -/
theorem octic_escape_whole :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B →
        Tendsto (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational paperSeries235)) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational paperSeries235) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational paperSeries235) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by
  refine ⟨octic_window_band, long_cap_div_eight_pow_tendsto,
    long_cap_le_shortPaperCap, short_cap_div_eight_pow_tendsto,
    long_cap_window_equivalenceR11, ?_, escape_zero_cap⟩
  exact octic_window_band shortPaperCap (fun B a _ => long_cap_le_shortPaperCap B a)
    (fun B _ => short_cap_div_eight_pow_tendsto B)

#print axioms octic_escape_whole

end ErdosProblems.Erdos269.PaperCompleteR20
