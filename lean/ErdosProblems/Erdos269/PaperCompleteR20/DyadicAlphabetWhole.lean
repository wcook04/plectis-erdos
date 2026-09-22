import ErdosProblems.Erdos269.PaperR7ActualOrbit
import ErdosProblems.Erdos269.PaperR9SourceCounts

/-! The full dyadic alphabet statement includes its non-positional warning.
The printed scale-four example is checked by the Lean kernel after transport
through the proved exact digit evaluator. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR9

theorem actual_digit_four : dyadicOrderedBlockDigit235 4 = 65 := by
  rw [← orderedDigitExact_correct 4]
  decide +kernel

theorem actual_base_four : dyadicBlockBase235 4 = 30 := by
  exact dyadicBlockBase235_four

theorem dyadic_alphabet_whole :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a) := by
  refine ⟨literal_integer_forcing_and_four_radices, ?_, actual_base_four, 4, ?_⟩
  · rw [literalForcing235_eq_digit, actual_digit_four]
    norm_num
  · rw [actual_base_four, actual_digit_four]
    norm_num

#print axioms dyadic_alphabet_whole

end ErdosProblems.Erdos269.PaperCompleteR20
