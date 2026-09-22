import Erdos249257.SquaredMersenneDiagonalEnclosure

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257
open FullTargetPrimeAdjunctionNoGo

/-- The complete Mobius-square reduction, including its irrationality
 equivalence. This proves no irrationality assertion without its equivalent input. -/
theorem mobius_square_reduction :
    totientSeries = (1 : ℝ) / 2 +
      ∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  rw [SquaredMersenneDiagonalEnclosure.totientSeries_eq_pnat_half_pow]
  exact MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq

theorem irrational_totient_iff_mobius_square :
    Irrational totientSeries ↔
      Irrational (∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  rw [mobius_square_reduction]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (irrational_ratCast_add_iff (q := (1 : ℚ) / 2))

theorem moebius_three_values (d : ℕ) :
    ArithmeticFunction.moebius d = -1 ∨ ArithmeticFunction.moebius d = 0 ∨
      ArithmeticFunction.moebius d = 1 := by
  by_cases h : ArithmeticFunction.moebius d = 0
  · exact Or.inr (Or.inl h)
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

#print axioms mobius_square_reduction
#print axioms irrational_totient_iff_mobius_square
#print axioms moebius_three_values
end ErdosProblems.Erdos249.PaperCompleteR20
