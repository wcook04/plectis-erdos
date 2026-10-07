import ErdosProblems.Erdos249.TotientTranslateSeparation
import ErdosProblems.Synthesis.UniformRankBarrier

/-!
# Exact uniform finite-rank distance of the normalized totient matrix

The infinite matrix `φ(i+j+2)/(i+j+2)` has distance exactly `1/2` from
the set of all finite-separated-rank real matrices in the uniform norm.
The constant matrix `1/2` attains the distance. Factors in the finite-rank
representation need not be bounded; unbounded approximation error is
represented in `ENNReal`.

The arithmetic separation and the generic compactness theorem live in
separate modules so that this consumer can be replayed with precisely those
premises. This is a uniform-norm statement, not an obstruction to mean-error
approximation or a proof of irrationality of the binary totient series.
-/

namespace ErdosProblems.Erdos249.TotientUniformRankBarrier

open TotientTranslateSeparation
open ErdosProblems.Erdos269.PaperR8
open ErdosProblems.Synthesis.UniformRankBarrier
open scoped BigOperators ENNReal

theorem totient_finite_rank_uniform_error_lower
    (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A)
    (E : ℝ) (hE : 0 ≤ E)
    (herr : ∀ i j, |totientHankel i j - A i j| ≤ E) :
    (1 : ℝ) / 2 ≤ E :=
  finite_rank_uniform_error_lower_of_row_separation totientHankel 1 1
    (by norm_num) totientHankel_abs_le_one totientHankel_row_separation
    A hA E hE herr

theorem totient_uniformError_lower (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A) :
    ENNReal.ofReal ((1 : ℝ) / 2) ≤ uniformError totientHankel A :=
  uniformError_lower_of_row_separation totientHankel 1 1
    (by norm_num) totientHankel_abs_le_one totientHankel_row_separation A hA

/-- Exact finite separated rank is impossible as a consequence of the quantitative barrier. -/
theorem not_finiteSeparatedRank_totientHankel : ¬ FiniteSeparatedRank totientHankel := by
  intro h
  have hgap := totient_finite_rank_uniform_error_lower totientHankel h 0 (by norm_num)
    (by intro i j; simp)
  norm_num at hgap

/-- A rank-one minimiser. -/
noncomputable def midpointMatrix : FiniteRankMatrix :=
  ⟨(fun _ _ => (1 : ℝ) / 2),
    ⟨1, (fun _ _ => (1 : ℝ) / 2), (fun _ _ => 1), by intros; simp⟩⟩

theorem midpoint_pointwise_error_le (i j : ℕ) :
    |totientHankel i j - midpointMatrix.val i j| ≤ (1 : ℝ) / 2 := by
  have h0 := normalizedTotient_nonneg (i + j + 2)
  have h1 := normalizedTotient_le_one (i + j + 2)
  change |normalizedTotient (i + j + 2) - 1 / 2| ≤ (1 : ℝ) / 2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem midpoint_uniformError :
    uniformError totientHankel midpointMatrix.val = ENNReal.ofReal ((1 : ℝ) / 2) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro j
    exact ENNReal.ofReal_le_ofReal (midpoint_pointwise_error_le i j)
  · exact totient_uniformError_lower midpointMatrix.val midpointMatrix.property

/-- The exact infimum ranges over all finite ranks, with no factor-bound hypothesis. -/
theorem iInf_totient_uniform_finite_rank_distance :
    (⨅ A : FiniteRankMatrix, uniformError totientHankel A.val) =
      ENNReal.ofReal ((1 : ℝ) / 2) := by
  apply le_antisymm
  · exact (iInf_le _ midpointMatrix).trans_eq midpoint_uniformError
  · exact le_iInf fun A => totient_uniformError_lower A.val A.property

theorem iInf_totient_uniform_finite_rank_distance_toReal :
    (⨅ A : FiniteRankMatrix, uniformError totientHankel A.val).toReal = (1 : ℝ) / 2 := by
  rw [iInf_totient_uniform_finite_rank_distance]
  exact ENNReal.toReal_ofReal (by norm_num)

#print axioms totient_finite_rank_uniform_error_lower
#print axioms midpoint_uniformError
#print axioms iInf_totient_uniform_finite_rank_distance

end ErdosProblems.Erdos249.TotientUniformRankBarrier
