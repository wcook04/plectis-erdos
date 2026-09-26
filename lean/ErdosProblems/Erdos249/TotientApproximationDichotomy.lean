import ErdosProblems.Erdos249.TotientMeanApproximation
import ErdosProblems.Erdos249.TotientUniformRankBarrier

/-!
# Two approximation modes for the same normalized totient matrix

The explicit Möbius truncation of `φ(i+j+2)/(i+j+2)` uses at most
`D * (D + 1) / 2` separated factors. Its mean absolute error on every
leading `N` by `N` square is at most `2 / D`, whereas its uniform error
is at least `1 / 2`. The latter is the exact distance to all finite-rank
matrices, attained by the constant matrix `1 / 2`.

This module only combines the two approximation theorems, translating the
positive indices of the mean estimate to the zero-based Hankel convention.
The displayed factor count is a representation budget, not a minimal rank.
-/

namespace ErdosProblems.Erdos249.TotientApproximationDichotomy

open ErdosProblems.Erdos269.PaperR8
open TotientTranslateSeparation (totientHankel)
open scoped BigOperators ENNReal

/-- The same Möbius truncation, with the indices of `totientHankel`. -/
noncomputable def hankelTruncation (D i j : ℕ) : ℝ :=
  TotientMeanApproximation.truncatedTotient D (i + j + 2)

/-- Shifting both factors by one preserves the explicit triangular budget. -/
theorem hankelTruncation_triangular_rank (D : ℕ) :
    ∃ f g : Fin (D * (D + 1) / 2) → ℕ → ℝ,
      ∀ i j, hankelTruncation D i j =
        ∑ k : Fin (D * (D + 1) / 2), f k i * g k j := by
  obtain ⟨f, g, h⟩ := TotientMeanApproximation.truncatedTotient_triangular_rank D
  refine ⟨(fun k i => f k (i + 1)), (fun k j => g k (j + 1)), ?_⟩
  intro i j
  have hshift : (i + 1) + (j + 1) = i + j + 2 := by omega
  simpa only [hshift, hankelTruncation] using h (i + 1) (j + 1)

theorem hankelTruncation_finite_rank (D : ℕ) :
    FiniteSeparatedRank (hankelTruncation D) := by
  obtain ⟨f, g, h⟩ := hankelTruncation_triangular_rank D
  exact ⟨D * (D + 1) / 2, f, g, h⟩

private theorem sum_Icc_one_eq_sum_range_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.Icc 1 N, f i) = ∑ i ∈ Finset.range N, f (i + 1) := by
  simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.add_sub_cancel, Nat.add_comm]
    using Finset.sum_Ico_eq_sum_range f 1 (N + 1)

/-- The finite-square mean estimate, for exactly the uniform-barrier matrix. -/
theorem hankelTruncation_mean_error_le (D N : ℕ) (hD : 0 < D) (hN : 0 < N) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      |totientHankel i j - hankelTruncation D i j|) / ((N : ℝ) ^ 2) ≤
        2 / (D : ℝ) := by
  have h := TotientMeanApproximation.normalizedTotient_mean_error_le D N hD hN
  simp_rw [sum_Icc_one_eq_sum_range_succ] at h
  have hshift (i j : ℕ) : (i + 1) + (j + 1) = i + j + 2 := by omega
  simpa only [totientHankel, hankelTruncation,
    TotientTranslateSeparation.normalizedTotient,
    TotientMeanApproximation.normalizedTotient, hshift] using h

theorem hankelTruncation_uniform_error_lower (D : ℕ) :
    ENNReal.ofReal ((1 : ℝ) / 2) ≤ uniformError totientHankel (hankelTruncation D) :=
  TotientUniformRankBarrier.totient_uniformError_lower
    (hankelTruncation D) (hankelTruncation_finite_rank D)

/-- One explicit family has arbitrarily small finite-square mean bounds, but
every member retains the uniform gap shared by all finite-rank matrices. -/
theorem totient_approximation_dichotomy (D : ℕ) (hD : 0 < D) :
    (∃ f g : Fin (D * (D + 1) / 2) → ℕ → ℝ,
      ∀ i j, hankelTruncation D i j =
        ∑ k : Fin (D * (D + 1) / 2), f k i * g k j) ∧
    (∀ N : ℕ, 0 < N →
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        |totientHankel i j - hankelTruncation D i j|) / ((N : ℝ) ^ 2) ≤
          2 / (D : ℝ)) ∧
    ENNReal.ofReal ((1 : ℝ) / 2) ≤ uniformError totientHankel (hankelTruncation D) ∧
    (⨅ A : FiniteRankMatrix, uniformError totientHankel A.val) =
      ENNReal.ofReal ((1 : ℝ) / 2) := by
  exact ⟨hankelTruncation_triangular_rank D,
    (fun N hN => hankelTruncation_mean_error_le D N hD hN),
    hankelTruncation_uniform_error_lower D,
    TotientUniformRankBarrier.iInf_totient_uniform_finite_rank_distance⟩

#print axioms totient_approximation_dichotomy

end ErdosProblems.Erdos249.TotientApproximationDichotomy
