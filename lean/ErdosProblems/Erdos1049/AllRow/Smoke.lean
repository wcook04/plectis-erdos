import ErdosProblems.Erdos1049.AllRow.Producer

/-!
# Focused all-row smoke checks

Verified locally by the focused all-row audit on 2026-09-09. These are
source-facing quantified checks, not imports alone and not tests of a
substituted toy moment sequence.
-/

namespace ErdosProblems.Erdos1049.AllRowSmoke

open scoped BigOperators
open ErdosProblems.Erdos1049

-- The exact requested universal proposition, without a producer assumption.
example : ∀ j : ℕ, ZudilinRowInitialMonomial j :=
  zudilinRowInitialMonomial_all

-- First previously unproved row, in every column: -40 q^(3l+6).
example (l : ℕ) :
    (∀ d, d < 3 * l + 6 →
      PowerSeries.coeff d (zudilinTransformedNormalizedMoment 3 l) = 0) ∧
    PowerSeries.coeff (3 * l + 6)
      (zudilinTransformedNormalizedMoment 3 l) = -40 := by
  have h := zudilinRowInitialMonomial_all 3 l
  norm_num [zudilinTransformedRowCoeff] at h
  simpa [Nat.add_comm] using h

-- A genuinely higher row, still uniformly in the column: -288 q^(7l+28).
example (l : ℕ) :
    PowerSeries.coeff (7 * l + 28)
      (zudilinTransformedNormalizedMoment 7 l) = -288 := by
  have h := (zudilinRowInitialMonomial_all 7 l).2
  norm_num [zudilinTransformedRowCoeff] at h
  simpa [Nat.add_comm] using h

-- All depths, not merely the two displayed examples.
example (j l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment j l) =
      ((j * (j + 1) / 2 + j * l : ℕ) : ℕ∞) :=
  order_zudilinTransformedNormalizedMoment_all j l

-- State zero, a positive state, and a state too high to survive at depth three.
example (l : ℕ) :
    PowerSeries.coeff (AllRow.rowExponent 3 l)
      (zudilinBackwardShiftApply 3 (3 + l) (fun n => zudilinNormalizedTail n 0)) =
        -30 := by
  rw [(AllRow.source_tail_initial 3 l 0).2]
  change AllRow.sourceTailCoefficient 3 0 = -30
  rw [AllRow.sourceTailCoefficient_zero]
  norm_num [Nat.choose]

example (l : ℕ) :
    PowerSeries.coeff (AllRow.rowExponent 3 l)
      (zudilinBackwardShiftApply 3 (3 + l) (fun n => zudilinNormalizedTail n 1)) =
        -6 := by
  rw [(AllRow.source_tail_initial 3 l 1).2]
  change AllRow.sourceTailCoefficient 3 1 = -6
  rw [AllRow.sourceTailCoefficient_pos 3 1 (by omega)]
  norm_num [Nat.choose]

example (l : ℕ) :
    PowerSeries.coeff (AllRow.rowExponent 3 l)
      (zudilinBackwardShiftApply 3 (3 + l) (fun n => zudilinNormalizedTail n 4)) =
        0 := by
  rw [(AllRow.source_tail_initial 3 l 4).2]
  exact AllRow.sourceTailCoefficient_above 3 4 (by omega)

-- Empty determinant: no off-by-one convention in the closed endpoint.
example : PowerSeries.order (zudilinNormalizedHankelDet 0) = 0 := by
  simpa using order_zudilinNormalizedHankelDet_all 0

example : PowerSeries.coeff 0 (zudilinNormalizedHankelDet 0) = 1 := by
  simpa using leadingCoeff_zudilinNormalizedHankelDet_all 0

-- Rank four is the first rank not covered by only rows j <= 2.
example : PowerSeries.order (zudilinNormalizedHankelDet 4) = 14 := by
  have h := order_zudilinNormalizedHankelDet_all 4
  norm_num at h
  exact h

example : PowerSeries.coeff 14 (zudilinNormalizedHankelDet 4) = 4320 := by
  have h := leadingCoeff_zudilinNormalizedHankelDet_all 4
  norm_num [Nat.factorial] at h
  omega

-- Universal composition is checked directly, independently of rank examples.
example (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
        ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) ∧
      PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
        (zudilinNormalizedHankelDet N) =
          ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) :=
  zudilinSharpHankelOrderAndCoeff_all N

example (N : ℕ) :
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N :=
  coeff_zudilinNormalizedHankelDet_all_rat N

example (N : ℕ) : zudilinNormalizedHankelDet N ≠ 0 :=
  zudilinNormalizedHankelDet_ne_zero_all N

end ErdosProblems.Erdos1049.AllRowSmoke
