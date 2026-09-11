import ErdosProblems.Erdos1049.AllRow.SourcePolynomial

/-!
# All normalized source rows and the existing determinant consumer

This module closes the authoring chain at the actual canonical definitions.
The determinant algebra is reused, not reproved. Verified locally by the
focused all-row audit on 2026-09-09.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.AllRow

open scoped BigOperators

/-- The already-canonical reciprocal recurrence, with the original source-tail
parameter selecting its ratio once and for all. -/
def sourceTailCoefficient (j t : ℕ) : ℤ :=
  hankelAssociatedCoeff (fun r => PowerSeries.coeff r (sourceGrade t)) j t

theorem sourceTailCoefficient_zero (j : ℕ) :
    sourceTailCoefficient j 0 = (-1 : ℤ) ^ j *
      PowerSeries.coeff j zudilinZeroTailAssociatedReciprocal := by
  rw [sourceTailCoefficient, sourceGrade, if_pos rfl,
    hankelAssociatedCoeff_zudilinZeroTail, if_pos (Nat.zero_le j), Nat.sub_zero]

theorem sourceTailCoefficient_pos (j t : ℕ) (ht : 0 < t) :
    sourceTailCoefficient j t =
      if t ≤ j then (-1 : ℤ) ^ j *
        PowerSeries.coeff (j - t) zudilinPositiveTailAssociatedReciprocal else 0 := by
  rw [sourceTailCoefficient, sourceGrade, if_neg (Nat.ne_of_gt ht)]
  exact hankelAssociatedCoeff_zudilinPositiveTail j t

theorem sourceTailCoefficient_above (j t : ℕ) (hjt : j < t) :
    sourceTailCoefficient j t = 0 :=
  associated_above _ j t hjt

/-- Sum all source states that can reach state zero. The reciprocal
coefficient assembly is the existing canonical theorem. -/
theorem sum_sourceTailCoefficient (j T : ℕ) (hjT : j < T) :
    (∑ t ∈ Finset.range T, sourceTailCoefficient j t) =
      (-1 : ℤ) ^ j * (zudilinTransformedRowCoeff j : ℤ) := by
  have hcut :
      (∑ t ∈ Finset.range (j + 1), sourceTailCoefficient j t) =
        ∑ t ∈ Finset.range T, sourceTailCoefficient j t := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro t _ ht
    apply sourceTailCoefficient_above
    simp only [Finset.mem_range, not_lt] at ht
    omega
  rw [← hcut, Finset.sum_range_succ', sourceTailCoefficient_zero]
  have hpos :
      (∑ s ∈ Finset.range j, sourceTailCoefficient j (s + 1)) =
        (-1 : ℤ) ^ j *
          ∑ s ∈ Finset.range j,
            PowerSeries.coeff (j - (s + 1)) zudilinPositiveTailAssociatedReciprocal := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [sourceTailCoefficient_pos j (s + 1) (by omega), if_pos]
    have := Finset.mem_range.mp hs
    omega
  have hreflect :
      (∑ s ∈ Finset.range j,
        PowerSeries.coeff (j - (s + 1)) zudilinPositiveTailAssociatedReciprocal) =
        ∑ r ∈ Finset.range j,
          PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal := by
    calc
      _ = ∑ s ∈ Finset.range j,
        PowerSeries.coeff (j - 1 - s) zudilinPositiveTailAssociatedReciprocal := by
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        rw [Nat.sub_sub, Nat.add_comm]
      _ = _ := Finset.sum_range_reflect
        (fun r => PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal) j
  rw [hpos, hreflect, ← zudilinAssociatedTailRowCoeff_eq j]
  ring

/-- Every coefficient of the exact moment is a finite tail sum, with a uniform
cut-off valid for all the indices in a backward difference. -/
theorem moment_agree_finite_tails (D n : ℕ) :
    Agree D (zudilinNormalizedMoment n)
      (∑ t ∈ Finset.range D, zudilinNormalizedTail n t) := by
  intro d hd
  rw [map_sum]
  apply coeff_zudilinNormalizedMoment_range
  have h : D ≤ (n + 1) * D := by
    have hm : 1 * D ≤ (n + 1) * D := Nat.mul_le_mul (by omega) (le_refl D)
    simpa using hm
  omega

/-- All finite-difference/summation exchanges are justified coefficientwise;
there is no analytic summability assumption hidden in this statement. -/
theorem coeff_transformed_eq_tail_sum (j l d : ℕ) :
    PowerSeries.coeff d (zudilinTransformedNormalizedMoment j l) =
      ∑ t ∈ Finset.range (d + 1),
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j (j + l) (fun n => zudilinNormalizedTail n t)) := by
  have h := Agree.backward (D := d + 1) j (j + l)
    zudilinNormalizedMoment
    (fun n => ∑ t ∈ Finset.range (d + 1), zudilinNormalizedTail n t)
    (fun n => moment_agree_finite_tails (d + 1) n)
  have hd := h d (by omega)
  change PowerSeries.coeff d (zudilinTransformedNormalizedMoment j l) = _ at hd
  rw [backward_sum, map_sum] at hd
  exact hd

/-- All lower coefficients vanish, at arbitrary depth and column. -/
theorem coeff_transformed_below (j l d : ℕ) (hd : d < rowExponent j l) :
    PowerSeries.coeff d (zudilinTransformedNormalizedMoment j l) = 0 := by
  rw [coeff_transformed_eq_tail_sum]
  apply Finset.sum_eq_zero
  intro t _
  exact (source_tail_initial j l t).1 d hd

/-- The first coefficient, with all source tails included. -/
theorem coeff_transformed_first (j l : ℕ) :
    PowerSeries.coeff (rowExponent j l) (zudilinTransformedNormalizedMoment j l) =
      (-1 : ℤ) ^ j * (zudilinTransformedRowCoeff j : ℤ) := by
  rw [coeff_transformed_eq_tail_sum]
  have hsum :
      (∑ t ∈ Finset.range (rowExponent j l + 1),
        PowerSeries.coeff (rowExponent j l)
          (zudilinBackwardShiftApply j (j + l) (fun n => zudilinNormalizedTail n t))) =
        ∑ t ∈ Finset.range (rowExponent j l + 1), sourceTailCoefficient j t := by
    apply Finset.sum_congr rfl
    intro t _
    exact (source_tail_initial j l t).2
  rw [hsum]
  exact sum_sourceTailCoefficient j (rowExponent j l + 1)
    (Nat.lt_succ_of_le (rowExponent_ge_depth j l))

end ErdosProblems.Erdos1049.AllRow

namespace ErdosProblems.Erdos1049

open scoped BigOperators

/-- The requested producer: all actual normalized Zudilin rows. No row
hypothesis occurs in the type. Verified locally on 2026-09-09. -/
theorem zudilinRowInitialMonomial_all (j : ℕ) : ZudilinRowInitialMonomial j := by
  intro l
  exact ⟨fun d hd => AllRow.coeff_transformed_below j l d hd,
    AllRow.coeff_transformed_first j l⟩

/-- Exact order of every transformed source row. -/
theorem order_zudilinTransformedNormalizedMoment_all (j l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment j l) =
      ((j * (j + 1) / 2 + j * l : ℕ) : ℕ∞) := by
  have h := zudilinRowInitialMonomial_all j l
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨?_, h.1⟩
  rw [h.2]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast (zudilinTransformedRowCoeff_pos j).ne'

/-- Same-turn composition into the supplied conditional determinant consumer.
No parallel determinant transformation or noncancellation proof is introduced.
Verified locally on 2026-09-09. -/
theorem zudilinSharpHankelOrderAndCoeff_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
        ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) ∧
      PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
          (zudilinNormalizedHankelDet N) =
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) :=
  zudilinSharpHankelOrderAndCoeff_of_rowInitialMonomial
    zudilinRowInitialMonomial_all N

/-- Exact closed q-order, including the empty determinant. -/
theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) := by
  have hsum : (∑ j ∈ Finset.range N, j ^ 2 : ℕ) =
      N * (N - 1) * (2 * N - 1) / 6 := by
    have h := six_mul_sum_range_sq N
    omega
  rw [← hsum]
  exact (zudilinSharpHankelOrderAndCoeff_all N).1

/-- Exact closed leading coefficient in division-free form. The multiplier
`2^N` is strictly positive, so this is precisely the stated factorial quotient. -/
theorem leadingCoeff_zudilinNormalizedHankelDet_all (N : ℕ) :
    (2 : ℤ) ^ N *
      PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
        (zudilinNormalizedHankelDet N) =
      (N.factorial : ℤ) ^ 2 * ((N + 1).factorial : ℤ) := by
  have hsum : (∑ j ∈ Finset.range N, j ^ 2 : ℕ) =
      N * (N - 1) * (2 * N - 1) / 6 := by
    have h := six_mul_sum_range_sq N
    omega
  rw [← hsum, (zudilinSharpHankelOrderAndCoeff_all N).2]
  exact_mod_cast twoPow_mul_prod_zudilinTransformedRowCoeff N

/-- The factorial quotient literally, after the injective embedding of the
integer coefficient into the rationals. Verified locally on 2026-09-09. -/
theorem coeff_zudilinNormalizedHankelDet_all_rat (N : ℕ) :
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N := by
  apply (eq_div_iff (show (2 : ℚ) ^ N ≠ 0 by positivity)).2
  have h := leadingCoeff_zudilinNormalizedHankelDet_all N
  have hq : (2 : ℚ) ^ N *
      ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
        (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) := by
    exact_mod_cast h
  simpa only [mul_comm] using hq

/-- In particular no normalized formal determinant is zero. -/
theorem zudilinNormalizedHankelDet_ne_zero_all (N : ℕ) :
    zudilinNormalizedHankelDet N ≠ 0 := by
  intro hz
  have h := leadingCoeff_zudilinNormalizedHankelDet_all N
  rw [hz, map_zero, mul_zero] at h
  have hp : (0 : ℤ) < (N.factorial : ℤ) ^ 2 * ((N + 1).factorial : ℤ) := by
    exact_mod_cast (show 0 < N.factorial ^ 2 * (N + 1).factorial by positivity)
  omega

end ErdosProblems.Erdos1049
