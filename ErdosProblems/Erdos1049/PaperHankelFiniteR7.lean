import ErdosProblems.Erdos1049.ZudilinSharpHankelCoefficient

/-!
# R7: finite-row Hankel assembly and unconditional ranks zero to three

NOT compiler-checked in this return. No admitted proofs.

The live library knows the actual transformed source rows j = 0, 1, 2.
Its all-rank consumer asks for EVERY row, even at a fixed rank. The first
lemma below restricts that input to j < N, using the same determinant proof.
This makes actual source determinants at N ≤ 3 unconditional. It does not
claim the missing all-depth row theorem, and it never substitutes the
associated leading matrix for the actual normalized Hankel determinant.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open scoped BigOperators

theorem hankel_order_coeff_of_rows_below (N : ℕ)
    (h : ∀ j : ℕ, j < N → ZudilinRowInitialMonomial j) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
        ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) ∧
      PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
          (zudilinNormalizedHankelDet N) =
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
  have hzero : ∀ i j : Fin N, ∀ d, d < zudilinLeadingEntryOrder i j →
      PowerSeries.coeff d (zudilinTransformedMomentMatrix N i j) = 0 :=
    fun i j d hd => (h (i : ℕ) i.isLt (j : ℕ)).1 d hd
  have hlead : ∀ i j : Fin N,
      PowerSeries.coeff (zudilinLeadingEntryOrder i j)
          (zudilinTransformedMomentMatrix N i j) =
        (-1 : ℤ) ^ (i : ℕ) * (zudilinTransformedRowCoeff (i : ℕ) : ℤ) :=
    fun i j => (h (i : ℕ) i.isLt (j : ℕ)).2
  have hentry : ∀ i j : Fin N,
      PowerSeries.order (zudilinTransformedMomentMatrix N i j) =
        (zudilinLeadingEntryOrder i j : ℕ∞) := by
    intro i j
    apply PowerSeries.order_eq_nat.mpr
    refine ⟨?_, fun d hd => hzero i j d hd⟩
    rw [hlead i j]
    have hc : (zudilinTransformedRowCoeff (i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (zudilinTransformedRowCoeff_pos (i : ℕ)).ne'
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc
  constructor
  · rw [← det_zudilinTransformedMomentMatrix N]
    exact order_det_eq_of_unique_minimizing_permutation
      (zudilinTransformedMomentMatrix N) zudilinLeadingEntryOrder
      (Fin.revPerm : Equiv.Perm (Fin N)) (∑ j ∈ Finset.range N, j ^ 2)
      hentry (sum_zudilinLeadingEntryOrder_revPerm N)
      (fun σ hσ => sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm σ hσ)
  · rw [← det_zudilinTransformedMomentMatrix N,
      coeff_det_eq_of_unique_minimizing_permutation
        (zudilinTransformedMomentMatrix N) zudilinLeadingEntryOrder
        (fun i _ =>
          (-1 : ℤ) ^ (i : ℕ) * (zudilinTransformedRowCoeff (i : ℕ) : ℤ))
        (Fin.revPerm : Equiv.Perm (Fin N)) (∑ j ∈ Finset.range N, j ^ 2)
        hzero hlead (sum_zudilinLeadingEntryOrder_revPerm N)
        (fun σ hσ => sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm σ hσ)]
    exact signedRowProduct_revPerm N


/-- Closed forms for the actual source determinant, conditional only on the
finitely many rows it uses. The coefficient equality is in ℚ, so no truncated
integer division or ENat division can silently weaken the statement. -/
theorem hankel_closed_form_of_rows_below (N : ℕ)
    (h : ∀ j : ℕ, j < N → ZudilinRowInitialMonomial j) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N := by
  obtain ⟨ho, hc⟩ := hankel_order_coeff_of_rows_below N h
  have hexp : (∑ j ∈ Finset.range N, j ^ 2) =
      N * (N - 1) * (2 * N - 1) / 6 := by
    have hs := six_mul_sum_range_sq N
    omega
  constructor
  · simpa only [hexp] using ho
  · rw [← hexp, hc]
    have hp : (2 : ℚ) ^ N *
        (∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℚ)) =
        (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) := by
      exact_mod_cast twoPow_mul_prod_zudilinTransformedRowCoeff N
    have htwo : (2 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    apply (eq_div_iff htwo).2
    push_cast
    calc
      (∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℚ)) * 2 ^ N =
          2 ^ N * (∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℚ)) :=
        mul_comm _ _
      _ = _ := hp

/-- Genuine partial coverage of both papers' `res:zudilin-sharp-qorder`:
the displayed equalities for the actual determinant, at every N ≤ 3.
The universal quantifier N ≥ 1 of the short paper is NOT closed by this. -/
theorem hankel_closed_form_through_rank_three (N : ℕ) (hN : N ≤ 3) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N := by
  apply hankel_closed_form_of_rows_below N
  intro j hj
  exact zudilinRowInitialMonomial_of_le_two (by omega)

/-- The full all-rank conclusion as a consumer. The one open premise is
explicitly the actual source-row theorem, not a numerical certificate. -/
theorem hankel_all_ranks_of_source_rows
    (h : ∀ j : ℕ, ZudilinRowInitialMonomial j) (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N :=
  hankel_closed_form_of_rows_below N (fun j _ => h j)

end ErdosProblems.Erdos1049.PaperR7
