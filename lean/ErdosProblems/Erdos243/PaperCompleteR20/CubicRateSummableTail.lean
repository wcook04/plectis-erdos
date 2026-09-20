import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateQuotientIncrement
import Mathlib.Analysis.PSeries

/-!
# Erdős 243: summing a cubic-rate increment

An increment which is `o(n⁻³)` has a convergent primitive whose tail is
`o(n⁻²)`.  This is the quantitative summation step needed for the literal
ratio error in the paper.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset

/-- The elementary telescoping majorant for the tail of the cubic p-series. -/
theorem tsum_one_div_cube_nat_add_le (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((n + k : ℕ) : ℝ) ^ 3) ≤ 1 / (n : ℝ) ^ 2 := by
  let u : ℕ → ℝ := fun k => 1 / ((n + k : ℕ) : ℝ) ^ 2
  have hu_nonneg : ∀ k, 0 ≤ u k - u (k + 1) := by
    intro k
    dsimp [u]
    have hpos : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n + k by omega)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (sq_pos_of_pos hpos)
    gcongr <;> norm_num
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hbase : Tendsto (fun k : ℕ => (((n + k : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp
        (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)
    simpa [u, one_div, inv_pow] using hbase.pow 2
  have htel : HasSum (fun k => u k - u (k + 1)) (1 / (n : ℝ) ^ 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hu_nonneg]
    have hlim : Tendsto (fun N => u 0 - u N) atTop (nhds (u 0)) := by
      simpa using tendsto_const_nhds.sub hu_zero
    simpa only [Finset.sum_range_sub', u, Nat.add_zero] using hlim
  have hcub : Summable (fun k : ℕ => 1 / ((n + k : ℕ) : ℝ) ^ 3) := by
    exact (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 3)).comp_injective
      (i := fun k : ℕ => n + k) (fun _ _ h => Nat.add_left_cancel h)
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) hcub htel.summable
  dsimp [u]
  push_cast
  have ha : (2 : ℝ) ≤ n + k := by exact_mod_cast le_trans hn (Nat.le_add_right n k)
  have ha0 : (0 : ℝ) < n + k := lt_of_lt_of_le (by norm_num) ha
  have ha1 : (0 : ℝ) < n + (k + 1) := by positivity
  field_simp
  nlinarith [sq_nonneg ((n + k : ℝ) - 1)]

/-- Quantitative summation of a literal cubic-rate little-o increment. -/
theorem exists_limit_with_square_scaled_tail
    (x : ℕ → ℝ)
    (hincr : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * (x (n + 1) - x n)) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (x n - K)) atTop (nhds 0) := by
  have hone : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) ^ 3 * (x (n + 1) - x n)| ≤ 1 := by
    have habs := hincr.abs
    exact ((tendsto_order.1 habs).2 1 (by norm_num)).mono (fun _ hn => le_of_lt hn)
  have hdist : ∀ᶠ n : ℕ in atTop,
      dist (x n) (x (n + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    filter_upwards [hone, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    rw [Real.dist_eq]
    have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [abs_sub_comm]
    calc
      |x (n + 1) - x n| =
          |(n : ℝ) ^ 3 * (x (n + 1) - x n)| / (n : ℝ) ^ 3 := by
            rw [abs_mul, abs_of_pos (pow_pos hn0r 3)]
            field_simp
      _ ≤ 1 / (n : ℝ) ^ 3 := div_le_div_of_nonneg_right hn (pow_nonneg hn0r.le 3)
  have hcube : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hsumdist : Summable (fun n : ℕ => dist (x n) (x (n + 1))) :=
    Summable.of_norm_bounded_eventually_nat hcube (by
      filter_upwards [hdist] with n hn
      simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hn)
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsumdist)
  refine ⟨K, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  have heps : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) ^ 3 * (x (n + 1) - x n)| < (ε / 2) := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 hincr (ε / 2) (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.1 heps
  refine ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hpoint : ∀ m : ℕ,
      dist (x (n + m)) (x (n + m + 1)) ≤ (ε / 2) / ((n + m : ℕ) : ℝ) ^ 3 := by
    intro m
    have hmN : N ≤ n + m := le_trans hnN (Nat.le_add_right n m)
    have hmpos : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) (le_trans hn2 (Nat.le_add_right n m))
    have hm := le_of_lt (hN _ hmN)
    rw [Real.dist_eq, abs_sub_comm]
    calc
      |x (n + m + 1) - x (n + m)| =
          |((n + m : ℕ) : ℝ) ^ 3 * (x (n + m + 1) - x (n + m))| /
            ((n + m : ℕ) : ℝ) ^ 3 := by
              rw [abs_mul, abs_of_pos (pow_pos hmpos 3)]
              field_simp
      _ ≤ (ε / 2) / ((n + m : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right hm (pow_nonneg hmpos.le 3)
  have htaildist : dist (x n) K ≤
      ∑' m : ℕ, dist (x (n + m)) (x (n + m + 1)) :=
    dist_le_tsum_dist_of_tendsto hsumdist hK n
  have htailmajor :
      (∑' m : ℕ, dist (x (n + m)) (x (n + m + 1))) ≤
        (ε / 2) * (1 / (n : ℝ) ^ 2) := by
    calc
      _ ≤ ∑' m : ℕ, (ε / 2) / ((n + m : ℕ) : ℝ) ^ 3 :=
        Summable.tsum_le_tsum hpoint
          (hsumdist.comp_injective (i := fun m : ℕ => n + m)
            (fun _ _ h => Nat.add_left_cancel h))
          (by
            simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using
              (hcube.comp_injective (i := fun m : ℕ => n + m)
                (fun _ _ h => Nat.add_left_cancel h)).mul_left (ε / 2))
      _ = (ε / 2) * (∑' m : ℕ, 1 / ((n + m : ℕ) : ℝ) ^ 3) := by
        simp only [div_eq_mul_inv, one_mul]
        rw [tsum_mul_left]
      _ ≤ (ε / 2) * (1 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (tsum_one_div_cube_nat_add_le n hn2) (half_pos hε).le
  rw [Real.dist_eq] at htaildist
  rw [Real.dist_eq]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) hn2
  calc
    |(n : ℝ) ^ 2 * (x n - K) - 0| = (n : ℝ) ^ 2 * |x n - K| := by
      rw [sub_zero, abs_mul, abs_of_nonneg (pow_nonneg hnpos.le 2)]
    _ ≤ (n : ℝ) ^ 2 * ((ε / 2) * (1 / (n : ℝ) ^ 2)) := by
      gcongr
      exact htaildist.trans htailmajor
    _ = (ε / 2) := by field_simp
    _ < ε := half_lt_self hε

/-- The literal ratio error supplies the paper's normalised cubic error once
the quotient increment theorem has supplied its cubic-rate increment. -/
theorem normalisedCubicError_tendsto_zero_of_quotient_increment
    (C : ℕ → ℝ)
    (hincr : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      (cubicQuotient C (n + 1) - cubicQuotient C n)) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by
  simpa [normalisedCubicError, cubicQuotient] using
    exists_limit_with_square_scaled_tail (cubicQuotient C) hincr

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.exists_limit_with_square_scaled_tail
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_tendsto_zero_of_quotient_increment

end ErdosProblems.Erdos243.PaperCompleteR20
