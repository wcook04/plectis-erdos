import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the exterior-fibre capacity gap

The analytic companion note uses the harmonic-measure fibre identity for a
finite Blaschke product.  This file checks the load-bearing rational algebra
which turns the fibre reciprocal-derivative bound into the sharp product
constant `k / (2*n-k)`.  It does not formalize the analytic fibre identity or
assert the unrestricted Erdős theorem.
-/

namespace ErdosProblems.Erdos1041.ExteriorBlaschkeFibreCapacityGap

/-- Clearing the positive denominators in the Blaschke fibre inequality. -/
theorem product_lt_of_fibre_reciprocal_bound
    {n m p : ℝ} (hn : 0 < n) (hm : 0 <= m) (hp : 0 <= p)
    (hfibre : m / n < (1 - p) / (1 + p)) :
    p < (n - m) / (n + m) := by
  have h1p : 0 < 1 + p := by linarith
  have hnm : 0 < n + m := by linarith
  rw [div_lt_div_iff₀ hn h1p] at hfibre
  rw [lt_div_iff₀ hnm]
  nlinarith

/-- Substituting `m=n-k` gives the component constant `k/(2*n-k)`. -/
theorem missing_roots_constant_identity {n k : ℝ} :
    (n - (n - k)) / (n + (n - k)) = k / (2 * n - k) := by
  ring

/-- The fibre-coupled constant is positive and below one for `0<k<n`. -/
theorem fibre_gap_mem_unit_interval
    {n k : ℝ} (hk : 0 < k) (hkn : k < n) :
    0 < k / (2 * n - k) ∧ k / (2 * n - k) < 1 := by
  have hden : 0 < 2 * n - k := by linarith
  constructor
  · exact div_pos hk hden
  · apply (div_lt_one hden).2
    linarith

end ErdosProblems.Erdos1041.ExteriorBlaschkeFibreCapacityGap
