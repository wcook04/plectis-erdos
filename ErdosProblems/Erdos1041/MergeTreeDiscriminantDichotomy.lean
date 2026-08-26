import Mathlib

/-!
# Merge-tree discriminant dichotomy: scalar kernel

The analytic companion proves a telescoping identity on the actual truncated
lemniscate merge forest.  This file checks the load-bearing local exponent
cancellation.  If the left and right subtrees contain `a+1` and `b+1` leaves,
their normalized edge factors carry exponents `a` and `b`; the parent carries
exponent `a+b+1`.
-/

namespace ErdosProblems.Erdos1041.MergeTreeDiscriminantDichotomy

/-- Binary local step in the merge-tree critical-product telescoping identity. -/
theorem binary_merge_telescoping
    (R x y : ℝ) (a b : ℕ) :
    R ^ (a + b + 1) * x ^ a * y ^ b =
      R * (R * x) ^ a * (R * y) ^ b := by
  simp only [mul_pow]
  rw [pow_add, pow_succ]
  ring

/-- The exponent left at a node with `d` children is its critical multiplicity
`d-1`: `sum (k_i-1) + (d-1) = (sum k_i)-1`, in additive coordinates. -/
theorem child_exponent_cancellation
    (internalChildExponents childCount : ℕ) :
    internalChildExponents + childCount =
      internalChildExponents + (childCount + 1) - 1 := by
  omega

/-- The terminal `k=n` specialization of `(2n-k)/k` is exactly one. -/
theorem terminal_capacity_ratio (n : ℝ) (hn : n ≠ 0) :
    (2 * n - n) / n = 1 := by
  field_simp
  ring

end ErdosProblems.Erdos1041.MergeTreeDiscriminantDichotomy
