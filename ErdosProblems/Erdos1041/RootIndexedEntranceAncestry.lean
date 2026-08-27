import Mathlib.Tactic

/-!
# Erdős 1041: root-indexed entrance ancestry

The companion note proves the combinatorial partition of derivative factors
by sibling subtrees and lowest common ancestors.  This module checks the
load-bearing scalar consequences used by the weighted and subtree-block
forms.
-/

namespace ErdosProblems.Erdos1041.RootIndexedEntranceAncestry

/-- Replacing a root derivative by its product over sibling subtrees exposes
the complete ancestor path in the entrance radius. -/
theorem entrance_eq_parent_div_ancestorProduct
    {q parentLevel derivative ancestorProduct : ℝ}
    (hderivative : derivative = ancestorProduct)
    (hq : q = parentLevel / derivative) :
    q = parentLevel / ancestorProduct := by
  rw [hq, hderivative]

/-- A subtree block has squared internal-pair factors and single boundary-cut
factors in its derivative product. -/
theorem subtree_block_product
    {qProduct parentProduct derivativeProduct internalProduct boundaryProduct : ℝ}
    (hderivative :
      derivativeProduct = internalProduct ^ 2 * boundaryProduct)
    (hq : qProduct = parentProduct / derivativeProduct) :
    qProduct =
      parentProduct / (internalProduct ^ 2 * boundaryProduct) := by
  rw [hq, hderivative]

/-- Multiplying two weighted root rows adds their exponents on a shared
cross-distance factor. -/
theorem two_row_cross_exponents_add
    {leftNumerator rightNumerator cross leftRow rightRow : ℝ}
    {leftWeight rightWeight : ℕ}
    (hcross : cross ≠ 0)
    (hl : leftRow = leftNumerator / cross)
    (hr : rightRow = rightNumerator / cross) :
    leftRow ^ leftWeight * rightRow ^ rightWeight =
      (leftNumerator ^ leftWeight * rightNumerator ^ rightWeight) /
        cross ^ (leftWeight + rightWeight) := by
  rw [hl, hr, div_pow, div_pow, pow_add]
  field_simp

/-- At constant weight one, a pair distance is counted once from each root
row and therefore becomes the squared discriminant factor. -/
theorem constant_weight_pair_is_square
    {leftNumerator rightNumerator cross leftRow rightRow : ℝ}
    (hcross : cross ≠ 0)
    (hl : leftRow = leftNumerator / cross)
    (hr : rightRow = rightNumerator / cross) :
    leftRow * rightRow =
      (leftNumerator * rightNumerator) / cross ^ 2 := by
  rw [hl, hr]
  field_simp
  ring

end ErdosProblems.Erdos1041.RootIndexedEntranceAncestry

