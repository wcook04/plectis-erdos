import Mathlib.Tactic

/-!
# Erdős 1041: leaf-entrance product identity

The analytic companion derives the product identity from the polynomial
resultant.  This module checks its load-bearing finite-tree and scalar algebra:
cherries outnumber pure binary nodes by one, mixed-node factors cancel, and
squaring gives the corresponding leaf-energy product.
-/

namespace ErdosProblems.Erdos1041.LeafEntranceProductIdentity

/-- In a full binary tree, counting leaf-child and internal-child edges implies
that the number of cherries is one more than the number of pure nodes. -/
theorem cherry_count_eq_pure_count_add_one
    (cherries mixed pure : ℕ)
    (h : 2 * cherries + mixed = 2 * pure + mixed + 2) :
    cherries = pure + 1 := by
  omega

/-- The mixed-node product cancels between the leaf-parent product and the
critical-value resultant product. -/
theorem mixed_node_product_cancellation
    {cherryProduct mixedProduct pureProduct degreePower : ℝ}
    (hm : mixedProduct ≠ 0) (hp : pureProduct ≠ 0)
    (hn : degreePower ≠ 0) :
    (cherryProduct * mixedProduct) /
        (degreePower * (pureProduct * mixedProduct)) =
      cherryProduct / (degreePower * pureProduct) := by
  field_simp
  ring

/-- Squaring the entrance-radius identity gives the geometric product of the
leaf-energy terms appearing in the charged lifetime inequality. -/
theorem squared_entrance_product
    {entranceProduct cherryProduct pureProduct degreePower : ℝ}
    (h : entranceProduct = cherryProduct / (degreePower * pureProduct)) :
    entranceProduct ^ 2 =
      (cherryProduct / (degreePower * pureProduct)) ^ 2 := by
  rw [h]

/-- On a comb there are no pure nodes, so the exact product sees only the
bottom cherry level. -/
theorem comb_specialization
    {entranceProduct firstLevel degreePower : ℝ}
    (h : entranceProduct = firstLevel / degreePower) :
    entranceProduct ^ 2 = firstLevel ^ 2 / degreePower ^ 2 := by
  rw [h, div_pow]

end ErdosProblems.Erdos1041.LeafEntranceProductIdentity
