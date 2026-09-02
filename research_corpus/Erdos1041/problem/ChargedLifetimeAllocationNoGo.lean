import Mathlib.Tactic

/-!
# Erdős 1041: charged-lifetime scalar allocation no-go

The companion note proves the analytic bound
`J_k(E; beta, delta) ≤ k E / 2`.  This module checks the exact aggregate
consequence: any strict uncharged slack admits positive node and leaf charges
while preserving the charged inequality.  Actual polynomial energies are not
asserted to be freely prescribable.
-/

namespace ErdosProblems.Erdos1041.ChargedLifetimeAllocationNoGo

/-- The positive parts introduced by `max` are pointwise bounded by the
energy term itself. -/
theorem max_sub_right_le_left {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y - y ≤ x := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy]
    linarith
  · rw [max_eq_left hyx]
    linarith

/-- Every strict uncharged budget admits strictly positive aggregate node and
leaf charges and still satisfies the charged budget. -/
theorem exists_positive_charges_below_slack
    {base target : ℝ} (hbase : base < target) :
    ∃ nodeCharge leafCharge : ℝ,
      0 < nodeCharge ∧ 0 < leafCharge ∧
      base + nodeCharge / 2 + leafCharge / 4 < target := by
  let slack := target - base
  have hs : 0 < slack := sub_pos.mpr hbase
  refine ⟨slack / 2, slack, by positivity, hs, ?_⟩
  dsimp [slack]
  linarith

/-- Consumer form: upper bounds on the actual node and leaf charges preserve
the explicitly constructed strict budget. -/
theorem charged_budget_of_small_upper_bounds
    {base target nodeCharge leafCharge slack : ℝ}
    (hslack : slack = target - base)
    (hbase : base < target)
    (hnode : nodeCharge ≤ slack / 2)
    (hleaf : leafCharge ≤ slack) :
    base + nodeCharge / 2 + leafCharge / 4 < target := by
  have hs : 0 < slack := by rw [hslack]; linarith
  nlinarith

/-- A componentwise energy ceiling `J ≤ kE/2` can be made smaller than any
positive requested margin by choosing a sufficiently small positive `E`. -/
theorem exists_positive_energy_with_charge_ceiling
    {k margin : ℝ} (hk : 0 < k) (hmargin : 0 < margin) :
    ∃ E : ℝ, 0 < E ∧ k * E / 2 < margin := by
  refine ⟨margin / k, by positivity, ?_⟩
  field_simp
  linarith

end ErdosProblems.Erdos1041.ChargedLifetimeAllocationNoGo
