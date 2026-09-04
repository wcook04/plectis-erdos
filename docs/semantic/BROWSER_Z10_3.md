# Z10_3: Support-coefficient calculus for #257: divisor incidence, dilation, sunflowers and the squarefree barrier

[All problems and zones](BROWSER.md)

<a id="node-d2c3c4382da7aea9"></a>
## wrap_ratio_lower_bounds_reciprocal_mass

Given an odd tail state with doubling period h, the reciprocal mass of the support equals the wrap ratio (wrap count over h) plus the Cesaro mean of the tail excess; since the excess is nonnegative, the wrap ratio is a lower bound for the reciprocal mass, or the reciprocal sum diverges. In particular 1/h is such a lower bound whenever the wrap count is at least one.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hstate : IsOddSupportTailState A p v u - existence of an odd-denominator tail state, which by the node rational_value_constructs_odd_tail_state is available only under the open assumption that the support series is rational"]

- Lean declaration: [reciprocalMass_eq_wrapRatio_add_oddTailExcessMean](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1355)
- Lean declaration: [doublingWrapRatio_le_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1376)
- Lean declaration: [doublingWrapRatio_reciprocalMassDivergesOrAtLeast](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1389)
- Lean declaration: [one_div_period_reciprocalMassDivergesOrAtLeast](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1402)

- incoming **specialises**: [Z10::rational_value_forces_order_wrap_ratio_bound](BROWSER_Z10_2.md#node-3845be9631e85dab). The fraction-facing form instantiates the general wrap-ratio bound at the multiplicative order of 2.
- outgoing **depends_on_open**: [Z10::cesaro_tail_mean_equals_reciprocal_mass](BROWSER_Z10_1.md#node-b2d5cd6a8b764d3b). The excess-mean identity is the Cesaro limit of the tails minus the Cesaro limit of the normalised residues.
- outgoing **depends_on_open**: [Z10::odd_tail_state_residue_excess_decomposition](BROWSER_Z10_2.md#node-1dc753b317ffad9e). The decomposition supplies the residue/excess split whose means are taken.
- incoming **generalises**: [Z10::common_multiple_collision_strengthens_wrap_bound](BROWSER_Z10_1.md#node-260e0b210929ac12). It adds a collision term to the same wrap-ratio inequality.

