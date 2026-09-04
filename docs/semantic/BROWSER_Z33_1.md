# Z33_1: Rational-base Lambert series: primitive local obstructions and additive repair

[All problems and zones](BROWSER.md)

<a id="node-a23e1059329b6e54"></a>
## binary_four_jet_collision_at_rank_threshold

PROVED CONDITIONAL CONSTRUCTION: at positive bottom depth, once the number of coefficient pairs reaches the explicit threshold n >= 4R+2S, two distinct binary selectors have the same four endpoint jets; subtracting them gives a nonzero {-1,0,1}-valued selector relation cancelling both bottom and top jets in both sequences.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem constructs a selector relation only. It does not prove that the combined polynomial pair or analytic remainder is nonzero, nor that the remainder decays fast enough for irrationality.

Open hypotheses: ["A growing-rank family whose resulting signed combination has a nonzero polynomial pair and a nonzero sufficiently small analytic remainder"]

- Lean declaration: [bottomJet3_eq_zero_iff_dvd](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L191)
- Lean declaration: [topJet2_eq_zero_iff_dvd](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L197)
- Lean declaration: [fourJetSignature_card](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L131)
- Lean declaration: [exists_distinct_binary_selectors_same_fourJet](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L142)
- Lean declaration: [exists_distinct_binary_selectors_same_fourJet_of_rank](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L161)

- outgoing **repair_of**: [Z33::common_specialized_multiplier_avoids_two_and_three](BROWSER_Z33_1.md#node-981d42f3bc2ce963). After the multiplicative route is excluded under unit endpoints, the four-jet collision supplies an additive cancellation mechanism whose remaining analytic obligations are explicit.

<a id="node-981d42f3bc2ce963"></a>
## common_specialized_multiplier_avoids_two_and_three

PROVED BARRIER: if one coefficient polynomial has a unit top endpoint, the other has a unit constant endpoint, and an integer divides both homogeneous evaluations at (3,2), then that common multiplier is divisible by neither 2 nor 3.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem is conditional on the unit endpoints and only excludes a common multiplier. It does not exclude additive cancellations or every primitive local-divisibility mechanism.

- Lean declaration: [commonMultiplier_not_two_not_three_of_endpoint_units](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L398)

- outgoing **implies**: [Z33::homogeneous_evaluation_sees_opposite_endpoints_mod_two_and_three](BROWSER_Z33_1.md#node-cb2281c1eb3272fb). The common-multiplier exclusion applies the separate modulo-2 and modulo-3 endpoint unit obstructions to the two entries of one coefficient pair.
- outgoing **complements**: [Z33::row_content_scales_local_and_archimedean_sides_equally](BROWSER_Z33_1.md#node-af1894867f3bd3a8). Endpoint residues exclude a common specialized multiplier, while row-content neutrality separately excludes scalar content as net local gain.
- incoming **repair_of**: [Z33::binary_four_jet_collision_at_rank_threshold](BROWSER_Z33_1.md#node-a23e1059329b6e54). After the multiplicative route is excluded under unit endpoints, the four-jet collision supplies an additive cancellation mechanism whose remaining analytic obligations are explicit.
- incoming **complements**: [Z33::three_halves_scalar_product_formula_margin_is_negative](BROWSER_Z33_1.md#node-c17b4fb0413b6995). The scalar-cone margin and endpoint/common-multiplier obstruction are independent checked failures of scalar multiplicative variants at 3/2.

<a id="node-cb2281c1eb3272fb"></a>
## homogeneous_evaluation_sees_opposite_endpoints_mod_two_and_three

PROVED: homogeneous evaluation of an integral polynomial at (3,2) is congruent modulo 3 to its constant coefficient times 2^W and modulo 2 to its top coefficient times 3^W; a unit constant endpoint therefore excludes divisibility by 3, and a unit top endpoint excludes divisibility by 2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result concerns endpoint residues of a fixed polynomial. It does not show that a useful Padé family has the required unit endpoints.

- Lean declaration: [homEvalThreeTwo_mod_three](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L203)
- Lean declaration: [homEvalThreeTwo_mod_two](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L320)
- Lean declaration: [three_not_dvd_homEvalThreeTwo_of_const_unit](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L338)
- Lean declaration: [two_not_dvd_homEvalThreeTwo_of_top_unit](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L356)

- incoming **implies**: [Z33::common_specialized_multiplier_avoids_two_and_three](BROWSER_Z33_1.md#node-981d42f3bc2ce963). The common-multiplier exclusion applies the separate modulo-2 and modulo-3 endpoint unit obstructions to the two entries of one coefficient pair.

<a id="node-af1894867f3bd3a8"></a>
## row_content_scales_local_and_archimedean_sides_equally

PROVED BARRIER: multiplying two integer coefficient rows by scalar contents multiplies their linear-form errors rowwise and multiplies both their exterior determinant and its absolute height by exactly the product of the two contents; the same product divides the scaled determinant, so content alone creates no net local-to-Archimedean gain.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This removes scalar row content as a source of gain. It does not construct primitive Padé rows, prove a nonzero determinant, estimate a remainder, or settle irrationality at 3/2.

- Lean declaration: [rationalPadeError_mul](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L84)
- Lean declaration: [rationalPadeExteriorDet_mul_contents](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L94)
- Lean declaration: [natAbs_rationalPadeExteriorDet_mul_contents](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L104)
- Lean declaration: [contentProduct_dvd_rationalPadeExteriorDet](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L116)
- Lean declaration: [rationalPadeExteriorDet_cast_eq](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L124)

- incoming **complements**: [Z33::common_specialized_multiplier_avoids_two_and_three](BROWSER_Z33_1.md#node-981d42f3bc2ce963). Endpoint residues exclude a common specialized multiplier, while row-content neutrality separately excludes scalar content as net local gain.

<a id="node-5405b060913ef0c0"></a>
## seven_halves_satisfies_external_height_criterion_arithmetic

PROVED ARITHMETIC INPUT: base 7/2 satisfies the explicit power, logarithmic, pi, margin, and final Archimedean height inequalities required by the cited Bundschuh–Väänänen criterion.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This node does not formalize or reprove the external analytic theorem and says nothing about the resistant base 3/2.

Open hypotheses: ["The external Bundschuh–Väänänen analytic irrationality theorem is cited rather than formalized"]

- Lean declaration: [sevenHalves_log_ratio_lt](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L48)
- Lean declaration: [one_div_pi_sq_lt_one_nine](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L64)
- Lean declaration: [sevenHalves_bundschuhVaananen_margin](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L73)
- Lean declaration: [sevenHalves_archimedean_height_condition](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L83)

- outgoing **complements**: [Z33::three_halves_scalar_product_formula_margin_is_negative](BROWSER_Z33_1.md#node-c17b4fb0413b6995). The cited external height criterion succeeds arithmetically at 7/2, while the checked scalar-cone product-formula margin is negative at the resistant base 3/2.

<a id="node-c17b4fb0413b6995"></a>
## three_halves_scalar_product_formula_margin_is_negative

PROVED CONDITIONAL BARRIER: under the source scalar-cone inequality used by the Zudilin-style construction, the corresponding product-formula margin at base 3/2 is strictly negative.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The source inequality is an explicit hypothesis. A negative scalar margin excludes that parameter lane; it does not exclude higher-rank additive kernels.

Open hypotheses: ["The source scalar-cone inequality assumed by the theorem"]

- Lean declaration: [three_two_scalar_margin_neg](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L428)

- outgoing **complements**: [Z33::common_specialized_multiplier_avoids_two_and_three](BROWSER_Z33_1.md#node-981d42f3bc2ce963). The scalar-cone margin and endpoint/common-multiplier obstruction are independent checked failures of scalar multiplicative variants at 3/2.
- incoming **complements**: [Z33::seven_halves_satisfies_external_height_criterion_arithmetic](BROWSER_Z33_1.md#node-5405b060913ef0c0). The cited external height criterion succeeds arithmetically at 7/2, while the checked scalar-cone product-formula margin is negative at the resistant base 3/2.

