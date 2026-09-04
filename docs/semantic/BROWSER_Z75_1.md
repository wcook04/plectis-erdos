# Z75_1: Erdős 1049 Padé exterior determinants: channel divisibility and sign-controlled noncancellation

[All problems and zones](BROWSER.md)

<a id="node-b9e9a5ff91296d74"></a>
## a_divisor_common_to_either_coefficient_channel_divides_the_exterior_determinant

PROVED DIVISIBILITY INTERFACE: if d divides both Un and Um, then d divides rationalPadeExteriorDet Un Vn Um Vm; symmetrically, if d divides both Vn and Vm, then d divides the same exterior determinant.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorems do not produce a nonunit divisor, a growing prime-power valuation, primitive Padé rows, or a favorable local-to-Archimedean balance. Separate divisors from the U and V channels each divide the determinant, but their product is not asserted to divide it without an additional coprimality argument.

- Lean declaration: [commonU_dvd_rationalPadeExteriorDet](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L135)
- Lean declaration: [commonV_dvd_rationalPadeExteriorDet](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L147)

- incoming **complements**: [Z75::positive_errors_and_alternating_first_coefficients_force_determinant_noncancellation](BROWSER_Z75_1.md#node-27dd9e6f318f56ce). The channel lemmas provide arithmetic divisibility of the determinant, while the sign packet provides conditional Archimedean noncancellation; neither supplies the other's hypotheses or a favorable size-versus-divisor inequality.

<a id="node-27dd9e6f318f56ce"></a>
## positive_errors_and_alternating_first_coefficients_force_determinant_noncancellation

PROVED CONDITIONAL SIGN PACKET: if both rational Padé errors are strictly positive and Un<0<Um, then the exterior determinant is strictly positive; if both errors are strictly positive and Um<0<Un, then it is strictly negative. In either alternating-sign configuration the determinant is nonzero.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The abstract implications are proved, but the intended Padé application still needs an actual coefficient family with positive remainders and alternating U signs. The packet gives no determinant-size bound, no local divisibility gain, no remainder decay, and no irrationality or transcendence conclusion.

Open hypotheses: ["For application to an actual adjacent Padé family, strict positivity of both real errors rationalPadeError S Un Vn and rationalPadeError S Um Vm.", "For the same selected adjacent rows, one of the two strict alternating sign patterns Un<0<Um or Um<0<Un."]

- Lean declaration: [rationalPadeExteriorDet_pos_of_left_neg_right_pos](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L158)
- Lean declaration: [rationalPadeExteriorDet_neg_of_left_pos_right_neg](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L179)
- Lean declaration: [rationalPadeExteriorDet_ne_zero_of_left_neg_right_pos](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L200)
- Lean declaration: [rationalPadeExteriorDet_ne_zero_of_left_pos_right_neg](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L212)

- outgoing **complements**: [Z75::a_divisor_common_to_either_coefficient_channel_divides_the_exterior_determinant](BROWSER_Z75_1.md#node-b9e9a5ff91296d74). The channel lemmas provide arithmetic divisibility of the determinant, while the sign packet provides conditional Archimedean noncancellation; neither supplies the other's hypotheses or a favorable size-versus-divisor inequality.

