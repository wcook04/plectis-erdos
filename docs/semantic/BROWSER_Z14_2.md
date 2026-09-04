# Z14_2: Last-producer analysis: middle and upper carries, the final -2 cell and its phase sieve

[All problems and zones](BROWSER.md)

<a id="node-e2e6eddcff985890"></a>
## tail_escape_equals_rational_take_decision

At every adjacent cut with s at least 5, the carry-minus-tail margin equals exactly four times the distance of the corrected floor coordinate Z above the rational take threshold, and Z can never equal that threshold. Hence the producer tail-escape inequality is not an analytic majorant at all: it holds precisely when the exact rational greedy remainder of the below word is at least the terminal Mersenne weight, that is, precisely when the rational greedy would take rank s.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

- Lean declaration: [middleProducer_tail_lt_carry_iff_takeThreshold_lt_floorZ](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1474)
- Lean declaration: [middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1551)
- Lean declaration: [middleProducer_carry_lt_tail_iff_floorZ_lt_takeThreshold](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1616)
- Lean declaration: [middleProducer_tail_lt_carry_iff_takeThreshold_le_floorZ](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1705)
- Lean declaration: [middleProducer_tail_lt_carry_iff_rational_take](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1726)

- outgoing **reformulates**: [Z14::producer_carry_exact_half_criterion](BROWSER_Z14_1.md#node-abd85fefcd4526c8). Rewrites the carry-versus-tail comparison in corrected floor coordinates and then as a rational greedy take decision.
- incoming **implies**: [Z14::final_middle_producer_must_violate_tail_inequality](BROWSER_Z14_1.md#node-ebba9d2041f7e4d5). Consumes the exact tail formula to give the reverse strict inequality at a hypothetical final middle producer.
- outgoing **equivalent_to**: [Z13::rational_take_comparison_in_floor_coordinates](BROWSER_Z13_1.md#node-a81c11f42592eccc). middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold and middleProducer_tail_lt_carry_iff_rational_take (HalfCylinderMiddleCarryLowerBound.lean) show the producer carry-minus-tail margin is four times the floorZ distance above exactly the take threshold of seamWord_take_iff_floorZ.

<a id="node-e42073fa443bf061"></a>
## two_sided_dyadic_invariant_branch_propagation

An upper successor always satisfies the lower half of the next-row two-sided dyadic bound. A middle successor satisfies one side whenever its signed coordinate is at most -4 or at least 0, and the complement of that safe range is exactly the three integers -3, -2, -1. A right successor preserves the remainder witness always and the overshoot witness whenever its pulse-corrected upper charge stays below twice the old gap; failure of that last condition is exactly a distance cell just below 2^s with 4k < abovePulse.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [seamUpperBranch_nextRemainder_le_pow](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3924)
- Lean declaration: [seamMiddleBranch_next_twoSided_of_not_neg_small](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3963)
- Lean declaration: [seamRightBranch_nextRemainder_le_pow_of_remainder_le](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4043)
- Lean declaration: [seamRightBranch_nextOvershoot_le_pow_of_charge_le](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4060)
- Lean declaration: [seamRightBranch_nextOvershoot_le_pow_of_overshoot_le_of_noPulseLeak](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4113)
- Lean declaration: [seamMiddleCoordinate_not_safe_iff_three_cells](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4125)
- Lean declaration: [seamRightPulseLeak_iff_distanceCell](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4202)

- outgoing **implies**: [Z14::two_sided_dyadic_invariant_under_cell_escape](BROWSER_Z14_2.md#node-a7d5bd16039a80ba). The branch lemmas are the induction step of the conditional invariant.
- incoming **reformulates**: [Z14::pure_half_prefix_normal_form](BROWSER_Z14_1.md#node-acdf5992da565f9f). Single-coordinate normal form of the same two-sided dyadic bound.

<a id="node-a7d5bd16039a80ba"></a>
## two_sided_dyadic_invariant_under_cell_escape

If no middle transition ever lands in the signed cells -3, -2 or -1 and no right transition with overshoot at most 2^s has upper charge above 2^(s+2), then the two-sided dyadic bound min(remainder, overshoot) at most 2^s holds at every row from five onward.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["SeamTwoSidedDyadicCellEscape: for all s >= 5, (a) at a genuine middle transition the coordinate 4*remainder - belowPulse - 4 is none of -3, -2, -1, and (b) at a right transition with overshoot <= 2^s one has 4*overshoot + abovePulse <= 2^(s+2)"]

- Lean declaration: [SeamTwoSidedDyadicCellEscape.step](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4398)
- Lean declaration: [SeamTwoSidedDyadicCellEscape.twoSided](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448)

- incoming **implies**: [Z14::two_sided_dyadic_invariant_branch_propagation](BROWSER_Z14_2.md#node-e42073fa443bf061). The branch lemmas are the induction step of the conditional invariant.
- incoming **depends_on_open**: [Z12::seam_gap_bound_yields_half](BROWSER_Z12_2.md#node-34a6eea19a93dd72). the nearest statement bounding the seam remainder by a dyadic power at every row; it delivers only min(remainder, overshoot) <= 2^s and is itself gated on the unproved SeamTwoSidedDyadicCellEscape, so it does not produce the one-sided bound rem(s) < 2^(s+1).

<a id="node-adac92563d1572b8"></a>
## upper_last_producer_impossible

An upper (successor-carry) transition at a row D at least 13 cannot be the last non-right transition of an eventually right seam: its terminal-augmented affine carry is at most -8, which puts the corresponding lazy endpoint above one half by a full Mersenne gap, while the eventual right tail puts it below one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Conclusion is False, so the theorem is the unconditional negative fact that no row D >= 13 is simultaneously an upper (successor-carry) transition and followed only by right extensions; it is not vacuous. Scope: it eliminates the upper branch at a last false terminal only. It says nothing about the middle branch, nothing about the pure right-tail branch, and nothing about rows below 13.

- Lean declaration: [upperProducer_not_last](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L299)

- incoming **implies**: [Z14::producer_carry_negative_forces_above_half](BROWSER_Z14_1.md#node-34ca9821b1e8f14e). The carry-at-most--8 Mersenne-gap margin is exactly the engine of the upper exclusion.

<a id="node-e6113688d6d6369d"></a>
## upper_reset_band_escape_row_thirteen

IF row thirteen is an upper (successor-carry) transition, then its upper reset charge avoids every dyadic danger band: the successor remainder seamIntegerGreedyRemainder 14 is exactly 392 (kernel-decided), the main boundary has margin 392, and every smaller boundary lies above the remainder. The corpus does not decide whether row thirteen actually is an upper transition.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Overclaim corrected on adversarial review: the earlier canonical statement called row thirteen 'the single non-late upper row', but the Lean theorem takes hcarry : (seamAdjacentCut 13 _).successorCarries as an unproved hypothesis. The corpus proves only that row thirteen has a false terminal (terminal_false_thirteen), i.e. that it is upper OR middle, and that 13 <= seamIntegerGreedyRemainder 13 rules out the row-small case, not the middle case. No declaration anywhere in Erdos249257 establishes (seamAdjacentCut 13 _).successorCarries. If row thirteen is a middle transition this certificate is vacuous. The computation itself (remainder 14 = 392) is unconditional.

- Lean declaration: [seamUpperResetDyadicBandEscape_at_thirteen](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4547)

- outgoing **finite_instance_of**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). Verifies the unproved band hypothesis at the single row d = 13.
- outgoing **specialises**: [Z13::upper_reset_band_escape_rows_13_to_30](BROWSER_Z13_2.md#node-f9a0ade9be7e30ef). `seamUpperResetDyadicBandEscape_at_thirteen` (HalfCylinderMiddleCarryLowerBound.lean:3512) is the d = 13 instance of `seamUpperResetDyadicBandEscape_through_thirty` (HalfCylinderUpperResetBandCertificates.lean:78): identical conclusion for all j <= d, with d fixed to 13.

<a id="node-5f0b5ebcc8e203ed"></a>
## upper_reset_dyadic_band_geometry

On an upper branch, the reset charge avoiding a linear-width band below a dyadic power is equivalent to the successor remainder avoiding the translated band above the complementary dyadic boundary; and a quarter-scale exclusion for the adjacent overshoot is sufficient for the full reset-charge exclusion, with the linear pulse loss paid explicitly.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamUpperReset_band_iff_successorRemainder_avoids](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4469)
- Lean declaration: [seamUpperReset_band_of_overshoot_band](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4514)

- outgoing **implies**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). Reduces the band hypothesis to a quarter-scale overshoot exclusion with explicit linear pulse loss.

<a id="node-e0ae925f8e970c59"></a>
## upper_reset_right_run_exact_cylinder

An upper reset satisfies next remainder plus reset charge equals 2^(d+1) exactly, and a right step satisfies next remainder plus 2^(s+1) plus below pulse plus 4 equals 4 times the current remainder. Iterating gives the exact dyadic cylinder identity: remainder after k right steps plus 4^k times the reset charge plus the accumulated affine right-run charge equals 2^(d+k+1). The same base-four iteration gives the exact signed-excess iterates along an eventual right tail and after a middle landing.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Mixed conditioning. seamUpperThenRightRun_exactCylinder and the length bound depend only on a finite, explicitly listed right run after an upper reset, so they are unconditional facts about whatever the seam does; but eventualRightTail_excess_exactIterate, middleThenAllRight_excess_exactIterate and eventualRightTail_charge_lt_scaledInitialExcess assume the unproved all-right tail and are vacuous without it.

- Lean declaration: [eventualRightTail_excess_exactIterate](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3361)
- Lean declaration: [middleThenAllRight_excess_exactIterate](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3398)
- Lean declaration: [eventualRightTail_charge_lt_scaledInitialExcess](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3451)
- Lean declaration: [seamUpperThenRightRun_exactCylinder](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3602)

- outgoing **implies**: [Z14::row_small_endpoint_reverse_classification](BROWSER_Z14_1.md#node-4b8cbfe162ed4daf). The exact dyadic cylinder identity is what turns row-smallness into a charge window.
- incoming **specialises**: [Z14::upper_reset_right_run_length_bound](BROWSER_Z14_2.md#node-373834cf72ead61a). Immediate consequence of the same cylinder identity.

<a id="node-373834cf72ead61a"></a>
## upper_reset_right_run_length_bound

An upper reset cannot be followed by more right steps than its reset row index: the reset charge is at least four, so a run longer than d would make its 4^k dilate exceed the dyadic capacity 2^(d+k+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamUpperThenRightRun_length_le_resetRow](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3626)

- outgoing **specialises**: [Z14::upper_reset_right_run_exact_cylinder](BROWSER_Z14_2.md#node-e0ae925f8e970c59). Immediate consequence of the same cylinder identity.

