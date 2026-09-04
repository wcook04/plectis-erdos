# Z44_1: Three-channel Mersenne tail bound and sharp single-skip fatal-gap criterion

[All problems and zones](BROWSER.md)

<a id="node-786a64d2f477df63"></a>
## actual_mersenne_tail_strictly_dominates_three_channel_bound

For every k, mersenneTailLB3 k is strictly smaller than the actual Mersenne tail mersenneTail k.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Dominating the auxiliary bound does not control the actual greedy residual.

- Lean declaration: [mersenneTailLB3_lt_mersenneTail](../../Erdos249257/HalfGreedyFatalGap.lean#L216)

- outgoing **complements**: [Z44::three_channel_mersenne_tail_bound_representation](BROWSER_Z44_1.md#node-a55245ae7e9988c3). The theorem validates the represented expression as a strict lower bound for the actual infinite tail.

<a id="node-f3d3c1c1ff8d85b3"></a>
## fatality_above_the_bound_forces_strict_two_thirds_region

If mersenneTailLB3 k<=T<u/(2L) under the positive represented decomposition, then 3a<2u.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The strict two-thirds region is necessary under the displayed fatality hypotheses, not sufficient and not known to occur.

- Lean declaration: [three_mul_lt_two_mul_of_fatal](../../Erdos249257/HalfGreedyFatalGap.lean#L146)

- outgoing **complements**: [Z44::two_thirds_margin_certifies_three_channel_skip_safety](BROWSER_Z44_1.md#node-18038be82701ab1b). Under mersenneTailLB3 k<=T, fatality forces the strict complement 3a<2u of the safe two-thirds region.
- incoming **implies**: [Z44::fatality_forces_numerator_at_least_two](BROWSER_Z44_1.md#node-6f4fbebda6fbb6d6). The strict fatal-region inequality and positivity exclude the unit numerator.

<a id="node-6f4fbebda6fbb6d6"></a>
## fatality_forces_numerator_at_least_two

The same fatality hypotheses force the numerator u to be at least two.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: It does not exclude any fatal numerator u>=2.

- Lean declaration: [two_le_of_fatal](../../Erdos249257/HalfGreedyFatalGap.lean#L161)

- outgoing **implies**: [Z44::fatality_above_the_bound_forces_strict_two_thirds_region](BROWSER_Z44_1.md#node-f3d3c1c1ff8d85b3). The strict fatal-region inequality and positivity exclude the unit numerator.
- incoming **specialises**: [Z44::odd_fatal_numerator_is_at_least_three](BROWSER_Z44_1.md#node-e516979674388bc0). Oddness sharpens the general lower bound u>=2 to u>=3.

<a id="node-e516979674388bc0"></a>
## odd_fatal_numerator_is_at_least_three

If the fatal numerator is odd, the same fatality hypotheses force u to be at least three.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Oddness is load-bearing; the theorem makes no assertion without it.

- Lean declaration: [three_le_of_fatal_of_odd](../../Erdos249257/HalfGreedyFatalGap.lean#L173)

- outgoing **specialises**: [Z44::fatality_forces_numerator_at_least_two](BROWSER_Z44_1.md#node-6f4fbebda6fbb6d6). Oddness sharpens the general lower bound u>=2 to u>=3.

<a id="node-687264757a7f7b5c"></a>
## sharp_safety_strictly_contains_dyadic_safety

The dyadic margin u<=a implies the sharper two-thirds margin 2u<=3a, and the latter implication is strict for an explicit existential pair.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Strict containment of sufficient arithmetic criteria is not equivalence with actual greedy survival.

- Lean declaration: [sharp_of_dyadic](../../Erdos249257/HalfGreedyFatalGap.lean#L197)
- Lean declaration: [sharp_strictly_stronger](../../Erdos249257/HalfGreedyFatalGap.lean#L200)

- outgoing **complements**: [Z44::two_thirds_margin_certifies_three_channel_skip_safety](BROWSER_Z44_1.md#node-18038be82701ab1b). The comparison node classifies the sharp hypothesis used by the safety theorem against the stronger dyadic sufficient condition.

<a id="node-adcffb5fd31a61c6"></a>
## three_channel_bound_exceeds_two_thirds_threshold

For every k at least one, 3/(3*2^k-1) is strictly smaller than mersenneTailLB3 k.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The comparison contains no greedy-orbit or achievement-set conclusion.

- Lean declaration: [three_div_lt_mersenneTailLB3](../../Erdos249257/HalfGreedyFatalGap.lean#L70)

- outgoing **generated_by**: [Z44::three_channel_mersenne_tail_bound_representation](BROWSER_Z44_1.md#node-a55245ae7e9988c3). The threshold theorem is the fundamental rational comparison proved from the explicit three-channel expression.
- incoming **generated_by**: [Z44::two_thirds_margin_certifies_three_channel_skip_safety](BROWSER_Z44_1.md#node-18038be82701ab1b). The represented decomposition and 2u<=3a reduce the skip fraction to the threshold dominated by the three-channel bound.

<a id="node-a55245ae7e9988c3"></a>
## three_channel_mersenne_tail_bound_representation

The quantity mersenneTailLB3 k is the explicit three-channel rational lower-bound expression used to compare represented greedy-skip fractions with the Mersenne tail.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition alone proves no inequality against the actual Mersenne tail and says nothing about the greedy orbit.

- Lean declaration: [mersenneTailLB3](../../Erdos249257/HalfGreedyFatalGap.lean#L56)

- incoming **generated_by**: [Z44::three_channel_bound_exceeds_two_thirds_threshold](BROWSER_Z44_1.md#node-adcffb5fd31a61c6). The threshold theorem is the fundamental rational comparison proved from the explicit three-channel expression.
- incoming **complements**: [Z44::actual_mersenne_tail_strictly_dominates_three_channel_bound](BROWSER_Z44_1.md#node-786a64d2f477df63). The theorem validates the represented expression as a strict lower bound for the actual infinite tail.

<a id="node-be6b5ee179ee1d9b"></a>
## two_thirds_margin_certifies_actual_tail_skip_safety

For the positive represented decomposition, 2u<=3a implies u/(2L)<mersenneTail k.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem is sufficient at one represented skip and gives no universal orbit avoidance.

- Lean declaration: [skipSafe_actualTail_of_two_mul_le_three_mul](../../Erdos249257/HalfGreedyFatalGap.lean#L235)

- outgoing **transport_of**: [Z44::two_thirds_margin_certifies_three_channel_skip_safety](BROWSER_Z44_1.md#node-18038be82701ab1b). The three-channel inequality transports to the actual tail through mersenneTailLB3 k<mersenneTail k.
- incoming **specialises**: [Z44::unit_numerator_is_actual_tail_safe](BROWSER_Z44_1.md#node-04523fb321c421ab). The actual-tail unit theorem is the u=1 specialization of the actual-tail two-thirds criterion.

<a id="node-18038be82701ab1b"></a>
## two_thirds_margin_certifies_three_channel_skip_safety

For positive k,u,a,L satisfying 2^k*u+a=2L+u, the arithmetic margin 2u<=3a implies u/(2L)<mersenneTailLB3 k.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is a sufficient single-rank criterion, not a necessary condition and not an orbit-wide producer.

- Lean declaration: [skipSafe_of_two_mul_le_three_mul](../../Erdos249257/HalfGreedyFatalGap.lean#L107)

- outgoing **generated_by**: [Z44::three_channel_bound_exceeds_two_thirds_threshold](BROWSER_Z44_1.md#node-adcffb5fd31a61c6). The represented decomposition and 2u<=3a reduce the skip fraction to the threshold dominated by the three-channel bound.
- incoming **specialises**: [Z44::unit_numerator_is_three_channel_safe](BROWSER_Z44_1.md#node-7e739f4328d6cd74). The unit-numerator theorem is the u=1 instance of the two-thirds safety criterion.
- incoming **complements**: [Z44::fatality_above_the_bound_forces_strict_two_thirds_region](BROWSER_Z44_1.md#node-f3d3c1c1ff8d85b3). Under mersenneTailLB3 k<=T, fatality forces the strict complement 3a<2u of the safe two-thirds region.
- incoming **complements**: [Z44::sharp_safety_strictly_contains_dyadic_safety](BROWSER_Z44_1.md#node-687264757a7f7b5c). The comparison node classifies the sharp hypothesis used by the safety theorem against the stronger dyadic sufficient condition.
- incoming **transport_of**: [Z44::two_thirds_margin_certifies_actual_tail_skip_safety](BROWSER_Z44_1.md#node-be6b5ee179ee1d9b). The three-channel inequality transports to the actual tail through mersenneTailLB3 k<mersenneTail k.

<a id="node-04523fb321c421ab"></a>
## unit_numerator_is_actual_tail_safe

Under the positive unit-numerator decomposition, 1/(2L) is strictly below the actual Mersenne tail.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: It does not prove that all actual skips have unit numerator.

- Lean declaration: [unitNumerator_skipSafe_actualTail](../../Erdos249257/HalfGreedyFatalGap.lean#L246)

- outgoing **transport_of**: [Z44::unit_numerator_is_three_channel_safe](BROWSER_Z44_1.md#node-7e739f4328d6cd74). The unit-numerator three-channel bound transports through the strict lower bound for the actual tail.
- outgoing **specialises**: [Z44::two_thirds_margin_certifies_actual_tail_skip_safety](BROWSER_Z44_1.md#node-be6b5ee179ee1d9b). The actual-tail unit theorem is the u=1 specialization of the actual-tail two-thirds criterion.

<a id="node-7e739f4328d6cd74"></a>
## unit_numerator_is_three_channel_safe

Under the positive represented decomposition with numerator one, 1/(2L) is strictly below mersenneTailLB3 k.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The conclusion concerns only the auxiliary three-channel bound.

- Lean declaration: [unitNumerator_skipSafe](../../Erdos249257/HalfGreedyFatalGap.lean#L135)

- outgoing **specialises**: [Z44::two_thirds_margin_certifies_three_channel_skip_safety](BROWSER_Z44_1.md#node-18038be82701ab1b). The unit-numerator theorem is the u=1 instance of the two-thirds safety criterion.
- incoming **transport_of**: [Z44::unit_numerator_is_actual_tail_safe](BROWSER_Z44_1.md#node-04523fb321c421ab). The unit-numerator three-channel bound transports through the strict lower bound for the actual tail.

