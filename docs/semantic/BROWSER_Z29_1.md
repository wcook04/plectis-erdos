# Z29_1: Boolean–Möbius exact-row capacity and cofinality frontier

[All problems and zones](BROWSER.md)

<a id="node-6d2292350a5319ec"></a>
## above_half_support_recycles_through_first_crossing

PROVED LOCAL PRODUCER: every finite positive-rank support whose Mersenne value is above 1/2 has a first crossing rank c>=4; its strict lower prefix is below half, adding c crosses above half, and the skipped-core construction yields an exact row at endpoint 2c-2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The recycled endpoint 2c-2 need not exceed the original endpoint. The theorem is a local exact-row producer, not a cofinality or strict-progress theorem.

- Lean declaration: [exists_first_localMersenne_crossing](../../Erdos249257/BooleanMobiusExactRowCrossing.lean#L31)
- Lean declaration: [exists_skippedCoreExactRow_of_value_above](../../Erdos249257/BooleanMobiusExactRowCrossing.lean#L155)
- Lean declaration: [exactLocalMersenneHalfRow_of_first_localMersenne_crossing](../../Erdos249257/BooleanMobiusExactRowCrossing.lean#L191)

- incoming **complements**: [Z29::below_half_exact_row_has_strict_doubling_extension](BROWSER_Z29_1.md#node-715fd5e6009a0ee3). The two nodes are the below-half and above-half branches used to continue an exact row after excluding equality to one half by odd-denominator parity.
- incoming **barrier_for**: [Z29::double_or_recycle_transition_does_not_imply_cofinality](BROWSER_Z29_1.md#node-b69f8cff5348de7c). The recycling branch can return to the same endpoint scale, so the local above-half producer needs an independent strict-progress invariant.

<a id="node-715fd5e6009a0ee3"></a>
## below_half_exact_row_has_strict_doubling_extension

PROVED LOCAL PRODUCER: every exact row at endpoint n>=6 whose support contains rank 2 and has value below 1/2 admits an exact extension at endpoint 2n-1, with every newly inserted rank strictly above n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result is uniform for rows satisfying its local hypotheses, but it does not show that every exact row is below half or that the construction can be iterated without the protected-core invariant.

- Lean declaration: [exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below](../../Erdos249257/BooleanMobiusExactRowDoubling.lean#L185)
- Lean declaration: [exactLocalMersenneHalfRow_two_mul_sub_one_of_exact_below](../../Erdos249257/BooleanMobiusExactRowDoubling.lean#L296)

- outgoing **complements**: [Z29::above_half_support_recycles_through_first_crossing](BROWSER_Z29_1.md#node-6d2292350a5319ec). The two nodes are the below-half and above-half branches used to continue an exact row after excluding equality to one half by odd-denominator parity.
- incoming **barrier_for**: [Z29::double_or_recycle_transition_does_not_imply_cofinality](BROWSER_Z29_1.md#node-b69f8cff5348de7c). The bounded transition model shows that possessing the doubling/recycling transition schema is insufficient to infer unbounded endpoint growth.

<a id="node-714e71287904b9d0"></a>
## cofinal_exact_rows_force_half_membership

PROVED CONDITIONAL: if exact Boolean–Möbius quotient rows occur at arbitrarily large endpoints, their finite support values lie in the Mersenne achievement set and approach 1/2 with error at most (n+1)/2^n; closedness therefore places 1/2 in that achievement set even when the row supports are mutually incompatible.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem consumes cofinal exact rows; it does not produce them. Finite rows, or an unbounded collection without verified endpoint cofinality, do not satisfy its hypothesis and do not prove Erdős #257.

Open hypotheses: ["CofinalExactLocalMersenneHalfRows"]

- Lean declaration: [exactLocalMersenneRowValue_mem_mersenneAchievementSet](../../Erdos249257/BooleanMobiusCofinalExactRows.lean#L47)
- Lean declaration: [abs_exactLocalMersenneRowValue_sub_half_le](../../Erdos249257/BooleanMobiusCofinalExactRows.lean#L58)
- Lean declaration: [half_mem_mersenneAchievementSet_of_cofinalExactLocalRows](../../Erdos249257/BooleanMobiusCofinalExactRows.lean#L71)

- incoming **finite_instance_of**: [Z29::endpoint_six_exact_row_seed](BROWSER_Z29_1.md#node-9b3d49f76690c324). The endpoint-six support is one exact row of the kind consumed by the approximation theorem, but one finite row does not meet the cofinal quantifier.
- incoming **implies**: [Z29::critical_supply_produces_strictly_growing_rows_and_half_membership](BROWSER_Z29_1.md#node-8bff126ec6c328d8). Strict protected successors generate cofinally many exact endpoints, which satisfy the exact-row approximation consumer and yield half membership.

<a id="node-f386fe23c780e0b7"></a>
## critical_quotient_supply_collapses_to_actual_skipped_orbit

PROVED EQUIVALENCES: the universal sharp quotient inequality over all crossing finite cores is equivalent to its canonical half-greedy specialization, and that specialization is equivalent to requiring the inequality only at ranks actually skipped by the half-greedy orbit.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The quantifier collapse is exact, but the resulting actual-skipped-rank inequality is still open. It is a sharper target, not a proof of its truth or of Erdős #257.

Open hypotheses: ["SkippedCoreCriticalQuotientSupply, equivalently HalfGreedySkippedCriticalQuotientSupply"]

- Lean declaration: [halfGreedyCriticalQuotientSupply_iff_skipped](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1030)
- Lean declaration: [skippedCoreCriticalQuotientSupply_iff_halfGreedy](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1052)
- Lean declaration: [skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1068)

- incoming **implies**: [Z29::precritical_supply_has_exact_crossing_tax_and_future_skip_forms](BROWSER_Z29_1.md#node-6188571fec53e981). The predecessor endpoint recurrence lifts the precritical suffix supply to the skipped critical quotient supply, after which the universal finite-core form follows by the exact quantifier collapse.
- outgoing **reformulates**: [Z29::sharp_skipped_core_capacity_exact_normal_forms](BROWSER_Z29_1.md#node-372489c198956ce0). The global critical supply asks for the same exact local capacity inequality, but only at the canonical cores corresponding to actual skipped half-greedy ranks.

<a id="node-8bff126ec6c328d8"></a>
## critical_supply_produces_strictly_growing_rows_and_half_membership

PROVED CONDITIONAL: the critical quotient supply makes every protected exact row admit a strictly later protected successor; iterating from the endpoint-six seed gives cofinally many exact rows and hence places 1/2 in the Mersenne achievement set. It is enough, equivalently through the reduction chain, to prove the precritical suffix bound only at skipped ranks immediately followed by takes.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Both displayed global supply routes are unproved. The theorem is a complete consumer and induction architecture, not an unconditional proof that 1/2 is attainable and not a solution of the universal Erdős #257 problem.

Open hypotheses: ["SkippedCoreCriticalQuotientSupply", "or the sufficient HalfGreedyPreTakePrecriticalSuffixSupply"]

- Lean declaration: [exists_laterProtectedExactLocalMersenneRow](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1139)
- Lean declaration: [protectedExactLocalMersenneRow_endpoint_lt_next](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1275)
- Lean declaration: [cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309)
- Lean declaration: [half_mem_mersenneAchievementSet_of_criticalQuotientSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1321)
- Lean declaration: [half_mem_mersenneAchievementSet_of_preTakePrecriticalSuffixSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1330)

- outgoing **depends_on_open**: [Z29::sharp_capacity_builds_strict_upper_exact_row](BROWSER_Z29_1.md#node-c96899f02a4019f4). Each protected successor uses either strict doubling below half or a strict-upper skipped-core fill above half; the open critical supply provides the latter fill at every crossing.
- outgoing **implies**: [Z29::cofinal_exact_rows_force_half_membership](BROWSER_Z29_1.md#node-714e71287904b9d0). Strict protected successors generate cofinally many exact endpoints, which satisfy the exact-row approximation consumer and yield half membership.
- outgoing **generated_by**: [Z29::endpoint_six_exact_row_seed](BROWSER_Z29_1.md#node-9b3d49f76690c324). The protected successor orbit starts from the explicit endpoint-six exact row and grows only under the unproved global critical-capacity input.

<a id="node-b69f8cff5348de7c"></a>
## double_or_recycle_transition_does_not_imply_cofinality

PROVED BARRIER: every exact row at endpoint n>=6 has either a doubled exact row at 2n-1 or a recycled exact row at 2c-2 for some 4<=c<=n, but this transition shape plus a seed does not imply cofinality; an explicit one-point model at endpoint 6 satisfies the same transition forever and is not cofinal.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The no-go concerns inference from the transition schema alone. It does not rule out cofinality after adding the sharp capacity or protected-progress input.

- Lean declaration: [exactLocalMersenneHalfRow_double_or_recycle](../../Erdos249257/BooleanMobiusExactRowDichotomy.lean#L26)
- Lean declaration: [exists_seeded_bounded_double_or_recycle_model](../../Erdos249257/BooleanMobiusExactRowDichotomy.lean#L91)

- outgoing **barrier_for**: [Z29::below_half_exact_row_has_strict_doubling_extension](BROWSER_Z29_1.md#node-715fd5e6009a0ee3). The bounded transition model shows that possessing the doubling/recycling transition schema is insufficient to infer unbounded endpoint growth.
- outgoing **barrier_for**: [Z29::above_half_support_recycles_through_first_crossing](BROWSER_Z29_1.md#node-6d2292350a5319ec). The recycling branch can return to the same endpoint scale, so the local above-half producer needs an independent strict-progress invariant.
- incoming **repair_of**: [Z29::sharp_capacity_builds_strict_upper_exact_row](BROWSER_Z29_1.md#node-c96899f02a4019f4). Support separation from the sharp fill is the extra invariant that prevents the crossing branch from recycling at the same cutoff.

<a id="node-9b3d49f76690c324"></a>
## endpoint_six_exact_row_seed

PROVED FINITE INSTANCE: the support {2,3,6} is an exact Boolean–Möbius quotient row at endpoint 6 because its quotient contributions are 21, 9, and 1, summing to 31=2^5-1; its Mersenne support value is strictly below 1/2.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: One exact row at endpoint 6 is only a finite seed. It neither supplies arbitrarily large rows nor places 1/2 in the achievement set.

- Lean declaration: [exactRowSixSupport_bounds](../../Erdos249257/BooleanMobiusExactRowSeed.lean#L16)
- Lean declaration: [exactRowSixSupport_quotient](../../Erdos249257/BooleanMobiusExactRowSeed.lean#L22)
- Lean declaration: [exactRowSixSupport_value_lt_half](../../Erdos249257/BooleanMobiusExactRowSeed.lean#L28)
- Lean declaration: [exactLocalMersenneHalfRow_six](../../Erdos249257/BooleanMobiusExactRowSeed.lean#L34)

- outgoing **finite_instance_of**: [Z29::cofinal_exact_rows_force_half_membership](BROWSER_Z29_1.md#node-714e71287904b9d0). The endpoint-six support is one exact row of the kind consumed by the approximation theorem, but one finite row does not meet the cofinal quantifier.
- incoming **generated_by**: [Z29::critical_supply_produces_strictly_growing_rows_and_half_membership](BROWSER_Z29_1.md#node-8bff126ec6c328d8). The protected successor orbit starts from the explicit endpoint-six exact row and grows only under the unproved global critical-capacity input.

<a id="node-26f661f43e4dbbd6"></a>
## fractional_mass_one_is_sufficient_but_not_necessary

PROVED CLASSIFICATION AND BARRIER: at a genuine skipped-core crossing, a total local fractional mass at most one is sufficient for the sharp capacity, and failure of capacity forces that mass above one; however the explicit crossing D={2,3}, c=5 has mass above one while sharp capacity still holds, so this convenient residue estimate is not necessary.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The finite fixture refutes necessity only for the one-unit fractional-mass criterion. It does not refute the sharp capacity socket itself or provide a uniform alternative estimate.

- Lean declaration: [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_splitFractionMass](../../Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L136)
- Lean declaration: [one_lt_splitFractionMass_of_criticalCapacity_failure](../../Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L164)
- Lean declaration: [splitFractionMass_one_bound_not_necessary_fixture](../../Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L183)

- outgoing **specialises**: [Z29::sharp_skipped_core_capacity_exact_normal_forms](BROWSER_Z29_1.md#node-372489c198956ce0). A one-unit fractional-mass bound supplies one sufficient analytic route to the exact capacity inequality, while the finite fixture proves that this route is not an equivalence.

<a id="node-c1f191cf2ef7bdc8"></a>
## future_skip_lookahead_closes_precritical_row

PROVED LOCAL PRODUCER: at a skipped half-greedy rank c, if the next t-1 ranks are taken, rank c+t is skipped, and c-2 fits in the remaining dyadic room, then the predecessor suffix at endpoint 2c-3 fits in c-3 bits; in particular, two consecutive skipped ranks satisfy the bound for every c>=6.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem does not establish that its future-skip hypothesis occurs at every required rank. The paper audit identifies that orbit-level skip-gap supply as unproved, so this local implication is not a global or cofinal producer.

- Lean declaration: [precriticalCrossingTax_of_futureThreshold](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L472)
- Lean declaration: [halfGreedy_precriticalSuffix_lt_iff_crossingTax](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L559)
- Lean declaration: [halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L603)
- Lean declaration: [halfGreedy_precriticalSuffix_lt_of_next_skip](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L682)

- outgoing **specialises**: [Z29::precritical_supply_has_exact_crossing_tax_and_future_skip_forms](BROWSER_Z29_1.md#node-6188571fec53e981). The finite-lookahead theorem proves the precritical suffix inequality for a concrete local skip/take/skip configuration represented by the global equivalent sockets.

<a id="node-6188571fec53e981"></a>
## precritical_supply_has_exact_crossing_tax_and_future_skip_forms

PROVED EQUIVALENCES: the global precritical suffix supply is exactly the crossing-overshoot versus fractional-tax inequality, exactly first-shell future-skip coverage of the terminal Möbius-centred carry, and exactly the restriction to skipped ranks immediately followed by an actual take; consecutive skips and the finite ranks 4 and 5 are already discharged.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalent supply remains unproved. The equivalences isolate the surviving producer at a skip immediately before a take; they do not show that crossing tax, frozen margin, or future-skip coverage has the required sign.

Open hypotheses: ["HalfGreedyPreTakePrecriticalSuffixSupply"]

- Lean declaration: [halfGreedySkippedPrecriticalSuffixSupply_iff_crossingTax](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L713)
- Lean declaration: [halfGreedySkippedPrecriticalSuffixSupply_iff_preTake](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L838)
- Lean declaration: [halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L949)
- Lean declaration: [halfGreedySkippedPrecriticalSuffixSupply_iff_futureSkipCoverage](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L979)
- Lean declaration: [halfGreedySkippedPrecriticalCrossingTaxSupply_iff_futureSkipCoverage](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L992)

- incoming **specialises**: [Z29::future_skip_lookahead_closes_precritical_row](BROWSER_Z29_1.md#node-c1f191cf2ef7bdc8). The finite-lookahead theorem proves the precritical suffix inequality for a concrete local skip/take/skip configuration represented by the global equivalent sockets.
- outgoing **implies**: [Z29::critical_quotient_supply_collapses_to_actual_skipped_orbit](BROWSER_Z29_1.md#node-f386fe23c780e0b7). The predecessor endpoint recurrence lifts the precritical suffix supply to the skipped critical quotient supply, after which the universal finite-core form follows by the exact quantifier collapse.

<a id="node-c96899f02a4019f4"></a>
## sharp_capacity_builds_strict_upper_exact_row

PROVED LOCAL PRODUCER: when a skipped core satisfies the sharp c-2-bit capacity inequality, its repair can be supported strictly above c and gives an exact row at endpoint 2c-2; that separation makes the next crossing either leave a below-half row in place or occur strictly later and yield a strictly larger exact-row endpoint.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The constructor is unconditional once its local sharp-capacity premise is given, but the corpus does not supply that premise uniformly or cofinally. This theorem is therefore not a cofinal row producer by itself.

Open hypotheses: ["the sharp local suffix-capacity inequality when required uniformly at all relevant skipped cores"]

- Lean declaration: [exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity](../../Erdos249257/BooleanMobiusSkipRow.lean#L238)
- Lean declaration: [exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity](../../Erdos249257/BooleanMobiusSkipRow.lean#L332)
- Lean declaration: [skippedCoreSharpCapacity_below_or_strictly_laterExactRow](../../Erdos249257/BooleanMobiusExactRowCrossing.lean#L233)

- outgoing **depends_on_open**: [Z29::sharp_skipped_core_capacity_exact_normal_forms](BROWSER_Z29_1.md#node-372489c198956ce0). The strict-upper constructor consumes the sharp c-2-bit inequality whose quotient and geometric forms are exact; the missing global input is that this inequality holds at every relevant crossing.
- outgoing **repair_of**: [Z29::double_or_recycle_transition_does_not_imply_cofinality](BROWSER_Z29_1.md#node-b69f8cff5348de7c). Support separation from the sharp fill is the extra invariant that prevents the crossing branch from recycling at the same cutoff.
- incoming **depends_on_open**: [Z29::critical_supply_produces_strictly_growing_rows_and_half_membership](BROWSER_Z29_1.md#node-8bff126ec6c328d8). Each protected successor uses either strict doubling below half or a strict-upper skipped-core fill above half; the open critical supply provides the latter fill at every crossing.

<a id="node-372489c198956ce0"></a>
## sharp_skipped_core_capacity_exact_normal_forms

PROVED EQUIVALENCE: for every below-half core below crossing rank c>=4, fitting its endpoint-(2c-2) repair suffix in c-2 bits is equivalent to the inserted core reaching the integral half target; after expanding each Mersenne quotient, the same socket is one explicit lower bound on a finite sum of shifted powers of two.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: These equivalences remove representational ambiguity but do not prove the inequality for every crossing core or along the half-greedy orbit.

- Lean declaration: [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff](../../Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L22)
- Lean declaration: [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore](../../Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L208)

- incoming **depends_on_open**: [Z29::sharp_capacity_builds_strict_upper_exact_row](BROWSER_Z29_1.md#node-c96899f02a4019f4). The strict-upper constructor consumes the sharp c-2-bit inequality whose quotient and geometric forms are exact; the missing global input is that this inequality holds at every relevant crossing.
- incoming **specialises**: [Z29::fractional_mass_one_is_sufficient_but_not_necessary](BROWSER_Z29_1.md#node-26f661f43e4dbbd6). A one-unit fractional-mass bound supplies one sufficient analytic route to the exact capacity inequality, while the finite fixture proves that this route is not an equivalence.
- incoming **reformulates**: [Z29::critical_quotient_supply_collapses_to_actual_skipped_orbit](BROWSER_Z29_1.md#node-f386fe23c780e0b7). The global critical supply asks for the same exact local capacity inequality, but only at the canonical cores corresponding to actual skipped half-greedy ranks.

