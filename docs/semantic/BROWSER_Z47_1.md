# Z47_1: Canonical critical-capacity sockets, fixed-horizon margin form, and protected-row state

[All problems and zones](BROWSER.md)

<a id="node-1795f3a67d95be76"></a>
## actual_skipped_orbit_critical_quotient_socket

HalfGreedySkippedCriticalQuotientSupply is the open critical quotient lower bound restricted to ranks actually skipped by the rational half-greedy orbit.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The predicate is not proved. Its equivalence with the universal socket does not establish either side.

Open hypotheses: ["HalfGreedySkippedCriticalQuotientSupply"]

- Lean declaration: [HalfGreedySkippedCriticalQuotientSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L178)

- outgoing **equivalent_to**: [Z47::universal_crossing_core_critical_quotient_socket](BROWSER_Z47_1.md#node-7ad9e48860a98913). The existing theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped proves the two sockets equivalent after canonical-core reduction.
- incoming **complements**: [Z47::critical_crossing_core_is_the_canonical_half_greedy_prefix](BROWSER_Z47_1.md#node-b5378148bc6b6e0b). Crossing-core uniqueness explains why the universal finite-core socket reduces to the canonical half-greedy orbit.
- incoming **complements**: [Z47::every_finite_half_greedy_prefix_is_strictly_below_half](BROWSER_Z47_1.md#node-ec16e78b75a11d7f). Strict below-halfness makes the canonical prefix's below-half premise automatic in the reduction.
- incoming **implies**: [Z47::precritical_suffix_supply_feeds_skipped_critical_quotient_supply](BROWSER_Z47_1.md#node-68152bc677dfbaf5). The exact conclusion of the transport theorem is HalfGreedySkippedCriticalQuotientSupply.

<a id="node-b5378148bc6b6e0b"></a>
## critical_crossing_core_is_the_canonical_half_greedy_prefix

Every finite support below rank c satisfying the exact below-half and crossing-deficit hypotheses is equal to halfGreedyPrefixSupport (c-1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Uniqueness collapses the core search space but proves no critical quotient inequality and no half-membership.

- Lean declaration: [eq_halfGreedyPrefixSupport_of_critical_crossing](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50)

- outgoing **complements**: [Z47::actual_skipped_orbit_critical_quotient_socket](BROWSER_Z47_1.md#node-1795f3a67d95be76). Crossing-core uniqueness explains why the universal finite-core socket reduces to the canonical half-greedy orbit.

<a id="node-ec16e78b75a11d7f"></a>
## every_finite_half_greedy_prefix_is_strictly_below_half

For every n, the rational Mersenne value of halfGreedyPrefixSupport n is strictly below one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Strict finite-prefix inequality does not imply convergence to one half or achievement-set membership.

- Lean declaration: [localMersennePrefixValue_halfGreedy_lt_half](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L138)

- outgoing **complements**: [Z47::actual_skipped_orbit_critical_quotient_socket](BROWSER_Z47_1.md#node-1795f3a67d95be76). Strict below-halfness makes the canonical prefix's below-half premise automatic in the reduction.

<a id="node-fb6f1025c53634d0"></a>
## pre_take_precritical_suffix_socket

HalfGreedyPreTakePrecriticalSuffixSupply requires that at every skipped rank c at least six immediately followed by a take, the predecessor suffix at endpoint 2c-3 fits in c-3 bits.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Defining the property does not assert it and does not assert that skip-then-take ranks occur cofinally.

Open hypotheses: ["HalfGreedyPreTakePrecriticalSuffixSupply"]

- Lean declaration: [HalfGreedyPreTakePrecriticalSuffixSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L200)

- incoming **reformulates**: [Z47::precritical_suffix_bound_is_fixed_horizon_frozen_margin_nonnegativity](BROWSER_Z47_1.md#node-fc1a7ca408713167). The fixed-horizon frozen-margin inequality is the exact coordinate form of the precritical suffix bound required at pre-take skipped ranks.
- incoming **depends_on_open**: [Z47::precritical_suffix_supply_feeds_skipped_critical_quotient_supply](BROWSER_Z47_1.md#node-68152bc677dfbaf5). The existing pre-take equivalence identifies the global skipped suffix supply consumed by the theorem with the pre-take socket.

<a id="node-fc1a7ca408713167"></a>
## precritical_suffix_bound_is_fixed_horizon_frozen_margin_nonnegativity

For c at least four, the endpoint-(2c-3) half-greedy prefix suffix fits in c-3 bits if and only if greedyHalfFrozenMargin (c-1) (c-3) is nonnegative.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The equivalence proves neither side and is fixed-horizon rather than eventual first passage.

- Lean declaration: [halfGreedy_precriticalSuffix_lt_iff_frozenMargin_nonneg](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L866)

- outgoing **reformulates**: [Z47::pre_take_precritical_suffix_socket](BROWSER_Z47_1.md#node-fb6f1025c53634d0). The fixed-horizon frozen-margin inequality is the exact coordinate form of the precritical suffix bound required at pre-take skipped ranks.

<a id="node-68152bc677dfbaf5"></a>
## precritical_suffix_supply_feeds_skipped_critical_quotient_supply

The global half-greedy skipped precritical suffix supply implies HalfGreedySkippedCriticalQuotientSupply by advancing the exact endpoint recurrence once.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem transports an unproved supply and establishes neither supply unconditionally.

Open hypotheses: ["HalfGreedySkippedPrecriticalSuffixSupply"]

- Lean declaration: [halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1001)

- outgoing **depends_on_open**: [Z47::pre_take_precritical_suffix_socket](BROWSER_Z47_1.md#node-fb6f1025c53634d0). The existing pre-take equivalence identifies the global skipped suffix supply consumed by the theorem with the pre-take socket.
- outgoing **implies**: [Z47::actual_skipped_orbit_critical_quotient_socket](BROWSER_Z47_1.md#node-1795f3a67d95be76). The exact conclusion of the transport theorem is HalfGreedySkippedCriticalQuotientSupply.

<a id="node-15ca89ba89e5cc03"></a>
## protected_exact_row_records_strict_progress_invariants

ProtectedExactLocalMersenneRow is the structured exact-row state carrying a below-half protected core, support separation above its cutoff, endpoint bounds, the exact quotient identity, and rank-two membership.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Declaring the structure proves neither arbitrarily many protected rows nor a successor; those consumers remain in Z29.

- Lean declaration: [ProtectedExactLocalMersenneRow](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1087)

- outgoing **complements**: [Z47::universal_crossing_core_critical_quotient_socket](BROWSER_Z47_1.md#node-7ad9e48860a98913). The protected-row structure is the consumer state whose conditional successor uses the universal critical supply; the structure itself proves no such supply.

<a id="node-7ad9e48860a98913"></a>
## universal_crossing_core_critical_quotient_socket

SkippedCoreCriticalQuotientSupply is the open universal property requiring every finite below-half crossing core to reach the endpoint-(2c-2) integral half target after inserting the crossing rank c.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The property is defined, not proved; the completed consumer chain does not discharge it.

Open hypotheses: ["SkippedCoreCriticalQuotientSupply"]

- Lean declaration: [SkippedCoreCriticalQuotientSupply](../../Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L30)

- incoming **equivalent_to**: [Z47::actual_skipped_orbit_critical_quotient_socket](BROWSER_Z47_1.md#node-1795f3a67d95be76). The existing theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped proves the two sockets equivalent after canonical-core reduction.
- incoming **complements**: [Z47::protected_exact_row_records_strict_progress_invariants](BROWSER_Z47_1.md#node-15ca89ba89e5cc03). The protected-row structure is the consumer state whose conditional successor uses the universal critical supply; the structure itself proves no such supply.

