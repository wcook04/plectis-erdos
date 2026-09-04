# Z65_1: Erdős #257 rational-half counterexample frontier

[All problems and zones](BROWSER.md)

<a id="node-44b4b1c0c47b2898"></a>
## one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two

For every finite set F of ranks all at least two, finiteErdosSum F 2 is not equal to 1/21.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem proves only that a 1/21 representation cannot terminate. It neither constructs an infinite representation nor proves that 1/21 belongs to the Mersenne achievement set, so it does not refute Erdős #257.

- Lean declaration: [finiteErdosSum_ne_one_div_twenty_one](../../ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L61)

- outgoing **complements**: [Z65::universal_mersenne_subseries_irrationality_is_the_erdos_257_assertion](BROWSER_Z65_1.md#node-f3b275f9978e8fd6). The theorem removes the finite-support loophole for one rational target but leaves both achievement-set membership and the universal assertion open.
- incoming **complements**: [Z65::primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity](BROWSER_Z65_1.md#node-4dcb4cb9c5b0afde). The finite-support obstruction shows what a successful 1/21 route must achieve, while the recurring primitive collisions identify the unresolved Booleanisation obstacle.

<a id="node-48880fc88558fa32"></a>
## primitive_23_cone_covers_every_rank_from_eleven

Every natural number n at least eleven has a positive coprime representation n=2p+3q.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Eventual rank coverage is not Booleanisation. It supplies primitive witnesses but does not show that the resulting multiplicities are all zero or one.

- Lean declaration: [exists_primitive23_solution_of_eleven_le](../../Erdos249257/Primitive23Multiplicity.lean#L52)

- outgoing **generated_by**: [Z65::primitive_23_solution_is_a_positive_coprime_rank_decomposition](BROWSER_Z65_1.md#node-ec1808e6c0a88873). The coverage theorem constructs explicit witnesses satisfying the primitive-rank definition.

<a id="node-4dcb4cb9c5b0afde"></a>
## primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity

The primitive 2p+3q cone has no witness at rank ten, already has two distinct witnesses at rank eleven, and has at least two distinct witnesses at every rank 10k with k at least two.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The recurring collisions diagnose why the primitive expansion is not already Boolean. They do not provide the cancellations or carry recurrence required to construct a zero-one support.

- Lean declaration: [no_primitive23_solution_ten](../../Erdos249257/Primitive23Multiplicity.lean#L26)
- Lean declaration: [exists_two_primitive23_solutions_eleven](../../Erdos249257/Primitive23Multiplicity.lean#L38)
- Lean declaration: [exists_two_primitive23_solutions_mul_ten](../../Erdos249257/Primitive23Multiplicity.lean#L86)

- outgoing **generated_by**: [Z65::primitive_23_solution_is_a_positive_coprime_rank_decomposition](BROWSER_Z65_1.md#node-ec1808e6c0a88873). The defect and collision theorems are exact instance and infinite-family results for the same primitive-rank definition.
- outgoing **complements**: [Z65::one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two](BROWSER_Z65_1.md#node-44b4b1c0c47b2898). The finite-support obstruction shows what a successful 1/21 route must achieve, while the recurring primitive collisions identify the unresolved Booleanisation obstacle.

<a id="node-ec1808e6c0a88873"></a>
## primitive_23_solution_is_a_positive_coprime_rank_decomposition

IsPrimitive23Solution n p q means that p and q are positive and coprime and satisfy 2p+3q=n.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition records rank multiplicity only. It does not identify a reciprocal-Mersenne coefficient or prove an expansion identity.

- Lean declaration: [IsPrimitive23Solution](../../Erdos249257/Primitive23Multiplicity.lean#L20)

- incoming **generated_by**: [Z65::primitive_23_cone_covers_every_rank_from_eleven](BROWSER_Z65_1.md#node-48880fc88558fa32). The coverage theorem constructs explicit witnesses satisfying the primitive-rank definition.
- incoming **generated_by**: [Z65::primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity](BROWSER_Z65_1.md#node-4dcb4cb9c5b0afde). The defect and collision theorems are exact instance and infinite-family results for the same primitive-rank definition.

<a id="node-42dea3a7f7d955dd"></a>
## terminal_scaled_vanishing_refutes_universal_mersenne_subseries_irrationality

Every HalfTerminalOnlyScaledVanishingSequence negates UniversalMersenneSubseriesIrrationality by supplying an infinite support whose series is the rational number one half.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem is conditional and does not disprove Erdős #257 without the unproved producer sequence. It adds no stronger producer than the Z12 terminal-scaled-vanishing route.

Open hypotheses: ["S : HalfTerminalOnlyScaledVanishingSequence"]

- Lean declaration: [not_universal_of_terminalScaledVanishing](../../ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L39)

- outgoing **generated_by**: [Z65::terminal_scaled_vanishing_supplies_an_infinite_exact_half_support](BROWSER_Z65_1.md#node-53fc7954e8eb2b9a). The proof obtains the infinite exact-half support from the preceding theorem and applies the rationality of one half.
- outgoing **complements**: [Z65::universal_mersenne_subseries_irrationality_is_the_erdos_257_assertion](BROWSER_Z65_1.md#node-f3b275f9978e8fd6). The conclusion is exactly the negation of the universal predicate represented by the definition.

<a id="node-53fc7954e8eb2b9a"></a>
## terminal_scaled_vanishing_supplies_an_infinite_exact_half_support

Every HalfTerminalOnlyScaledVanishingSequence supplies an infinite set A with erdosSupportSeries 2 A exactly equal to one half.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: No scaled-vanishing sequence is constructed. Finite cutoff checks do not discharge the antecedent or supply an infinite counterexample.

Open hypotheses: ["S : HalfTerminalOnlyScaledVanishingSequence"]

- Lean declaration: [exists_rational_half_counterexample_of_terminalScaledVanishing](../../ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L31)

- outgoing **complements**: [Z65::universal_mersenne_subseries_irrationality_is_the_erdos_257_assertion](BROWSER_Z65_1.md#node-f3b275f9978e8fd6). The exact rational half support is the counterexample object needed to negate the universal assertion, but it remains conditional on the open producer.
- incoming **generated_by**: [Z65::terminal_scaled_vanishing_refutes_universal_mersenne_subseries_irrationality](BROWSER_Z65_1.md#node-42dea3a7f7d955dd). The proof obtains the infinite exact-half support from the preceding theorem and applies the rationality of one half.

<a id="node-f3b275f9978e8fd6"></a>
## universal_mersenne_subseries_irrationality_is_the_erdos_257_assertion

UniversalMersenneSubseriesIrrationality means that for every infinite set A of natural numbers, erdosSupportSeries 2 A is irrational.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is a definition, not a proof or disproof of the universal assertion.

Open hypotheses: ["UniversalMersenneSubseriesIrrationality, the unresolved universal assertion of Erdős #257"]

- Lean declaration: [UniversalMersenneSubseriesIrrationality](../../ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L26)

- incoming **complements**: [Z65::terminal_scaled_vanishing_supplies_an_infinite_exact_half_support](BROWSER_Z65_1.md#node-53fc7954e8eb2b9a). The exact rational half support is the counterexample object needed to negate the universal assertion, but it remains conditional on the open producer.
- incoming **complements**: [Z65::terminal_scaled_vanishing_refutes_universal_mersenne_subseries_irrationality](BROWSER_Z65_1.md#node-42dea3a7f7d955dd). The conclusion is exactly the negation of the universal predicate represented by the definition.
- incoming **complements**: [Z65::one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two](BROWSER_Z65_1.md#node-44b4b1c0c47b2898). The theorem removes the finite-support loophole for one rational target but leaves both achievement-set membership and the universal assertion open.

