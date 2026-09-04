# Z56_1: Global Boolean-Mobius repair: frozen coordinates, open feasibility, and endpoint approximation

[All problems and zones](BROWSER.md)

<a id="node-8a03e92381df5a36"></a>
## endpoint_exponential_bound_is_the_named_open_uniform_producer

OPEN PREDICATE: GlobalEndpointExponentialBound T requires, uniformly for every n >= 2, the lower-support inequality 2^(endpointDivisorContribution D n - 1) - 1 <= localBinarySuffix D 1 (n - 1), where D = globalRepairLowerSupport T.bit n.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition is Lean-checked, but the uniform inequality is not proved or promoted from finite observations. It is only one clause of the larger feasibility package.

Open hypotheses: ["A proof that the displayed endpoint inequality holds for one trajectory T at every endpoint n >= 2; the module defines this obligation but proves no such uniform inhabitant."]

- Lean declaration: [GlobalEndpointExponentialBound](../../Erdos249257/BooleanMobiusGlobalRepair.lean#L139)

- incoming **depends_on_open**: [Z56::global_repair_feasibility_is_a_four_clause_open_receipt_bundle](BROWSER_Z56_1.md#node-aab10982e5b18d16). The exponential bound is literally the first conjunct of feasibility, and none of the other three clauses discharges it.

<a id="node-0c2cdd132db08dfe"></a>
## exact_endpoint_quotient_gives_an_explicit_half_error_bound

PROVED QUANTITATIVE ESTIMATE: if n >= 2, every d in D lies in [2,n], and localPrefixQuotient D n = 2^(n-1)-1, then the real absolute difference between localMersennePrefixValue D and 1/2 is at most (n+1)/2^n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The exact quotient is a theorem hypothesis. The result proves neither a supply of exact rows nor coherence, monotonicity, convergence, or membership of 1/2; rows may overshoot or undershoot.

- Lean declaration: [abs_localMersennePrefixValue_sub_half_le](../../Erdos249257/BooleanMobiusGlobalRepair.lean#L243)

- outgoing **complements**: [Z56::global_repair_feasibility_is_a_four_clause_open_receipt_bundle](BROWSER_Z56_1.md#node-aab10982e5b18d16). The approximation theorem is independent and local; feasibility's fourth clause supplies its exact-quotient hypothesis when instantiated on a stage support.

<a id="node-aab10982e5b18d16"></a>
## global_repair_feasibility_is_a_four_clause_open_receipt_bundle

OPEN FEASIBILITY PACKAGE: GlobalBooleanMobiusRepairFeasible T is the conjunction of the endpoint exponential bound, exact signed-dyadic realization of every upper word, the upper-word capacity inequality, and localPrefixQuotient (globalRepairStageSupport T.bit n) n = 2^(n-1)-1 for every n >= 2.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Defining the package does not prove that such a trajectory exists. It is a sufficient fallback interface, not an equivalence with Erdos #257 and not a proved counterexample.

Open hypotheses: ["A trajectory T satisfying GlobalEndpointExponentialBound T.", "Uniform proofs of the word-value, capacity, and exact-quotient clauses for the same trajectory T."]

- Lean declaration: [GlobalBooleanMobiusRepairFeasible](../../Erdos249257/BooleanMobiusGlobalRepair.lean#L174)

- outgoing **depends_on_open**: [Z56::endpoint_exponential_bound_is_the_named_open_uniform_producer](BROWSER_Z56_1.md#node-8a03e92381df5a36). The exponential bound is literally the first conjunct of feasibility, and none of the other three clauses discharges it.
- outgoing **complements**: [Z56::repair_trajectory_coordinates_freeze_at_their_double_endpoint](BROWSER_Z56_1.md#node-35738ad30dae5c36). Coordinate freezing is automatic structural information carried by any trajectory, while feasibility adds the unresolved arithmetic receipts.
- incoming **complements**: [Z56::exact_endpoint_quotient_gives_an_explicit_half_error_bound](BROWSER_Z56_1.md#node-0c2cdd132db08dfe). The approximation theorem is independent and local; feasibility's fourth clause supplies its exact-quotient hypothesis when instantiated on a stage support.

<a id="node-35738ad30dae5c36"></a>
## repair_trajectory_coordinates_freeze_at_their_double_endpoint

PROVED STRUCTURAL INVARIANT: for every repair trajectory T, coordinate d, and endpoint n, if 2*d <= n, then T.bit n d = T.bit (2*d) d.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem proves stability for any supplied trajectory. It does not construct a trajectory satisfying an arithmetic receipt or the feasibility predicate.

- Lean declaration: [BooleanMobiusGlobalRepairTrajectory.bit_stable](../../Erdos249257/BooleanMobiusGlobalRepair.lean#L82)

- incoming **complements**: [Z56::global_repair_feasibility_is_a_four_clause_open_receipt_bundle](BROWSER_Z56_1.md#node-aab10982e5b18d16). Coordinate freezing is automatic structural information carried by any trajectory, while feasibility adds the unresolved arithmetic receipts.

