# Z60_1: Endpoint-six countermodel for double-or-recycle cofinality

[All problems and zones](BROWSER.md)

<a id="node-6dfcc6a8bf07f902"></a>
## bounded_double_or_recycle_model_is_the_endpoint_six_singleton

boundedDoubleOrRecycleModel n holds exactly when n=6. It is a free-standing one-point model, not the predicate of actual exact local Mersenne half rows.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The auxiliary predicate is not ExactLocalMersenneHalfRow and asserts nothing about the actual seam.

- Lean declaration: [boundedDoubleOrRecycleModel](../../Erdos249257/BooleanMobiusExactRowDichotomy.lean#L58)

- incoming **generated_by**: [Z60::endpoint_six_singleton_satisfies_the_double_or_recycle_transition](BROWSER_Z60_1.md#node-89905c51c2356827). Unfolding the singleton definition reduces the transition to the fixed recycle witness c=4.
- incoming **generated_by**: [Z60::endpoint_six_singleton_is_not_cofinal](BROWSER_Z60_1.md#node-07d21b3d366d1734). The predicate's support is the bounded singleton {6}.

<a id="node-07d21b3d366d1734"></a>
## endpoint_six_singleton_is_not_cofinal

The endpoint-six singleton model is not cofinal: it is false that for every N there exists n≥N with P(n). The witness threshold N=7 contradicts P(n) iff n=6.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Noncofinality of this auxiliary predicate does not prove actual exact rows noncofinal. It refutes only inference from the abstract seeded transition shape alone and leaves strict-progress or independent arithmetic cofinality inputs available.

- Lean declaration: [boundedDoubleOrRecycleModel_not_cofinal](../../Erdos249257/BooleanMobiusExactRowDichotomy.lean#L79)

- outgoing **generated_by**: [Z60::bounded_double_or_recycle_model_is_the_endpoint_six_singleton](BROWSER_Z60_1.md#node-6dfcc6a8bf07f902). The predicate's support is the bounded singleton {6}.
- outgoing **barrier_for**: [Z60::endpoint_six_singleton_satisfies_the_double_or_recycle_transition](BROWSER_Z60_1.md#node-89905c51c2356827). A seeded predicate can obey this transition forever while remaining bounded, so the transition shape alone does not force endpoint growth.

<a id="node-89905c51c2356827"></a>
## endpoint_six_singleton_satisfies_the_double_or_recycle_transition

For n≥6, if the singleton model P holds at n, then P(2n-1) or there exists c with 4≤c≤n and P(2c-2). Since P(n) forces n=6, the proof takes the recycle branch c=4 and returns to endpoint 6.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem concerns only the auxiliary singleton predicate. It neither reformulates nor refutes the actual exact-row transition theorem.

- Lean declaration: [boundedDoubleOrRecycleModel_transition](../../Erdos249257/BooleanMobiusExactRowDichotomy.lean#L64)

- outgoing **generated_by**: [Z60::bounded_double_or_recycle_model_is_the_endpoint_six_singleton](BROWSER_Z60_1.md#node-6dfcc6a8bf07f902). Unfolding the singleton definition reduces the transition to the fixed recycle witness c=4.
- incoming **barrier_for**: [Z60::endpoint_six_singleton_is_not_cofinal](BROWSER_Z60_1.md#node-07d21b3d366d1734). A seeded predicate can obey this transition forever while remaining bounded, so the transition shape alone does not force endpoint growth.

