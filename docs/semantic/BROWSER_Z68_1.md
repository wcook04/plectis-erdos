# Z68_1: Exact local Mersenne rows: producer coordinates, skipped-core transport, and the one-bit capacity boundary

[All problems and zones](BROWSER.md)

<a id="node-a58322dfa9a6481e"></a>
## a_first_crossing_core_transports_to_an_exact_even_endpoint_row

localMersenneCrossingRanks E is the set of selected ranks c whose inclusive ordered prefix already has Mersenne value above one half. More generally, whenever c >= 4 and D is supported in [2,c), has value below one half, and has deficit smaller than the rank-c Mersenne weight, D can be completed to an ExactLocalMersenneHalfRow at endpoint 2c-2.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem produces one finite exact row from one supplied crossing core. It does not prove that such cores occur cofinally, that the new endpoint exceeds any previous endpoint, or that the resulting supports are compatible.

- Lean declaration: [localMersenneCrossingRanks](../../Erdos249257/BooleanMobiusExactRowCrossing.lean#L24)
- Lean declaration: [exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore](../../Erdos249257/BooleanMobiusSkipRow.lean#L149)

- outgoing **specialises**: [Z68::exact_rows_are_floor_quotient_hits_and_cofinality_requires_no_witness_coherence](BROWSER_Z68_1.md#node-9085fc364715d1e7). The skipped-core theorem supplies an explicit family of instances of ExactLocalMersenneHalfRow, at endpoints 2c-2, from local crossing data.
- outgoing **generated_by**: [Z68::upper_half_mersenne_quotients_are_pure_binary_coins](BROWSER_Z68_1.md#node-da9b23a041dbe8dd). The exact-row adapter encodes the missing quotient as a Boolean word because every selected rank in its upper window contributes the pure coin 2^(M-d).
- outgoing **generated_by**: [Z68::skipped_cores_fit_the_loose_upper_window_but_not_the_sharp_window](BROWSER_Z68_1.md#node-f0c3929e69d10b4c). The proved c-1-bit capacity bound ensures that the skipped-core deficit fits in the full upper-half Boolean window used by the exact-row construction.
- incoming **complements**: [Z68::sharp_capacity_has_a_division_free_geometric_normal_form](BROWSER_Z68_1.md#node-8c773a9228d5f437). The skipped-core transport constructs a bare exact row using the full c-1-bit upper window; the sharp geometric coordinate records the stronger c-2-bit condition used elsewhere to obtain strict support separation.

<a id="node-78431a4db8be3d57"></a>
## every_nontrivial_exact_quotient_row_forces_rank_two

For every endpoint n >= 3 and every support D contained in [2,n], if localPrefixQuotient D n = 2^(n-1)-1, then rank 2 belongs to D.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rank-two membership removes one side condition from later extension arguments. It neither determines the remaining support nor supplies exact rows at any endpoint.

- Lean declaration: [two_mem_of_exact_localMersenneQuotient](../../Erdos249257/BooleanMobiusExactRowRankTwo.lean#L23)

- outgoing **complements**: [Z68::exact_rows_are_floor_quotient_hits_and_cofinality_requires_no_witness_coherence](BROWSER_Z68_1.md#node-9085fc364715d1e7). The definition leaves the witness support existential, while rank-two forcing proves that every witness at an endpoint at least three contains the same mandatory rank.

<a id="node-9085fc364715d1e7"></a>
## exact_rows_are_floor_quotient_hits_and_cofinality_requires_no_witness_coherence

ExactLocalMersenneHalfRow n means that some finite support D contained in the ranks from 2 through n has localPrefixQuotient D n exactly equal to 2^(n-1)-1. CofinalExactLocalMersenneHalfRows asks for such an endpoint beyond every bound, with no compatibility condition between the witnessing supports. The named finite seed support is exactRowSixSupport = {2,3,6}.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definitions prove neither the existence of any exact row nor cofinality. The named set {2,3,6} is only the support coordinate; Z29 separately owns the checked theorem that it is an exact endpoint-six row. A single seed cannot imply the cofinal predicate or half membership.

Open hypotheses: ["CofinalExactLocalMersenneHalfRows -- the definition names the open cofinal supply; this node does not prove it"]

- Lean declaration: [ExactLocalMersenneHalfRow](../../Erdos249257/BooleanMobiusCofinalExactRows.lean#L31)
- Lean declaration: [CofinalExactLocalMersenneHalfRows](../../Erdos249257/BooleanMobiusCofinalExactRows.lean#L38)
- Lean declaration: [exactRowSixSupport](../../Erdos249257/BooleanMobiusExactRowSeed.lean#L14)

- incoming **specialises**: [Z68::a_first_crossing_core_transports_to_an_exact_even_endpoint_row](BROWSER_Z68_1.md#node-a58322dfa9a6481e). The skipped-core theorem supplies an explicit family of instances of ExactLocalMersenneHalfRow, at endpoints 2c-2, from local crossing data.
- incoming **complements**: [Z68::every_nontrivial_exact_quotient_row_forces_rank_two](BROWSER_Z68_1.md#node-78431a4db8be3d57). The definition leaves the witness support existential, while rank-two forcing proves that every witness at an endpoint at least three contains the same mandatory rank.

<a id="node-8c773a9228d5f437"></a>
## sharp_capacity_has_a_division_free_geometric_normal_form

For d at least 2, localMersenneQuotient M d is exactly 2^(M mod d) times the finite geometric sum of (2^d)^j for j < M/d. Consequently, for a below-half core D supported in [2,c), the sharp suffix-capacity inequality localBinarySuffix D 1 (2c-2) < 2^(c-2) is equivalent to the inserted support's division-free geometric prefix quotient reaching the integral half target 2^((2c-2)-1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is an exact change of coordinates. It does not establish the sharp capacity inequality for any core, let alone uniformly or cofinally, and therefore does not produce half membership.

- Lean declaration: [localMersenneQuotient_eq_geometric](../../Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L27)
- Lean declaration: [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric](../../Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L196)

- incoming **barrier_for**: [Z68::skipped_cores_fit_the_loose_upper_window_but_not_the_sharp_window](BROWSER_Z68_1.md#node-f0c3929e69d10b4c). The unconditional theorem reaches only the threshold 2^(c-1), whereas the geometric equivalence exposes the strict separated-repair threshold 2^(c-2); the intervening one-bit band is not ruled out.
- outgoing **complements**: [Z68::a_first_crossing_core_transports_to_an_exact_even_endpoint_row](BROWSER_Z68_1.md#node-a58322dfa9a6481e). The skipped-core transport constructs a bare exact row using the full c-1-bit upper window; the sharp geometric coordinate records the stronger c-2-bit condition used elsewhere to obtain strict support separation.

<a id="node-f0c3929e69d10b4c"></a>
## skipped_cores_fit_the_loose_upper_window_but_not_the_sharp_window

If c >= 4, D is supported in [2,c), its value is below one half, and its deficit is smaller than the rank-c Mersenne weight, then localBinarySuffix D 1 (2c-2) is strictly less than 2^(c-1). This is a proved c-1-bit upper-half capacity bound; it does not establish the sharper c-2-bit inequality required by the strict separated repair socket.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem leaves the possible band from 2^(c-2) through the proved c-1-bit ceiling unresolved. It therefore cannot discharge the sharp capacity socket, strict support separation, cofinal exact rows, or half membership.

- Lean declaration: [localBinarySuffix_two_mul_sub_two_lt_upperHalfCapacity](../../Erdos249257/BooleanMobiusSkippedCoreExactRow.lean#L123)

- incoming **generated_by**: [Z68::a_first_crossing_core_transports_to_an_exact_even_endpoint_row](BROWSER_Z68_1.md#node-a58322dfa9a6481e). The proved c-1-bit capacity bound ensures that the skipped-core deficit fits in the full upper-half Boolean window used by the exact-row construction.
- outgoing **barrier_for**: [Z68::sharp_capacity_has_a_division_free_geometric_normal_form](BROWSER_Z68_1.md#node-8c773a9228d5f437). The unconditional theorem reaches only the threshold 2^(c-1), whereas the geometric equivalence exposes the strict separated-repair threshold 2^(c-2); the intervening one-bit band is not ruled out.

<a id="node-da9b23a041dbe8dd"></a>
## upper_half_mersenne_quotients_are_pure_binary_coins

If 2 <= d <= M and d lies strictly above M/2, then localMersenneQuotient M d is exactly the pure power of two 2^(M-d).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem is a local quotient identity. It gives no Boolean word, skipped core, exact row, cofinal supply, or irrationality conclusion by itself.

- Lean declaration: [localMersenneQuotient_eq_two_pow_sub_of_half_lt](../../Erdos249257/BooleanMobiusLocalRepair.lean#L26)

- incoming **generated_by**: [Z68::a_first_crossing_core_transports_to_an_exact_even_endpoint_row](BROWSER_Z68_1.md#node-a58322dfa9a6481e). The exact-row adapter encodes the missing quotient as a Boolean word because every selected rank in its upper window contributes the pure coin 2^(M-d).

