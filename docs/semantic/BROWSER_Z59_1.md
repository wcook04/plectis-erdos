# Z59_1: Cofinal positive half-greedy skips: local exact rows and the conditional half-membership chain

[All problems and zones](BROWSER.md)

<a id="node-dfa1c5ace752e4d7"></a>
## cofinal_positive_half_greedy_skips_force_half_membership

Cofinal positive half-greedy skips yield cofinal exact rows and therefore place one half in the Mersenne achievement set.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is only a forward conditional. It proves no half-membership, infinite support, or universal Erdős #257 result without the open antecedent; the reverse equivalence is not proved in this module.

Open hypotheses: ["CofinalPositiveHalfGreedySkips"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips](../../Erdos249257/BooleanMobiusSkipRowCofinal.lean#L97)

- outgoing **depends_on_open**: [Z59::cofinal_positive_half_greedy_skips_is_the_open_orbit_socket](BROWSER_Z59_1.md#node-db91ce3646eef041). The achievement-set conclusion remains conditional on the unproved cofinal positive-skip predicate.
- outgoing **generated_by**: [Z59::cofinal_positive_half_greedy_skips_produce_cofinal_exact_rows](BROWSER_Z59_1.md#node-34ec3e8542898d10). The proof feeds the cofinal exact-row theorem into the existing cofinal-row achievement-set consumer.

<a id="node-db91ce3646eef041"></a>
## cofinal_positive_half_greedy_skips_is_the_open_orbit_socket

CofinalPositiveHalfGreedySkips means that beyond every bound there is a rank c at least four where the rational half-greedy remainder after c-1 steps is positive and strictly smaller than mersenneWeightRat c.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This declaration proves neither a cofinal supply nor an equivalence. The paper identifies the predicate with half-membership only after combining external positivity and skipped-support results; no named Lean iff with this predicate exists.

Open hypotheses: ["CofinalPositiveHalfGreedySkips"]

- Lean declaration: [CofinalPositiveHalfGreedySkips](../../Erdos249257/BooleanMobiusSkipRowCofinal.lean#L22)

- incoming **depends_on_open**: [Z59::cofinal_positive_half_greedy_skips_produce_cofinal_exact_rows](BROWSER_Z59_1.md#node-34ec3e8542898d10). The cofinal-row theorem takes CofinalPositiveHalfGreedySkips as its sole global hypothesis.
- incoming **depends_on_open**: [Z59::cofinal_positive_half_greedy_skips_force_half_membership](BROWSER_Z59_1.md#node-dfa1c5ace752e4d7). The achievement-set conclusion remains conditional on the unproved cofinal positive-skip predicate.

<a id="node-34ec3e8542898d10"></a>
## cofinal_positive_half_greedy_skips_produce_cofinal_exact_rows

If positive half-greedy skips occur cofinally, the associated endpoints 2c-2 carry exact local Mersenne half rows cofinally.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem consumes the full open orbit-level supply and does not prove it.

Open hypotheses: ["CofinalPositiveHalfGreedySkips"]

- Lean declaration: [cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips](../../Erdos249257/BooleanMobiusSkipRowCofinal.lean#L84)

- outgoing **depends_on_open**: [Z59::cofinal_positive_half_greedy_skips_is_the_open_orbit_socket](BROWSER_Z59_1.md#node-db91ce3646eef041). The cofinal-row theorem takes CofinalPositiveHalfGreedySkips as its sole global hypothesis.
- outgoing **generated_by**: [Z59::one_positive_half_greedy_skip_produces_an_exact_row](BROWSER_Z59_1.md#node-16f5cf8d71208ec1). Each cofinal skip witness is mapped to endpoint 2c-2 by the local exact-row producer, and elementary arithmetic preserves cofinality.
- incoming **generated_by**: [Z59::cofinal_positive_half_greedy_skips_force_half_membership](BROWSER_Z59_1.md#node-dfa1c5ace752e4d7). The proof feeds the cofinal exact-row theorem into the existing cofinal-row achievement-set consumer.

<a id="node-16f5cf8d71208ec1"></a>
## one_positive_half_greedy_skip_produces_an_exact_row

Every c at least four where the rational half-greedy remainder is positive and below the next Mersenne weight produces ExactLocalMersenneHalfRow (2c-2).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem assumes one skip event and supplies neither infinitely many events nor coherent rows. Having no capacity hypothesis at this step does not solve the global supply problem.

- Lean declaration: [exactLocalMersenneHalfRow_of_positiveHalfGreedySkip](../../Erdos249257/BooleanMobiusSkipRowCofinal.lean#L55)

- incoming **generated_by**: [Z59::cofinal_positive_half_greedy_skips_produce_cofinal_exact_rows](BROWSER_Z59_1.md#node-34ec3e8542898d10). Each cofinal skip witness is mapped to endpoint 2c-2 by the local exact-row producer, and elementary arithmetic preserves cofinality.

