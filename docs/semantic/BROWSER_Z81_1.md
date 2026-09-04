# Z81_1: Erdős 249 rank-one obstruction: geometric tails and uniform rung bounds

[All problems and zones](BROWSER.md)

<a id="node-7b0f83ae6ffed7e7"></a>
## every_mobius_mersenne_rung_at_least_three_is_strictly_below_one

PROVED STRICT UPPER BOUND: for every r at least three, 3^r is strictly smaller than 2^r(2^r-1); combined with the two-atom decomposition and its tail bound, this forces the Möbius–Mersenne rung Θ_r to be strictly below one.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The bound is one-sided and concerns rungs r≥3. It does not determine their signs, monotonicity, algebraic nature, or limit.

- Lean declaration: [three_pow_lt_mersenne_product](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L147)
- Lean declaration: [mobiusMersenneTheta_lt_one](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L196)

- outgoing **complements**: [Z81::the_target_mobius_mersenne_rung_two_is_strictly_below_eight_ninths](BROWSER_Z81_1.md#node-75f8ae220a35848c). The first node controls all source rungs r≥3 in the rank-one quotient, while the finite target estimate controls Θ_2 on the other side of the obstruction gap.

<a id="node-8ef860e122993b22"></a>
## four_atom_prefixes_approximate_every_rung_at_least_three_uniformly

PROVED PREFIX PACKET: every Möbius–Mersenne rung is exactly its first Y atoms plus the tail after Y; when Y is at least four and r is at least three, the absolute difference between the full rung and that prefix is at most 1/3584.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The estimate is a uniform analytic input to the rank-one quotient obstruction. It does not show that any prefix is nonzero or produce an irrationality certificate.

- Lean declaration: [mobiusMersenneTheta_eq_prefix_add_tail](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L62)
- Lean declaration: [abs_mobiusMersenneTheta_sub_prefix_le](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L73)

- incoming **complements**: [Z81::rungs_at_least_three_admit_a_uniform_one_eighth_geometric_majorant](BROWSER_Z81_1.md#node-f197e8f6d5b62c77). The termwise one-eighth envelope is the quantitative input used to estimate the exact prefix-tail decomposition uniformly after four atoms.

<a id="node-f197e8f6d5b62c77"></a>
## rungs_at_least_three_admit_a_uniform_one_eighth_geometric_majorant

PROVED GEOMETRIC ENVELOPE: if r is at least three, then 2^3 is at most 2^r, hence 2^(-r) is at most 1/8, and the absolute n-th Möbius–Mersenne term is bounded by (1/8)^n for every n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The majorant controls only absolute tail size. It supplies no cancellation, nonvanishing linear form, denominator growth, or irrationality conclusion.

- Lean declaration: [two_pow_three_le_two_pow](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L41)
- Lean declaration: [geometric_base_le_eighth](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L45)
- Lean declaration: [norm_term_le_eighth_geometric](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L52)

- outgoing **complements**: [Z81::four_atom_prefixes_approximate_every_rung_at_least_three_uniformly](BROWSER_Z81_1.md#node-8ef860e122993b22). The termwise one-eighth envelope is the quantitative input used to estimate the exact prefix-tail decomposition uniformly after four atoms.

<a id="node-75f8ae220a35848c"></a>
## the_target_mobius_mersenne_rung_two_is_strictly_below_eight_ninths

PROVED TARGET-RUNG BOUND: the Möbius–Mersenne rung Θ_2 is strictly smaller than 8/9.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is a numerical upper bound on Θ_2, not an irrationality or transcendence statement about Θ_2 or the original totient series.

- Lean declaration: [mobiusMersenneTheta_two_lt_eight_ninths](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L223)

- incoming **complements**: [Z81::every_mobius_mersenne_rung_at_least_three_is_strictly_below_one](BROWSER_Z81_1.md#node-7b0f83ae6ffed7e7). The first node controls all source rungs r≥3 in the rank-one quotient, while the finite target estimate controls Θ_2 on the other side of the obstruction gap.

