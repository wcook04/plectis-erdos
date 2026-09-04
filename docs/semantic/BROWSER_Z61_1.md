# Z61_1: Boolean-Mobius greedy reduction: Mersenne gap dominance and unique half-target words

[All problems and zones](BROWSER.md)

<a id="node-a38c4e928258c38d"></a>
## below_gap_defect_exactly_characterises_the_greedy_word

PROVED ABSTRACT UNIQUE-WINDOW HINGE: for a positive gap, a gap-dominating weight list, an equal-length Boolean word, and an admissible target C, the defect C - weightedBoolSum weights bits is below the gap iff bits is exactly integerGreedyBits weights C and the deterministic greedy remainder is itself below the gap.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The right side retains the greedy-remainder inequality. Gap dominance alone does not put that remainder inside the window, and the theorem does not assert existence of a below-gap representative.

- Lean declaration: [remainder_lt_gap_iff_eq_integerGreedyBits](../../Erdos249257/BooleanMobiusGreedyReduction.lean#L918)

- incoming **specialises**: [Z61::exact_half_target_lower_words_are_forced_to_be_greedy](BROWSER_Z61_1.md#node-ae546da2e64cf7a6). Instantiate the abstract target with 2^(M-1)-1 and the weights with localMersenneWeights M R, then identify the defect with A using the exact-fill equation.
- outgoing **complements**: [Z61::local_mersenne_quotient_words_are_gap_dominated](BROWSER_Z61_1.md#node-7331e8216b641555). The concrete theorem proves that Mersenne lists have the required separation, while the abstract theorem explains what any below-gap admissible representative must be.

<a id="node-ae546da2e64cf7a6"></a>
## exact_half_target_lower_words_are_forced_to_be_greedy

PROVED HALF-TARGET SPECIALISATION: if R <= M, bits has the local Mersenne weight-list length, weightedBoolSum (localMersenneWeights M R) bits + A = 2^(M-1)-1, and A < lowerBinaryWindow M R, then bits is the deterministic integer-greedy word for the half target and A equals its integer-greedy remainder.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The exact-fill and inside-window statements are theorem inputs, not outputs. The theorem canonicalises any such construction but produces neither the construction nor a uniform small-remainder or repair-load theorem.

- Lean declaration: [localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq](../../Erdos249257/BooleanMobiusGreedyReduction.lean#L997)

- outgoing **specialises**: [Z61::below_gap_defect_exactly_characterises_the_greedy_word](BROWSER_Z61_1.md#node-a38c4e928258c38d). Instantiate the abstract target with 2^(M-1)-1 and the weights with localMersenneWeights M R, then identify the defect with A using the exact-fill equation.
- outgoing **generated_by**: [Z61::local_mersenne_quotient_words_are_gap_dominated](BROWSER_Z61_1.md#node-7331e8216b641555). The concrete Mersenne dominance theorem discharges the abstract GapDominates premise needed for unique-window canonicalisation.

<a id="node-7331e8216b641555"></a>
## local_mersenne_quotient_words_are_gap_dominated

PROVED CONCRETE DOMINANCE: if R <= M and 1 <= d, then the quotient-weight list localMersenneWeightsFrom M R d is recursively gap-dominated by lowerBinaryWindow M R = 2^(M-R); every head exceeds its complete remaining tail by at least that window.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Gap dominance supplies separation only. It does not prove that a greedy remainder lies below the window, that an exact half-target word exists, or that the remaining repair load is safe.

- Lean declaration: [localMersenneWeightsFrom_gapDominates](../../Erdos249257/BooleanMobiusGreedyReduction.lean#L684)

- incoming **generated_by**: [Z61::exact_half_target_lower_words_are_forced_to_be_greedy](BROWSER_Z61_1.md#node-ae546da2e64cf7a6). The concrete Mersenne dominance theorem discharges the abstract GapDominates premise needed for unique-window canonicalisation.
- incoming **complements**: [Z61::below_gap_defect_exactly_characterises_the_greedy_word](BROWSER_Z61_1.md#node-a38c4e928258c38d). The concrete theorem proves that Mersenne lists have the required separation, while the abstract theorem explains what any below-gap admissible representative must be.

