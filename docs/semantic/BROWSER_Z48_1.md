# Z48_1: Supported Mersenne achievement sets: topology, coordinate splitting, and exact volume dichotomy

[All problems and zones](BROWSER.md)

<a id="node-b25b1ac6ea523412"></a>
## allowing_one_coordinate_gives_disjoint_faces_and_doubles_volume

PROVED ONE-COORDINATE SELF-SIMILARITY: if k is not in J, the zero face supported on J and its translate by mersenneWeight (k+1) are disjoint; consequently allowing k doubles the Lebesgue measure of the supported achievement set.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The result compares measures after adding one allowed coordinate. It does not assert that an arbitrary supported set has positive measure.

- Lean declaration: [supportedMersenneAchievementSet_insert](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L203)
- Lean declaration: [disjoint_supportedMersenneAchievementSet_translate](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L262)
- Lean declaration: [volume_supportedMersenneAchievementSet_insert](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L286)

- outgoing **complements**: [Z48::supported_mersenne_achievement_sets_are_compact_and_nowhere_dense](BROWSER_Z48_1.md#node-9c3ac79ad246aa12). The face split uses compact measurability and injective coding but adds an exact metric self-similarity statement.
- incoming **generated_by**: [Z48::supported_mersenne_sets_have_an_exact_finite_or_infinite_codimension_volume_dichotomy](BROWSER_Z48_1.md#node-98ac4fd349a3170f). The finite-codimension branch iterates the one-coordinate doubling law; the infinite-codimension branch is obtained by monotone comparison with those finite faces.

<a id="node-3d0ead3059dfc370"></a>
## infinite_support_gives_a_perfect_supported_achievement_set

PROVED INFINITE-SUPPORT GEOMETRY: if J is infinite, then the supported digit subspace has no isolated points, and the supported Mersenne achievement set is perfect.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem is an implication from infinitude of J; these selected declarations do not prove the converse. Perfectness still makes no arithmetic classification of individual points.

- Lean declaration: [preperfect_supportedMersenneDigitSet](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L120)
- Lean declaration: [perfect_supportedMersenneAchievementSet](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L167)

- outgoing **complements**: [Z48::supported_mersenne_achievement_sets_are_compact_and_nowhere_dense](BROWSER_Z48_1.md#node-9c3ac79ad246aa12). For infinite J, the no-isolated-point argument supplements the compact closed geometry with perfectness; nowhere density remains valid for every J.

<a id="node-9c3ac79ad246aa12"></a>
## supported_mersenne_achievement_sets_are_compact_and_nowhere_dense

PROVED TOPOLOGICAL GEOMETRY: supportedMersenneAchievementSet J is the range of Mersenne digit values supported on J; for every support J it is compact and nowhere dense.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Compactness and nowhere density classify the set geometrically. They decide neither membership of 1/2 nor irrationality of any individual supported subseries.

- Lean declaration: [supportedMersenneAchievementSet](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L76)
- Lean declaration: [isCompact_supportedMersenneAchievementSet](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L90)
- Lean declaration: [isNowhereDense_supportedMersenneAchievementSet](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L112)

- incoming **complements**: [Z48::infinite_support_gives_a_perfect_supported_achievement_set](BROWSER_Z48_1.md#node-3d0ead3059dfc370). For infinite J, the no-isolated-point argument supplements the compact closed geometry with perfectness; nowhere density remains valid for every J.
- incoming **complements**: [Z48::allowing_one_coordinate_gives_disjoint_faces_and_doubles_volume](BROWSER_Z48_1.md#node-b25b1ac6ea523412). The face split uses compact measurability and injective coding but adds an exact metric self-similarity statement.

<a id="node-98ac4fd349a3170f"></a>
## supported_mersenne_sets_have_an_exact_finite_or_infinite_codimension_volume_dichotomy

PROVED COMPLETE VOLUME CLASSIFICATION: for every J, either J is the complement of a finite set F and the supported achievement set has volume (2^|F|)^-1, or J has infinite complement and the supported achievement set has volume zero.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Measure classifies the size of each value set, not the arithmetic nature of its points. The dichotomy does not settle Erdős #257.

- Lean declaration: [volume_supportedMersenneAchievementSet_finset_compl](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L349)
- Lean declaration: [volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L368)
- Lean declaration: [volume_supportedMersenneAchievementSet_dichotomy](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397)

- outgoing **generated_by**: [Z48::allowing_one_coordinate_gives_disjoint_faces_and_doubles_volume](BROWSER_Z48_1.md#node-b25b1ac6ea523412). The finite-codimension branch iterates the one-coordinate doubling law; the infinite-codimension branch is obtained by monotone comparison with those finite faces.

