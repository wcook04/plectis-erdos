# Z16_2: Suffix-cylinder feedback tree: endpoint-indexed cylinders, profiled two-sheet gaps and promotion

[All problems and zones](BROWSER.md)

<a id="node-c949624af282f482"></a>
## terminal_only_projection

Lossy projection to the compactness-free consumer: any all-prefix reachable terminal state, hence any nonempty selected window and hence any full cylinder stage, forgets its history into a terminal-only square-root-strip witness at the same depth; and a realized localized one-hole seam also gives such a witness, because a one-hole seam cannot delete both carries 3 and 4. Consequently at an exact half-divisor horizon a terminal-only witness exists at the next row in both branches of the total feedback theorem.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [CylinderStage.halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L63)
- Lean declaration: [halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L74)
- Lean declaration: [CylinderStage.halfTerminalOnlyStripWitness_after_feedback](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L140)

- incoming **finite_instance_of**: [Z16::certified_terminal_witnesses_51_52](BROWSER_Z16_1.md#node-4412dd0ecc306fff). depths 51 and 52 are the projection applied to the two certified stages.
- outgoing **reformulates**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). the projection is applied to both branches of the total feedback step, so a witness survives either way.
- incoming **reformulates**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). it composes the projection with the downstream achievement-set consumer.
- outgoing **transport_of**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). CylinderStage.halfTerminalOnlyStripWitness and halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt are the forgetting maps into HalfTerminalOnlyStripWitness, exactly the object quantified in HalfCarryCofinalTerminalOnlyStrip.
- incoming **depends_on_open**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). the projection is the general route producing terminal-only strip witnesses from windows, stages and realized seams; it converts whatever stage supply exists into this antecedent, but produces witnesses only at depths already reached, so it discharges nothing on its own.

<a id="node-87c9d7f712ef9c84"></a>
## tracked_parent_survival_normal_form

Exact normal form for whether the two tracked sheets of a profiled gap still supply a canonical parent for the next strip. With gap [a,b] inside carries 1..R and sheet coefficients cL, cU, some target in 1..B has its canonical cL-parent below a exactly when cL + 3 <= 2a, and some target has its canonical cU-parent in b+1..R exactly when 2b + 1 <= B + cU. Hence at least one tracked sheet survives iff cL + 3 <= 2a or 2b + 1 <= B + cU, and the sharp swallow cell is the negation: 2a <= cL + 2 and B + cU <= 2b.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence concerns only the two sheets the stage happens to track; a swallow of the tracked sheets is not by itself a statement about all admissible words, since a ProfiledGapStage is a selected witness subtree rather than an exhaustivity certificate. Both sides are decidable arithmetic; neither is open. The two directions are not hypothesis-free: lowerParentSurvives_iff assumes 1 <= B, and upperParentSurvives_iff (hence trackedParentSurvives_iff and its negation) additionally assumes the divisor buffer B + cU <= 2*R, so the stated normal form is an equivalence only inside that arithmetic cell.

- Lean declaration: [lowerParentSurvives_iff](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L60)
- Lean declaration: [upperParentSurvives_iff](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L75)
- Lean declaration: [trackedParentSurvives_iff](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L96)
- Lean declaration: [not_trackedParentSurvives_iff](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L109)

- incoming **specialises**: [Z16::singleton_gap_no_swallow](BROWSER_Z16_1.md#node-47b1c3f543a0b11d). it is the normal form evaluated at a one-point gap using the adjacency coefficient bound.

<a id="node-4425f8a68a1bbc68"></a>
## two_sheet_hole_only_reachability

A two-sheet state realizes every terminal carry of the full square-root strip except its single hole, which is strictly stronger than the protected 3..27 realization interface; projecting it therefore reproduces the localized one-hole protected even seam consumer whenever the strip is at least 27 wide.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [InStripTwoSheetStage.halfTerminalReachable_of_ne_hole](../../Erdos249257/SuffixCylinderInStrip.lean#L409)
- Lean declaration: [InStripTwoSheetStage.protectedEvenSeamRealizedAt](../../Erdos249257/SuffixCylinderInStrip.lean#L422)

- outgoing **specialises**: [Z16::in_strip_two_sheet_split](BROWSER_Z16_1.md#node-31d4c25c3644fda8). it reads reachability off the two sheets produced by the split.
- outgoing **supersedes**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). InStripTwoSheetStage.halfTerminalReachable_of_ne_hole realizes every terminal carry of the full square-root strip except the single hole - the Z16 node states this is strictly stronger than the protected 3..27 realization interface - and InStripTwoSheetStage.protectedEvenSeamRealizedAt reproduces the same consumer that protectedEvenSeamRealizedAt_succ_of_profile was built to feed, without the two-valued threshold-profile hypothesis.
- outgoing **generalises**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). `InStripTwoSheetStage.halfTerminalReachable_of_ne_hole` realizes every terminal carry of the full square-root strip except the single hole, and `InStripTwoSheetStage.protectedEvenSeamRealizedAt` projects that onto the localized 3..27 ProtectedEvenSeamRealizedAt interface Z15 produces; the two-sheet state is the strictly stronger object.

<a id="node-b2488aa5c69c6e63"></a>
## two_sheet_next_row_off_child_gap

If the two sheets of a two-sheet state genuinely share one next-row coefficient C, then every target carry of the next row whose canonical fixed-C parent is not the old hole is realized one row later; by the parent doubling law the sole parent hole becomes exactly the adjacent child pair {2*hole - C - 1, 2*hole - C} intersected with the target strip.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The Lean conclusion covers only carries q <= B for a supplied bound B satisfying B <= halfStripBound (N+1) and the divisor buffer B + C <= 2*halfStripBound N; it is not stated for the full next strip outright, although the sqrt coefficient envelope discharges the buffer at B = halfStripBound (N+1). This is a one-row statement: it produces HalfTerminalReachable at N+1, not another two-sheet stage.

Open hypotheses: ["hcommon : T.HasCommonNextCoeff C, i.e. (forall q, 1 <= q -> q <= T.hole - 1 -> supportCoeff (wordSupport (T.lower.word q ..)) (N+1) = C) and (forall q, T.hole + 1 <= q -> q <= halfStripBound N -> supportCoeff (wordSupport (T.upper.word q ..)) (N+1) = C). Cross-sheet coefficient equality is proved in this corpus only at the single odd row immediately after the split (InStripTwoSheetStage.hasCommonNextCoeff_at_oddSuccessor); it is not proved at any later row, and after a cutoff promotion the two sheets provably acquire different prefixes."]

- Lean declaration: [InStripTwoSheetStage.halfTerminalReachable_succ_off_childGap](../../Erdos249257/SuffixCylinderInStrip.lean#L377)

- outgoing **specialises**: [Z16::parent_gap_doubling_law](BROWSER_Z16_1.md#node-8fc1866d2affdf7b). the surviving child set is the complement of the two adjacent children of the old hole.
- outgoing **depends_on_open**: [Z16::complementary_prefix_coefficient_agreement](BROWSER_Z16_1.md#node-418fd5b0434127a9). its common-coefficient hypothesis is discharged only at the single odd row supplied by that node and is unproved at every later row.
- incoming **generalises**: [Z16::common_next_coeff_gap_advance](BROWSER_Z16_1.md#node-aa8dc9cf22b9c781). it propagates the whole two-sheet package rather than pointwise reachability, under the same common-coefficient hypothesis.
- outgoing **depends_on_open**: [Z15::restriction_fixes_next_row_coefficient](BROWSER_Z15_1.md#node-49ec48a85fead70c). the only law producing equality of next-row coefficients: agreement on every divisor of the row forces equal support coefficients. Once a cutoff promotion gives the two sheets different prefixes the premise fails, which is exactly why HasCommonNextCoeff is proved only at the odd successor row.

