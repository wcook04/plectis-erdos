# Z74_1: Erdős 257 terminal-only bridge: operational feedback, profiled-gap survival, and depths 53–54

[All problems and zones](BROWSER.md)

<a id="node-e35db374d474e201"></a>
## a_binary_adjacent_singleton_gap_cannot_kill_the_next_terminal_witness

If a ready ProfiledGapStage M N at N >= 1 has adjacent binary prefixes and gapLo = gapHi, then HalfTerminalOnlyStripWitness (N+1) holds. The singleton-gap no-swallow theorem supplies tracked-parent survival automatically, which the proof-bearing parent consumer converts into an actual admissible successor witness.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The conclusion is local to one successor row and assumes readiness, prefix adjacency, and a singleton gap. It says nothing about wider gaps, preservation of the singleton condition, repeated continuation, or cofinal stage production.

- Lean declaration: [ProfiledGapStage.halfTerminalOnlyStripWitness_after_singletonGap](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L217)

- outgoing **specialises**: [Z74::tracked_parent_survival_realises_a_next_terminal_witness](BROWSER_Z74_1.md#node-765b3ceeb22397be). Adjacent singleton gaps furnish the tracked-parent-survival hypothesis and then apply the general proof-bearing consumer.

<a id="node-185a05b50fc127aa"></a>
## an_in_strip_two_sheet_stage_always_retains_a_terminal_witness

Every InStripTwoSheetStage K N yields a HalfTerminalOnlyStripWitness N. Its unique missing carry cannot be both 1 and 2, and whichever of those two carries survives lies in every half strip and is reachable in the retained two-sheet object.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is a same-depth witness extraction. It neither fills the missing carry nor constructs a next cylinder stage, an iterative continuation, a cofinal witness family, or a set whose Mersenne support series is 1/2.

- Lean declaration: [InStripTwoSheetStage.halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L97)

- incoming **generated_by**: [Z74::operational_feedback_preserves_a_terminal_witness_without_the_legacy_width_bound](BROWSER_Z74_1.md#node-36283632746a1319). The operational feedback consumer invokes the two-sheet projection in exactly its non-cylinder branch; its other branch uses the older full-cylinder projection already owned by Z16.
- incoming **complements**: [Z74::tracked_parent_survival_realises_a_next_terminal_witness](BROWSER_Z74_1.md#node-765b3ceeb22397be). Both theorems forget a richer branch object to the same terminal-only interface, but one consumes a profiled gap plus a surviving canonical parent while the other consumes a one-hole two-sheet stage directly.

<a id="node-97d4f3d450fbb621"></a>
## certified_terminal_witnesses_extend_the_finite_chain_to_depths_53_and_54

There are concrete HalfTerminalOnlyStripWitness instances at depths 53 and 54. Depth 53 is obtained by projecting the ordinary successor fullCylinderStage53, while depth 54 consumes both possible outputs at the next feedback boundary through the operational feedback theorem. Together with the already authored depth-51 and depth-52 instances, these results extend the certified finite witness chain exactly through 54.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Four consecutive witnesses at depths 51–54 are still only a finite chain. These declarations do not prove a CylinderStage at depth 54, a stage or witness beyond 54, cofinal nonempty full-cylinder stages, equivalence with O3 or O4, or the existence of an infinite positive Mersenne support summing to 1/2.

- Lean declaration: [fullCylinderStage53_halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L250)
- Lean declaration: [fullCylinderStage54_halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L257)

- outgoing **finite_instance_of**: [Z74::operational_feedback_preserves_a_terminal_witness_without_the_legacy_width_bound](BROWSER_Z74_1.md#node-36283632746a1319). The depth-54 declaration is the exact numerical specialization of the operational feedback consumer to fullCylinderStage53; the paired depth-53 declaration is the immediately preceding ordinary full-cylinder projection.

<a id="node-36283632746a1319"></a>
## operational_feedback_preserves_a_terminal_witness_without_the_legacy_width_bound

If S is a CylinderStage K N with 1 <= N, K+1 <= N, and N+1 = 2(K+1), then HalfTerminalOnlyStripWitness (N+1) holds. The operational feedback dichotomy is consumed directly: a full-cylinder output is projected by the ordinary cylinder consumer, while an in-strip two-sheet output is projected by its unavoidable surviving carry. Unlike the legacy protected-seam route, no hypothesis 27 <= halfStripBound (N+1) is required.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem produces only a terminal witness at the next row. In the two-sheet branch it does not recover a full CylinderStage, so it gives no unconditional iteration and no cofinal stage or witness supply.

- Lean declaration: [CylinderStage.halfTerminalOnlyStripWitness_after_operational_feedback](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L118)

- outgoing **generated_by**: [Z74::an_in_strip_two_sheet_stage_always_retains_a_terminal_witness](BROWSER_Z74_1.md#node-185a05b50fc127aa). The operational feedback consumer invokes the two-sheet projection in exactly its non-cylinder branch; its other branch uses the older full-cylinder projection already owned by Z16.
- incoming **finite_instance_of**: [Z74::certified_terminal_witnesses_extend_the_finite_chain_to_depths_53_and_54](BROWSER_Z74_1.md#node-97d4f3d450fbb621). The depth-54 declaration is the exact numerical specialization of the operational feedback consumer to fullCylinderStage53; the paired depth-53 declaration is the immediately preceding ordinary full-cylinder projection.

<a id="node-765b3ceeb22397be"></a>
## tracked_parent_survival_realises_a_next_terminal_witness

For a ready ProfiledGapStage M N with 1 <= N, the project-specific tracked-next-parent survival predicate, evaluated at the actual next-row coefficients of the lower and upper prefixes, implies HalfTerminalOnlyStripWitness (N+1). In either surviving-sheet case the proof selects the certified parent word, appends the parity bit dictated by the exact parent recurrence, obtains a reachable successor state, and then forgets it to the terminal-only interface.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Tracked-parent survival is a local theorem hypothesis, not a proved invariant for arbitrary profiled gaps. This result does not advance the whole gap object, bound future gap widths, or establish survival at unboundedly many rows.

- Lean declaration: [ProfiledGapStage.halfTerminalOnlyStripWitness_after_trackedParentSurvives](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L160)

- incoming **specialises**: [Z74::a_binary_adjacent_singleton_gap_cannot_kill_the_next_terminal_witness](BROWSER_Z74_1.md#node-e35db374d474e201). Adjacent singleton gaps furnish the tracked-parent-survival hypothesis and then apply the general proof-bearing consumer.
- outgoing **complements**: [Z74::an_in_strip_two_sheet_stage_always_retains_a_terminal_witness](BROWSER_Z74_1.md#node-185a05b50fc127aa). Both theorems forget a richer branch object to the same terminal-only interface, but one consumes a profiled gap plus a surviving canonical parent while the other consumes a one-hole two-sheet stage directly.

