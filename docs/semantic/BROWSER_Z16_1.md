# Z16_1: Suffix-cylinder feedback tree: endpoint-indexed cylinders, profiled two-sheet gaps and promotion

[All problems and zones](BROWSER.md)

<a id="node-b014e76f54753079"></a>
## adjacent_prefix_invariant

Binary adjacency of the two profiled sheet prefixes is an invariant of the whole profiled machinery: it holds for the state produced by the in-strip split (the true and false children of one boundary prefix), it is preserved by the fixed-cutoff profiled successor (which does not touch the prefixes), and it is preserved by cutoff promotion (which appends false to the lower and true to the upper prefix, sending n, n-1 to 2n, 2n-1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [ProfiledGapStage.promoteCutoff_hasAdjacentPrefixes](../../Erdos249257/SuffixCylinderProfiledPromotionAdjacency.lean#L65)
- Lean declaration: [ProfiledGapStage.advanceOfReady_hasAdjacentPrefixes](../../Erdos249257/SuffixCylinderProfiledAutoStep.lean#L80)
- Lean declaration: [ProfiledGapStage.promoteThenAdvance_hasAdjacentPrefixes](../../Erdos249257/SuffixCylinderProfiledAutoStep.lean#L110)
- Lean declaration: [profiledGapStageOfTwoSheet_hasAdjacentPrefixes](../../Erdos249257/SuffixCylinderProfiledAdjacency.lean#L243)
- Lean declaration: [ProfiledGapStage.advanceOfNextCoeffProfile_hasAdjacentPrefixes](../../Erdos249257/SuffixCylinderProfiledAdjacency.lean#L270)

- outgoing **implies**: [Z16::binary_increment_coefficient_bound](BROWSER_Z16_1.md#node-dcfe937361428149). the preserved adjacency is precisely the hypothesis of the coefficient bound, so the bound holds at every profiled stage.
- incoming **specialises**: [Z16::boundary_words_binary_consecutive](BROWSER_Z16_1.md#node-4f7bd3fd6e31ca03). the two boundary words realise prefix adjacency at the extreme suffix values 0 and 2^(N-M)-1.

<a id="node-dcfe937361428149"></a>
## binary_increment_coefficient_bound

If two binary words of the same length are consecutive as numerals (lower = upper + 1) then, at any inspected row, the lower word's divisor coefficient exceeds the upper word's by at most one; if they are equal as numerals the coefficients are equal. The stage form gives lowerNextCoeff <= upperNextCoeff + 1 for adjacent profiled sheets.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ](../../Erdos249257/SuffixCylinderProfiledAdjacency.lean#L112)
- Lean declaration: [ProfiledGapStage.lowerNextCoeff_le_upperNextCoeff_add_one](../../Erdos249257/SuffixCylinderProfiledAdjacency.lean#L232)

- incoming **implies**: [Z16::adjacent_prefix_invariant](BROWSER_Z16_1.md#node-b014e76f54753079). the preserved adjacency is precisely the hypothesis of the coefficient bound, so the bound holds at every profiled stage.
- outgoing **reformulates**: [Z15::half_divisor_bit_unit_drop](BROWSER_Z15_1.md#node-734cf5a2f912a631). supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ generalises supportCoeff_extend_true_eq_false_add_one_at_double: consecutive words differ by at most one in divisor coefficient, by exactly one at the half divisor.

<a id="node-4f7bd3fd6e31ca03"></a>
## boundary_words_binary_consecutive

For a profiled gap with adjacent prefixes and both sheets nonempty, the top word of the lower sheet and the bottom word of the upper sheet are consecutive full binary words: the lower boundary word is the lower prefix followed by all zeros (its suffix numeral is 0) and the upper boundary word is the upper prefix followed by all ones (its suffix numeral is 2^(N-M) - 1), so the former equals the latter plus one.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [ProfiledGapStage.boundaryWordsAdjacent](../../Erdos249257/SuffixCylinderProfiledPromotionAdjacency.lean#L112)

- outgoing **specialises**: [Z16::adjacent_prefix_invariant](BROWSER_Z16_1.md#node-b014e76f54753079). the two boundary words realise prefix adjacency at the extreme suffix values 0 and 2^(N-M)-1.
- outgoing **reformulates**: [Z13::seam_word_adjacency_and_missing_rank_normal_form](BROWSER_Z13_2.md#node-b294bb7301a2e56c). ProfiledGapStage.boundaryWordsAdjacent and weightedBoolSum_adjacent_cut are the same adjacency statement for prefix-false-all-true versus prefix-true-all-false, one in binary-numeral order and one in weighted-sum order.
- incoming **depends_on_open**: [Z15::boundary_pair_supplies_unit_drop](BROWSER_Z15_1.md#node-03f57ba7c8b09eec). the nearest producer of the boundary-pair shape: the two sheet boundary words are consecutive binary numerals. It does not give that the two adjacent rewind ancestors are the opposite terminal extensions of one common half-depth word, and boundary_pair_not_forced_by_scalar_seam refutes that at depth 26.

<a id="node-bf9e1a5ea4c4344d"></a>
## certified_cylinder_run_to_depth_52

The normalised depth-29 stage at cutoff 25 with endpoint 14 advances unconditionally through the entire band to depth 51, with no feedback decision required, because its cutoff already sees every divisor of every row up to 51. Evaluating the literal cutoff-25 word's coefficients at rows 30..51 (the table 3,0,1,1,1,1,3,0,1,1,2,0,6,0,1,1,1,0,3,1,1,1) gives the exact depth-51 endpoint 51327745, which exceeds 2^25 + halfStripBound 51 = 33554432 + 18, so the second feedback row promotes to cutoff 26 and advances to a full cylinder stage at depth 52.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [fullCylinderStage51_endpoint](../../Erdos249257/SuffixCylinderStage51.lean#L520)
- Lean declaration: [fullCylinderStage52](../../Erdos249257/SuffixCylinderStage51.lean#L547)

- outgoing **finite_instance_of**: [Z16::literal_prefix_endpoint_run_law](BROWSER_Z16_1.md#node-f4a9608547c0084a). the 22-row endpoint evaluation is the scalar recurrence at the literal cutoff-25 word.
- outgoing **finite_instance_of**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). depths 29 to 51 are one application of advanceWithinCutoff with d = 22.
- outgoing **finite_instance_of**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). the cutoff-25 stage advances through rows 30..51 and promotes to a full cylinder stage at depth 52, extending the supply of selected protected windows to depth 52; the consumer needs them at every depth beyond some N0.
- incoming **depends_on_open**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). the certified run is the deepest producer of full-strip reachability, reaching depth 52; beyond that the continuation is gated on the unproved NextArithmetic cell of the profiled gap step, so reachability at every level is not produced.
- incoming **depends_on_open**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). admissible finite words are produced at every depth up to 52 by this run and nowhere beyond, so cofinal admissibility is unproduced.
- incoming **depends_on_open**: [Z12::strip_admissible_branch_forces_half](BROWSER_Z12_2.md#node-0e98feddc11597cf). an infinite strip-admissible branch would follow by Koenig from admissibility at every level; the run supplies levels up to 52 only, so the branch hypothesis has no producer.
- incoming **depends_on_open**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). the run is the actual production route for the cofinal window supply and reaches depth 52; past that the continuation depends on the unproved NextArithmetic cell, so the supply from some N0 onward is not produced.

<a id="node-4412dd0ecc306fff"></a>
## certified_terminal_witnesses_51_52

The certified depth-51 and depth-52 cylinder stages give concrete normalized terminal strip witnesses at depths 51 and 52.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [fullCylinderStage51_halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L231)
- Lean declaration: [fullCylinderStage52_halfTerminalOnlyStripWitness](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L238)

- outgoing **finite_instance_of**: [Z16::terminal_only_projection](BROWSER_Z16_2.md#node-c949624af282f482). depths 51 and 52 are the projection applied to the two certified stages.
- outgoing **finite_instance_of**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). the depth-51 and depth-52 stages project to normalized finite words with terminal carry inside the square-root strip, i.e. the HalfCarryCofinalTerminalOnlyStrip witness at exactly two depths.
- incoming **depends_on_open**: [Z12::terminal_scaled_vanishing_yields_half](BROWSER_Z12_3.md#node-acd42d13a4214f3a). the deepest terminal witnesses produced anywhere sit at depths 51 and 52; the antecedent needs a sequence of depths tending to infinity, which two depths cannot supply.

<a id="node-8553dd45a9fd93a3"></a>
## cofinal_stages_conditional_export

Conditional export to the #257-side target. If full cylinder stages exist at cofinally many depths, then terminal-only square-root-strip witnesses exist at cofinally many depths, and hence there is an infinite set A of exponents, with 0 excluded, whose Mersenne support series sums exactly to 1/2. The construction supplies such stages only at the finitely many depths reached so far (through 52); the cofinality hypothesis is exactly the open crux of the whole programme and is proved nowhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hstages : forall N : Nat, exists M K : Nat, max N 1 <= M and Nonempty (CylinderStage K M) - cofinal existence of full-strip suffix-cylinder stages. No theorem in this zone or elsewhere in the corpus produces stages at unboundedly many depths; the zone's own feedback theorems are one-row step laws that consume a stage and may return a two-sheet state or a seam instead of a stage, and the profiled continuation of the two-sheet branch is itself gated on the unproved NextArithmetic cell."]

- Lean declaration: [cofinalTerminalOnlyStrip_of_cofinalCylinderStages](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L264)
- Lean declaration: [exists_infinite_support_half_of_cofinalCylinderStages](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L277)
- Lean declaration: [exists_infinite_positive_support_half_of_cofinalCylinderStages](../../Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L287)

- outgoing **reformulates**: [Z16::terminal_only_projection](BROWSER_Z16_2.md#node-c949624af282f482). it composes the projection with the downstream achievement-set consumer.
- outgoing **depends_on_open**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). its hypothesis asks for stages at cofinally many depths, which the one-row step laws of this zone never produce.
- outgoing **depends_on_open**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). the residual two-sheet branch can only be continued through the unproved NextArithmetic cell, so it supplies no stages either.
- outgoing **depends_on_open**: [Z16::in_strip_two_sheet_split](BROWSER_Z16_1.md#node-31d4c25c3644fda8). the split is the one branch of the fan-in that does not return a stage, and closing it is what the cofinality hypothesis silently assumes.
- outgoing **transport_of**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). cofinalTerminalOnlyStrip_of_cofinalCylinderStages (SuffixCylinderTerminalOnlyBridge.lean) converts cofinal full-strip cylinder stages into the cofinal terminal-only strip supply consumed by exists_infinite_support_half_of_cofinalTerminalOnlyStrip (TerminalOnlyCofinal.lean).
- outgoing **depends_on_open**: [Z15::full_strip_step_from_divisor_agreement](BROWSER_Z15_1.md#node-80222181e708c6f3). the nearest one-row advance law with a full-strip conclusion, which iterated would give stages at every depth; it is itself gated on next-row divisor agreement and produces selected windows rather than cylinder stages, so the cofinal-stage hypothesis is unproduced.
- outgoing **specialises**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). `cofinalTerminalOnlyStrip_of_cofinalCylinderStages` (SuffixCylinderTerminalOnlyBridge.lean:125) derives `HalfCarryCofinalTerminalOnlyStrip` from cofinal full cylinder stages; that predicate is the antecedent of Z12's `half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip`, and the conclusions agree.

<a id="node-aa8dc9cf22b9c781"></a>
## common_next_coeff_gap_advance

Structure-preserving successor for a closed carry gap under a genuinely common next-row coefficient: the parent gap [a,b] becomes the child gap [2a - C - 1, 2b - C], and both selected families, both suffix-cylinder endpoints and the two complementary literal prefixes survive the step. The one-hole feedback state is the singleton-gap instance of this package.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hcommon : T.HasCommonNextCoeff C - one coefficient shared by both sheets at row N+1, unproved beyond the immediate odd successor row", "hchildLoPos : 1 <= 2 * T.gapLo - C - 1 - the child gap must not fall below carry one", "hchildHiStrip : 2 * T.gapHi - C <= halfStripBound (N + 1) - the child gap must not exceed the next strip"]

- Lean declaration: [InStripGapStage.advanceOfCommonNextCoeff](../../Erdos249257/SuffixCylinderFiniteGap.lean#L256)

- outgoing **generalises**: [Z16::two_sheet_next_row_off_child_gap](BROWSER_Z16_2.md#node-b2488aa5c69c6e63). it propagates the whole two-sheet package rather than pointwise reachability, under the same common-coefficient hypothesis.
- outgoing **depends_on_open**: [Z16::complementary_prefix_coefficient_agreement](BROWSER_Z16_1.md#node-418fd5b0434127a9). the cross-sheet coefficient equality it assumes is proved nowhere beyond the immediate odd successor row.
- incoming **repair_of**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). it drops the non-iterable cross-sheet coefficient equality in favour of two independent per-sheet coefficients.
- outgoing **depends_on_open**: [Z15::restriction_fixes_next_row_coefficient](BROWSER_Z15_1.md#node-49ec48a85fead70c). same producer and same limit: the shared-restriction premise is available below the half-depth cutoff and fails after promotion, so a genuinely common cross-sheet coefficient is not produced at later rows.

<a id="node-418fd5b0434127a9"></a>
## complementary_prefix_coefficient_agreement

The two complementary one-bit extensions of a common prefix (append true, append false) have the same divisor coefficient at the odd row immediately after their doubled feedback row, because the only divisor at which they differ, K+1, does not divide 2*(K+1)+1. Hence the two literal sheets of a freshly split two-sheet state automatically share one next-row coefficient at that single row.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_extend_true_eq_false_at_double_add_one](../../Erdos249257/SuffixCylinderInStrip.lean#L226)
- Lean declaration: [InStripTwoSheetStage.hasCommonNextCoeff_at_oddSuccessor](../../Erdos249257/SuffixCylinderInStrip.lean#L293)

- incoming **depends_on_open**: [Z16::two_sheet_next_row_off_child_gap](BROWSER_Z16_2.md#node-b2488aa5c69c6e63). its common-coefficient hypothesis is discharged only at the single odd row supplied by that node and is unproved at every later row.
- incoming **depends_on_open**: [Z16::common_next_coeff_gap_advance](BROWSER_Z16_1.md#node-aa8dc9cf22b9c781). the cross-sheet coefficient equality it assumes is proved nowhere beyond the immediate odd successor row.

<a id="node-fcdeb390d153df7d"></a>
## crossing_unit_drop_profile

When the cylinder endpoint genuinely crosses the head weight, the head bit is true exactly on the initial carry segment k <= E - 2^(N-(K+1)) and false above it; consequently at the exact doubled row N + 1 = 2*(K+1) the next-row divisor coefficient has the literal unit-drop profile, equal to c+1 on that initial segment and c above it, for one constant c read off the false child of the shared prefix.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [headBit_true_iff_le_crossingCut](../../Erdos249257/SuffixCylinderGlobalProducer.lean#L28)
- Lean declaration: [supportCoeff_profile_of_crossingSuffixCylinder](../../Erdos249257/SuffixCylinderGlobalProducer.lean#L60)

- outgoing **specialises**: [Z16::head_threshold_promotion_criterion](BROWSER_Z16_1.md#node-a034881200ee26b1). the crossing case is exactly the third alternative excluded by the criterion's two branches.
- outgoing **reformulates**: [Z15::rewind_seam_transports_unit_drop_to_profile](BROWSER_Z15_1.md#node-b1b5630fd7bc9659). supportCoeff_profile_of_crossingSuffixCylinder and nextRow_profile_of_rewindSeam produce the identical two-valued next-row coefficient profile (c+1 below a cut, c above) consumed by protectedEvenSeamRealizedAt_succ_of_profile; the cut is seamCut(cs) in one presentation and E - 2^(N-(K+1)) in the other.
- incoming **depends_on_open**: [Z15::rewind_seam_plus_unit_drop_realizes_protected_seam](BROWSER_Z15_1.md#node-a6029d30ac804cf0). at a genuine endpoint crossing this produces the literal unit-drop coefficient profile c+1 / c at the doubled row - the shape RewindBaseUnitDropAt asserts - but for cylinder endpoints, not for the two adjacent rewind base ancestors, so it does not discharge the hypothesis.
- incoming **depends_on_open**: [Z15::rewind_seam_transports_unit_drop_to_profile](BROWSER_Z15_1.md#node-b1b5630fd7bc9659). the same nearest producer of RewindBaseUnitDropAt: an endpoint crossing yields the literal c+1 / c profile at the doubled row, but on cylinder endpoints rather than on the two adjacent rewind base ancestors, so hbaseProfile is not produced for any cofinal family.
- incoming **depends_on_open**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). the corpus's only producer of a two-valued threshold coefficient profile (c+1 on the initial carry segment, c above); it requires a genuine endpoint crossing of the head weight, so it produces the profile at crossing feedback rows only, not across an arbitrary window.

<a id="node-0f660c5a0e7275b5"></a>
## cylinder_stage_advance_within_cutoff

A full-strip cylinder stage at cutoff K and depth N advances one row unconditionally whenever the fixed cutoff already sees every proper divisor of the next row, that is whenever (N+1)/2 <= K: the shared prefix forces a common next-row coefficient C, the square-root coefficient envelope supplies the successor buffer, and the new stage has endpoint 2E - C on the full strip at depth N+1. Iterating gives a stage at every depth N + d with N + d <= 2K + 1, i.e. through the entire band before the next feedback row; and one feedback macrostep combines a high-side cutoff promotion with an ordinary advance.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [CylinderStage.advance](../../Erdos249257/SuffixCylinderThreshold.lean#L835)
- Lean declaration: [CylinderStage.advanceWithinCutoff](../../Erdos249257/SuffixCylinderThreshold.lean#L874)
- Lean declaration: [CylinderStage.feedbackAdvanceHigh](../../Erdos249257/SuffixCylinderThreshold.lean#L904)

- outgoing **specialises**: [Z16::suffix_cylinder_endpoint_propagation](BROWSER_Z16_1.md#node-c67d33b8d0a3d858). the stage advance is the propagation law applied on the full square-root strip.
- incoming **reformulates**: [Z16::literal_prefix_endpoint_run_law](BROWSER_Z16_1.md#node-f4a9608547c0084a). it replaces a whole band of stage advances by a scalar recurrence on the endpoint.
- incoming **finite_instance_of**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). depths 29 to 51 are one application of advanceWithinCutoff with d = 22.
- incoming **depends_on_open**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). its hypothesis asks for stages at cofinally many depths, which the one-row step laws of this zone never produce.
- outgoing **transport_of**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). CylinderStage.advance is SelectedHalfWindow.stepExplicit with the hp_common hypothesis internalised: a shared prefix forces the common next-row coefficient and the sqrt envelope discharges the buffer, so the cylinder is the hypothesis-free packaging of the same window step.
- incoming **depends_on_open**: [Z15::full_strip_step_from_divisor_agreement](BROWSER_Z15_1.md#node-80222181e708c6f3). this is the bulk producer of next-row divisor agreement: whenever (N+1)/2 <= K the shared prefix forces a common coefficient and the stage advances unconditionally through the band to N = 2K+1. It produces agreement only inside a cutoff horizon, never at a feedback row.
- outgoing **specialises**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). `CylinderStage.advanceWithinCutoff` is the same canonical fixed-coefficient step restricted to a stage whose cutoff already sees every proper divisor of the next row, which discharges Z15's common-coefficient hypothesis (from the shared prefix) and its buffer hypothesis (from the square-root divisor envelope).

<a id="node-af558350a7b26d45"></a>
## depth29_cutoff25_normalisation

The depth-29 cylinder is normalised as far as its endpoint permits: repeated low-side promotions carry the cutoff from 14 through 19 with endpoint 782 unchanged, a high-side promotion at cutoff 20 drops it to 270, a further high-side promotion at cutoff 21 drops it to 14, and low-side promotions carry the cutoff to 25 with endpoint 14. The literal cutoff-25 word is exhibited bit by bit as the depth-13 base prefix followed by true, false, false, false, false, false, true, true, false, false, false, false.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFive](../../Erdos249257/SuffixCylinderThreshold.lean#L796)

- outgoing **finite_instance_of**: [Z16::one_bit_cutoff_promotion](BROWSER_Z16_1.md#node-f8ce3cc87ef6ecb4). eleven concrete low-side and high-side promotions of one window.
- incoming **barrier_for**: [Z16::depth29_cutoff26_promotion_impossible](BROWSER_Z16_1.md#node-44a005a0e257bc93). it is the exact reason the normalisation of that window stops at cutoff 25.

<a id="node-44a005a0e257bc93"></a>
## depth29_cutoff26_promotion_impossible

The cutoff 25 is maximal for the depth-29 window: its depth-26 restriction is not common, because the promotion criterion fails on both sides for endpoint 14 and strip width 14 against head weight 2^3 = 8, the consecutive suffix interval straddling that weight exactly.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only the promotion of this one depth-29 window past cutoff 25; it says nothing about progress, since the run continues at cutoff 25 unchanged to depth 51. It rules out no other window, no other depth, no other promotion strategy, and does not bear on whether cylinder stages exist beyond depth 52.

- Lean declaration: [depth29SelectedHalfWindow_not_commonRestrictionAt_twentySix](../../Erdos249257/SuffixCylinderThreshold.lean#L806)

- outgoing **barrier_for**: [Z16::depth29_cutoff25_normalisation](BROWSER_Z16_1.md#node-af558350a7b26d45). it is the exact reason the normalisation of that window stops at cutoff 25.

<a id="node-fe2a93ce8cb81ca0"></a>
## endpoint_indexed_suffix_cylinder_calculus

Definition and basic calculus of the endpoint-indexed suffix cylinder: a selected family of half-words is said to have a suffix cylinder at cutoff M with endpoint E when all its words agree on their first M bits and the binary value of the bits after M, added to the terminal carry index k, is the same number E for every k. The supporting binary calculus is: a suffix numeral of length L is below 2^L; it splits as (head bit)*2^(L-1) plus the shorter numeral; it depends only on membership in the window it reads; and appending one bit doubles it and adds that bit.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [wordSuffixNumeral_split_head](../../Erdos249257/SuffixCylinderPromotion.lean#L45)
- Lean declaration: [supportSuffixNumeral_extendHalfWord](../../Erdos249257/SelectedSuffixCylinder.lean#L55)

- incoming **specialises**: [Z16::suffix_cylinder_endpoint_propagation](BROWSER_Z16_1.md#node-c67d33b8d0a3d858). the E' = 2E - C law is the one-bit suffix-numeral doubling identity applied along the canonical successor.
- incoming **specialises**: [Z16::head_threshold_promotion_criterion](BROWSER_Z16_1.md#node-a034881200ee26b1). the criterion is the head split of the suffix numeral read against a consecutive endpoint interval.
- outgoing **reformulates**: [Z15::prefix_truncation_adds_suffix_numeral](BROWSER_Z15_1.md#node-7fa45c879f5b2789). Both are about supportSuffixNumeral: Z15 proves the frozen-prefix carry exceeds the live carry by exactly that numeral (integerHalfCarry_prefix_eq_add_supportSuffixNumeral), Z16 uses the same numeral as the endpoint offset k + numeral = E.

<a id="node-06ebb4e4c7e8aa6f"></a>
## escaping_hole_recylindrification

When a crossing hole escapes the next strip, a full endpoint cylinder is recovered rather than lost. If the hole lies above the strip, restricting the parent window to its true-bit initial segment, promoting that segment's common bit and taking the ordinary explicit step gives a full stage at (K+1, N+1). If the hole lies below carry one, every target of the next strip has its canonical fixed-c parent in the false-bit tail; reindexing that tail by the canonical parent gives a full stage at (K+1, N+1) with endpoint 2E - c.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [CylinderStage.feedbackAdvanceCrossingAbove](../../Erdos249257/SuffixCylinderTwoSheet.lean#L43)
- Lean declaration: [CylinderStage.feedbackAdvanceCrossingBelow](../../Erdos249257/SuffixCylinderBelow.lean#L136)

- outgoing **implies**: [Z16::feedback_fan_in_hole_in_strip](BROWSER_Z16_1.md#node-60cdb264ae157a27). the two escaping-hole constructors are what turn two of the crossing subcases back into full stages.

<a id="node-60cdb264ae157a27"></a>
## feedback_fan_in_hole_in_strip

Sharpened feedback fan-in. The crossing branch is split further by the exact integer hole 2*delta - c: if the hole falls below carry one or above the next strip bound, the crossing is recylindrified and the stage still advances to a full cylinder at (K+1, N+1). Therefore the only non-advancing outcome is a realized protected even seam whose exact integer hole lies inside the next full strip, that is 1 <= 2*delta - c <= halfStripBound (N+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [CylinderStage.feedbackAdvance_or_protectedSeam_inStrip](../../Erdos249257/SuffixCylinderFeedbackFanIn.lean#L62)

- outgoing **specialises**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). it refines the crossing branch of the trichotomy by the position of the exact integer hole.
- incoming **implies**: [Z16::escaping_hole_recylindrification](BROWSER_Z16_1.md#node-06ebb4e4c7e8aa6f). the two escaping-hole constructors are what turn two of the crossing subcases back into full stages.
- incoming **repair_of**: [Z16::in_strip_two_sheet_split](BROWSER_Z16_1.md#node-31d4c25c3644fda8). it replaces the existential seam receipt of the residual branch by a structure retaining both sheets, the hole, the endpoints and the prefixes.

<a id="node-b14b3eaa0fc6c96a"></a>
## feedback_trichotomy_advance_or_seam

Total one-row feedback step. Given a full-strip cylinder stage at an exact half-divisor horizon (N + 1 = 2*(K+1)) with a strip wide enough for the protected consumer, exactly three cases can occur for the endpoint relative to the head weight - below, above, or crossing - and in the first two the stage promotes and advances to a full stage at (K+1, N+1), while in the crossing case the unit-drop coefficient profile realizes a localized one-hole protected even seam at the produced row. There is no fourth object-level case.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder](../../Erdos249257/SuffixCylinderGlobalProducer.lean#L117)
- Lean declaration: [CylinderStage.feedbackStep_or_protectedSeam](../../Erdos249257/SuffixCylinderGlobalProducer.lean#L174)

- incoming **specialises**: [Z16::feedback_fan_in_hole_in_strip](BROWSER_Z16_1.md#node-60cdb264ae157a27). it refines the crossing branch of the trichotomy by the position of the exact integer hole.
- incoming **generalises**: [Z16::rewind_history_promotion_dichotomy](BROWSER_Z16_1.md#node-7803df419e54746c). the cylinder route obtains the same advance-or-seam dichotomy without assuming a retained rewind history, so the history version is superseded.
- incoming **reformulates**: [Z16::terminal_only_projection](BROWSER_Z16_2.md#node-c949624af282f482). the projection is applied to both branches of the total feedback step, so a witness survives either way.
- outgoing **supersedes**: [Z15::history_alternative_needs_canonical_seam_bridge](BROWSER_Z15_1.md#node-38ee19ceeb12b902). SelectedHalfWindow.historyAlternative_of_rewindHistory delivers its disjunction only under an assumed, unproved bridge from the scalar seam pair to an actual canonical even seam. CylinderStage.feedbackStep_or_protectedSeam is total and unconditional at an exact half-divisor horizon: below, above or crossing, with the crossing branch routed through the unit-drop profile into protectedEvenSeamRealizedAt_succ_of_profile, and there is no fourth object-level case.
- incoming **depends_on_open**: [Z15::cofinal_protected_seam_consumer](BROWSER_Z15_1.md#node-8914ed1068ade432). the only law whose conclusion can be a realized localized one-hole protected even seam; it fires at one feedback row of an EXISTING full-strip stage, so it produces seams only as far as stages exist (depth 52), never cofinally.
- incoming **depends_on_open**: [Z15::mixed_cofinal_window_or_seam_consumer](BROWSER_Z15_1.md#node-e5cf1d1a8c038506). the trichotomy delivers exactly this consumer's disjunction - a promoted full stage or a realized protected seam - at each feedback row, but only from an existing full-strip stage at an exact half-divisor horizon, so it produces the disjunction at reached depths only.
- outgoing **generalises**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). Z15's `protectedEvenSeamRealizedAt_succ_of_profile` assumes the two-valued threshold coefficient profile; Z16's `supportCoeff_profile_of_crossingSuffixCylinder` proves that exact profile for a crossing endpoint cylinder, so `protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder` reaches the same conclusion with the profile hypothesis discharged.

<a id="node-dc4415c505244611"></a>
## first_feedback_promotion_depth_27_to_29

At the first genuine half-divisor feedback row the depth-27 endpoint 8389 exceeds the head weight 2^13 = 8192 by more than the strip width 14, so the depth-14 bit is common and true: the cylinder promotes to cutoff 14 with endpoint 8389 - 8192 = 197, the shared prefix becomes the depth-13 base prefix extended by true, the depth-28 row has common coefficient 3 giving endpoint 2*197 - 3 = 391, and the depth-29 row has common coefficient 0 giving endpoint 782. Full protected selected windows and admissible words exist at depths 28 and 29.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [depth27SelectedHalfWindow_commonRestrictionAt_fourteen](../../Erdos249257/SuffixCylinderThreshold.lean#L508)
- Lean declaration: [depth27SelectedHalfWindow_hasSuffixCylinderAt_fourteen](../../Erdos249257/SuffixCylinderThreshold.lean#L521)
- Lean declaration: [depth27SelectedHalfWindow_restrict_fourteen](../../Erdos249257/SuffixCylinderThreshold.lean#L542)
- Lean declaration: [depth28SelectedHalfWindow_hasSuffixCylinderAt_fourteen](../../Erdos249257/SuffixCylinderThreshold.lean#L602)
- Lean declaration: [depth29SelectedHalfWindow_hasSuffixCylinderAt_fourteen](../../Erdos249257/SuffixCylinderThreshold.lean#L686)

- outgoing **finite_instance_of**: [Z16::one_bit_cutoff_promotion](BROWSER_Z16_1.md#node-f8ce3cc87ef6ecb4). the depth-27 promotion is the high-side lemma at K = 13, E = 8389.
- outgoing **finite_instance_of**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). the promotion yields full protected selected windows at depths 28 and 29, two further instances of the same cofinal window supply.
- outgoing **finite_instance_of**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). admissible words exist for every terminal carry of the strip at depths 28 and 29, i.e. full-strip reachability at two further levels.

<a id="node-bb41c657e044dea7"></a>
## gap_width_recurrence

Exact width arithmetic for a profiled gap in signed coordinates. One row sends the closed gap [a,b] to [2a - cL - 1, 2b - cU], so the inclusive width doubles and picks up the signed coefficient difference cL - cU. Two consecutive rows send the endpoints to the base-four affine coordinates 4a - 2*cLodd - cLeven - 3 and 4b - 2*cUodd - cUeven, so the width quadruples and picks up the difference of the two combined row pulses 2*oddCoeff + evenCoeff.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [signedGapWidth_next](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L216)
- Lean declaration: [signedGapWidth_macro](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L239)

- incoming **depends_on_open**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). its unproved childHiStrip inequality is exactly the width control that the doubling recurrence makes non-automatic against a strip bound growing like 2*sqrt(N).
- incoming **specialises**: [Z16::macro_swallow_quarter_band_bound](BROWSER_Z16_1.md#node-05a80c3c58b98c35). it is the two-row width recurrence read as a necessary condition on the swallow branch.

<a id="node-a034881200ee26b1"></a>
## head_threshold_promotion_criterion

Exact geometric criterion for extending the common prefix by one bit: for a selected family whose suffix cylinder at cutoff K has endpoint E over carries 1..R, the (K+1)-bit is common to all words if and only if the consecutive suffix interval E-R,...,E-1 lies entirely below the head weight 2^(N-(K+1)) or entirely at or above it, i.e. iff E <= 2^(N-(K+1)) or 2^(N-(K+1)) + R <= E. Supporting facts: a false head bit forces the suffix below the head weight and a true head bit forces it at or above; and two adjacent endpoint-indexed words can only flip the head bit from true (smaller index) to false (larger index).

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Both sides of the equivalence are decidable properties of a supplied finite object; neither side is an open problem.

- Lean declaration: [commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold](../../Erdos249257/SuffixCylinderThreshold.lean#L29)
- Lean declaration: [commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint](../../Erdos249257/SuffixCylinderThreshold.lean#L107)
- Lean declaration: [wordSuffixNumeral_lt_headPower_of_false](../../Erdos249257/SuffixCylinderPromotion.lean#L84)
- Lean declaration: [headPower_le_wordSuffixNumeral_of_true](../../Erdos249257/SuffixCylinderPromotion.lean#L92)
- Lean declaration: [adjacent_endpoint_head_orientation](../../Erdos249257/SuffixCylinderPromotion.lean#L101)

- outgoing **specialises**: [Z16::endpoint_indexed_suffix_cylinder_calculus](BROWSER_Z16_1.md#node-fe2a93ce8cb81ca0). the criterion is the head split of the suffix numeral read against a consecutive endpoint interval.
- incoming **specialises**: [Z16::one_bit_cutoff_promotion](BROWSER_Z16_1.md#node-f8ce3cc87ef6ecb4). the two promotion lemmas are the two sides of the criterion with the endpoint arithmetic attached.
- incoming **specialises**: [Z16::crossing_unit_drop_profile](BROWSER_Z16_1.md#node-fcdeb390d153df7d). the crossing case is exactly the third alternative excluded by the criterion's two branches.
- outgoing **reformulates**: [Z15::rewind_dyadic_phase_criterion](BROWSER_Z15_1.md#node-5576062eeee0b5e7). commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold (SuffixCylinderThreshold.lean) and rewind_interval_singleton_iff_phase_fit (HalfCarryCeilParentContraction.lean) are the same 'consecutive interval fits on one side of a dyadic threshold' criterion; phase_eq_denom_sub_one_sub_suffixNumeral converts the rewind phase into the cylinder's suffix-numeral coordinate.
- outgoing **reformulates**: [Z15::live_support_singleton_criterion](BROWSER_Z15_1.md#node-c4e16b860a2f525d). rewind_supportCoeffHistory_singleton_iff_prefixCarry_covers states the singleton condition as B <= frozen-prefix carry, the same inequality the cylinder criterion states as E <= headweight or headweight + R <= E.

<a id="node-31d4c25c3644fda8"></a>
## in_strip_two_sheet_split

When the crossing hole stays inside the next strip the live words split into two exact endpoint cylinders rather than disappearing: a lower selected window on carries 1..hole-1 with endpoint hole-1 and literal prefix (boundary prefix extended by true), an upper selected interval on carries hole+1..stripBound with endpoint 2E-c and literal prefix (boundary prefix extended by false), the two endpoints separated by exactly one head weight, together with the scalar seam coordinates whose one-hole predicate is exactly the complement of the hole. Consequently every full cylinder stage at a feedback row either advances as a full cylinder or produces this exact two-sheet state.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: By the module's own statement this is a one-depth split, not an iteration closure: continuing past the produced row still needs next-row coefficient receipts, which are supplied only by the separately conditional gap advances.

- Lean declaration: [CylinderStage.feedbackAdvance_or_inStripTwoSheet](../../Erdos249257/SuffixCylinderInStrip.lean#L665)

- outgoing **repair_of**: [Z16::feedback_fan_in_hole_in_strip](BROWSER_Z16_1.md#node-60cdb264ae157a27). it replaces the existential seam receipt of the residual branch by a structure retaining both sheets, the hole, the endpoints and the prefixes.
- incoming **specialises**: [Z16::two_sheet_hole_only_reachability](BROWSER_Z16_2.md#node-4425f8a68a1bbc68). it reads reachability off the two sheets produced by the split.
- incoming **depends_on_open**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). the split is the one branch of the fan-in that does not return a stage, and closing it is what the cofinality hypothesis silently assumes.
- outgoing **repair_of**: [Z13::raw_dyadic_safety_does_not_force_seam_escape](BROWSER_Z13_1.md#node-105d9051e0bb7665). The barrier's witness has scalar seam hole H = 3 lying inside the strip of half width eight, i.e. exactly the crossing case where the hole fails to escape. CylinderStage.feedbackAdvance_or_inStripTwoSheet proves that when the crossing hole stays inside the next strip the live words split into two exact endpoint cylinders rather than dying, so seam escape is not needed for the stage to survive.
- outgoing **transport_of**: [Z12::even_seam_one_hole_theorem](BROWSER_Z12_1.md#node-faa46a4f5d916b2a). InStripTwoSheetStage carries the scalar seam coordinates whose one-hole predicate is the complement of its hole (halfTerminalReachable_of_ne_hole, InStripTwoSheetStage.protectedEvenSeamRealizedAt): the object-level realisation of the scalar one-hole reachability theorem.

<a id="node-f4a9608547c0084a"></a>
## literal_prefix_endpoint_run_law

Before a row is reached by feedback, a word's next divisor coefficient is already determined by its literal cutoff restriction; the canonical successor preserves any common literal prefix; and therefore the endpoint of a stage carrying a fixed literal cutoff word, advanced d rows inside its cutoff horizon, is computed exactly by the scalar recurrence E_{d+1} = 2 E_d - (coefficient of the literal cutoff word at row N+d+1). This turns a whole band of stage advances into a finite scalar evaluation.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [FullCylinderStageHasLiteralPrefix_advance](../../Erdos249257/SuffixCylinderStage51.lean#L437)
- Lean declaration: [FullCylinderStageHasLiteralPrefix_advanceWithinCutoff](../../Erdos249257/SuffixCylinderStage51.lean#L449)
- Lean declaration: [fullCylinderStage_nextCoeff_eq_literalPrefix](../../Erdos249257/SuffixCylinderStage51.lean#L475)
- Lean declaration: [fullCylinderStage_endpoint_advanceWithinCutoff_eq_literalPrefixEndpointRun](../../Erdos249257/SuffixCylinderStage51.lean#L495)
- Lean declaration: [SelectedHalfWindow.stepExplicit_preserves_literalPrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L258)
- Lean declaration: [supportCoeff_word_eq_of_restrict_before_feedback](../../Erdos249257/SuffixCylinderThreshold.lean#L343)

- outgoing **reformulates**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). it replaces a whole band of stage advances by a scalar recurrence on the endpoint.
- incoming **finite_instance_of**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). the 22-row endpoint evaluation is the scalar recurrence at the literal cutoff-25 word.
- incoming **depends_on_open**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). the nearest producer of a common next-row coefficient: before a row is reached by feedback the coefficient is fixed by the literal cutoff restriction, so representatives sharing that restriction share C. It stops exactly at the feedback rows, which is why hp_common is realised only at depths 18 and 26.

<a id="node-05a80c3c58b98c35"></a>
## macro_swallow_quarter_band_bound

If a two-row macro step swallows the next strip and the two sheets' combined coefficient pulses differ by at most two, then the old gap already occupied at least a quarter of the next strip bound, up to the sharp additive two: nextBound <= 4*(b - a + 1) + 2. This is a necessary condition on the swallow branch, not an exclusion of it.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is deliberately not a barrier: the module states that it does not assert the quarter-band branch is impossible, and nothing in this zone excludes it.

- Lean declaration: [nextBound_le_four_gapWidth_add_two_of_macro_swallow](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L254)

- outgoing **specialises**: [Z16::gap_width_recurrence](BROWSER_Z16_1.md#node-bb41c657e044dea7). it is the two-row width recurrence read as a necessary condition on the swallow branch.

<a id="node-f8ce3cc87ef6ecb4"></a>
## one_bit_cutoff_promotion

One-bit promotion with exact endpoint arithmetic. If the endpoint is at least one full window width above the head weight the newly common bit is true, the cylinder promotes to cutoff K+1 and the endpoint drops by exactly the head weight; if the endpoint is at or below the head weight the newly common bit is false and the endpoint is unchanged. Both forms also refine the shared prefix to the literal word extended by that bit, and both persist to the covering condition R <= new endpoint. The same statement is proved for windows indexed by an initial carry segment and for families indexed by a shifted closed interval, and is packaged as the promoteHigh / promoteLow operations on full-strip stages.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold](../../Erdos249257/SuffixCylinderStage51.lean#L40)
- Lean declaration: [promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint](../../Erdos249257/SuffixCylinderThreshold.lean#L120)
- Lean declaration: [promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold](../../Erdos249257/SuffixCylinderThreshold.lean#L163)
- Lean declaration: [restrictWord_succ_eq_extend_true_of_headThreshold_add_width_le_endpoint](../../Erdos249257/SuffixCylinderThreshold.lean#L206)
- Lean declaration: [CylinderStage.promoteHigh](../../Erdos249257/SuffixCylinderThreshold.lean#L888)
- Lean declaration: [selectedHalfWindowPromoteLow](../../Erdos249257/SuffixCylinderProfiledPromotion.lean#L50)
- Lean declaration: [selectedHalfIntervalPromoteHigh](../../Erdos249257/SuffixCylinderProfiledPromotion.lean#L107)
- Lean declaration: [promoteSuffixCylinderAt_succ_of_commonRestriction](../../Erdos249257/SuffixCylinderPromotion.lean#L231)
- Lean declaration: [CylinderStage.promoteLow](../../Erdos249257/SuffixCylinderGlobalProducer.lean#L158)

- outgoing **specialises**: [Z16::head_threshold_promotion_criterion](BROWSER_Z16_1.md#node-a034881200ee26b1). the two promotion lemmas are the two sides of the criterion with the endpoint arithmetic attached.
- incoming **finite_instance_of**: [Z16::first_feedback_promotion_depth_27_to_29](BROWSER_Z16_1.md#node-dc4415c505244611). the depth-27 promotion is the high-side lemma at K = 13, E = 8389.
- incoming **finite_instance_of**: [Z16::depth29_cutoff25_normalisation](BROWSER_Z16_1.md#node-af558350a7b26d45). eleven concrete low-side and high-side promotions of one window.

<a id="node-8fc1866d2affdf7b"></a>
## parent_gap_doubling_law

Exact iteration law for the canonical fixed-coefficient parent map. A target carry q has parent h if and only if q equals 2h - C or 2h - C - 1; equivalently q avoids the parent h exactly when it avoids both of those two adjacent children. For a closed forbidden parent block [a,b] the pullback under one row is exactly the closed child block [2a - C - 1, 2b - C], whose untruncated integer width is exactly doubled.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: All three evidence lemmas are literal iffs (parent C q = h <-> ..., parent C q != h <-> ..., a <= parent C q <= b <-> ...). Both sides of each are decidable statements of Nat/Int arithmetic about the fixed map k -> 2k - C - bit; neither side is an open problem, so this is a closed classification, not a restatement. It is about the canonical fixed-coefficient parent only, not about admissibility of the resulting words.

- Lean declaration: [parent_eq_iff_eq_two_adjacent_children](../../Erdos249257/SuffixCylinderInStrip.lean#L162)
- Lean declaration: [parent_ne_iff_avoids_two_adjacent_children](../../Erdos249257/SuffixCylinderInStrip.lean#L189)
- Lean declaration: [parent_mem_interval_iff_mem_doubled_child_interval](../../Erdos249257/SuffixCylinderInStrip.lean#L212)

- incoming **specialises**: [Z16::two_sheet_next_row_off_child_gap](BROWSER_Z16_2.md#node-b2488aa5c69c6e63). the surviving child set is the complement of the two adjacent children of the old hole.
- outgoing **reformulates**: [Z15::fixed_coefficient_parent_cover](BROWSER_Z15_1.md#node-bc784f2cd72bb27b). parent_eq_iff_eq_two_adjacent_children and explicitParent_recurrence are the same relation q + C + bit = 2 * parent C q, read once as an iff on the parent map and once as a cover of the target interval.

<a id="node-ca287b00ab093584"></a>
## pre_feedback_run_to_depth_27

Starting from the certified depth-18 executable base, whose twelve words share a depth-13 prefix and have common endpoint 17, the canonical selected successor runs unbroken through depth 27 while preserving the depth-13 suffix cylinder, because every proper divisor read before row 28 lies at or below that prefix. The endpoints are exactly 17, 34, 67, 132, 263, 526, 1049, 2098, 4195, 8389 at depths 18 through 27, computed from the base prefix coefficients 0,1,2,1,0,3,0,1,1. The output is a full protected selected window at depth 27 on the whole strip, with an admissible word for every terminal carry.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [nonempty_stage_of_eighteen_le_of_le_twentySeven](../../Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L118)
- Lean declaration: [depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen](../../Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L141)
- Lean declaration: [depth27SelectedHalfWindow_endpoint_covers_strip](../../Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L147)
- Lean declaration: [depth27SelectedHalfWindow_admissible](../../Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L153)

- outgoing **finite_instance_of**: [Z16::suffix_cylinder_endpoint_propagation](BROWSER_Z16_1.md#node-c67d33b8d0a3d858). ten concrete applications of the endpoint step at depths 18 through 27.
- outgoing **finite_instance_of**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). the run produces a full protected selected window on the whole square-root strip at every depth 18..27, i.e. HalfCarryFullStripReachabilityAt N for ten consecutive N and no more.
- outgoing **finite_instance_of**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). the ten iterated Stage.step outputs are selected protected windows with positive radius at depths 18..27, instances of the cofinal window supply this consumer assumes from some N0 onward.

<a id="node-459826d313d51117"></a>
## profiled_cutoff_promotion

At an odd feedback boundary N = 2M + 1 with M >= 4, the square-root strip lies below the new binary head weight 2^M, so the lower sheet promotes through a false head bit with its endpoint unchanged, while the endpoint-separation invariant puts the entire upper interval a full head weight beyond that boundary and forces a true head bit, dropping its endpoint by exactly 2^M. The carry gap and both selected families are unchanged; only the extracted prefixes and the upper endpoint are renormalised, and the promoted cutoff is again ready for the next coefficient row.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [ProfiledGapStage.promoteCutoff](../../Erdos249257/SuffixCylinderProfiledPromotion.lean#L168)

- outgoing **implies**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). promotion at N = 2M+1 restores readiness so that another profiled row is available.

<a id="node-98206c2f8a389f38"></a>
## profiled_gap_advance

Profiled successor for a finite carry gap with two independent sheet prefixes and two independent coefficients: the child gap is [2*gapLo - lowerCoeff - 1, 2*gapHi - upperCoeff], and both cylinders, both literal prefixes, the endpoint-separation invariant and the strip cover are propagated. At a ready cutoff the coefficient profile and the divisor buffer are synthesized internally, so the step consumes only a four-inequality arithmetic cell; promote-then-advance packages a feedback-boundary promotion followed by such a step.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hnext : T.NextArithmetic, i.e. the four inequalities childLoPos : 1 <= 2 * T.gapLo - T.lowerNextCoeff - 1; upperCoeffFits : T.upperNextCoeff <= 2 * T.gapHi; childOrder : 2 * T.gapLo - T.lowerNextCoeff - 1 <= 2 * T.gapHi - T.upperNextCoeff; childHiStrip : 2 * T.gapHi - T.upperNextCoeff <= halfStripBound (N + 1). Nothing in this zone proves that a canonical profiled gap satisfies these along any infinite run; the gap-width recurrence in fact shows the child gap width doubles each row while the strip bound grows like 2*sqrt(N), so childHiStrip is exactly the unproved control.", "hready : T.Ready, i.e. N <= 2 * M - required for the coefficient profile, restored at a feedback boundary only by promoteCutoff and otherwise assumed"]

- Lean declaration: [ProfiledGapStage.advanceOfNextCoeffProfile](../../Erdos249257/SuffixCylinderProfiledGap.lean#L124)
- Lean declaration: [ProfiledGapStage.advanceOfReady](../../Erdos249257/SuffixCylinderProfiledAutoStep.lean#L70)
- Lean declaration: [ProfiledGapStage.promoteThenAdvance](../../Erdos249257/SuffixCylinderProfiledAutoStep.lean#L101)

- outgoing **repair_of**: [Z16::common_next_coeff_gap_advance](BROWSER_Z16_1.md#node-aa8dc9cf22b9c781). it drops the non-iterable cross-sheet coefficient equality in favour of two independent per-sheet coefficients.
- incoming **implies**: [Z16::ready_cutoff_determines_per_sheet_coefficients](BROWSER_Z16_1.md#node-1c6fd9fe51135010). readiness supplies automatically the coefficient profile that the advance would otherwise have to assume.
- incoming **implies**: [Z16::profiled_cutoff_promotion](BROWSER_Z16_1.md#node-459826d313d51117). promotion at N = 2M+1 restores readiness so that another profiled row is available.
- outgoing **depends_on_open**: [Z16::gap_width_recurrence](BROWSER_Z16_1.md#node-bb41c657e044dea7). its unproved childHiStrip inequality is exactly the width control that the doubling recurrence makes non-automatic against a strip bound growing like 2*sqrt(N).
- incoming **depends_on_open**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). the residual two-sheet branch can only be continued through the unproved NextArithmetic cell, so it supplies no stages either.
- outgoing **depends_on_open**: [Z10::divisor_pair_square_root_envelope](BROWSER_Z10_1.md#node-1d5f5df7a851affd). the only unconditional control available for the NextArithmetic cell; it bounds each next-row coefficient by 2*sqrt(n) but says nothing about gap width, and gap_width_recurrence shows the child gap doubles each row while halfStripBound grows like 2*sqrt(N), so childHiStrip cannot be produced from it.

<a id="node-1c6fd9fe51135010"></a>
## ready_cutoff_determines_per_sheet_coefficients

If the retained cutoff M of a profiled gap still covers the next row (N <= 2M), then each sheet's next-row divisor coefficient is exactly the coefficient of its own retained literal prefix. This produces the per-sheet coefficient profile automatically and, unlike the cross-sheet common-coefficient requirement it replaces, it survives cutoff promotion, since the two prefixes are allowed to differ.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [ProfiledGapStage.hasNextCoeffProfile_of_ready](../../Erdos249257/SuffixCylinderProfiledGap.lean#L100)

- outgoing **implies**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). readiness supplies automatically the coefficient profile that the advance would otherwise have to assume.
- outgoing **supersedes**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). The Z15 step requires all representatives of the window to share the SAME next-row proper-divisor coefficient C. ProfiledGapStage.hasNextCoeffProfile_of_ready derives each sheet's next-row coefficient from its own retained literal prefix whenever N <= 2M, producing the per-sheet profile automatically; the Z16 node records that this replaces the cross-sheet common-coefficient requirement and, unlike it, survives cutoff promotion.

<a id="node-7803df419e54746c"></a>
## rewind_history_promotion_dichotomy

For a window carrying a width-valid exact rewind history back to a base window with a suffix cylinder, either the cylinder promotes through the next prefix bit (with the endpoint covering the carry window), or the two adjacent base ancestors are literally the marked true/false boundary pair; at a full-strip feedback row this yields either a promoted cylinder or a realized localized one-hole protected even seam.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hprov : W.HasRewindRestrictionAt W0 hMN cs - an exact rewind history of the current window back to a base window", "hwidth : halfStripBound N <= denom cs - width validity of that history. Nothing inside this zone produces such a history at an arbitrary feedback row; the later GlobalProducer route was written precisely to obtain the same dichotomy from the cylinder itself without a retained history."]

- Lean declaration: [commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt](../../Erdos249257/SuffixCylinderPromotion.lean#L128)
- Lean declaration: [promoteSuffixCylinderAt_succ_or_boundaryPair_of_rewindHistory](../../Erdos249257/SuffixCylinderPromotion.lean#L281)
- Lean declaration: [promotedSuffixCylinder_or_protectedEvenSeamRealizedAt](../../Erdos249257/SuffixCylinderPromotion.lean#L322)

- outgoing **generalises**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). the cylinder route obtains the same advance-or-seam dichotomy without assuming a retained rewind history, so the history version is superseded.
- outgoing **repair_of**: [Z15::boundary_pair_not_forced_by_scalar_seam](BROWSER_Z15_1.md#node-8251970cbe05aaa5). The barrier shows one instance where exact rewind provenance plus a width-valid scalar seam pair does not entail RewindBaseHalfDivisorBoundaryPairAt. commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt replaces that unforced implication by a total dichotomy: either the suffix cylinder promotes through the next prefix bit, or the two adjacent base ancestors are literally the marked true/false boundary pair - so no route needs the boundary pair to be forced.
- outgoing **reformulates**: [Z15::object_level_singleton_or_seam_dichotomy](BROWSER_Z15_1.md#node-d21154a1df7943f3). commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt and scalarHistoryAlternative_of_rewindHistory are the same width dichotomy (promotion / divisor agreement, or an adjacent-ancestor seam pair) at cylinder and scalar level.
- outgoing **depends_on_open**: [Z15::rewind_provenance_of_explicit_step](BROWSER_Z15_1.md#node-e7f9bf1bfcde38a1). this produces HasRewindRestrictionAt unconditionally along any chain of canonical fixed-coefficient steps, so the provenance half of the hypothesis is available on such chains; the width validity halfStripBound N <= denom cs at an arbitrary feedback row is produced nowhere.

<a id="node-5f954bbf6382c7ff"></a>
## shifted_interval_cylinder_machinery

Selected families indexed by an arbitrary closed carry interval (possibly empty) support the same canonical fixed-coefficient successor as initial-segment windows, provided the coefficient hypothesis is imposed only on the canonical parents actually used. The successor preserves admissibility and the exact terminal-carry identity, preserves any common literal cutoff prefix, and propagates an interval suffix cylinder with the same endpoint law E' = 2E - C. Separately, one arbitrary admissible parent word with known terminal carry and known next coefficient already realizes its two children, so no initial carry segment is needed to advance a shifted sheet.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfTerminalReachable_succ_of_admissibleParent](../../Erdos249257/SuffixCylinderInStrip.lean#L325)
- Lean declaration: [selectedHalfIntervalStepExplicit_preserves_literalPrefix](../../Erdos249257/SuffixCylinderFiniteGap.lean#L141)
- Lean declaration: [selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit](../../Erdos249257/SuffixCylinderFiniteGap.lean#L164)

- outgoing **generalises**: [Z16::suffix_cylinder_endpoint_propagation](BROWSER_Z16_1.md#node-c67d33b8d0a3d858). the same endpoint law is proved for families indexed by an arbitrary closed carry interval.
- outgoing **generalises**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). Z16 carries the canonical fixed-coefficient successor for families indexed by an arbitrary closed carry interval, imposing the coefficient hypothesis only on the canonical parents actually used (`selectedHalfIntervalStepExplicit_preserves_literalPrefix`, `selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit`); Z15's `SelectedHalfWindow.stepExplicit` on an initial carry segment is the special case.

<a id="node-47b1c3f543a0b11d"></a>
## singleton_gap_no_swallow

A one-point tracked gap with binary-adjacent sheet prefixes can never swallow the next strip: swallowing would force the next strip bound to be at most three, while every square-root strip has width at least four. In particular the initial one-hole profiled state, and any later profiled state whose gap has returned to a single point, always has a canonical parent in one of its two tracked sheets at the next row.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Scoped to the two sheets the stage tracks. trackedParentSurvives_of_singletonGap is about the TrackedParentSurvives predicate only, and its stage form additionally consumes the adjacency invariant (HasAdjacentPrefixes) plus the built-in strip buffer; by the module's own header a ProfiledGapStage is a selected witness subtree, not an exhaustivity certificate, so 'never swallows' means the tracked pair still supplies a canonical parent, NOT that the construction survives. It also says nothing about gaps of width two or more, where the swallow cell is not excluded (see macro_swallow_quarter_band_bound), and nothing about whether a canonical profiled gap ever returns to a single point.

- Lean declaration: [trackedParentSurvives_of_singletonGap](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L153)
- Lean declaration: [ProfiledGapStage.trackedNextParentSurvives_of_singletonGap](../../Erdos249257/SuffixCylinderProfiledSwallow.lean#L168)

- outgoing **specialises**: [Z16::tracked_parent_survival_normal_form](BROWSER_Z16_2.md#node-87c9d7f712ef9c84). it is the normal form evaluated at a one-point gap using the adjacency coefficient bound.

<a id="node-c67d33b8d0a3d858"></a>
## suffix_cylinder_endpoint_propagation

Under the canonical explicit successor of a selected window at a row whose coefficient C is common to all carries, the suffix cylinder propagates: the cutoff is unchanged, and the endpoint updates by exactly E' = 2E - C. The same window buffer that makes the successor well formed also proves the new endpoint still covers the whole new carry interval.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit](../../Erdos249257/SelectedSuffixCylinder.lean#L136)

- outgoing **specialises**: [Z16::endpoint_indexed_suffix_cylinder_calculus](BROWSER_Z16_1.md#node-fe2a93ce8cb81ca0). the E' = 2E - C law is the one-bit suffix-numeral doubling identity applied along the canonical successor.
- incoming **specialises**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). the stage advance is the propagation law applied on the full square-root strip.
- incoming **generalises**: [Z16::shifted_interval_cylinder_machinery](BROWSER_Z16_1.md#node-5f954bbf6382c7ff). the same endpoint law is proved for families indexed by an arbitrary closed carry interval.
- incoming **finite_instance_of**: [Z16::pre_feedback_run_to_depth_27](BROWSER_Z16_1.md#node-ca287b00ab093584). ten concrete applications of the endpoint step at depths 18 through 27.

