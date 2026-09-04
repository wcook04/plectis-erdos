# Z15_2: Selected protected windows and the fixed-coefficient rewind seam

[All problems and zones](BROWSER.md)

<a id="node-628caa7217f6f389"></a>
## threshold_profile_realizes_protected_seam

A window whose next-row coefficients follow a two-valued threshold profile (c+1 below the threshold delta, c above) realizes the localized one-hole even seam at depth N+1 on the protected carries 3..27, provided 27 <= S <= halfStripBound (N+1) and the buffer S + (c+1) <= 2R. The same holds stated in the selectedRowCoeff coordinate.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hprofile : forall h in [1,R], supportCoeff (wordSupport (W.word h)) (N+1) = if h <= delta then c+1 else c (a two-valued threshold coefficient profile across the whole protected window) -- never established for any window in this corpus", "the existence of the window W : SelectedHalfWindow N R with R large enough for the buffer S + (c+1) <= 2R at 27 <= S"]

- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_profile](../../Erdos249257/RewindSeamOperationalBridge.lean#L217)
- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_selectedRowCoeff_threshold](../../Erdos249257/RewindSeamOperationalBridge.lean#L317)

- incoming **implies**: [Z15::selected_parent_realizes_both_children](BROWSER_Z15_1.md#node-3cf8358ae1e4bd65). every branch of the EvenSeamReachable case split is closed by realizing one child of a selected parent
- outgoing **implies**: [Z15::rewind_seam_plus_unit_drop_realizes_protected_seam](BROWSER_Z15_1.md#node-a6029d30ac804cf0). the rewind-seam theorem is the threshold theorem with the profile supplied by provenance
- incoming **supersedes**: [Z16::two_sheet_hole_only_reachability](BROWSER_Z16_2.md#node-4425f8a68a1bbc68). InStripTwoSheetStage.halfTerminalReachable_of_ne_hole realizes every terminal carry of the full square-root strip except the single hole - the Z16 node states this is strictly stronger than the protected 3..27 realization interface - and InStripTwoSheetStage.protectedEvenSeamRealizedAt reproduces the same consumer that protectedEvenSeamRealizedAt_succ_of_profile was built to feed, without the two-valued threshold-profile hypothesis.
- outgoing **depends_on_open**: [Z16::crossing_unit_drop_profile](BROWSER_Z16_1.md#node-fcdeb390d153df7d). the corpus's only producer of a two-valued threshold coefficient profile (c+1 on the initial carry segment, c above); it requires a genuine endpoint crossing of the head weight, so it produces the profile at crossing feedback rows only, not across an arbitrary window.
- incoming **generalises**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). Z15's `protectedEvenSeamRealizedAt_succ_of_profile` assumes the two-valued threshold coefficient profile; Z16's `supportCoeff_profile_of_crossingSuffixCylinder` proves that exact profile for a crossing endpoint cylinder, so `protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder` reaches the same conclusion with the profile hypothesis discharged.
- incoming **generalises**: [Z16::two_sheet_hole_only_reachability](BROWSER_Z16_2.md#node-4425f8a68a1bbc68). `InStripTwoSheetStage.halfTerminalReachable_of_ne_hole` realizes every terminal carry of the full square-root strip except the single hole, and `InStripTwoSheetStage.protectedEvenSeamRealizedAt` projects that onto the localized 3..27 ProtectedEvenSeamRealizedAt interface Z15 produces; the two-sheet state is the strictly stronger object.

