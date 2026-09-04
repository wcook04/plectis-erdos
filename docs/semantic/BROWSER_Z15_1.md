# Z15_1: Selected protected windows and the fixed-coefficient rewind seam

[All problems and zones](BROWSER.md)

<a id="node-4c945b493ad4307d"></a>
## actual_history_affine_realization

For any set P and any M, L with 1 <= M, the actual coefficient history of P satisfies the exact affine identity K_P(M+L-1) + offset(history) + 1 = denom(history) * (K_P(M-1) + 1). Combined with the truncation identity, a terminal carry of one at row M+L gives the natural-number realization equation offset + X + 2 = denom * (ancestor + 1) for the truncated history, which is exactly the hypothesis the phase identity needs.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [integerHalfCarry_add_offset_eq_denom_mul_initial](../../Erdos249257/HalfCarryRewindPhase.lean#L239)
- Lean declaration: [supportHistory_realization](../../Erdos249257/HalfCarryRewindPhase.lean#L272)

- outgoing **implies**: [Z15::realized_history_phase_identity](BROWSER_Z15_1.md#node-7a7d16f86fdf5ae9). the affine identity is exactly the realization equation the phase identity assumes, so it is discharged for live histories
- incoming **implies**: [Z15::prefix_truncation_adds_suffix_numeral](BROWSER_Z15_1.md#node-7fa45c879f5b2789). the truncation identity supplies the carry-one endpoint K_{A cap [0,M]}(M+L-1) = 1 + X that supportHistory_realization consumes; neither node has an open dependence, so the previous depends_on_open label contradicted its own basis text

<a id="node-8251970cbe05aaa5"></a>
## boundary_pair_not_forced_by_scalar_seam

At the depth-26 two-carry window with history [1], the right adjacent rewind ancestor still has bit 14 set to true. Therefore no depth-13 word can make the two adjacent ancestors the true/false terminal extensions required by the marked half-divisor boundary-pair predicate at half divisor 14. Consequently the conjunction of exact rewind provenance, a genuine width-valid scalar seam pair, and the doubled-row identity 27 + 1 = 2*(13+1) does NOT entail RewindBaseHalfDivisorBoundaryPairAt.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This rules out ONE implication at ONE instance, and much less than a reader might assume. (1) It does not touch RewindBaseUnitDropAt, which is the hypothesis the operational seam theorem actually consumes; the half-divisor boundary pair is only one sufficient route to that unit drop, so the operational seam route is NOT closed. (2) The falsifying window has radius R = 2 and one-row history [1] with denominator 2, whereas the cofinal consumer needs 27 <= S and S + (c+1) <= 2R, i.e. R >= 14, and needs denom(cs) >= R, i.e. histories of length at least 4; the module's own docstring concedes the protected-window buffer is 'intentionally absent'. The counterexample therefore lives entirely outside the parameter regime of interest. (3) It says nothing about other depths, other marked half divisors, other base windows, longer coefficient histories, full-strip windows, or the divisor-agreement (singleton) branch. (4) It does not show the boundary-pair predicate is false at large depths; only that scalar one-row seam data does not force it. (5) NOT FORMALISED, but checkable from the certified table and recorded here so point (1) is not read the wrong way: at this same instance RewindBaseUnitDropAt also fails. Row 28 has divisors 1,2,4,7,14,28; both depth26Word 1 and depth26Word 2 carry exponents 2,7,14 and neither carries 1 or 4, and 28 is beyond depth 26, so both adjacent ancestors have row-28 coefficient 3 and no c satisfies 3 = c+1 and 3 = c. (The same evaluation reproduces the kernel-proved row-27 coefficient 1, so the arithmetic mirror is sound.) The instance is therefore not evidence that the operational unit-drop route survives where the boundary-pair route dies; it is simply an instance the zone's Lean says nothing about. The barrier as formalised still closes only the boundary-pair implication.

- Lean declaration: [depth26RightAncestor_bit14_true](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L145)
- Lean declaration: [depth26FirstTwo_not_rewindBaseHalfDivisorBoundaryPairAt](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L155)
- Lean declaration: [depth27_actualRewindSeam_not_boundaryPair](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L169)

- outgoing **barrier_for**: [Z15::boundary_pair_supplies_unit_drop](BROWSER_Z15_1.md#node-03f57ba7c8b09eec). it falsifies the boundary-pair antecedent at a concrete instance with provenance, seam and doubled row all present
- incoming **finite_instance_of**: [Z15::depth26_two_carry_window_and_step](BROWSER_Z15_1.md#node-457242e6650bec54). the certified depth-26/27 pair is the carrier of the falsifier
- incoming **repair_of**: [Z16::rewind_history_promotion_dichotomy](BROWSER_Z16_1.md#node-7803df419e54746c). The barrier shows one instance where exact rewind provenance plus a width-valid scalar seam pair does not entail RewindBaseHalfDivisorBoundaryPairAt. commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt replaces that unforced implication by a total dichotomy: either the suffix cylinder promotes through the next prefix bit, or the two adjacent base ancestors are literally the marked true/false boundary pair - so no route needs the boundary pair to be forced.

<a id="node-56fe7a4c2fd7cb6a"></a>
## boundary_pair_realizes_protected_seam

If the produced row is exactly twice the marked half divisor (N + 1 = 2(K+1)), a half-divisor boundary pair discharges the only extra semantic hypothesis of the rewind-seam realization theorem, giving a localized realized one-hole seam at depth N+1 with hole parameter seamCut(cs). A full-strip variant needs no explicit buffer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Its antecedent hpair is exactly the predicate falsified by boundary_pair_not_forced_by_scalar_seam at the depth-26/27 instance, where exact rewind provenance, a genuine width-valid scalar seam pair and the doubled-row identity 27+1 = 2*(13+1) all hold. So this theorem has no certified instance and is known not to be reachable from provenance + seam + doubled row alone. The cross-reference is stated in boundary_pair_supplies_unit_drop but was missing here.

Open hypotheses: ["hpair : RewindBaseHalfDivisorBoundaryPairAt W0 hKM cs a at cofinally many depths", "hprov + hseam: selected windows with exact rewind provenance and a width-valid scalar seam pair at cofinally many depths"]

- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_rewindHalfDivisorBoundaryPair](../../Erdos249257/RewindHalfDivisorAdapter.lean#L120)
- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindHalfDivisorBoundaryPair](../../Erdos249257/RewindHalfDivisorAdapter.lean#L147)

- incoming **implies**: [Z15::boundary_pair_supplies_unit_drop](BROWSER_Z15_1.md#node-03f57ba7c8b09eec). the boundary pair discharges RewindBaseUnitDropAt in the rewind-seam realization theorem
- incoming **specialises**: [Z15::rewind_seam_plus_unit_drop_realizes_protected_seam](BROWSER_Z15_1.md#node-a6029d30ac804cf0). the adapter instantiates the unit-drop hypothesis by the structural boundary-pair predicate

<a id="node-03f57ba7c8b09eec"></a>
## boundary_pair_supplies_unit_drop

If the two adjacent rewind ancestors restrict, through the marked half divisor K+1, to the true and false terminal extensions of one common depth-K word (with the base depth M satisfying K+1 <= M < 2(K+1)), then the unit coefficient drop RewindBaseUnitDropAt holds at the doubled row 2(K+1) with c the coefficient of the false extension.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hpair : RewindBaseHalfDivisorBoundaryPairAt W0 hKM cs a (the two adjacent rewind ancestors are the opposite terminal extensions of one common half-depth word) -- unproved in general, and demonstrably false at the depth-26 instance in this same zone"]

- Lean declaration: [rewindBaseUnitDropAt_of_halfDivisorBoundaryPair](../../Erdos249257/RewindHalfDivisorAdapter.lean#L86)

- incoming **implies**: [Z15::half_divisor_bit_unit_drop](BROWSER_Z15_1.md#node-734cf5a2f912a631). the boundary pair reduces the two ancestors to opposite terminal extensions, where the unit drop is the bit identity
- outgoing **implies**: [Z15::boundary_pair_realizes_protected_seam](BROWSER_Z15_1.md#node-56fe7a4c2fd7cb6a). the boundary pair discharges RewindBaseUnitDropAt in the rewind-seam realization theorem
- incoming **barrier_for**: [Z15::boundary_pair_not_forced_by_scalar_seam](BROWSER_Z15_1.md#node-8251970cbe05aaa5). it falsifies the boundary-pair antecedent at a concrete instance with provenance, seam and doubled row all present
- outgoing **depends_on_open**: [Z16::boundary_words_binary_consecutive](BROWSER_Z16_1.md#node-4f7bd3fd6e31ca03). the nearest producer of the boundary-pair shape: the two sheet boundary words are consecutive binary numerals. It does not give that the two adjacent rewind ancestors are the opposite terminal extensions of one common half-depth word, and boundary_pair_not_forced_by_scalar_seam refutes that at depth 26.

<a id="node-8914ed1068ade432"></a>
## cofinal_protected_seam_consumer

A one-hole even seam cannot delete both protected carries 3 and 4, since its unique hole is 2*delta - c. Hence a cofinal supply of localized realized one-hole seams (forward realization only, on carries 3..27) yields cofinal finite admissibility, and therefore an infinite A whose Mersenne series sums to exactly 1/2.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : HalfCarryCofinalProtectedEvenSeamRealization, i.e. forall N, exists M >= N and delta, c with ProtectedEvenSeamRealizedAt M delta c -- no theorem in the corpus produces this at even one large depth"]

- Lean declaration: [cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization](../../Erdos249257/HalfCarryProtectedSeamConsumer.lean#L31)
- Lean declaration: [exists_infinite_support_half_of_cofinalProtectedEvenSeamRealization](../../Erdos249257/HalfCarryProtectedSeamConsumer.lean#L53)

- incoming **implies**: [Z15::rewind_seam_plus_unit_drop_realizes_protected_seam](BROWSER_Z15_1.md#node-a6029d30ac804cf0). the seam-realization theorem produces exactly the ProtectedEvenSeamRealizedAt receipt the consumer collects
- outgoing **specialises**: [Z15::mixed_cofinal_window_or_seam_consumer](BROWSER_Z15_1.md#node-e5cf1d1a8c038506). the mixed consumer is the seam consumer with a disjunctive receipt
- outgoing **transport_of**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization (HalfCarryProtectedSeamConsumer.lean) converts the cofinal localized one-hole seam supply into the same cofinal admissibility antecedent.
- outgoing **depends_on_open**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). the only law whose conclusion can be a realized localized one-hole protected even seam; it fires at one feedback row of an EXISTING full-strip stage, so it produces seams only as far as stages exist (depth 52), never cofinally.
- outgoing **specialises**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). `cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization` (HalfCarryProtectedSeamConsumer.lean:31) derives the same `HalfCarryCofinalAdmissibility` antecedent from the cofinal localized-seam hypothesis; identical conclusion.

<a id="node-7dc33561132cdf17"></a>
## depth18_selected_window_base

A kernel-reflected Boolean table (twelve words, exponents 2,3,6,7 common and exponents 14..18 encoding 17-k) certifies a selected protected window at depth 18 covering the entire square-root strip halfStripBound 18 = 12. All twelve representatives restrict to the same depth-13 word, so the base already carries next-row divisor agreement at row 19.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [depth18TableCheck_eq_true](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L79)
- Lean declaration: [depth18SelectedHalfWindow](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L129)
- Lean declaration: [depth18SelectedHalfWindow_commonRestrictionAt_thirteen](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L161)
- Lean declaration: [depth18SelectedHalfWindow_nextRowDivisorAgreement](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L172)

- outgoing **finite_instance_of**: [Z15::full_strip_step_from_divisor_agreement](BROWSER_Z15_1.md#node-80222181e708c6f3). the depth-18 table is the only certified input the agreement step has ever been applied to
- incoming **implies**: [Z15::executable_word_carry_bridge](BROWSER_Z15_1.md#node-b7a7186174fa836e). the kernel-reduced Boolean table is transferred to the live carry by the bridge
- outgoing **finite_instance_of**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). the depth-18 kernel-reflected table realises every terminal carry up to halfStripBound 18 = 12, i.e. HalfCarryFullStripReachabilityAt 18 - the predicate this conditional needs at every level, supplied here at exactly one level.
- outgoing **finite_instance_of**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). the twelve certified representatives are strip-admissible finite words at depth 18, one level of the cofinal-admissibility hypothesis.

<a id="node-457242e6650bec54"></a>
## depth26_two_carry_window_and_step

A kernel-reflected table certifies a selected window at depth 26 on carries 1 and 2 only (exponents 2,3,6,7,14,20 common, 21..26 encoding 35-k). Both representatives have actual common row-27 coefficient one, so the canonical explicit step is available and produces a depth-27 window on the same two carries whose recorded rewind history is the one-row list [1]; that history has denominator two and makes [1,2] a genuine scalar seam pair.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [depth26FirstTwoCheck_eq_true](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L46)
- Lean declaration: [depth26FirstTwo](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L89)
- Lean declaration: [depth26FirstTwo_selectedRowCoeff_eq_one](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L104)
- Lean declaration: [depth27FirstTwo](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L114)
- Lean declaration: [depth27FirstTwo_hasRewindRestrictionAt](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L123)
- Lean declaration: [oneRowHistory_isSeamPair](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L137)
- Lean declaration: [oneRowHistory_width](../../Erdos249257/RewindBoundaryPairCounterexample.lean#L140)

- incoming **implies**: [Z15::executable_word_carry_bridge](BROWSER_Z15_1.md#node-b7a7186174fa836e). same transfer for the depth-26 table
- outgoing **finite_instance_of**: [Z15::boundary_pair_not_forced_by_scalar_seam](BROWSER_Z15_1.md#node-8251970cbe05aaa5). the certified depth-26/27 pair is the carrier of the falsifier
- outgoing **finite_instance_of**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). the depth-26 and derived depth-27 tables give strip-admissible words at those two levels; note it is a window on carries 1 and 2 ONLY, so it instantiates cofinal admissibility but NOT full-strip reachability.

<a id="node-b7a7186174fa836e"></a>
## executable_word_carry_bridge

The fully computable divisor coefficient and carry recursion on finite Boolean words agree with the Set-based support coefficient of wordSupport and with the integer half carry of that set. This is what lets kernel-reduced Boolean tables certify statements about the live carry.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [wordCoeff_eq_supportCoeff_wordSupport](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L22)
- Lean declaration: [wordCarry_eq_integerHalfCarry](../../Erdos249257/HalfCarrySelectedWindowBase.lean#L46)

- outgoing **implies**: [Z15::depth18_selected_window_base](BROWSER_Z15_1.md#node-7dc33561132cdf17). the kernel-reduced Boolean table is transferred to the live carry by the bridge
- outgoing **implies**: [Z15::depth26_two_carry_window_and_step](BROWSER_Z15_1.md#node-457242e6650bec54). same transfer for the depth-26 table
- outgoing **reformulates**: [Z12::half_strip_admissible_word_system](BROWSER_Z12_1.md#node-5a97937c528b1bfe). wordCarry_eq_integerHalfCarry and wordCoeff_eq_supportCoeff_wordSupport (HalfCarrySelectedWindowBase.lean) identify the executable Boolean-word carry with the Set-based integerHalfCarry on which HalfStripAdmissible is defined.

<a id="node-bc784f2cd72bb27b"></a>
## fixed_coefficient_parent_cover

If a row's proper-divisor coefficient equals a constant C on every parent carry in [1,R], and the buffer inequality S + C <= 2R holds, then every target carry q in [1,S] has a parent k in [1,R] and a Boolean bit b with q = 2k - C - b. The explicit witness is the canonical ceiling parent k = floor((q + C + 1)/2), for which positivity, the bound k <= R, the Boolean-ness of the residual bit, and the child recurrence all hold identically.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [protectedChild_cover_Icc_of_constant](../../Erdos249257/HalfCarrySelectedWindow.lean#L27)
- Lean declaration: [explicitParent_pos](../../Erdos249257/HalfCarrySelectedWindow.lean#L364)
- Lean declaration: [explicitParent_le](../../Erdos249257/HalfCarrySelectedWindow.lean#L371)
- Lean declaration: [explicitParentBitZ_zero_or_one](../../Erdos249257/HalfCarrySelectedWindow.lean#L382)
- Lean declaration: [explicitParent_recurrence](../../Erdos249257/HalfCarrySelectedWindow.lean#L398)

- outgoing **implies**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). the canonical ceiling parent and Boolean residual bit are what the object-level step extends
- incoming **reformulates**: [Z16::parent_gap_doubling_law](BROWSER_Z16_1.md#node-8fc1866d2affdf7b). parent_eq_iff_eq_two_adjacent_children and explicitParent_recurrence are the same relation q + C + bit = 2 * parent C q, read once as an iff on the parent map and once as a cover of the target interval.

<a id="node-fa3af1821cd45b29"></a>
## fixed_coefficient_window_step

Given a selected protected window at depth N with radius R whose representatives all have the SAME next-row proper-divisor coefficient C, and given the strip condition S <= halfStripBound (N+1) and the buffer S + C <= 2R, one can construct a selected protected window at depth N+1 with radius S. The child for target q is the one-bit extension of the representative at the canonical parent floor((q+C+1)/2).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hp_common : forall k, 1 <= k -> k <= R -> selectedRowCoeff W k = C (all window representatives share one next-row proper-divisor coefficient) -- proved in this corpus only at isolated finite depths (18, 26), never for a cofinal family", "the existence of the input window W : SelectedHalfWindow N R at unbounded N"]

- Lean declaration: [SelectedHalfWindow.stepOpaque](../../Erdos249257/HalfCarrySelectedWindow.lean#L245)
- Lean declaration: [SelectedHalfWindow.stepExplicitWithHistory](../../Erdos249257/HalfCarrySelectedWindow.lean#L417)
- Lean declaration: [SelectedHalfWindow.stepExplicit](../../Erdos249257/HalfCarrySelectedWindow.lean#L517)
- Lean declaration: [SelectedHalfWindow.step](../../Erdos249257/HalfCarrySelectedWindow.lean#L772)

- incoming **implies**: [Z15::fixed_coefficient_parent_cover](BROWSER_Z15_1.md#node-bc784f2cd72bb27b). the canonical ceiling parent and Boolean residual bit are what the object-level step extends
- incoming **implies**: [Z15::one_bit_extension_preserves_admissibility](BROWSER_Z15_1.md#node-310bd79fd25f3cd9). each child is a one-bit extension whose admissibility comes from the extension lemma
- incoming **depends_on_open**: [Z15::rewind_provenance_of_explicit_step](BROWSER_Z15_1.md#node-e7f9bf1bfcde38a1). direction corrected: the open hypothesis (hp_common) is carried by fixed_coefficient_window_step, and it is the provenance theorems that are stated about the object built from it -- matching the convention used by the other depends_on_open edge, where the target node is the one holding the unproved assumption
- incoming **specialises**: [Z15::full_strip_step_from_divisor_agreement](BROWSER_Z15_1.md#node-80222181e708c6f3). the agreement version fixes R = S = halfStripBound and discharges the buffer from the sqrt divisor envelope
- incoming **supersedes**: [Z16::ready_cutoff_determines_per_sheet_coefficients](BROWSER_Z16_1.md#node-1c6fd9fe51135010). The Z15 step requires all representatives of the window to share the SAME next-row proper-divisor coefficient C. ProfiledGapStage.hasNextCoeffProfile_of_ready derives each sheet's next-row coefficient from its own retained literal prefix whenever N <= 2M, producing the per-sheet profile automatically; the Z16 node records that this replaces the cross-sheet common-coefficient requirement and, unlike it, survives cutoff promotion.
- incoming **transport_of**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). CylinderStage.advance is SelectedHalfWindow.stepExplicit with the hp_common hypothesis internalised: a shared prefix forces the common next-row coefficient and the sqrt envelope discharges the buffer, so the cylinder is the hypothesis-free packaging of the same window step.
- outgoing **depends_on_open**: [Z16::literal_prefix_endpoint_run_law](BROWSER_Z16_1.md#node-f4a9608547c0084a). the nearest producer of a common next-row coefficient: before a row is reached by feedback the coefficient is fixed by the literal cutoff restriction, so representatives sharing that restriction share C. It stops exactly at the feedback rows, which is why hp_common is realised only at depths 18 and 26.
- incoming **generalises**: [Z16::shifted_interval_cylinder_machinery](BROWSER_Z16_1.md#node-5f954bbf6382c7ff). Z16 carries the canonical fixed-coefficient successor for families indexed by an arbitrary closed carry interval, imposing the coefficient hypothesis only on the canonical parents actually used (`selectedHalfIntervalStepExplicit_preserves_literalPrefix`, `selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit`); Z15's `SelectedHalfWindow.stepExplicit` on an initial carry segment is the special case.
- incoming **specialises**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). `CylinderStage.advanceWithinCutoff` is the same canonical fixed-coefficient step restricted to a stage whose cutoff already sees every proper divisor of the next row, which discharges Z15's common-coefficient hypothesis (from the shared prefix) and its buffer hypothesis (from the square-root divisor envelope).

<a id="node-80222181e708c6f3"></a>
## full_strip_step_from_divisor_agreement

If a full square-root-strip selected window at depth N has next-row divisor agreement, then a full square-root-strip selected window at depth N+1 exists, with NO extra buffer hypothesis: the common coefficient is read off the carry-1 representative and the buffer halfStripBound(N+1) + C <= 2*halfStripBound(N) is discharged automatically by the sharp divisor envelope C <= 2*sqrt(N+1).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hagree : W.NextRowDivisorAgreement at the depth being stepped -- established in this corpus only for the depth-18 base (and, in a neighbouring zone, for finitely many further depths), never for all large N"]

- Lean declaration: [SelectedHalfWindow.stepOfAgreement](../../Erdos249257/HalfCarrySelectedWindow.lean#L786)

- incoming **implies**: [Z15::restriction_fixes_next_row_coefficient](BROWSER_Z15_1.md#node-49ec48a85fead70c). agreement makes selectedRowCoeff constant, which is the hypothesis the step needs
- outgoing **specialises**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). the agreement version fixes R = S = halfStripBound and discharges the buffer from the sqrt divisor envelope
- incoming **finite_instance_of**: [Z15::depth18_selected_window_base](BROWSER_Z15_1.md#node-7dc33561132cdf17). the depth-18 table is the only certified input the agreement step has ever been applied to
- outgoing **depends_on_open**: [Z16::cylinder_stage_advance_within_cutoff](BROWSER_Z16_1.md#node-0f660c5a0e7275b5). this is the bulk producer of next-row divisor agreement: whenever (N+1)/2 <= K the shared prefix forces a common coefficient and the stage advances unconditionally through the band to N = 2K+1. It produces agreement only inside a cutoff horizon, never at a feedback row.
- incoming **depends_on_open**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). the nearest one-row advance law with a full-strip conclusion, which iterated would give stages at every depth; it is itself gated on next-row divisor agreement and produces selected windows rather than cylinder stages, so the cofinal-stage hypothesis is unproduced.

<a id="node-734cf5a2f912a631"></a>
## half_divisor_bit_unit_drop

At the doubled row 2(N+1), two words that differ only in the terminal bit at exponent N+1 have support coefficients differing by exactly one: the true extension has coefficient one more than the false extension, because N+1 is a divisor of 2(N+1) and no other divisor incidence changes. The identity is restated for any pair of words explicitly identified with those two extensions.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [supportCoeff_extend_true_eq_false_add_one_at_double](../../Erdos249257/HalfDivisorUnitDrop.lean#L20)
- Lean declaration: [supportCoeff_boundaryPair_unitDrop_at_double](../../Erdos249257/HalfDivisorUnitDrop.lean#L35)

- outgoing **implies**: [Z15::boundary_pair_supplies_unit_drop](BROWSER_Z15_1.md#node-03f57ba7c8b09eec). the boundary pair reduces the two ancestors to opposite terminal extensions, where the unit drop is the bit identity
- incoming **reformulates**: [Z16::binary_increment_coefficient_bound](BROWSER_Z16_1.md#node-dcfe937361428149). supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ generalises supportCoeff_extend_true_eq_false_add_one_at_double: consecutive words differ by at most one in divisor coefficient, by exactly one at the half divisor.

<a id="node-38ee19ceeb12b902"></a>
## history_alternative_needs_canonical_seam_bridge

The object-level history alternative (next-row divisor agreement, or an actual canonical one-hole even seam at a doubled row N+1 = 2d) follows from rewind provenance and width ONLY once one assumes a bridge sending the scalar seam pair to an actual canonical even seam. That bridge is assumed, not proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hseamBridge : IsSeamPair cs R -> exists d delta c, N + 1 = 2 * d and IsCanonicalEvenSeam d delta c (the scalar adjacent-ancestor pair is the actual canonical one-hole even seam at the produced row)"]

- Lean declaration: [SelectedHalfWindow.historyAlternative_of_rewindHistory](../../Erdos249257/HalfCarrySelectedWindow.lean#L755)

- incoming **depends_on_open**: [Z15::object_level_singleton_or_seam_dichotomy](BROWSER_Z15_1.md#node-d21154a1df7943f3). the seam branch is closed only by assuming the scalar pair is an actual canonical even seam
- incoming **supersedes**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). SelectedHalfWindow.historyAlternative_of_rewindHistory delivers its disjunction only under an assumed, unproved bridge from the scalar seam pair to an actual canonical even seam. CylinderStage.feedbackStep_or_protectedSeam is total and unconditional at an exact half-divisor horizon: below, above or crossing, with the crossing branch routed through the unit-drop profile into protectedEvenSeamRealizedAt_succ_of_profile, and there is no fourth object-level case.
- incoming **depends_on_open**: [Z12::canonical_even_seam_supply_route](BROWSER_Z12_1.md#node-809811770b153c81). the only route in the corpus toward an ACTUAL canonical one-hole even seam; it delivers one only after assuming the seam bridge from a scalar seam pair, itself unproved, so the canonical-seam supply has no unconditional producer.

<a id="node-c4e16b860a2f525d"></a>
## live_support_singleton_criterion

For an actual support A with terminal carry one at row M+L, before feedback (M + L <= 2M + 1), and for any B with 1 <= B <= denom of the truncated history: the interval [1,B] rewinds to a single ancestor if and only if B - 1 <= X, equivalently if and only if B <= K_{A cap [0,M]}(M+L-1), the carry of the frozen prefix. All phase and suffix encoding is eliminated: the whole singleton question is one inequality between the protected width and the frozen-prefix carry.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [rewind_supportCoeffHistory_singleton_iff](../../Erdos249257/HalfCarryRewindPhase.lean#L327)
- Lean declaration: [rewind_supportCoeffHistory_singleton_iff_prefixCarry_covers](../../Erdos249257/HalfCarryRewindPhase.lean#L352)

- incoming **reformulates**: [Z15::realized_history_phase_identity](BROWSER_Z15_1.md#node-7a7d16f86fdf5ae9). eliminating phase and suffix leaves the single inequality B <= frozen-prefix carry
- incoming **specialises**: [Z15::rewind_dyadic_phase_criterion](BROWSER_Z15_1.md#node-5576062eeee0b5e7). the live criterion is the scalar phase criterion instantiated at an actual truncated support history
- incoming **reformulates**: [Z16::head_threshold_promotion_criterion](BROWSER_Z16_1.md#node-a034881200ee26b1). rewind_supportCoeffHistory_singleton_iff_prefixCarry_covers states the singleton condition as B <= frozen-prefix carry, the same inequality the cylinder criterion states as E <= headweight or headweight + R <= E.

<a id="node-e5cf1d1a8c038506"></a>
## mixed_cofinal_window_or_seam_consumer

At each requested scale it suffices to produce EITHER one selected protected window with positive radius OR one localized realized one-hole seam on carries 3..27; both branches contain an admissible finite word, so the mixed cofinal producer already yields cofinal admissibility and an infinite A summing to exactly 1/2.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : HalfCarryCofinalSelectedWindowOrProtectedSeam, i.e. forall N, exists M >= N such that a selected window with 1 <= R exists at M or a localized realized seam exists at M -- unproved"]

- Lean declaration: [cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam](../../Erdos249257/HalfCarryCofinalWindowOrSeamConsumer.lean#L32)
- Lean declaration: [exists_infinite_support_half_of_cofinalSelectedWindowOrProtectedSeam](../../Erdos249257/HalfCarryCofinalWindowOrSeamConsumer.lean#L58)

- incoming **specialises**: [Z15::cofinal_protected_seam_consumer](BROWSER_Z15_1.md#node-8914ed1068ade432). the mixed consumer is the seam consumer with a disjunctive receipt
- incoming **specialises**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). the window branch of the mixed consumer repeats the selected-window consumer verbatim
- incoming **implies**: [Z15::object_level_singleton_or_seam_dichotomy](BROWSER_Z15_1.md#node-d21154a1df7943f3). the disjunctive interface is shaped to match the singleton-or-seam dichotomy at each depth
- outgoing **depends_on_open**: [Z16::feedback_trichotomy_advance_or_seam](BROWSER_Z16_1.md#node-b14b3eaa0fc6c96a). the trichotomy delivers exactly this consumer's disjunction - a promoted full stage or a realized protected seam - at each feedback row, but only from an existing full-strip stage at an exact half-divisor horizon, so it produces the disjunction at reached depths only.
- outgoing **specialises**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). `cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam` derives `HalfCarryCofinalAdmissibility` from the disjunctive cofinal producer; Z12's node is the weakest socket both branches factor through.

<a id="node-d21154a1df7943f3"></a>
## object_level_singleton_or_seam_dichotomy

A sufficiently long exact rewind history (R <= denom cs) over a half-depth base cutoff forces the disjunction: either the depth-N window already has next-row divisor agreement, or the scalar interval [1,R] is a seam pair. This transports the scalar width dichotomy to the object level with no extra hypothesis.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [SelectedHalfWindow.scalarHistoryAlternative_of_rewindHistory](../../Erdos249257/HalfCarrySelectedWindow.lean#L739)

- incoming **generalises**: [Z15::rewind_width_dichotomy](BROWSER_Z15_1.md#node-d769dbd549f61cc0). the object-level alternative is the scalar dichotomy transported through rewind provenance
- outgoing **depends_on_open**: [Z15::history_alternative_needs_canonical_seam_bridge](BROWSER_Z15_1.md#node-38ee19ceeb12b902). the seam branch is closed only by assuming the scalar pair is an actual canonical even seam
- outgoing **implies**: [Z15::mixed_cofinal_window_or_seam_consumer](BROWSER_Z15_1.md#node-e5cf1d1a8c038506). the disjunctive interface is shaped to match the singleton-or-seam dichotomy at each depth
- incoming **reformulates**: [Z16::rewind_history_promotion_dichotomy](BROWSER_Z16_1.md#node-7803df419e54746c). commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt and scalarHistoryAlternative_of_rewindHistory are the same width dichotomy (promotion / divisor agreement, or an adjacent-ancestor seam pair) at cylinder and scalar level.

<a id="node-310bd79fd25f3cd9"></a>
## one_bit_extension_preserves_admissibility

Appending one Boolean bit to a strip-admissible depth-N word yields a strip-admissible depth-(N+1) word, provided the new terminal carry itself lies in the strip [1, halfStripBound (N+1)]. All earlier prefix carries are unchanged because the added exponent N+1 is beyond every divisor window already used.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [HalfStripAdmissible.extend](../../Erdos249257/HalfCarrySelectedWindow.lean#L137)

- outgoing **implies**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). each child is a one-bit extension whose admissibility comes from the extension lemma

<a id="node-7fa45c879f5b2789"></a>
## prefix_truncation_adds_suffix_numeral

For an arbitrary set A and any horizon before feedback can return (M + L <= 2M + 1), truncating A at M raises the integer half carry at time M+L by exactly the binary numeral of the removed suffix bits: K_{A cap [0,M]}(M+L-1) = K_A(M+L-1) + X, where X is the value of the bits at exponents M+1,...,M+L read newest-lowest. The single-row input is that below the feedback threshold, truncating removes from row n only the divisor n itself. When the actual terminal carry is one, the frozen-prefix endpoint is Z = 1 + X.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_eq_prefix_add_currentBit](../../Erdos249257/HalfCarryRewindPhase.lean#L116)
- Lean declaration: [integerHalfCarry_prefix_eq_add_supportSuffixNumeral](../../Erdos249257/HalfCarryRewindPhase.lean#L183)
- Lean declaration: [integerHalfCarry_prefix_eq_one_add_supportSuffixNumeral](../../Erdos249257/HalfCarryRewindPhase.lean#L209)

- outgoing **implies**: [Z15::actual_history_affine_realization](BROWSER_Z15_1.md#node-4c945b493ad4307d). the truncation identity supplies the carry-one endpoint K_{A cap [0,M]}(M+L-1) = 1 + X that supportHistory_realization consumes; neither node has an open dependence, so the previous depends_on_open label contradicted its own basis text
- incoming **reformulates**: [Z16::endpoint_indexed_suffix_cylinder_calculus](BROWSER_Z16_1.md#node-fe2a93ce8cb81ca0). Both are about supportSuffixNumeral: Z15 proves the frozen-prefix carry exceeds the live carry by exactly that numeral (integerHalfCarry_prefix_eq_add_supportSuffixNumeral), Z16 uses the same numeral as the endpoint offset k + numeral = E.

<a id="node-007b9db84e2d2d57"></a>
## protected_even_seam_realization_interface

ProtectedEvenSeamRealizedAt N delta c means exactly that, for every carry k in the protected band 3 through 27, scalar reachability across the one-hole even seam with parameters delta and c implies terminal reachability by an admissible half word at depth N. It is only the forward realization implication on this finite band.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The predicate records realization at specified N, delta and c; it proves no instance by itself. The corpus does not produce such receipts at cofinally many depths, so this node does not resolve the half-value endpoint or Erdős #257.

- Lean declaration: [ProtectedEvenSeamRealizedAt](../../Erdos249257/HalfCarryProtectedSeamConsumer.lean#L18)


<a id="node-7a7d16f86fdf5ae9"></a>
## realized_history_phase_identity

For any coefficient history realized by an actual carry-one orbit, the dyadic phase is exactly theta = D - 1 - X, where D = 2^L is the denominator and X the suffix numeral. Consequently the interval [1,B] rewinds to a single ancestor if and only if B - 1 <= X. The same identity holds in live support coordinates for the actual truncated coefficient history.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [phase_eq_denom_sub_one_sub_suffixNumeral](../../Erdos249257/HalfCarryRewindPhase.lean#L39)
- Lean declaration: [rewind_interval_singleton_iff_suffixNumeral_covers](../../Erdos249257/HalfCarryRewindPhase.lean#L65)
- Lean declaration: [phase_supportCoeffRewindHistory_eq](../../Erdos249257/HalfCarryRewindPhase.lean#L307)

- incoming **implies**: [Z15::actual_history_affine_realization](BROWSER_Z15_1.md#node-4c945b493ad4307d). the affine identity is exactly the realization equation the phase identity assumes, so it is discharged for live histories
- outgoing **reformulates**: [Z15::live_support_singleton_criterion](BROWSER_Z15_1.md#node-c4e16b860a2f525d). eliminating phase and suffix leaves the single inequality B <= frozen-prefix carry

<a id="node-49ec48a85fead70c"></a>
## restriction_fixes_next_row_coefficient

Agreement on membership of every divisor of n forces equal support coefficients at n. Consequently, if two finite words share a common restriction at a cutoff M with (n)/2 <= M, they have the same coefficient at row n: every proper divisor of n is at most n/2 and hence below the cutoff, while n itself is absent from both finite words. In particular a window with a common restriction beyond half depth has next-row divisor agreement and a genuinely constant selectedRowCoeff; the same argument applies verbatim at a doubled row 2(K+1) inspected through the half divisor K+1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [supportCoeff_eq_of_divisorAgreement](../../Erdos249257/HalfCarrySelectedWindow.lean#L202)
- Lean declaration: [SelectedHalfWindow.selectedRowCoeff_eq](../../Erdos249257/HalfCarrySelectedWindow.lean#L219)
- Lean declaration: [SelectedHalfWindow.nextRowDivisorAgreement_of_commonRestriction](../../Erdos249257/HalfCarrySelectedWindow.lean#L551)
- Lean declaration: [supportCoeff_nextRow_eq_of_restriction](../../Erdos249257/RewindSeamOperationalBridge.lean#L84)
- Lean declaration: [supportCoeff_eq_of_restriction_at_halfDivisor](../../Erdos249257/RewindHalfDivisorAdapter.lean#L26)

- outgoing **implies**: [Z15::rewind_singleton_gives_divisor_agreement](BROWSER_Z15_1.md#node-21e75f5cc14bdd5e). a singleton rewind gives one literal common prefix, which the half-depth divisor argument converts to agreement
- outgoing **implies**: [Z15::full_strip_step_from_divisor_agreement](BROWSER_Z15_1.md#node-80222181e708c6f3). agreement makes selectedRowCoeff constant, which is the hypothesis the step needs
- outgoing **implies**: [Z15::rewind_seam_transports_unit_drop_to_profile](BROWSER_Z15_1.md#node-b1b5630fd7bc9659). the coefficient of a window word is read off its base ancestor through half-depth restriction
- incoming **depends_on_open**: [Z16::two_sheet_next_row_off_child_gap](BROWSER_Z16_2.md#node-b2488aa5c69c6e63). the only law producing equality of next-row coefficients: agreement on every divisor of the row forces equal support coefficients. Once a cutoff promotion gives the two sheets different prefixes the premise fails, which is exactly why HasCommonNextCoeff is proved only at the odd successor row.
- incoming **depends_on_open**: [Z16::common_next_coeff_gap_advance](BROWSER_Z16_1.md#node-aa8dc9cf22b9c781). same producer and same limit: the shared-restriction premise is available below the half-depth cutoff and fails after promotion, so a genuinely common cross-sheet coefficient is not produced at later rows.

<a id="node-1fc9f857a24d6dcd"></a>
## rewind_closed_form

Iterating the ceiling parent maps T_c(k) = floor((k+c+1)/2) over a coefficient list, earliest row first, equals a single floor division: rewind(cs, k) = floor((k + offset(cs)) / 2^len(cs)), where offset accumulates each coefficient plus one with doubling weight. The resulting map is monotone in the terminal carry.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rewind_eq_closedForm](../../Erdos249257/HalfCarryCeilParentContraction.lean#L49)
- Lean declaration: [rewind_mono](../../Erdos249257/HalfCarryCeilParentContraction.lean#L69)

- outgoing **implies**: [Z15::rewind_dyadic_phase_criterion](BROWSER_Z15_1.md#node-5576062eeee0b5e7). the phase criterion is the closed form plus a residue condition on the single division

<a id="node-5576062eeee0b5e7"></a>
## rewind_dyadic_phase_criterion

For an interval [1,B] of width at most the rewind denominator D = 2^L with phase theta = (1 + offset) mod D: the whole interval rewinds to a single ancestor if and only if theta + (B-1) < D, and the interval is a seam pair (endpoints one apart) if and only if D <= theta + (B-1). Singleton behaviour on the whole interval is equivalent to singleton behaviour on the two endpoints alone.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rewind_endpoint_eq_iff_phase_fit](../../Erdos249257/HalfCarryCeilParentContraction.lean#L99)
- Lean declaration: [isSeamPair_iff_phase_overflow](../../Erdos249257/HalfCarryCeilParentContraction.lean#L123)
- Lean declaration: [rewind_interval_singleton_iff_endpoint_eq](../../Erdos249257/HalfCarryCeilParentContraction.lean#L158)
- Lean declaration: [rewind_interval_singleton_iff_phase_fit](../../Erdos249257/HalfCarryCeilParentContraction.lean#L171)

- incoming **implies**: [Z15::rewind_closed_form](BROWSER_Z15_1.md#node-1fc9f857a24d6dcd). the phase criterion is the closed form plus a residue condition on the single division
- outgoing **implies**: [Z15::rewind_width_dichotomy](BROWSER_Z15_1.md#node-d769dbd549f61cc0). the dichotomy is the excluded middle on the phase-fit inequality, with the endpoint gap bound
- outgoing **reformulates**: [Z15::seam_cut_threshold_classification](BROWSER_Z15_1.md#node-04ccc09b3d8d80e7). seamCut = denom - phase turns the residue inequality into a threshold on the target
- outgoing **specialises**: [Z15::live_support_singleton_criterion](BROWSER_Z15_1.md#node-c4e16b860a2f525d). the live criterion is the scalar phase criterion instantiated at an actual truncated support history
- incoming **reformulates**: [Z16::head_threshold_promotion_criterion](BROWSER_Z16_1.md#node-a034881200ee26b1). commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold (SuffixCylinderThreshold.lean) and rewind_interval_singleton_iff_phase_fit (HalfCarryCeilParentContraction.lean) are the same 'consecutive interval fits on one side of a dyadic threshold' criterion; phase_eq_denom_sub_one_sub_suffixNumeral converts the rewind phase into the cylinder's suffix-numeral coordinate.

<a id="node-e7f9bf1bfcde38a1"></a>
## rewind_provenance_of_explicit_step

Along any chain of canonical fixed-coefficient steps, the provenance bookkeeping is exact and unconditional: at the empty history a window restricts to itself at the identity index; consing one coefficient C onto a history cs sends the index k to rewind (C :: cs) k; and the public explicit step inherits this. Hence every word of a depth-N window restricts to the base representative indexed by the closed-form rewind ancestor of its terminal carry.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Two of the four evidence declarations are NOT hypothesis-free. SelectedHalfWindow.restrictWord_stepExplicit and SelectedHalfWindow.hasRewindRestrictionAt_stepExplicit both take hp_common : forall k in [1,R], selectedRowCoeff W k = C -- the very hypothesis flagged as an open antecedent of fixed_coefficient_window_step -- and both state their conclusion about the object W.stepExplicit ... hp_common ..., which does not exist without it. The node is kept unconditional because hp_common occurs only as a constructor argument (the theorem is an identity about whatever object the constructor returns) and because the whole chain is instantiated with no hypotheses at all in depth27FirstTwo_hasRewindRestrictionAt. It is NOT unconditional in the sense of holding at unbounded depth: at every depth beyond 26 the provenance statement is vacuous until hp_common is supplied there.

- Lean declaration: [SelectedHalfWindow.restrictWord_stepExplicit](../../Erdos249257/HalfCarrySelectedWindow.lean#L527)
- Lean declaration: [SelectedHalfWindow.hasRewindRestrictionAt_nil](../../Erdos249257/HalfCarrySelectedWindow.lean#L625)
- Lean declaration: [SelectedHalfWindow.FixedCoeffSuccessor.hasRewindRestrictionAt_cons](../../Erdos249257/HalfCarrySelectedWindow.lean#L636)
- Lean declaration: [SelectedHalfWindow.hasRewindRestrictionAt_stepExplicit](../../Erdos249257/HalfCarrySelectedWindow.lean#L670)

- outgoing **depends_on_open**: [Z15::fixed_coefficient_window_step](BROWSER_Z15_1.md#node-fa3af1821cd45b29). direction corrected: the open hypothesis (hp_common) is carried by fixed_coefficient_window_step, and it is the provenance theorems that are stated about the object built from it -- matching the convention used by the other depends_on_open edge, where the target node is the one holding the unproved assumption
- outgoing **implies**: [Z15::rewind_singleton_gives_divisor_agreement](BROWSER_Z15_1.md#node-21e75f5cc14bdd5e). the singleton fan-in consumes exactly HasRewindRestrictionAt
- incoming **depends_on_open**: [Z16::rewind_history_promotion_dichotomy](BROWSER_Z16_1.md#node-7803df419e54746c). this produces HasRewindRestrictionAt unconditionally along any chain of canonical fixed-coefficient steps, so the provenance half of the hypothesis is available on such chains; the width validity halfStripBound N <= denom cs at an arbitrary feedback row is produced nowhere.

<a id="node-a6029d30ac804cf0"></a>
## rewind_seam_plus_unit_drop_realizes_protected_seam

Exact rewind provenance, an actual scalar seam pair, and the unit coefficient drop between the two adjacent base ancestors together realize a localized one-hole even seam at depth N+1 with hole parameter delta = seamCut(cs), with no global canonical-even-seam equivalence needed. For a full square-root-strip window the buffer is discharged automatically by the divisor envelope, so the unit drop is the only remaining semantic input.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hbaseProfile : RewindBaseUnitDropAt W0 (N+1) cs c -- the unit coefficient drop between the two adjacent base ancestors; unproved except by the boundary-pair route, which is itself unproved", "hprov + hseam at unbounded depths: the existence of selected windows W0, W with R <= denom cs and IsSeamPair cs R at cofinally many N"]

- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_rewindSeam](../../Erdos249257/RewindSeamOperationalBridge.lean#L339)
- Lean declaration: [protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindSeam](../../Erdos249257/RewindSeamOperationalBridge.lean#L358)

- incoming **implies**: [Z15::rewind_seam_transports_unit_drop_to_profile](BROWSER_Z15_1.md#node-b1b5630fd7bc9659). the profile is the exact hypothesis of the threshold realization theorem
- incoming **implies**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). the rewind-seam theorem is the threshold theorem with the profile supplied by provenance
- outgoing **specialises**: [Z15::boundary_pair_realizes_protected_seam](BROWSER_Z15_1.md#node-56fe7a4c2fd7cb6a). the adapter instantiates the unit-drop hypothesis by the structural boundary-pair predicate
- outgoing **implies**: [Z15::cofinal_protected_seam_consumer](BROWSER_Z15_1.md#node-8914ed1068ade432). the seam-realization theorem produces exactly the ProtectedEvenSeamRealizedAt receipt the consumer collects
- outgoing **depends_on_open**: [Z16::crossing_unit_drop_profile](BROWSER_Z16_1.md#node-fcdeb390d153df7d). at a genuine endpoint crossing this produces the literal unit-drop coefficient profile c+1 / c at the doubled row - the shape RewindBaseUnitDropAt asserts - but for cylinder endpoints, not for the two adjacent rewind base ancestors, so it does not discharge the hypothesis.

<a id="node-b1b5630fd7bc9659"></a>
## rewind_seam_transports_unit_drop_to_profile

Under exact rewind provenance at a half-depth cutoff, a width-valid scalar seam pair, and the assumption that the two adjacent base ancestors have next-row coefficients c+1 (left) and c (right), the live depth-N window has the exact piecewise next-row coefficient profile: coefficient c+1 for targets h <= seamCut(cs) and c for h > seamCut(cs).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hbaseProfile : RewindBaseUnitDropAt W0 (N+1) cs c (the left adjacent base ancestor has row-(N+1) coefficient c+1 and the right adjacent base ancestor has coefficient c) -- not proved for any cofinal family", "hseam : IsSeamPair cs R together with hprov : W.HasRewindRestrictionAt W0 hMN cs at unbounded depth"]

- Lean declaration: [nextRow_profile_of_rewindSeam](../../Erdos249257/RewindSeamOperationalBridge.lean#L140)

- incoming **implies**: [Z15::seam_cut_threshold_classification](BROWSER_Z15_1.md#node-04ccc09b3d8d80e7). the piecewise profile is the threshold classification composed with restriction transfer
- incoming **implies**: [Z15::restriction_fixes_next_row_coefficient](BROWSER_Z15_1.md#node-49ec48a85fead70c). the coefficient of a window word is read off its base ancestor through half-depth restriction
- outgoing **implies**: [Z15::rewind_seam_plus_unit_drop_realizes_protected_seam](BROWSER_Z15_1.md#node-a6029d30ac804cf0). the profile is the exact hypothesis of the threshold realization theorem
- incoming **reformulates**: [Z16::crossing_unit_drop_profile](BROWSER_Z16_1.md#node-fcdeb390d153df7d). supportCoeff_profile_of_crossingSuffixCylinder and nextRow_profile_of_rewindSeam produce the identical two-valued next-row coefficient profile (c+1 below a cut, c above) consumed by protectedEvenSeamRealizedAt_succ_of_profile; the cut is seamCut(cs) in one presentation and E - 2^(N-(K+1)) in the other.
- outgoing **depends_on_open**: [Z16::crossing_unit_drop_profile](BROWSER_Z16_1.md#node-fcdeb390d153df7d). the same nearest producer of RewindBaseUnitDropAt: an endpoint crossing yields the literal c+1 / c profile at the doubled row, but on cylinder endpoints rather than on the two adjacent rewind base ancestors, so hbaseProfile is not produced for any cofinal family.

<a id="node-21e75f5cc14bdd5e"></a>
## rewind_singleton_gives_divisor_agreement

If a depth-N window has exact rewind provenance over a base window at cutoff M with (N+1)/2 <= M, and the rewind map is constant on the protected interval [1,R], then all representatives share one literal prefix and hence have next-row divisor agreement. The phase-fit inequality theta + (R-1) < denom(cs), together with R <= denom(cs), is a sufficient arithmetic trigger.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The singleton trigger is never instantiated anywhere in this zone, and at the only concrete rewind history the zone actually certifies it is FALSE: depth27FirstTwo_hasRewindRestrictionAt gives cs = [1] with R = 2, and oneRowHistory_isSeamPair proves IsSeamPair [1] 2, i.e. phase [1] + (2-1) = denom [1], so hsingle / hphase fails there. Zero certified instances of the singleton branch versus one certified instance of the seam branch. The node is therefore an empty route so far, not a working one; only the depth-18 base carries divisor agreement, and it gets it from an explicit common prefix, not from this theorem.

- Lean declaration: [SelectedHalfWindow.commonRestrictionAt_of_rewind_singleton](../../Erdos249257/HalfCarrySelectedWindow.lean#L687)
- Lean declaration: [SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_singleton](../../Erdos249257/HalfCarrySelectedWindow.lean#L706)
- Lean declaration: [SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_phaseFit](../../Erdos249257/HalfCarrySelectedWindow.lean#L719)

- incoming **implies**: [Z15::restriction_fixes_next_row_coefficient](BROWSER_Z15_1.md#node-49ec48a85fead70c). a singleton rewind gives one literal common prefix, which the half-depth divisor argument converts to agreement
- incoming **implies**: [Z15::rewind_provenance_of_explicit_step](BROWSER_Z15_1.md#node-e7f9bf1bfcde38a1). the singleton fan-in consumes exactly HasRewindRestrictionAt

<a id="node-d769dbd549f61cc0"></a>
## rewind_width_dichotomy

If 1 <= B <= denom(cs) then the two endpoint ancestors differ by at most one, so either every target in [1,B] rewinds to the same ancestor or [1,B] is a seam pair; and in the seam-pair case every interior target lands on one of exactly those two adjacent ancestors. Width alone therefore yields a disjunction, not a singleton.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rewind_endpoint_le_succ](../../Erdos249257/HalfCarryCeilParentContraction.lean#L86)
- Lean declaration: [rewind_eq_left_or_right_of_isSeamPair](../../Erdos249257/HalfCarryCeilParentContraction.lean#L147)
- Lean declaration: [rewind_singleton_or_isSeamPair](../../Erdos249257/HalfCarryCeilParentContraction.lean#L180)

- incoming **implies**: [Z15::rewind_dyadic_phase_criterion](BROWSER_Z15_1.md#node-5576062eeee0b5e7). the dichotomy is the excluded middle on the phase-fit inequality, with the endpoint gap bound
- outgoing **generalises**: [Z15::object_level_singleton_or_seam_dichotomy](BROWSER_Z15_1.md#node-d21154a1df7943f3). the object-level alternative is the scalar dichotomy transported through rewind provenance

<a id="node-04ccc09b3d8d80e7"></a>
## seam_cut_threshold_classification

The scalar seam is a clean threshold. With seamCut(cs) = denom(cs) - phase(cs), a target k in [1,B] (B <= denom cs) rewinds to the left ancestor exactly when k <= seamCut(cs), and, when [1,B] is a genuine seam pair, rewinds to the right ancestor exactly when k > seamCut(cs). A genuine seam pair has seamCut(cs) < B, so both sides are nonempty.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rewind_eq_left_iff_le_seamCut](../../Erdos249257/RewindSeamOperationalBridge.lean#L32)
- Lean declaration: [seamCut_lt_rightEndpoint](../../Erdos249257/RewindSeamOperationalBridge.lean#L50)
- Lean declaration: [rewind_eq_right_iff_seamCut_lt](../../Erdos249257/RewindSeamOperationalBridge.lean#L62)

- incoming **reformulates**: [Z15::rewind_dyadic_phase_criterion](BROWSER_Z15_1.md#node-5576062eeee0b5e7). seamCut = denom - phase turns the residue inequality into a threshold on the target
- outgoing **implies**: [Z15::rewind_seam_transports_unit_drop_to_profile](BROWSER_Z15_1.md#node-b1b5630fd7bc9659). the piecewise profile is the threshold classification composed with restriction transfer

<a id="node-3cf8358ae1e4bd65"></a>
## selected_parent_realizes_both_children

If one representative of a selected window at depth N has next-row coefficient C, then for either Boolean terminal bit the corresponding child carry q = 2h - C - b is terminally reachable at depth N+1, provided q is positive and inside the strip. This is the single-word realization step underlying every seam consumer.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfTerminalReachable_succ_of_selectedParent](../../Erdos249257/RewindSeamOperationalBridge.lean#L167)

- outgoing **implies**: [Z15::threshold_profile_realizes_protected_seam](BROWSER_Z15_2.md#node-628caa7217f6f389). every branch of the EvenSeamReachable case split is closed by realizing one child of a selected parent

<a id="node-c8d8cb0761e11f61"></a>
## selected_window_cofinal_consumer

If selected protected windows with positive radius exist at every depth from some N0 onward (either given directly or generated by a base window plus a forward step function, iterated as data so the chosen words survive), then admissible finite words exist at cofinally many depths, and by the imported inverse-limit compactness theorem there is an infinite A whose Mersenne series sums to exactly 1/2.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hwindow : forall N >= N0, SelectedHalfWindow N (R N) with 1 <= R N (a cofinal supply of selected protected windows) -- nothing in the corpus produces one", "in the induction form: hstep : forall N >= N0, SelectedHalfWindow N (R N) -> SelectedHalfWindow (N+1) (R (N+1)) (an unconditional forward step at every large depth) -- available in this zone only under the unproved common-coefficient or divisor-agreement hypothesis"]

- Lean declaration: [selectedHalfWindowIterate](../../Erdos249257/HalfCarrySelectedWindow.lean#L816)
- Lean declaration: [cofinalAdmissibility_of_selectedHalfWindows](../../Erdos249257/HalfCarrySelectedWindow.lean#L831)
- Lean declaration: [cofinalAdmissibility_of_selectedHalfWindow_induction](../../Erdos249257/HalfCarrySelectedWindow.lean#L847)
- Lean declaration: [exists_infinite_support_half_of_selectedHalfWindows](../../Erdos249257/HalfCarrySelectedWindow.lean#L864)
- Lean declaration: [exists_infinite_support_half_of_selectedHalfWindow_induction](../../Erdos249257/HalfCarrySelectedWindow.lean#L875)

- outgoing **specialises**: [Z15::mixed_cofinal_window_or_seam_consumer](BROWSER_Z15_1.md#node-e5cf1d1a8c038506). the window branch of the mixed consumer repeats the selected-window consumer verbatim
- outgoing **transport_of**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). cofinalAdmissibility_of_selectedHalfWindows (HalfCarrySelectedWindow.lean) is a formal theorem converting a cofinal selected-window supply into HalfCarryCofinalAdmissibility, the antecedent of exists_infinite_support_half_of_cofinalAdmissibility.
- incoming **finite_instance_of**: [Z16::pre_feedback_run_to_depth_27](BROWSER_Z16_1.md#node-ca287b00ab093584). the ten iterated Stage.step outputs are selected protected windows with positive radius at depths 18..27, instances of the cofinal window supply this consumer assumes from some N0 onward.
- incoming **finite_instance_of**: [Z16::first_feedback_promotion_depth_27_to_29](BROWSER_Z16_1.md#node-dc4415c505244611). the promotion yields full protected selected windows at depths 28 and 29, two further instances of the same cofinal window supply.
- incoming **finite_instance_of**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). the cutoff-25 stage advances through rows 30..51 and promotes to a full cylinder stage at depth 52, extending the supply of selected protected windows to depth 52; the consumer needs them at every depth beyond some N0.
- outgoing **depends_on_open**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). the run is the actual production route for the cofinal window supply and reaches depth 52; past that the continuation depends on the unproved NextArithmetic cell, so the supply from some N0 onward is not produced.
- outgoing **specialises**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). `cofinalAdmissibility_of_selectedHalfWindows` (HalfCarrySelectedWindow.lean:831) derives `HalfCarryCofinalAdmissibility` from the cofinal-selected-window hypothesis; that predicate is exactly the antecedent of Z12's `exists_infinite_support_half_of_cofinalAdmissibility` (HalfCarryReachability.lean:984) and the conclusions coincide, so Z15's theorem is the hypothesis-strengthened form.

<a id="node-ae0e82614fcb2221"></a>
## selected_window_history_alternative_interface

For a selected half window W at depth N, HistoryAlternative W is exactly the disjunction that either W already has next-row divisor agreement, or there are d, delta and c with N+1 = 2d for which the actual depth-d transition is a canonical even seam. This definition packages the two object-level branches; it does not assert that either branch holds for an arbitrary window.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: No theorem proves HistoryAlternative for every selected window or supplies it at cofinally many depths. In particular, the definition itself provides neither next-row divisor agreement nor canonical-seam realization.

- Lean declaration: [SelectedHalfWindow.HistoryAlternative](../../Erdos249257/HalfCarrySelectedWindow.lean#L236)


