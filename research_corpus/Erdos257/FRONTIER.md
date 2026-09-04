# erdos_257 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Prove irrationality of sum_{n in A} 1/(2^n-1) for every infinite support A.

## Established results and their evidence

### localized_dilation_incidence_transfer_boundary

For a in A, the divisor-incidence identity f_A(a*n)-f_A(n)=1-1_{a divides n} for every n holds exactly when a is coprime to every other element of A. Thus pairwise coprimality is the minimum algebraic condition for every support element to serve as a localized dilation parameter. Independently, A=2P has divergent reciprocal mass but no localized dilation parameter; distinct atoms 2p and 2q have covariance 1/(4pq), whose off-diagonal mass is quadratic in the reciprocal mass, and f_A(n)f_A(n+1)=0. Hence arbitrary reciprocal divergence cannot directly replace prime support in the Tao--Teravainen incidence argument.

Evidence/status: source_current_exact_algebraic_classification_and_countermodel

- [TaoTeravainenIncidenceBoundary.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/TaoTeravainenIncidenceBoundary.md)

claim_boundary: The arbitrary-a if-and-only-if classification and the A=2P covariance/countermodel are source-verified elementary arguments in the named markdown note, not Lean-checked declarations. The adjacent Lean module proves only the narrower prime/coprimality pullback identities. This result blocks a naive transfer from reciprocal divergence alone; it neither proves irrationality for any new support, decides the Mersenne subseries on 2P, nor supplies a counterexample to Erdős 257.

surviving_obligation: This is a transfer obstruction, not an irrationality proof or a counterexample to Erdős 257. It does not decide the Mersenne subseries on 2P and does not settle arbitrary dense supports.

### reciprocal_summable_supports_base_two

For every infinite support A of positive integers with summable reciprocal conductor mass sum_(a in A) 1/a, the reciprocal-power subseries sum_(a in A) 1/(b^a-1) is irrational for every integer base b>=2. The binary LCM-prefix/Cesaro close return transfers uniformly to every radix because each radix-b shifted-atom displacement is at most twice the binary displacement; an exact radix integer orbit supplies the final gap contradiction.

Evidence/status: lean_checked_complete_all_base_support_regime_theorem

- [AllBaseReciprocalSupportIrrationality.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean)

claim_boundary: The three named declarations prove the all-base irrationality theorem and its binary-to-radix transfer under the explicit infinite-support and summable-reciprocal-conductor hypotheses. They do not cover divergent reciprocal mass, identify the base-two proof with Erdős's omitted argument, establish novelty or priority, or solve universal Erdős #257.

### one_half_fatal_borrow_reduced_to_middle_reset_scale

A mature fatal selected-ancestry borrow has midpoint residual R with R<2*sqrt(2d)+3 and aligned seam remainder R+1<d, hence is a row-small middle reset. The first-bad-row proof exposes the last false terminal before the first row-small seam state: an actual upper reset s>=13 followed by k literal right recurrences to endpoint s+k+1. Exact cylinder scaling turns its danger inequality into R_(s+k+1)+C_k<4^k*2(s+k), retaining the complete affine pulse packet. Lean packages the matching producer SeamActualUpperRightPacketLinearEscape, which asks for the reverse weak inequality at every literal upper/right prefix, proves it is weaker than the old all-index dyadic-band producer, and proves it implies row escape, SeamMiddleProducerRowEscape, and (1/2 : real) membership. This is an exact conditional counterexample endpoint, not a proof of the lower envelope. Separately, the stronger middle reset scale inequality also contradicts the fatal square-root envelope. All statements handle residual zero and positive residual uniformly.

Evidence/status: lean_checked_actual_last_upper_ancestor_thin_packet_and_actual_scale_linear_escape_endpoint

- [FatalBorrowMiddleScaleContradiction.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/FatalBorrowMiddleScaleContradiction.lean)

claim_boundary: The checked declarations reduce a mature fatal borrow to an actual last-upper-ancestor packet and prove that the explicit all-depth linear-escape producers would imply 1/2-membership. They do not prove either producer, exclude every fatal row, establish 1/2-membership unconditionally, or resolve Erdős #257.

surviving_obligation: Prove SeamActualUpperRightPacketLinearEscape, its last-ancestor-only specialization, SeamMiddleProducerRowEscape, or another fatal-row-only contradiction. The checked consumers are conditional and do not prove 1/2 membership or settle Erdős #257.

### one_half_fatal_midpoint_cofinite_carry_transfer

If an actual half-greedy skip at rank d has nonpositive complement budget, the fatal midpoint transfer supplies an exact row Q_(A_(d-1) union {d})(2d)+R=2^(2d-1), with seam remainder R+1. Completing the actual lower word by the open tail above d gives the exact centered-carry identity e_(2d+1)=4R+3-P_d, where P_d is the paired boundary pulse. When d>=13 and R=0, the cofinite completion is strictly below 1/2, the endpoint carry is nonzero, and the selected rank 2 supplies positive pulse; hence P_d is exactly 1 or 2 and the producer carry is exactly -1 or -2. The zero midpoint residual is therefore routed into the two already-surviving arithmetic cells and cannot be cell -3 or a fourth exceptional mechanism.

Evidence/status: lean_checked_exact_fatal_branch_coordinate_transfer_and_zero_branch_cell_collapse

- [FatalBorrowCofiniteCarryTransfer.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/FatalBorrowCofiniteCarryTransfer.lean)

claim_boundary: The checked transfer classifies a mature fatal midpoint row and narrows its zero-residual case to the surviving minus-one or minus-two cofinite carry cells. It does not exclude those cells, exclude the positive-residual branch, prove complement-budget positivity, establish 1/2-membership, or resolve Erdős #257.

surviving_obligation: Exclude both mature zero-residual pulse cells and the positive-residual second-shell branch, thereby proving that the complement budget stays positive at every depth. The result does not yet prove 1/2 membership or settle Erdős #257.

### twenty_one_nested_height_exact_alive_cylinder_discriminator

Instead of choosing small-denominator rational targets and filtering survivors, the exact probe chooses an arbitrary Boolean prefix A through rank N and a dyadic residual 0<=r<=2^-N<T_N. Strict superincreasingness puts x=sum_(a in A)1/(2^a-1)+r inside the exact greedy survival cylinder of A; the executable rechecks every take and skip by integer cross-multiplication and reconstructs binary digits, divisor loads, defects, records, and heights with one common denominator. This distinguishes target-space breadth from another horizon extension.

Evidence/status: exact_target_space_probe_with_survival_conditioning_route_warning

- [nested_height_alive_cylinder_probe.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/nested_height_alive_cylinder_probe.py)

surviving_obligation: Prove a genuinely pre-survival period-six nested-height/causal-service theorem, or prove the one-half skipped full-shell charge J_N>2^N(Q_N-1). Erdős #257 remains open.

### twenty_one_selected_divisor_height_reduction_and_alive_prefix_guard

Let S(d)=max_{m<=d} tau_A(m) for the canonical denominator-21 greedy support and H(d)=max(1,1+max_{N<d}Q_N). Lean proves tau_A(N+1)<=2Q_N+1 directly from the exact defect recurrence and successor nonnegativity, then proves S(d)+1<=2H(d). Therefore the single unconditional socket H(2d)<=S(d)+1 implies H(2d)<=2H(d), 1/21 membership, and the negation of universal Mersenne-subseries irrationality. The companion defect sandwich Q_N<=floor(D_N)+1 is valid only at alive ranks. Its measured floor-tail and record-divisor inequalities have the socket's numerical shape only on an already-alive prefix and cannot imply the all-depth socket across a hypothetical fatal tail.

Evidence/status: lean_checked_p1_reduction_with_corrected_alive_prefix_circularity_boundary

- [TwentyOneSelectedDivisorHeightReduction.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/TwentyOneSelectedDivisorHeightReduction.lean)

claim_boundary: The checked declarations reduce the denominator-21 height route to the unconditional all-depth bound H(2d)≤S(d)+1 and show why an alive-prefix defect sandwich cannot prove it. They do not establish that all-depth bound, exclude the fatal branch, prove 1/21-membership, or resolve Erdős #257.

surviving_obligation: Prove TwentyOneSelectedDivisorHalfRangeBound without assuming survival, or rule out the denominator-21 fatal branch by another coordinate. Erdős #257 remains open.

### one_half_pulse_register_exact_multiplicity_window_bridge

For every finite support A, one base-four pulse digit at row b is exactly c_A(2b+2)+2c_A(2b+1), so k fixed-support pulse steps equal the division-free binary coefficient-window numerator F_A(2b,2k). After subtracting the all-ones baseline, the window telescopes exactly to 2^J e_A(n-1)-e_A(n+J-1) in the centered Mobius carry. Clearing the affine digit denominator gives 3*C_affine=3*F_A(2b,2k)+4*(4^k-1). This is a literal coordinate bridge from the half-cylinder register to selected-divisor excess multiplicity, not an analogy.

Evidence/status: lean_checked_exact_coordinate_identity_with_rank_2500_sign_falsifier

- [HalfCylinderPullbackCardPropagation.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfCylinderPullbackCardPropagation.lean)

claim_boundary: The checked declarations identify the pulse register exactly with a selected-divisor multiplicity window and a Möbius-carry boundary difference, while finite evidence falsifies a sign-monotone hole-only transfer. They do not prove the upper terminal packet bound, a replacement scale producer, 1/2-membership, or Erdős #257.

surviving_obligation: For the one-half lane, prove the upper terminal packet inequality R_(d+k+1)+C_k<2^(d+k), or a scale producer that bypasses it. Erdős #257 remains open.

### one_half_symmetric_middle_reset_return_from_compulsory_rank_two_pulse

For every carry row s>=12, the adjacent-cut upper pulse is positive: carry identifies the next greedy word with the false-extension of the upper word, while compulsory selected rank 2 contributes rowPulse(s,2)=1. Separation gives 2^(s+1)<=R_s+O_s and carry gives 4O_s+abovePulse_s<=2^(s+1); positivity makes the latter strict after removing the pulse, hence R_s>3*2^(s-1). For any actual right run of length k from source d>=12 which terminates in such a carry, the exact signed cylinder R_(d+k+1)-2^(d+k+1)+C_k=4^k*dev_d converts this terminal remainder bound into 2^(d+k)<4^k*dev_d. This is the symmetric middle-reset lower return inequality requested by the reset-law roadmap.

Evidence/status: lean_checked_all_mature_terminal_carries_with_exact_rank_2000_upper_packet_audit

- [HalfCylinderPullbackCardPropagation.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfCylinderPullbackCardPropagation.lean)

claim_boundary: The checked declarations prove the mature middle-origin lower return inequality for right runs ending in a carry. They do not prove the complementary upper-origin terminal bound, the resulting all-depth reset law, square-root escape, 1/2-membership, or Erdős #257.

surviving_obligation: Establish the upper terminal-reset packet inequality at every mature upper/right block, then use the two-sided reset law to bound right-run length below half-row scale, obtain square-root escape, and invoke the existing Lean consumer for one-half membership. Erdős #257 remains open.

### one_half_quantitative_late_upper_two_block_amplification

At an actual late upper reset, let Q be the nonnegative earlier critical pullback coordinate, G=2^(s-k+1)-seamUpperResetCharge(s) the forward critical gap, and R the endpoint seam remainder after k right steps. The support-sensitive premise card(endpoint)+2<=Q gives a 2Q digit budget in the backward fixed-support block and a 2G digit budget in the forward affine block. Lean proves 4^(s-d)Q+2Q<=3G and 4^kG+2G<=3R, hence 4^(s-d+k)Q+2*4^kQ+6G<=9R. This retains both base-four amplification factors and strictly strengthens the earlier order-only implication R>=G>=Q. The premise remains exactly LateUpperPreviousMiddleStaircaseEscape after rewriting Q through the preceding middle recurrence; it is not proved at all depths.

Evidence/status: lean_checked_actual_late_upper_parent_child_amplifier_with_exact_finite_specialization_audit

- [HalfCylinderPullbackCardPropagation.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfCylinderPullbackCardPropagation.lean)

claim_boundary: The named Lean declarations prove conditional exact-cylinder and two-block amplification inequalities from explicit nonnegativity, support-cardinality, carry, right-run, largest-false-rank, lateness, factor-range, and pullback-card hypotheses. They do not prove the all-depth pullback-card or LateUpperPreviousMiddleStaircaseEscape premise, the remaining seam-remainder or non-midpoint obligations, one-half membership, a rational counterexample, or Erdős #257. The rank-2000 specialization is finite mechanism evidence only.

surviving_obligation: Establish the all-depth pullback-card or equivalent middle-staircase premise, then discharge the remaining base/middle/right fan-in to SeamRemainderCardGapFromEight and the non-midpoint quotient-prefix comparison. One-half membership and Erdős #257 remain open.

### one_half_reset_sqrt_escape_three_margin_discharge

A middle reset entered by another middle branch has R_s >= 2^s - 2*(s-2) unconditionally. Entered by a right branch the new remainder equals EXACTLY the previous take-decision margin (new SeamTakeMarginScaleProducer). Entered from an upper reset it equals 2^s - E_(s-1) exactly (needs new SeamUpperResetChargeCeilingProducer: 4*E_d + 3*2^((d+6)/2) + 2*(d-1) <= 2^(d+3)). Consequently floor+ceiling+take-margin jointly imply SeamResetSqrtEscape and 1/2 membership: every seam-greedy decision must clear half-row scale.

Evidence/status: lean_checked_build_3346_jobs_middle_producer_discharged_into_three_margin_producers

- [HalfResetSqrtEscapeMiddleDischarge.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfResetSqrtEscapeMiddleDischarge.lean)

surviving_obligation: Prove SeamUpperResetChargeScaleProducer, SeamUpperResetChargeCeilingProducer, SeamTakeMarginScaleProducer unconditionally.

### hereditary_selected_tail_dominance

For every set of selected future offsets, the selected Mersenne tail is strictly smaller than the current positive-index weight.

Evidence/status: lean_checked

- [MersenneSubseriesRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean)

### supported_digit_unique_coding

The Mersenne digit-value map remains injective after restriction to any chosen support.

Evidence/status: lean_checked

- [MersenneSubseriesRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean)

### hereditary_mersenne_subachievement_topology

For every selected support the supported digit space is closed and its Mersenne achievement set is compact, closed, and nowhere dense with unique coding. If the support is infinite, a free-coordinate flip in every basic product neighbourhood proves that the digit space and its achievement-set image are preperfect, hence the achievement set is perfect.

Evidence/status: lean_checked

- [MersenneSubseriesRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean)

### hereditary_mersenne_subachievement_measure

The Lebesgue measure is exactly 2^-c when the support omits c coordinates and is zero when the complement is infinite. The proof kernel-checks the one-coordinate disjoint translated-face split, measure doubling, finite-complement induction, arbitrary-support monotonicity, and the limiting dyadic squeeze.

Evidence/status: lean_checked

- [MersenneSubseriesRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean)

### mersenne_bernoulli_phase_diagram

The Bernoulli subseries law is absolutely continuous exactly for cofinite support with fair bits; then it is normalized Lebesgue measure restricted to the subachievement set. Every other parameter is singular.

Evidence/status: advisory_complete_proof_pending_lean


### arithmetic_stride_dimension

For support m*N+, m>=2, the achievement set is Ahlfors regular of Hausdorff dimension 1/m, and the p-biased law has entropy dimension H(p)/(m log 2).

Evidence/status: advisory_complete_proof_pending_lean


### rational_half_counterexample_consumer

Any cofinal terminal scaled-vanishing sequence produces an infinite support A with sum_{n in A} 1/(2^n-1)=1/2 and therefore negates the universal irrationality assertion.

Evidence/status: lean_checked_conditional_disproof

- [TerminalOnlyScaledVanishing.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TerminalOnlyScaledVanishing.lean)

claim_boundary: The checked consumer converts an explicit cofinal scaled-terminal sequence into an infinite support summing to 1/2 and hence a counterexample to the universal assertion. It does not construct the sequence, establish 1/2-membership unconditionally, or resolve Erdős #257.

### suffix_cylinder_terminal_frontier

Lean proves an unconditional terminal-only strip witness at depth 55. A dependency-free integer replay follows the deterministic cylinder through 1000000 further feedback decisions without a crossing. It ends at cutoff 1000026 with 501016 high and 498984 low decisions, support size 501024, and smallest raw clearance 3984366 at cutoff 26. The canonical payload digest is 67df53225ae50a9b7d5f0133fb29cd1c1c022ef061bd1eb5d6f3f5eccca2f44b.

Evidence/status: lean_checked_to_depth_55_and_exact_computation_to_cutoff_1000026

- [SuffixCylinderTerminalOnlyBridge.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SuffixCylinderTerminalOnlyBridge.lean)

### suffix_orbit_centered_recurrence

For natural endpoint and coefficient data satisfying the exact two-row endpoint step, Lean proves the centered update delta_(k+1)=4 delta_k+(1-2b_k)2^(k+1)-2d_k-a_(k+1), with delta_k=2E_k-a_k-2^k. From cutoff two onward it also proves the necessary mod-8 pulse 8 | delta_(k+1)+2d_k+a_(k+1)-4a_k. This exposes the infinite producer as a support-dependent perturbed signed-doubling problem but does not prove global no-crossing.

Evidence/status: source_current_formal_anchor_validation_deferred

- [SuffixCylinderGlobalProducer.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SuffixCylinderGlobalProducer.lean)

### orthogonal_petal_bouquet_reciprocal_subsumption

Every OrthogonalPetalBouquet support is reciprocal-summable: each ray reciprocal is bounded by its petal reciprocal and the exceptional frame is finite. The existing reciprocal-support theorem therefore proves its Erdős support series irrational with no forced-slot selector. The older conditional bouquet endpoint remains correct but is subsumed, and this support class cannot enter the reciprocal-divergent or positive-density regime.

Evidence/status: lean_checked_route_elimination


### mersenne_deficit_coefficient_phase_tower

For the construction family y_k=3/(2^k-1), the exact deficit coefficient a_j=(2^j-2)^2/(2^j-1) has reduced denominator 2^j-1 and 2 has exact order j modulo it, so the joint raw coefficient phase period through J is lcm(2,...,J) and cannot stabilize. Certified support-bit comparisons additionally eliminate the concrete phase moduli 2, 6, 60, 420, and 2520 as complete nonlinear block-state descriptors: same-residue target pairs agree through all prior tested 64-bit block-boundary suffixes and first split at blocks 4, 6, 8, 10, and 12. This does not eliminate an adaptive growing-state transducer or a proved quotient that cancels the raw phases.

Evidence/status: exact_arithmetic_plus_certified_finite_route_elimination


### one_over_twenty_one_finite_support_exclusion

For every finite Boolean support F using only ranks n>=2, the finite base-two Mersenne sum finiteErdosSum F 2 is not 1/21. Therefore a future rank-at-least-two Boolean representation of 1/21 would necessarily have infinite support; this theorem does not construct such a representation, prove 1/21 membership, or settle universal Erdős #257.

Evidence/status: lean_checked

- [HalfCounterexampleFrontier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean)

### one_over_twenty_one_terminal_fringe_absorption

The six former preterminal fringe exclusions are unnecessary. A single twice-last-coin preterminal ceiling yields full-row quotient defect at most three, which vanishes after 4^R normalization and proves 1/21 is in the Mersenne achievement set. The coarse ceiling itself remains unproved.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

### one_over_twenty_one_next_coin_reduction

The ordinary greedy next-coin invariant is enough: if every preterminal quotient remainder is below the next quotient coin, a checked constant-excess bound converts it to geometrically vanishing quotient error and proves 1/21 membership. No fixed fringe width, equality exclusion, or terminal defect cap remains in the producer.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

### one_over_twenty_one_cofinal_full_overshoot_reduction

It is enough to find an unbounded subsequence of deterministic full quotient-greedy rows whose rational prefix values reach or exceed 1/21. The exact scaled identity then bounds quotient defect by support cardinality, so the resulting linear numerator error vanishes against the exponential normalization. This is strictly weaker than proving a uniform next-coin or fixed-defect bound.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

### one_over_twenty_one_rational_greedy_divergence_reduction

A cofinal sequence of full quotient-greedy Boolean words that differs from exact rational greedy by the same horizon is sufficient for 1/21 membership. Lean proves a no-first-divergence comparison: every completed quotient row that remains rationally safe agrees with exact rational greedy, so any Boolean disagreement certifies strict overshoot and feeds the existing cofinal-overshoot endpoint. This supplies a finite-word recognizer for the producer but does not prove cofinal divergence or weaken the canonical overshoot hypothesis.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

### one_over_twenty_one_eventual_rational_alignment_dichotomy

Lean proves the unconditional terminal dichotomy: either 1/21 already belongs to the Mersenne achievement set, or all sufficiently deep full quotient-greedy Boolean words agree bit-for-bit with exact rational greedy through the same horizon. Equivalently, failure of achievement-set membership forces eventual rational alignment. The theorem sharpens the surviving nonmembership branch but does not decide which side holds.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

claim_boundary: The checked dichotomy proves that failure of 1/21-membership forces eventual agreement between the quotient-greedy and exact rational-greedy words. It does not select a side of the dichotomy, exclude the aligned fatal branch, establish 1/21-membership, or resolve Erdős #257.

### one_over_twenty_one_fatal_aligned_branch_classification

Lean now identifies the exact remaining 1/21 frontier. Non-membership is equivalent to one explicit branch carrying a fatal greedy witness, finite skipped support and hence cofinite selected support, eventual full quotient/rational-greedy alignment, and eventual occupation of every doubling block. Equivalently, 1/21 belongs to the Mersenne achievement set exactly when this fatal/cofinite/aligned branch is impossible. This is an exact logical classification, not a proof that the branch is impossible or that 1/21 is represented.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

claim_boundary: The checked equivalence classifies 1/21 non-membership by one explicit fatal, cofinite, eventually aligned branch. It does not show that branch impossible, establish 1/21-membership, produce a rational counterexample to the universal problem, or resolve Erdős #257.

### one_over_twenty_one_fatal_right_boundary_factorization

Inside TwentyOneFatalAlignedBranch, Lean factors every sufficiently late dyadic prefix boundary through one fixed ancestor: after the fatal rank, P_(n+t)+1=2^t(P_n+1), and hence every late right boundary carries the entire forced power of two from the cofinite selected suffix. This is a negative result for the correction-amplification route: the right-boundary long-selected-run alternative contains no fresh forcing-depth growth. It redirects the surviving contradiction search toward the denominator-21 defect or another coordinate, but does not exclude the fatal branch or prove 1/21 membership.

Evidence/status: lean_checked

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

claim_boundary: The checked factorization shows that a late right boundary inside the fatal aligned branch contains no new forcing-depth growth, thereby closing that correction-amplification mechanism. It does not exclude the fatal branch, establish 1/21-membership, or resolve Erdős #257.

### one_over_twenty_one_closed_row_canonicalization

Lean proves that one denominator-21 lower quotient row with defect s<=2^R at every even depth is sufficient for 1/21 membership. The denominator-specific strong separation estimate shows that every such closed Boolean row is exactly the deterministic quotient-greedy row, including equality at s=2^R; there is no alternative Boolean support hidden at the saturated boundary. The recursive socket is now sharp at that boundary: because the new coin contributes one unit beyond its binary skeleton, the unique nonzero target pulse needs only two local endpoint-divisor units rather than three. Lean further classifies every newly saturated boundary state. Under the closed capacity bound it comes from exactly C=2^(R+1) in the skip branch or C=2^(R+2)+1 in the take branch; after a strict predecessor the exceptional take value is impossible, so new saturation is equivalent to the single exact mid-carry C=2^(R+1). The even target pulse is three-periodic in half-depth and equals three exactly when R mod 3=2. Endpoint pulses at the next two positions have a finite-memory horizon: for support bounded by R they depend only on denominators at most floor((2R+2)/3). In the signed capacity margin m_R=2^R-s, Lean gives exact affine take and skip recurrences. If a strict predecessor lands at the exact saturated mid-carry and that new endpoint fails the following saturated socket, then R mod 3=1 and an explicit older support hole occurs at a+1 or 2(a+1). The alignment bridge identifies the canonical quotient support with the actual greedy support on every sufficiently deep fatal-branch row. Cofinite selection fills both possible ancestor digits, so the fatal branch cannot sustain a bad saturated socket at sufficiently large R. Full alignment also identifies the entire canonical lower support with the audited rational greedy prefix and proves that its prefix value is at most 1/21. Consequently the fatal branch eventually satisfies the lower, nonnegative-carry inequality. Lean now proves more on the complementary side: any unbounded sequence of closed canonical rows s<=2^R already gives the compactness decay required for membership. Therefore the fatal branch is eventually strictly supercapacity, 2^R<s_R, at every rank; there the boundary coin always fits, the support appends R+1, and the scalar follows one literal affine recurrence with no residual Boolean branch. If an aligned row enters strict supercapacity from exact saturation, then the entrance occurs only at R mod 3=2 with local support pulse at most one and forces a missing canonical ancestor at rank a+1 or 2(a+1), where R=3a+2. That hole transports into the real greedy orbit: some skipped d satisfies d<=R<=3d and Q_d<2 sqrt(d)+6. This quantitatively connects quotient escape to the Lambert carry coordinate but does not prove that a late entrance occurs or contradict the permanent affine regime. These results remove the older bad-socket and negative-carry patterns and identify permanent affine supercapacity as the only remaining late fatal regime. They do not force an unbounded closed return, contradict that supercapacity regime, exclude the fatal branch, or establish 1/21 membership.

Evidence/status: lean_checked


### one_over_twenty_one_fatal_erdos_borwein_interval

If 1/21 is not represented, the finite skipped support has a greatest actual exponent M. Its finite Mersenne sum gives a rational approximation to the Erdos--Borwein Mersenne constant from above: the positive error is exactly the fatal greedy residual minus the complete tail and is strictly smaller than mersenneGap M. The reduced denominator of the skipped-prefix sum has odd binary doubling order exactly equal to the lcm of the skipped exponents, so in particular that order is at least M. The final skip is also dyadically unsafe: if N_(M-1) and N_(M+1) are the reduced rational greedy-remainder numerators immediately before the skip and after its forced successor take, then 2^M-1<|N_(M-1)| |N_(M+1)|. Hence at least one adjacent numerator is exponentially large. These are precise bridges from the fatal branch to height-, order-, and numerator-sensitive rational approximation. Irrationality of the constant supplies strict positivity but does not exclude one approximation in this interval. No theorem yet relates the numerator product or lcm/order to the approximation height strongly enough to contradict the gap, proves an applicable irrationality-measure lower bound for this structured family, or otherwise rules out the fatal branch.

Evidence/status: lean_checked_structured_approximation_interface_open_quantitative_exclusion

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

claim_boundary: The checked declarations send 1/21 non-membership to a structured one-sided rational approximation with exact error, odd-order, lcm, and adjacent-numerator constraints. They do not supply an applicable irrationality-measure or height contradiction, exclude the fatal branch, establish 1/21-membership, or resolve Erdős #257.

surviving_obligation: Exclude the structured rational interval forced by a last skip; equivalently continue to rule out TwentyOneFatalAlignedBranch by a closed-return, bounded-remainder, supercapacity, or other checked route.

### one_over_twenty_one_skipped_rank_sqrt_defect_bound

Lean now gives a denominator-specific quantitative bound at every actually skipped positive rank N: the scaled Mersenne tail weight is at most two, and the canonical denominator-21 defect satisfies Q_N < 2 sqrt(N) + 6. The one-step floor bit is at most one, so Q_(N+L)+1 <= 2^L(Q_N+1); consequently a skip at N forces Q_(N+L)+1 < 2^L(2 sqrt(N)+7) at every later offset L. Contrapositively, crossing that explicit threshold certifies that N was selected. This converts sufficiently large later defect into a checked selected-rank witness, but it does not prove that the threshold is crossed on an unbounded family, establish the normalized-small-return producer, rule out TwentyOneFatalAlignedBranch, or prove 1/21 membership.

Evidence/status: lean_checked


### one_over_twenty_one_slope_danger_reduction

Lean replaces the false translation-invariant six-step contraction with the exact floor-slope obligation. Writing Q_N for the denominator-21 greedy defect and L_N for the weighted six-step repair load, the next slope step Q_(N+6)<=floor((N+6)/6) is equivalent to 64Q_N+3(2^N mod 21)<=L_N+floor(N/6)+1. Outside the explicit slope-danger predicate this is automatic from L_N>=0, and every dangerous rank satisfies N<384Q_N+354. Commit 397638dc weakens the required supply from an all-depth induction to cofinally many successful slope steps: arbitrarily late non-danger ranks already prove 1/21 membership, and more generally it is enough that arbitrarily late danger ranks satisfy the exact repair inequality. Equivalently, non-membership forces every sufficiently late rank to be slope-dangerous and forces the eventual lower bound N<384Q_N+354. The same commit gives the exact bridge between Q_N, the scaled greedy remainder, and a bounded finite-prefix divisor tail. These are conditional and contrapositive reductions; they do not prove a cofinal safe-or-repaired supply or 1/21 membership unconditionally.

Evidence/status: lean_checked

- [BooleanMobiusCarry.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)

### one_over_twenty_one_small_lambert_defect_return_evidence

Exact integer regeneration through rank 200000 records 96 returns of the denominator-21 Lambert defect to zero, the last at rank 193690, and 4956 returns to defect at most one, the last at rank 199930, with maximum observed gap 492. Commit 3ac10c supplies the exact Lean consumer: cofinal recurrence of defect at most one already proves 1/21 membership, with no global defect bound or bounded return-gap hypothesis. The earlier rank-10000 receipt is retained for comparison. Neither the extended counts nor the observed gap proves that the returns are unbounded or cofinal, so this finite evidence does not promote the open claim.

Evidence/status: locally_regenerated_exact_finite_only


### one_over_twenty_one_full_quotient_terminal_zero_evidence

Exact integer regeneration through rank 200000 certifies that every audited canonical lower quotient state is strictly below 2^R. Completing each audited row with the exact binary suffix at ranks R+1 through 2R therefore leaves terminal defect zero, with no nonzero terminal row in the finite window. This is direct finite evidence for the closed-lower-state producer and rules out saturation only through the audited cutoff. It does not prove strict closure at every depth, the all-depth supply, cofinal attainment, 1/21 membership, or Erdős #257.

Evidence/status: locally_regenerated_exact_finite_only


### one_over_twenty_one_cofinally_bounded_defect_reduction

Lean proves that no uniform all-depth slope, maximum, or return-gap bound is needed: if the denominator-21 greedy defect visits any one fixed bounded band beyond every cutoff, then the carry has cofinal linear returns and 1/21 belongs to the Mersenne achievement set. The concrete band Q_N<=1 exactly matches the finite checker receipt. Proving that those observed small-defect returns continue cofinally is now the complete residual for this route.

Evidence/status: lean_checked


### one_over_twenty_one_fatal_tail_subexponential_defect_split

Lean now identifies the exact asymptotic content of the prescribed-point problem in the canonical denominator-21 defect coordinate. Once a greedy state is fatal, its positive excess over the complete remaining Mersenne tail is conserved, so non-membership supplies n and delta>0 with 2^(n+k) delta <= Q_(n+k)+1 for every k. Conversely, membership forces the canonical greedy carry divided by 2^N to tend to zero; the periodic carry/defect decomposition transfers that limit to (Q_N+1)/2^N. Therefore 1/21 belongs to the Mersenne achievement set if and only if TwentyOneGreedyDefectSubexponential holds. The equivalence makes subexponential defect growth the canonical residual rather than an arbitrary sufficient estimate, but it does not prove that estimate or establish 1/21 membership unconditionally.

Evidence/status: lean_checked


### one_over_twenty_one_cofinal_normalized_return_characterization

Lean now identifies the weakest checked positive producer in the normalized denominator-21 defect coordinate. Membership is equivalent to the following cofinal small-return condition: for every delta>0 and every cutoff K, some N>=K satisfies Q_N+1<2^N delta. Membership supplies the condition through the stronger full limit (Q_N+1)/2^N -> 0. Conversely, non-membership fixes one positive fatal excess and forces a geometric lower bound at every later rank, contradicting even one sufficiently small normalized return beyond the fatal rank. The theorem imposes no eventual upper bound and proves neither the cofinal returns nor 1/21 membership unconditionally.

Evidence/status: lean_checked


### one_over_twenty_one_cofinal_scaled_remainder_characterization

Lean gives an exact bounded-return characterization in the native greedy-remainder coordinate. Write r_N for the canonical greedy remainder of 1/21 after rank N. Membership is equivalent to the existence of one real B such that, beyond every cutoff K, some N>=K satisfies 2^N r_N<=B. On a surviving branch, r_N is at most the complete Mersenne tail and its scaled tail tends to 1. After a fatal rank, one fixed positive tail excess is conserved, so 2^N r_N eventually exceeds every proposed ceiling. This condition asks for neither convergence, a prescribed ceiling, nor a return frequency. It is an exact reformulation, not a proof that the bounded returns occur or that 1/21 is represented.

Evidence/status: lean_checked


### one_over_twenty_one_period_six_full_row_sign_classifier

Along the cofinal residue class 3 | R, the target fraction is exactly 1/21 and full-row overshoot is equivalent to the concrete inequality quotient-greedy defect + 1/21 <= local fractional mass. The remaining producer is therefore a bitwise/fractional-mass sign problem, not a generic real-analytic or quotient-remainder bound.

Evidence/status: lean_checked


### one_over_twenty_one_final_skip_numerator_floor

A hypothetical final denominator-21 skip has a reduced predecessor residual x=p/q in the exact three-channel window. Its dyadic excess Delta=p*2^M-q satisfies p<3Delta and Delta<p. Every denominator on the 1/21 greedy orbit is odd. These two facts exclude predecessor numerators p=1,2,3: p=2 is the already-forbidden Mersenne exceptional coordinate, while p=3 would force q even. Hence every final skip has predecessor numerator at least four. This sharpens the previously checked exponential adjacent-numerator product condition but is still only a necessary signature. It gives no upper bound on p, no contradiction with the fatal interval, no exclusion of TwentyOneFatalAlignedBranch, and no proof of 1/21 membership or Erdős #257.

Evidence/status: lean_checked_necessary_fatal_branch_signature

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

surviving_obligation: Exclude TwentyOneFatalAlignedBranch by contradicting its final-skip numerator/height signature or permanent affine-supercapacity regime, or establish one of the existing cofinal return, overshoot, or divergence producers.

### one_half_reciprocal_floor_obstruction_consumer

For a positive natural numerator p, a block that is both skipped and dyadically unsafe forces floor(2D/p+1)=2^k. Specializing this exact arithmetic lemma to the displayed half-greedy residual proves that it is enough to exclude power-of-two floors at actual skipped ranks; no condition is needed at taken ranks. This skipped-rank predicate implies dyadic safety at every skip and therefore implies (1/2 : real) belongs to the Mersenne achievement set. The earlier orbit-wide predicate remains a checked stronger specialization. The result supplies the previously missing logical bridge and weakens its source hypothesis, but it does not prove the skipped-rank obstruction, does not prove one-half membership unconditionally, and does not settle Erdos Problem 257.

Evidence/status: lean_checked_conditional_membership_reduction

- [HalfGreedyDyadicSafe.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfGreedyDyadicSafe.lean)

claim_boundary: The named Lean declarations prove the conditional chain from excluding power-of-two reciprocal floors at every actual skipped half-greedy rank to skipwise dyadic safety and then to one-half membership; the orbit-wide predicate is only a stronger specialization. They do not establish the skipped-rank floor obstruction, prove one-half membership unconditionally, construct a rational counterexample, or resolve Erdős #257.

surviving_obligation: At every actual skipped half-greedy rank n, prove that floor(2D_n/p_n+1) is not a power of two, or establish another global producer for dyadic safety of every skipped rank.

### one_half_skipped_two_thirds_margin_consumer

At every actual skipped half-greedy rank n, write the displayed residual as p/q with q=2D and X=2^(n+1). Lean proves that the margin 3pX<=3q+p puts p/q strictly below the full remaining Mersenne tail, and that this rankwise hypothesis implies (1/2 : real) belongs to the Mersenne achievement set. A named actual-coordinate bridge now carries nonpositive dyadic excess into block safety and then carries orbit-wide dyadic safety into the two-thirds hypothesis. The exact skipped state (p,D,k)=(7,13,2) satisfies the two-thirds margin while failing dyadic safety, so this is a genuine weakening rather than another equivalent floor reformulation. The result does not prove the margin along every actual orbit rank, does not prove one-half membership unconditionally, and does not settle Erdos Problem 257.

Evidence/status: lean_checked_strictly_weaker_conditional_membership_reduction

- [HalfGreedyDyadicSafe.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfGreedyDyadicSafe.lean)

claim_boundary: The named Lean declarations prove that the orbit-wide skipped two-thirds margin is a sufficient condition for one-half membership, that dyadic safety is a stronger sufficient specialization, and that the two-thirds predicate is strictly weaker on an explicit abstract skipped state. They do not prove the two-thirds margin at every actual half-greedy skip, prove one-half membership unconditionally, construct a rational counterexample, or resolve Erdős #257. The rank-64 replay is finite evidence only.

surviving_obligation: At every actual skipped half-greedy rank n, prove 3*p_n*2^(n+1)<=3*(2D_n)+p_n, or establish another global tail-survival producer.

### one_half_target_zero_quotient_row_small_slack_reduction

Lean treats the exact target-zero quotient rows sum_d floor(2^N/(2^d-1))=2^(N-1) directly. Cofinal existence of those rows produces achievement-set points converging to 1/2 from above, hence an infinite rational support and a counterexample to universal_257. A midpoint quotient-take/real-skip event is forced onto the unique deterministic seam word: its seam remainder is E=R+1, its residual satisfies R<=card(seam support), and hence E<d. Therefore the all-depth inequality E>=card+2 from d>=8 eliminates every mature midpoint mismatch. Along an upper reset followed by right branches, failure of this support-cardinality gap is Lean-equivalent to the exact reset-and-pulse charge entering the top cylinder window of width card+2. The late-upper pullback theorem now proves more structure: if s>=13, the largest non-right rank d is late, and rank s is an upper reset, then d is a middle producer, every intervening filled rank is an actual right branch, R_d>=d, and R_s>=2^s+s. These declarations do not prove the all-depth seam gap, cofinal target-zero row existence, the LargestSkipLateStepSocket, or the remaining non-midpoint comparison, so they do not decide Erdős Problem 257.

Evidence/status: landed_lean_checked_support_cardinality_reduction_with_late_upper_pullback_and_exact_finite_mechanism_audit

- [HalfCounterexampleFrontier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean)

claim_boundary: The cited Lean sources prove the target-zero compactness implication, the midpoint support-cardinality reduction, and the conditional late-upper pullback/amplification theorems. They do not prove cofinal target-zero rows, the all-depth SeamRemainderCardGapFromEight or LateUpperPreviousMiddleStaircaseEscape producers, LargestSkipLateStepSocket, or the remaining non-midpoint comparison. The finite audits discriminate mechanisms only and do not prove one-half membership or resolve Erdős 257.

surviving_obligation: Prove LateUpperPreviousMiddleStaircaseEscape and discharge the remaining base/middle/right branch fan-in to SeamRemainderCardGapFromEight, or independently prove LargestSkipLateStepSocket. Then finish the non-midpoint quotient-prefix comparison or the all-depth target-zero row producer.

### one_over_twenty_one_final_skip_parity_cancellation

At a hypothetical final denominator-21 skip, write the reduced predecessor residual as p/q. Lean turns the three-channel dyadic-excess window into an exact parity dichotomy. If p is odd, then 3*gcd(q,2^M-1)<p. If p is even, then 2*gcd(q,2^(M+1)-1)<p. In the even branch the adjacent numerator-product condition strengthens from 2^M-1<|N_(M-1)||N_(M+1)| to 2(2^M-1)<|N_(M-1)||N_(M+1)|. The coefficients are parity-sensitive: the odd branch does not assert the false uniform bound 2*gcd(q,2^M-1)<p. These are necessary final-skip signatures only. They give no incompatible upper-height, recurrence, or approximation bound, no contradiction with the fatal interval, no exclusion of TwentyOneFatalAlignedBranch, and no proof of 1/21 membership or Erdős #257.

Evidence/status: lean_checked_necessary_parity_sensitive_fatal_branch_signature

- [TwentyOneQuotientGreedy.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)

surviving_obligation: Exclude both parity branches of the final-skip signature, contradict permanent affine supercapacity, or establish one of the existing cofinal return, overshoot, or divergence producers.

### rational_greedy_skip_cofinality_characterization

For every nonnegative rational q, Lean proves that q belongs to the Mersenne achievement set if and only if its canonical greedy orbit omits infinitely many positive exponents, equivalently if and only if the actual greedy branch skips at arbitrarily late ranks. The forward implication uses irrationality of the full Erdos-Borwein constant: finitely many omissions would write that constant as q plus a finite rational Mersenne sum. The reverse implication is the existing absorbing-fatal-state consumer. The former half-specific theorem is retained as a wrapper. This is a general rational normal form, not a proof of cofinal skips for 1/2, 1/21, or any other unresolved target, and it does not decide Erdos Problem 257.

Evidence/status: lean_checked_general_rational_membership_normal_form

- [GreedyAchievementSet.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/GreedyAchievementSet.lean)

claim_boundary: The named Lean declarations characterize achievement-set membership for each nonnegative rational target by infinite omitted support, equivalently by actual greedy skips beyond every cutoff. They do not supply those cofinal skips for 1/2, 1/21, or any other unresolved rational target, produce a rational member, prove universal irrationality, or resolve Erdős #257.

surviving_obligation: For one nonterminating rational target, prove that the canonical greedy orbit skips beyond every cutoff, or prove a downstream scaled lower-separatrix condition that implies this exact cofinal-skip statement.

### rational_scaled_lower_separatrix_characterization

Lean now expresses the exact lower separatrix in the native scaled coordinate y_N=2^N r_N. Rank N+1 is skipped exactly when 2*y_N is strictly below c_(N+1)=2^(N+1)/(2^(N+1)-1). Hence, for every nonnegative rational q, membership in the Mersenne achievement set is equivalent to crossing this moving lower barrier beyond every cutoff. The 1/21 endpoint is packaged as that exact equivalence. No theorem proves the positive cofinal-crossing side for 1/21, so this sharpens the remaining producer without deciding Erdős #257.

Evidence/status: lean_checked_exact_scaled_separatrix_normal_form

- [GreedyTrapDynamics.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/GreedyTrapDynamics.lean)

claim_boundary: The named Lean declarations identify each skip with the exact scaled lower-branch inequality and characterize nonnegative-rational membership by cofinal crossings of that moving barrier; the 1/21 theorem is only this equivalence specialized to the target. They do not prove a cofinal crossing for 1/21 or any other unresolved rational target, establish membership, produce a counterexample, prove universal irrationality, or resolve Erdős #257.

surviving_obligation: Prove that the canonical 1/21 scaled greedy orbit crosses the exact moving lower separatrix beyond every cutoff.

### one_half_reset_sqrt_escape_crossing_reduction

Lean reconstructs the actual reset at the largest false rank and the actual intervening right suffix. If that suffix reaches either integer cell where the late rank crosses the two-thirds boundary while the current branch is still right, then the reset deviation at its creating row d has absolute value at most 2^((d+4)/2)+2d+3. Lean proves the square of that envelope is at most 2^(d+5) for d>=10. Consequently, the all-depth square-root escape 2^(d+5)<dev_d^2 discharges LargestSkipLateStepSocket and implies (1/2) belongs to the Mersenne achievement set. No theorem proves square-root escape, one-half membership unconditionally, or Erdos Problem 257.

Evidence/status: landed_lean_checked_all_depth_conditional_reset_crossing_reduction_with_exact_return_time_experiment

- [HalfCylinderResetSqrtEscape.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfCylinderResetSqrtEscape.lean)

claim_boundary: The checked declarations prove that an explicit all-depth square-root escape condition would close the late largest-skip socket and imply 1/2-membership; finite reset experiments only select the return-time mechanism. They do not prove square-root escape, an all-depth return-time bound, 1/2-membership, or Erdős #257.

surviving_obligation: Prove SeamResetSqrtEscape at every actual upper-or-middle reset r>=10. The experiment selects the stronger structural route: if L is the exact number of following right branches before the next reset, prove 2^r<=|seamResetDeviation r|*2^L and an all-depth half-row upper bound on L strong enough to force 2^(r+5)<seamResetDeviation(r)^2.

### one_half_reset_sqrt_escape_scale_producer_collapse

On middle branches the landed recurrence gives dev_s = 4*R_s - belowPulse_s with the universal pulse bound belowPulse <= 2*(s-2), so middle sqrt escape follows from the producer 3*2^((s+5)/2)+2*(s-2) <= 4*R_s. On upper branches the landed reset identity gives dev_d = -(4*overshoot_d+abovePulse_d), so upper sqrt escape is exactly the producer 3*2^((d+5)/2) <= E_d. The factor 3 absorbs both parities since (3*2^k)^2 >= 9*2^(r+4) > 2^(r+5). The two named producers jointly imply SeamResetSqrtEscape and hence 1/2 membership. Boundary forms restate each producer on the post-reset landing remainder, the quantity the nested backward pullback identities control.

Evidence/status: lean_checked_exact_collapse_of_sqrt_escape_into_two_named_scale_producers

- [HalfResetSqrtEscapeScaleProducers.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfResetSqrtEscapeScaleProducers.lean)

claim_boundary: The checked collapse proves that the named middle- and upper-reset scale producers jointly imply square-root escape and therefore 1/2-membership. It does not prove either producer, square-root escape, 1/2-membership unconditionally, or Erdős #257.

surviving_obligation: Prove SeamMiddleResetRemainderScaleProducer and SeamUpperResetChargeScaleProducer unconditionally; validation of the collapse module under lease tickets rct_7b5bda46a2c92d249cd0 and rct_625c4847d9ddafe39e66.

### four_ninths_diagonal_small_margin_obstruction

For the exact 4/9 diagonal recurrence, coprimality of 2d-1 and 2d and the forced bit b_1=0 bound the full paired divisor load by twice the selected count s. Lean proves that skipped rows automatically preserve the reserve 2s<=3rho, so global nonnegativity is reduced to the single selected-landing producer b_(d+1)=1 -> 2s_(d+1)<=3rho_(d+1). The stronger sufficient producer b_(d+1)=1 -> d+1<=rho_(d+1) is equivalent to the literal endpoint inequality saying that the selected predecessor clears the dyadic coin by at least the landing rank. An exact kernel-checked countermodel retains the complete certified depth-twelve bit word 010110110001, the exact count six, load three, pulse one, and a large incoming reserve, but changes rho_12 to 2049; rank thirteen is then selected and lands at rho_13=1, violating the reserve for the new count seven. Therefore local phase, load, count, forced anchors, and even the full certified bit prefix do not imply the producer when rho is detached from history. Lean now proves the missing reachability identity: rho_d is the finite base-four weighted sum of every actual earlier pulse, divisor load, and selected coin. It rewrites failure of the landing-rank producer as existence of one actual selected endpoint inside the explicit rank-wide bad history window. This is an exact transformation, not an anti-concentration estimate. No theorem yet excludes that history window, proves the selected-landing producer, proves rho_d>=0 at all depths, establishes membership of 4/9, or resolves Erdős #257.

Evidence/status: lean_checked_arithmetic_reduction

- [FourNinthsDiagonalMarginProducer.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/FourNinthsDiagonalMarginProducer.lean)

surviving_obligation: Prove the actual selected-landing producer b_(d+1)=1 -> 2s_(d+1)<=3rho_(d+1), or the stronger landing-rank producer d+1<=rho_(d+1). These imply rho_d>=0 at every depth, but neither is yet proved.

### one_half_selected_ancestry_budget_and_first_window_charge

For the rational half-greedy orbit, write e_n=1/(2^n-1)-2^-n. The selected-ancestry budget starts at B_0=1/2, deposits e_n on a take, and spends 2^-n on a skip. Lean proves r_N=2^-N-B_N and 2^N r_N=1-2^N B_N, so the sharp phase ceiling is exactly B_N>0. A first negative crossing can occur only on a skip and lands in the strict recoverable interval -e_(N+1)<B_(N+1)<0. At an actual skipped rank N, the new bridge proves frozenMargin(N-1,N)=2^(2N)B_N-Phi_(A_N)(2N). It then proves that positivity of this selected-ancestry full-shell expression is equivalent to the already-landed HalfGreedySkippedFullShellNonnegative producer and consumes it to half-membership. Thus the first-window charge, future-skip capacity, frozen margin, and seam sign are exact views of one open producer, not independent advances.

Evidence/status: lean_checked_budget_conjugacy_and_source_current_frozen_margin_reconciliation_with_bounded_charge_audit

- [SelectedAncestryBudget.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/SelectedAncestryBudget.lean)

claim_boundary: The cited Lean modules prove the selected-ancestry coordinate identities, first-negative-crossing localization, conditional membership consumers, and equivalence of full-shell coverage with the existing skipped-full-shell nonnegativity producer. They do not prove that producer at every actual skip, prove the all-scale first-window charge inequality, establish one-half membership, produce a rational counterexample, or resolve Erdős #257. The rank-100000 and bounded charge audits are finite evidence only, and the failed atom-tail shortcut cannot be used as a proof premise.

surviving_obligation: Prove HalfGreedySkippedFullShellNonnegative, equivalently the all-scale actual-skip first-window charge inequality J_N>2^N(Q_N-1), or find a genuinely different construction/exclusion route for the exceptional null point.

### one_half_selected_ancestry_tail_survival_equivalence

For the pinned half-greedy orbit, let B_N be the selected-ancestry budget, E_N=mersenneTail(N)-2^-N the positive correction tail, and C_N=B_N+E_N. Lean proves C_N=mersenneTail(N)-r_N. A take preserves C_N and a skip subtracts exactly the omitted Mersenne weight. Every complete Mersenne tail is irrational, so the rational budget cannot meet the boundary B_N=-E_N. Consequently 1/2 belongs to the Mersenne achievement set if and only if C_N>0 for every N, equivalently B_N>-E_N for every N. This is strictly weaker than the previously targeted B_N>0/full-shell condition and changes the canonical selected-ancestry endpoint, but it is an exact equivalence rather than a proof of survival.

Evidence/status: lean_checked_exact_weak_endpoint_equivalence

- [SelectedAncestryTailSurvival.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/SelectedAncestryTailSurvival.lean)

claim_boundary: The named declarations identify 1/2-membership exactly with all-depth complement-budget survival and prove survival from an explicit cofinal first-negative-crossing hypothesis. They do not prove that hypothesis, prove complement-budget positivity for the actual orbit, establish 1/2-membership, produce a rational counterexample, or resolve Erdős #257.

surviving_obligation: Prove that every actual half-greedy depth satisfies 0<C_N, equivalently B_N>-mersenneCorrectionTail(N); or solve Erdős #257 through a structurally distinct target or universal route.

### one_over_twenty_one_multiple120_primorial_repair_socket

Let U_30(n) count actual selected divisors lying in the union of the n/2, n/3, and n/5 divisor columns. Lean proves the exact subtraction-free seven-column inclusion-exclusion identity, the doubled-layer identity, the coupled factor-descent consumer, and the nineteen-position prime-pullback normal form. Those identities remain valid. The proposed universal inequalities do not: the deeper certified orbit first violates PU240+ at n=5,296,080=240*22,067 with Q_(n-1)=12 and pullback-column load 6, so the required 12<=11 fails. Through rank 20,000,002 there are 17 PU120 violations and 11 PU240+ violations. This closes PU120, PU240+, the prime-column bound, and their coupled factor-descent route as proof producers without affecting the open 1/21 membership question.

Evidence/status: lean_checked_exact_conditional_reduction_with_deeper_canonical_falsification

- [TwentyOnePrimorialRepair.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/TwentyOnePrimorialRepair.lean)

claim_boundary: The named declarations and finite falsifiers are source-current, but this packet row proves neither 1/21 membership nor a universal inequality: it retires the stated primorial-repair producers while retaining exact finite coordinate reductions.

surviving_obligation: Contradict TwentyOneFatalAlignedBranch by a source-sensitive return mechanism, prove 1/2 membership through the actual last-upper-ancestor endpoint packet, or solve Erdős #257 through another structurally distinct route.

### prime_slack_two_valued_closed_form

At a prime p the only divisor of p that can lie in A is p itself, since 1 is never selected, so tau_A(p)=1_A(p) in {0,1} and the carry identity becomes the subtraction-free t+cp=e+2*cm with t=tau_A(p)<=1, e=eps_p<=1, cp=C_p, cm=C_(p-1). Lean proves from that hypothesis alone: the halving bound 2*C_(p-1)<=C_p+1; that the prime slack s(p)=(C_p+1)/2-C_(p-1) is two-valued; the closed forms s(p)=1 iff (tau_A(p)=0 and eps_p=1) and s(p)=0 iff (tau_A(p)=1 or eps_p=0), so the vanishing set is exactly {p in A} union {p : eps_p=0}; and the parity corollary C_p = tau_A(p)+eps_p mod 2, which needs no bounds on t or e at all because the 2*cm term is even. The whole module is pure linear arithmetic over N with division by the literal 2 -- the fragment omega decides -- and contains no divisor theory, which is why section 84's result states abstractly.

Evidence/status: lean_checked_closed_form_for_the_sharpest_local_carry_constraint

- [PrimeSlackTwoValued.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/PrimeSlackTwoValued.lean)

claim_boundary: The named Lean declarations prove only the abstract local linear-arithmetic consequences of t+cp=e+2cm under t,e<=1, plus the parity consequence without those bounds. Applying them at a prime uses the separately stated identification t=tau_A(p)=1_A(p); the module itself contains no divisor theory. The closed form supplies no survival discriminator, global carry control, rational member, universal irrationality theorem, or progress toward resolving Erdős #257.

surviving_obligation: Unchanged. This proves the local constraint; it supplies no producer and is not progress on Erdos 257.

### socket_run_rational_cap_and_parity_obstruction_on_candidates

A socket run of length K at N forces 2^k | tau_A(N+k) for k=1..K, so each head term tau_A(N+k)2^-k is an integer and drops out of the fractional part: frac(2^N y) <= sum_{k>K} tau_A(N+k)2^-k = S/2^K with S = sum_{j>=1} tau_A(N+K+j)2^-j the local divisor mass, whose floor is the forward carry, so S < C_(N+K)+1. If y = p/q in lowest terms with q odd then frac(2^N y) is a multiple of 1/q, hence vanishes or is at least 1/q. Lean proves the resulting cap 2^K < q*(C_(N+K)+1), i.e. K < log2 q + log2(C+1), together with its contrapositive producer form: a support with socket runs longer than log2(q(C+1)) cannot sum to p/q. Separately, the identity Odd_A = {m : tau_A(m) odd} = {m : eps_m != C_m mod 2} bridges section 46's parity obstruction to the section-11 carry transducer, two previously unlinked lanes.

Evidence/status: lean_checked_rationality_cap_on_socket_runs_plus_computed_parity_obstruction_slack_on_every_candidate

- [SocketRunRationalCap.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/SocketRunRationalCap.lean)

claim_boundary: Lean proves the conditional rationality cap for a socket run when the represented rational has the stated odd denominator, plus the parity/transducer identity. It does not force a socket run beyond that cap on any candidate support. The depth-bounded candidate censuses measure slack and eliminate one proposed parity route only; they do not prove an all-depth producer, irrationality, or Erdős 257.

surviving_obligation: Force socket runs longer than log2(q(C+1)) on a candidate support, which no one has. Until then this is a necessary condition on a counterexample, not a producer, and not progress on Erdos 257.

### four_ninths_coin_cancellation_removes_the_exponential

Split the coin 2^(j+1)+1 in the history identity (5). Its power part is divisible by 2^d at every base-four weight, so rho_d modulo 2^d is a bounded-magnitude base-four sum over only the last ceil(d/2) pulse/load/decision increments. Independently, every old finite Mersenne quotient at endpoint 2d scales by four plus exactly the paired divisor load, while a newly selected boundary rank contributes 2^(d+1)+1. Therefore rho_d is exactly floor(4^(d+1)/9) minus the actual selected finite quotient row. The compactness module proves that the all-depth window 0<=rho_d<=2^d makes those finite supports converge to 4/9 and hence proves membership by closedness. The saturation module then proves that a first saturation must be a skipped row whose predecessor satisfies 4*rho_d=2^(d+1)+load-pulse, hence load=pulse mod 4; avoiding the corresponding final-half-history midline gives the strict upper window. Equivalently, it is sufficient that no skipped remainder have full-rank dyadic divisibility. The adaptive module proves that 2^d | rho_d forces, simultaneously for every 2k<=d, divisibility by 4^k of the weighted last-k small-increment suffix. Those increments lie between -(2j+1) and 2 after rank two; the newest digit is a nonpositive multiple of four, while a positive digit can occur only at pulse three with load at most two. The no-go companion proves that the local suffix conditions admit an arbitrary-depth -4,-3,-3,... carry. The midpoint companion restores the missing source coupling: at even depth 2k, rho_(2k)=4^k(rho_k-W_k)+S_k for the complete actual future-half take word W_k; full divisibility writes S_k=4^k c with c<=0, so saturation forces rho_k+c-W_k=1 and W_k<rho_k. At odd depth 2k+1 the exact quotient is two and saturation forces W_k^odd+2<=rho_(k+1). The module packages exclusion of those two exact equalities and proves that it is equivalent, with no slack, to the strict upper window rho_d<2^d at every depth; together with the independent selected-landing rank producer it feeds the compactness membership consumer. The cylinder transport companion now formalizes the base-four affine endpoint transport and deletes every state-dependent proper-divisor load except the midpoint m+1. It proves that suffix width L<=m-1 places that midpoint in the common prefix, making both next-row loads parent-independent, and separately proves that exact zero-defect even quotient rows at every depth imply 4/9 membership without any nesting assumption. The cofinal-repair companion introduces the scalar floor defect Q_N=floor(4*2^N/9)-P_N for the actual rational greedy orbit. Its exact recurrence, fatal-tail geometric lower bound, and divisor-pair cap prove that repairs Q_(N+1)<=Q_N beyond every cutoff force 4/9 membership. It also proves from the reduced-denominator order theorem that no finite rank-at-least-two Boolean support sums to 4/9: the support lcm divides six, leaving only ranks 2,3,6, and all eight subsets fail. Thus cofinal repairs conditionally yield an infinite exact-4/9 support and negate universal irrationality. The causal module now exposes the live 2-3-5 producer at multiples of 120, an exact but falsified 2-3-7 comparator at multiples of 84, and the stronger 2-3-5-7 candidate at multiples of 420. For modulus 84 Lean proves the seven-column identity, base load six, inclusion in the full load, conditional counterexample endpoint, and prime-row normal form with an eleven-position proper-divisor column and defect ceiling seventeen; the fifty-million-rank replay falsifies both its causal inequality and its actual periodic repair law. For modulus 420 Lean defines the subtraction-free four-parent union, proves inclusion in the full load, evaluates the exact base load as twelve, and connects its all-depth hypothesis to the same counterexample endpoint; the exact fifty-million replay retains minimum causal margin two with no violations or equalities. These are sharp producer/consumer and falsifier interfaces, not the missing global ancestry or cofinality theorem: excluding the exact midpoint carry equality, keeping the reachable cylinder below its midpoint seam, or proving the surviving modulus-120 periodic inequality still requires complete selected-divisor ancestry. Nonmembership remains reduced to a selected accumulated-history bad window, a skipped row with full-rank dyadic divisibility, or eventual strict scalar-defect increase. These are exact reductions, not the missing all-depth producer.

Evidence/status: source_current_lean_checked_cancellation_exact_even_quotient_compactness_saturated_boundary_midpoint_reachability_and_conditional_full_counterexample_reductions

- [FourNinthsCoinCancellation.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/FourNinthsCoinCancellation.lean)

claim_boundary: The cited Lean modules prove the exact quotient/carry identities, compactness consumers, obstruction equivalences, and conditional membership or counterexample endpoints stated here. They do not prove the selected-landing producer, exclude every full-rank skipped remainder or midpoint equality, or establish cofinal one-step repairs. The finite audits calibrate candidate producers only; they do not supply an all-depth quantifier, prove 4/9 membership, or resolve Erdős 257.

surviving_obligation: Neither the selected-landing rank producer, the skipped-remainder two-adic or midline-avoidance producer, nor cofinal one-step repairs are proved. The exact consumers and finite audits therefore do not establish 4/9 membership or resolve Erdos 257.

### prime_power_rich_powerful_support_irrationality

The earlier ordinary theorem treated prime-power-rich powerful supports at every integer base. It is now strictly subsumed: every support contained in the powerful integers has summable reciprocal mass, so the stronger checked reciprocal-summable theorem covers every infinite powerful support at every integer base, with no isolated-prime-power hypothesis.

Evidence/status: superseded_as_a_consequence_of_the_all_base_reciprocal_summable_theorem

- [erdos257_iteration46_powerful_supports_2026_08_24.md](docs/formal_math/erdos257_iteration46_powerful_supports_2026_08_24.md)

surviving_obligation: The unresolved #257 region has divergent reciprocal mass. Formalizing the standard powerful-number reciprocal-summability bridge would yield a named Lean corollary but would not strengthen the current mathematical theorem.

## Known failed routes

The 4/9 modulus-84 2-3-7 causal producer is false despite explaining all eight maximum observed repair-gap rescues and surviving through rank one million. The exact fifty-million replay first fails at 2008356=84*23909 with margin -1; it has 375 causal violations, 888 equalities, and minimum margin -6 among 595238 rows, while the actual modulus-84 repair law also reaches -6. Prime rows account for 318 violations among 48743 primes p>7. The Lean-checked base-six and eleven-position prime-column normal forms remain useful exact falsifiers, but modulus 84 is retired as a cofinal producer.

A single fatal gap, finitely many fatal gaps, or even a density statement about fast indices does not imply Cantor topology; the returned theorem uses strict dominance at every selected coordinate.

Achievement-set uniqueness, topology, positive measure, or Bernoulli-law regularity does not determine whether a particular support subseries value is rational.

The theorem does not decide membership of 1/2 in the full Mersenne achievement set and does not upgrade finite half-cylinder evidence.

The denominator-21 saturated equality s=2^R does not conceal an alternative closed Boolean row: the strong quotient gap forces the canonical quotient-greedy row even at equality. This removes Boolean ambiguity, not the need to prove closed-window supply or cofinal attainment.

The saturated transition does not require all three units of the unique nonzero denominator-21 target pulse: the boundary coin's extra unit reduces the exact local requirement to two. After a strict predecessor, saturation can still be born at the single exact mid-carry C=2^(R+1), but saturation alone is no longer the recursive obstruction. Failure of the following socket forces R mod 3=1, an incoming divisor pulse 4k, the exact half-state s=2^(R-1)+k, and a following local pulse of at most one. For R>=4 it also forces one of the older support positions a+1 or 2(a+1), where R=3a+1, to be absent. The exact fatal/cofinite/aligned branch fills both positions eventually, so it cannot sustain this bad socket at sufficiently large depth. Lean does not prove that bad saturated sockets must occur cofinally, so this exclusion still does not rule out the fatal branch.

The uniform six-step contraction Q_(N+6)<=Q_N+1 is not the correct all-depth producer: exact computation first falsifies it at N=73. The Lean-checked replacement spends the accumulated floor slack and asks for repair-load arithmetic only at explicit slope-danger ranks.

The square-root defect bound Q_N<2 sqrt(N)+6 holds at skipped ranks only. Its iterated growth envelope can certify that an earlier rank was selected when a later defect crosses an explicit dyadic-square-root threshold, but no theorem proves cofinally many such crossings. It therefore does not by itself provide a cofinal normalized return or prove 1/21 membership.

Neither named sunflower socket is a genuine route into the unresolved regime. SunflowerForcedCarrySupply is an exact-value near-return property strictly stronger than irrationality, while OrthogonalPetalBouquet is Lean-proved reciprocal-summable and its selector endpoint is subsumed by unconditional reciprocal-support irrationality.

For the Mersenne block-renormalisation construction, no fixed modulus can retain all raw deficit-coefficient phases, whose exact joint period is lcm(2,...,J). The actual nonlinear cascade also defeats the tested fixed phase moduli through 2520 at certified finite block boundaries. This kills that small-state simplification, not the construction family or an adaptive quotient.

The dyadic-block skip statement is not a weaker consequence of the existing seam/card machinery. Under SeamRemainderCardGapFromEight it is equivalent to B_N>=0, hence to the same sharp half-phase ceiling. Parent-block pulse bounds classify a negative-budget all-take block but do not exclude it.

Support-independent factor-grid Booleanisation fails immediately. Symmetrically carrying the ordered pairs in E_*=sum_{d,k>=2}2^(-dk) gives Möbius coefficients a_8=-1 and a_9=2. The stronger beyond-block atom-tail payment also has 30 exact skipped-rank counterexamples through 500. A successful carry must use the live selected-divisor ancestry and integer sheet.

The 1/21 primorial-repair sockets are canonically falsified beyond their original horizon. The first PU240+ violation is n=5296080=240*22067, where 22067 is prime, Q_(n-1)=12, and the nineteen-position pullback column has load 6, so the isolated bound 12<=6+5 fails. Through rank 20000002 there are 17 PU120 violations and 11 PU240+ violations. The exact seven-column, doubled-layer, and prime-pullback identities survive, but PU120, PU240+, the prime-column bound, and their coupled factor-descent route are not live producers.

The crude divisor ceiling on the forward carry cannot be the binding constraint, and the quantitative branch left open by scripts/carry_divisor_bound.py is closed. Writing rho_d(m) for the least k>=1 with d | m+k, the swap of summation gives S_m(B)=sum_{k>=1} tau_B(m+k)2^-k = sum_{d in B} 2^-rho_d(m) 2^d/(2^d-1) for ANY index set B, so the ceiling itself has the support-free closed form Theta(m)=sum_{d>=1} 2^-rho_d(m) 2^d/(2^d-1) and splits exactly as Theta(m)=S_m(A)+S_m(A^c). The ceiling's slack is therefore the divisor supply of the complement support, which for a surviving target is the greedy support of the dual target E-y; the complement remainder is exactly the corpus's complement budget Tail_N-r_N. Since rho_d(m)<=d and 1..D_0 with D_0=max{d: w_d>y} can never be selected, Theta(m)-C_m >= sum_{d<=D_0} w_d >= 1 for every m and every surviving y<1: the ceiling is never tight. Hence C_m/Theta(m)->1 is exactly equivalent to the dual target's carry being o(Theta), a statement about another surviving target rather than about a bound. Exact integer verification at depth 4000 over six targets and 2172 ranks sampled across dyadic bands 6-12: zero violations of the swap and of the split, min slack 1.89-2.50 against proved lower bounds 1.00-1.60, and max C_m/Theta(m) confined to [0.34,0.68] with no approach to 1. The dyadic target 1/2 independently reproduces the section-11 transducer degeneracy C_m=floor(S_m(A))-1. This is a route closure inside the lane CertificateSocketCollapse.md section 19 already closed for every LINEAR functional; it does not enter the non-linear residual of section 73.4 and is not progress on Erdos 257. Note ErdosProblems/Erdos257/DivisorCeilingDuality.md; probe scripts/divisor_ceiling_duality.py; receipt state/formal_math/erdos257_period_noncollapse/divisor_ceiling_duality_receipt.json.

The height/denominator lane is dominated everywhere, not merely dead for the current candidates, because its threshold and the transcendence lane's threshold are the same axis: the support density. By the cyclotomic factorisation, log2 lcm{2^d-1 : d in A_N} = sum_{k in Div(A_N)} log2 Phi_k(2), which exact computation shows equals (3/pi^2) delta_N N^2 with the normalised constant flat at 0.302 across a 64-fold range of density (N=400, delta=1..1/64), and 0.34-0.39 for the actual greedy supports of 1/2, 1/21, 4/9, 1/465, 1/5, 5/12 at N=100..700. A separation argument needs log2(den) <= 2N to beat the fatal window (2/3)4^-N, hence needs delta_N <= 2 pi^2/(3N) ~ 6.6/N -- support density exactly zero. The Mahler-Nishioka / Adamczewski-Bugeaud lane instead has a FIXED measured density threshold delta ~ 2^-5 (RunLengthMarginLawAndDivisorMultiplicity.md s.14), so the two cross at N ~ 212 and thereafter the height route requires a strictly sparser support than the regime the complexity machinery already covers. The containment is permanent regardless of where the complexity threshold actually sits, because 6.6/N tends to zero and any fixed threshold does not. Sections 10 and 14 are therefore one inequality read at two densities, not two independent failures. Neither lane closes any target: s.14's claim boundary stands, sub-exponential complexity being strictly weaker than those theorems' hypotheses. Route closure and an explanation, not progress on Erdos 257. Note ErdosProblems/Erdos257/HeightComplexityDichotomy.md; probe scripts/height_complexity_dichotomy.py; receipt state/formal_math/erdos257_period_noncollapse/height_complexity_dichotomy_receipt.json.

The characteristic-two lift lane collapses onto a single binary word, the carry parity, and that word is high-entropy -- so CharacteristicTwoRealLiftScan.md section 4's 'larger source period / larger real period' caveat is not a horizon a longer scan would clear. In that lane the F_2 Dirichlet inverse b = g*mu (mod 2) makes tau_A(n) = g(n) (mod 2) hold by construction, so the corpus's carry identity eps_m = (tau_A(m)+C_m) mod 2 becomes eps_m = g(m)+C_m mod 2 with g periodic, giving the exact equivalence: the real lift S_B is rational iff C_m mod 2 is eventually periodic. Measured at depth 4000 with exact integer carries (K=64, zero ambiguous floor ranks) over seven sources including the squarefree witness and the scan's best finite fit: tau_A(m)=g(m) mod 2 verified at every rank; no eventual period of the carry parity at all up to preperiod 64 and period 512 for any infinite support; subword complexity p(12)=1473-1581 against matched Bernoulli nulls 1570-1615; entropy 0.9958-1.0000 bits. The single source with periodic carry parity has |A|=1 through depth 4000 -- the finite-support boundary of LambertPeriodicBooleanisationNoGo.md reappearing as the lane's only periodic point, i.e. its sole success is the case that is not a counterexample. Any future lift law must act on C mod 2. This relocates the characteristic-two problem and does not solve it; it proves no irrationality and is not progress on Erdos 257. Note ErdosProblems/Erdos257/GF2ParityBooleanisation.md; probe scripts/gf2_parity_booleanisation.py; receipt state/formal_math/erdos257_period_noncollapse/gf2_parity_booleanisation_receipt.json.

The 4/9 residue-certificate suffix excess is unbounded and the total window tracks log2 d, which closes the fixed-suffix route structurally and quantifies what an adaptive proof must control. FourNinthsDiagonalMarginInvariant.md left this exactly open ('neither prove that the required suffix excess is unbounded nor rule out a genuinely nonlocal use of (5)') and asked for a computation that discriminates arithmetic descriptions of the overshoots rather than extending the horizon. Executed at horizon 200000 with predictions declared before the run: modelling rho_d mod 4^k as equidistributed gives P[excess >= e] ~ 4^-e, so the max excess over a dyadic band of ~2^i ranks should grow linearly in i with slope ~0.5. Measured: 100,098 selected ranks, ZERO landing-rank violations, fitted slope 0.6648 over 13 bands, inside the declared [0.3,0.8]; the plateau falsifier did not fire. Three calibrators hit exactly -- the Lean base fixture (bit prefix 010110110001, rho_12=2460), the first base-certificate failure at rank 20 with rho_20 mod 64 = 12, and max excess 14 at rank 146803, the last two being the exact values the invariant note records, reproduced by an independently written instrument. Reading, both directions: NO fixed-suffix residue certificate can work, since any constant k is defeated once the horizon passes ~4^k, so a proof of the selected-landing rank producer cannot be a bounded-suffix argument; but the required window is only LOGARITHMIC, total k sitting at log2 d plus max-statistic fluctuation (k=14 at d=25002 against log2 d=14.6; k=17 at d=45203 against 15.5), so an adaptive certificate needs the last Theta(log d) increments. That is outside the closeout's forbidden 'bounded window of divisor loads' class and explains why the depth-twelve local countermodel does not reach it: the countermodel fixes a constant depth while the requirement grows. Growth is COMPUTED on one target to horizon 200000 and the geometric model behind the prediction is HEURISTIC; this proves neither the producer nor unboundedness at all depths, supplies no producer, and is falsification and calibration evidence under the allocation guard. Note ErdosProblems/Erdos257/FourNinthsResidueExcessGrowth.md; probe scripts/four_ninths_residue_excess_growth.py; receipt state/formal_math/erdos257_period_noncollapse/four_ninths_residue_excess_growth_receipt.json.

## Open implications

### contradict_twenty_one_permanent_affine_supercapacity

Contradict the exact permanent affine-supercapacity regime forced by TwentyOneFatalAlignedBranch. Commit bad43508 proves that any unbounded sequence of closed canonical rows s_R<=2^R already gives the compactness decay required for 1/21 membership, so the fatal branch must eventually satisfy 2^R<s_R at every rank. Combined with commit f23727a, the boundary coin is then always taken: support appends R+1 and the scalar follows one literal affine recurrence with no residual Boolean branch. Commit 73f417a additionally proves that an aligned crossing from exact saturation into strict supercapacity must occur at R=3a+2 and omit a canonical ancestor at a+1 or 2(a+1). This restricts one entrance mechanism but does not show that the fatal branch enters late from exact saturation or contradict the regime after entry. One direct producer is an arbitrarily deep closed return, or any checked consequence of the affine recurrence that is incompatible with permanent supercapacity. Cofinal overshoot, rational-greedy divergence, bounded scaled-remainder returns, cofinal small normalized defect, and the older bad-socket route remain sufficient alternates. No theorem currently supplies the contradiction, excludes TwentyOneFatalAlignedBranch, proves 1/21 membership, or decides Erdős #257.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_cofinal_full_overshoot

The exact surviving obligation after bad43508 is to contradict permanent affine supercapacity, or force an arbitrarily deep closed return. Any unbounded sequence of closed canonical rows already proves 1/21 membership, so TwentyOneFatalAlignedBranch must eventually satisfy 2^R<s_R at every rank; under the exact aligned transition the boundary coin is then always taken and the support and scalar follow one literal affine recurrence. The cofinal full-overshoot route remains a checked alternate: establish quotient-greedy defect + 1/21 <= local fractional mass for an unbounded sequence of full rows with 3 | R, or prove that the full quotient-greedy Boolean word differs cofinally from exact rational greedy. Those producers feed the existing membership endpoint, while finiteErdosSum_ne_one_div_twenty_one upgrades membership to an infinite rational support counterexample. No theorem supplies the affine-regime contradiction, an unbounded closed return, cofinal overshoot, or cofinal divergence; the fatal branch, 1/21 membership, and Erdős #257 therefore remain open.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_closed_lower_state_supply

Prove that at every even depth the canonical quotient-greedy remainder lies in the closed window s<=2^R. Commit 089167b proves that one such closed lower state at every depth already yields 1/21 membership. Commit a16f6a1 proves that any closed Boolean row is necessarily this canonical row, including at equality. Commits a33fbc8 through a3e5d1e reduce failure of the recursive saturated socket to a rigid older hole: at R=3a+1, either a+1 or 2(a+1) is absent. Commit 4c615519 identifies the quotient support with the actual greedy support under full alignment and uses cofinite fatal-branch selection to fill both ancestors eventually. Hence the exact nonmembership branch cannot realize late bad saturated sockets. The surviving recursive task is no longer to rule out arbitrary ancestor holes; it is to force bad saturated sockets cofinally, or otherwise prove closed-window supply by a different route. Commit 516de51f supplies finite evidence through rank 200000: every audited state is strict and every completed row has terminal defect zero. The finite audit proves neither cofinal bad-socket recurrence nor all-depth closed-window supply.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_slope_danger_repair_load

Produce arbitrarily late ranks at which the exact six-step floor slope succeeds. A non-danger rank succeeds automatically; at a danger rank it is enough to prove the exact repair-load inequality. Commit 397638dc proves that either cofinal supply yields 1/21 membership and, contrapositively, that non-membership would force every sufficiently late rank into the explicit danger region N<384Q_N+354. Commit c1b2689 separately proves Q_N<2 sqrt(N)+6 at every skipped positive rank. Commit c616692 propagates that estimate forward and makes a later violation of the resulting dyadic-square-root envelope certify that the earlier rank was selected. This sharply constrains the skip branch but does not control the selected ranks that are eventually cofinal under nonmembership or prove cofinally many threshold violations. Thus the remaining input is no longer an all-rank repair theorem, while the selected-rank certificate alone is not the missing cofinal producer. The rank-200000 replay supplies finite evidence of late safe ranks but does not prove that such ranks occur beyond every cutoff.

Evidence/status: weakened_to_cofinal_safe_or_repaired_supply


### prove_twenty_one_cofinal_small_defect_returns

Prove that the exact denominator-21 greedy defect returns to Q_N<=1 beyond every cutoff. Commit 3ac10c proves this concrete cofinal-return statement is already sufficient for 1/21 membership; no global defect bound and no bounded return-gap theorem is required. The rank-200000 exact receipt records defect zero 96 times through rank 193690 and defect at most one 4956 times through rank 199930 with maximum observed gap 492. The finite counts and observed gap alone are not a cofinality theorem.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_cofinal_scaled_remainder_bounded

Prove the exact moving-barrier recurrence statement: for every cutoff K, some N>=K satisfies 2*scaledGreedyRemainder (1/21) N < mersenneScale (N+1). Commit dab61d2f proves this condition equivalent to 1/21 membership by identifying it exactly with a cofinal supply of actual skips. The older commit 7286acea remains a valid equivalent endpoint using an unspecified bounded cofinal subsequence, but the moving separatrix is the sharp native target and asks for neither a global bound nor a return frequency. No cofinal lower-branch crossing is yet proved.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_cofinal_normalized_small_returns

Prove that the normalized defect has cofinally arbitrarily small returns: for every delta>0 and every cutoff K, some N>=K satisfies Q_N+1<2^N delta. Commit 586d2506 proves this condition equivalent to 1/21 membership. It is strictly weaker as a producer than eventual subexponentiality because it asks only for one sufficiently small normalized return beyond each cutoff, while the fatal geometric lower bound rules out even that under non-membership. No cofinal normalized-small-return estimate is yet proved.

Evidence/status: see the source; no formal status inferred


### prove_twenty_one_defect_subexponential

Prove that Q_N+1 is subexponential relative to 2^N in the exact quantified sense: for every delta>0 it is eventually below 2^N delta. Commit ebd61913 proves this condition is equivalent to 1/21 membership, not merely sufficient: membership tempers the canonical greedy carry, while any fatal state conserves a positive tail excess and forces Q_(n+k)+1 to dominate 2^(n+k) times that fixed excess. The producer is weaker than a polynomial or uniform defect bound, but no subexponential estimate is yet proved.

Evidence/status: see the source; no formal status inferred


### prove_four_ninths_modulus420_tetraprime_repair

Prove that the 2-3-5-7 selected-divisor union at every positive multiple of 420 clears the preceding four-ninths defect. Lean defines the subtraction-free four-parent union, proves its inclusion in the full load, evaluates the base load at 420 as twelve, proves the zero predecessor floor bit, and connects the all-depth hypothesis to the infinite rational counterexample endpoint. The exact fifty-million replay has zero causal violations, zero equalities, and minimum causal margin +2 among 119047 rows; the actual repair inequality has zero violations and minimum margin +4 on the same class. The all-depth causal inequality remains open despite this positive finite slack.

Evidence/status: see the source; no formal status inferred


### prove_four_ninths_diagonal_nonnegative

Prove that every actual selected landing restores 2s<=3rho, or prove the stronger rho_(d+1)>=d+1. Lean already propagates either producer to global nonnegativity, unrolls rho_d as the exact base-four weighted history of earlier pulses, loads, and selected coins, and proves that failure of the stronger producer is exactly one selected endpoint inside an explicit rank-wide bad history window. Skipped rows require no further input. The exact depth-twelve countermodel shows why detached local state data are insufficient. The exact residue audit separately falsifies the least-length recent-history certificate at rank 20 and observes an adaptive excess of 14 base-four digits by rank 146803. The open analytic input is therefore to exclude the bad window using genuinely nonlocal or adaptively long arithmetic control of the actual history. All finite audits remain evidence only.

Evidence/status: see the source; no formal status inferred


### formalise_fair_pushforward

Construct the infinite fair-bit trajectory measure and prove its pushforward is normalized Lebesgue restriction on the Mersenne achievement set.

Evidence/status: see the source; no formal status inferred


### prove_half_selected_first_window_charge

This is not a separate producer. For every actual skipped half-greedy rank N, let Q_N be the live integer cell and J_N=sum_(N<m<=2N) f_(A_N)(m)2^(2N-m) be the first old-divisor incidence window. The source-current bridge identifies J_N>2^N(Q_N-1) with the already-landed full-shell frozen-margin sign, while the existing factorization identifies it with future skip capacity minus terminal carry. The exact audit verifies this equivalent inequality and factorization at every skipped N<=10000 with minimum margin 7, but the beyond-2N atom tail alone fails at 30 ranks. The remaining task is to inject genuinely new ordered-divisor or selected-history arithmetic into the canonical full-shell producer. Proving it would give 1/2 membership and an infinite rational counterexample to Erdős #257; no all-scale proof is currently known.

Evidence/status: see the source; no formal status inferred


### exclude_half_complement_budget_overspend

Prove that the half-greedy complement budget C_N=mersenneTail(N)-r_N remains positive at every depth, equivalently that no actual greedy skip overspends the surviving future mass. This is strictly weaker than B_N>0 and HalfGreedySkippedFullShellNonnegative. Lean reduces every mature first fatal row, including both midpoint residual branches, to a row-small middle reset and then to its last upper ancestor/right-run packet below 4^k*2(d+k). The named actual-scale producer SeamActualUpperRightPacketLinearEscape asks for the reverse inequality at every literal upper/right prefix and directly implies row escape and one-half membership. Exact integer audit through row 2500 checks all 1242 mature upper/right prefixes with zero violations, zero equalities, zero scaled-gap identity failures, and minimum slack 366; this remains finite evidence. The next proof should establish this packet law or only the last-ancestor specialization through the previous-middle staircase coordinate.

Evidence/status: see the source; no formal status inferred


### prove_rational_half_no_crossing

Prove the all-depth target-zero quotient-row producer, or prove quotient/real lower-core agreement by excluding the first strict quotient-take/real-skip event. For an upper-to-middle landing s with support size m, the source-current Lean floor-error bounds sharpen the sufficient sign target from R_s>=m to R_s>=min(floor(4m/7)+1,2*floor(sqrt(2s))+4), which is O(sqrt(s)) on large rows. The low-bit identity turns this into a canonical remainder certificate; without controlled width, the full window collapses exactly to the original remainder inequality through finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry and the full-shell seam identity. An exact CRT construction shows that arbitrary finite windows can have zero residue even with forced ranks 2,3, omitted ranks 4,5, coefficient ceiling three, and strict next-late upper-to-middle word geometry, so actual canonical greedy ancestry is indispensable. Exact canonical replay through source row 50000 has 6214 strict events and no failure of the direct-card, amplified, or sharpened sign target. It falsifies the earlier observed +8/+9 additive-width guesses (records reach 14 and 18); the exact remaining width statistic is the binary zero-run immediately above the target scale. These are a proved reduction, an exact local no-go, and bounded computation, not the all-depth ancestry theorem. The late-upper route through LateUpperPreviousMiddleStaircaseEscape remains a stronger alternate. The target-zero compactness consumer would give an infinite support of exact rational value 1/2 and disprove Erdős #257 only after the all-depth sign/ancestry boundary is closed.

Evidence/status: see the source; no formal status inferred


### formalise_arithmetic_stride_dimension

Kernel-check the Ahlfors-regular dimension 1/m theorem for arithmetic-stride supports and the biased entropy-dimension formula.

Evidence/status: see the source; no formal status inferred
