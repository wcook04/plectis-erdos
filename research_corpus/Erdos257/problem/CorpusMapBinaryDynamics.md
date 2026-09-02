# Erdős 257: binary/additive dynamics and information loss

This note records the binary and additive representations currently present in
the formal corpus. It is a map of exact interfaces and lost state, not a new
proof. “Proved” means proved by the cited Lean theorem; “conditional” means
that the cited theorem has an explicit unresolved hypothesis; and “open” means
that the hypothesis is not supplied by the corpus.

The starting identity is the exact channel decomposition
\[
 (2^n-1)^{-1}=2^{-n}+2^{-2n}+2^{-3n}+\cdots.
\]
The first channel gives binary/additive geometry. The higher channels become
divisor coefficients after reindexing, so the same object also carries
multiplicative ancestry. The map below tracks what each projection retains and
what it cannot see.

## 1. The full object and its first projection

The source object is a Boolean support (A\subseteq\mathbb N) and its Mersenne
value. In `GreedyAchievementSet.lean`,
`positiveMersenneSupportValue` and `mersenneAchievementSet` retain the
complete support, while `positiveMersenneSupportSuffix` is the exact
unresolved suffix after a finite prefix. Theorems
`positiveMersenneSupportSuffix_eq_indicator_add` and
`positiveMersenneSupportValue_eq_prefix_add_suffix` give the deterministic
prefix/suffix decomposition. `greedyMersenneRemainder_supportValue` then
identifies the greedy residual with that exact support suffix, and
`greedySupport_supportValue_eq` proves recovery of every positive support bit
from a genuine support value.

Thus the real greedy residual is not merely an approximation to the original
object: on the achievement set it is a lossless coordinate for the future
support. The loss occurs when the residual is projected further to a scalar
bound, a finite word, or a divisor-free integer.

## 1a. The fatal gap is the broken binary seam

Write

\[
 e_n=(2^n-1)^{-1}-2^{-n}.
\]

The ordinary binary tail has the exact seam identity

\[
 2^{-m}=\sum_{n>m}2^{-n},
\]

the two expansions usually written as \(0.1111\ldots=1.0000\ldots\).
Subtracting this identity from the Mersenne tail gives the exact gap identity

\[
 \frac1{2^m-1}-\sum_{n>m}\frac1{2^n-1}
   =e_m-\sum_{n>m}e_n.
\]

In the formalization this is the correction-tail form
`mersenneGap_eq_weightCorrection_sub_correctionTail`, together with
`mersenneCorrectionTail_eq`. Its strict positivity is
`mersenneTail_lt_weight`; its scale and error term are bounded by
`mersenneGap_asymptotic_bound` (leading term \((2/3)4^{-m}\), with an
explicit \(8^{-m}\)-scale remainder). Consequently the open interval in
`GreedyMersenneHoleAt` is the positive Mersenne perturbation of the exact
binary seam, not merely an analogous gap.

The cylinder link is exact. `correctionWindow_dyadic_crossing_unique`
says that the correction window can meet at most one dyadic boundary at the
relevant depth; `IsStraddlePrefix.half_step_forced` and
`isStraddlePrefix_step_trichotomy` classify the resulting step as a take
refinement, a skip refinement, or the fatal-gap branch. Thus the finite hole
normal form (`two_mul_scaledTail_sub_scaledWeight` and
`mem_mersenneAchievementSet_iff_holeFree`) is the dynamical version of the
broken seam.

## 2. Representation map

| Representation | Retained state | Exact deterministic law | Success event | Fatal/blind configuration | Information discarded | Fact that would rule it out |
|---|---|---|---|---|---|---|
| Full greedy residual | (R_n), with complete support recoverable when (x\in\mathcal A) | `greedyMersenneRemainder_succ`; subtract next weight iff it is at most (R_n) | (R_n\le T_n) at every level; `mem_mersenneAchievementSet_of_greedy_survival` reconstructs support | First (R_n>T_n); first failure is a skip | None on a genuine support value; outside (mathcal A), it no longer represents an infinite suffix | Exact all-level survival, or existence of recovered support |
| Hole normal form | Scalar residual and next weight/tail | `two_mul_scaledTail_sub_scaledWeight` leaves one uncovered interval between take and skip images | Avoid every `GreedyMersenneHoleAt x n`; `mem_mersenneAchievementSet_iff_holeFree` | Open hole ((T_{n+1},w_{n+1})) at a skipped rank | Divisor ancestry and future Boolean word compressed into interval location | Prove that the original orbit never enters a hole; not supplied for live rationals |
| Scaled trap | (y_n=2^nR_n) | `scaledGreedyRemainder_succ`: (2y_n-c_{n+1}) on take and (2y_n) on skip, (c_n=2^n/(2^n-1)) | Permanent (y_n<2), equivalently one bounded cofinal return | Barrier crossing forces exponential escape by `scaledGreedyRemainder_tendsto_atTop_of_not_mem` | Exact bits, divisor pulses, and phase history | Cofinal lower-separatrix crossing (`rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally`) or direct trapping |
| Sliver coordinate | `mersenneSliverCoordinateRat` or doubled `sharpMersenneSliverCoordinateRat` | Selected step has factor (4+2/(2^n-1)) and shift (-1); doubled form has (4\rho-2) plus finite correction | Stay outside every next decision sliver | Open binary/Mersenne sliver | Boolean prefix and multiplicative origin | Exclude exact sliver inequalities cofinally; not proved |
| Integer excess/dyadic prefix | Displayed `(p,D)` and `E` (`nextDyadicExcessIntNumerator`) | Constant-denominator skip run: `E_{n+1}=2E_n+L`, with closed form `nextDyadicExcessIntNumerator_add` | `E≤0` is dyadically safe; unsafe iff `0<E` and `2E<p` | Exact finite integer window `0<E, 2E<p` | Detailed prefix and future divisor feedback | Reciprocal-floor exclusion (`firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne`) or skipped-excess bound |
| Two-channel cap | Residual plus `halfDyadicCap` or `halfTwoChannelCap` | Selected branches transport caps strictly; skipped branches are the only arithmetic burden | Every actual skip satisfies cap; then `half_mem_mersenneAchievementSet_of_skipped_twoChannelCap` applies | Skipped residual exceeds cap | Higher channels replaced by lower analytic cap; no divisor pulse | Exact integer inequality in `greedyHalfRemainder_le_twoChannelCap_iff_excess` |
| Three-channel/two-thirds band | Integer relation (2u\le3a), or reciprocal band coordinate | `skipSafe_of_two_mul_le_three_mul`; unsafe singleton lies in width (<1/9) band | Sharp tail-mass inequality; integral reciprocals are safe | Actual-tail fatality forces odd numerator (\ge3) | Higher-channel distribution and pulse replaced by coarse mass | Prove orbit avoids localized band; no cofinal proof exists |
| Cut locator/finite straddle | Finite Boolean word, correction window, target straddle | `correctionWindow_dyadic_crossing_unique`; half macrostep `IsStraddlePrefix.half_step_forced` | Straddle at every depth; `mem_mersenneAchievementSet_of_straddle_all_depths` | Finite fatal gap; exact complement by `existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet` | Infinite continuation replaced by finite word and tail enclosure | Prove no finite fatal half-gap (`half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`) |
| Truncated integer greedy/seam | Truncated weights, integer capacity, Boolean row word | `truncatedMersenneWeight_eq_divisorIndicatorSum`; gap domination; `integerGreedyBits`; `wordDefect_succ` | Remainder stays in allowed terminal strip; branches satisfy `nextRemainder_trichotomy` | Adjacent cut, quarter band, or middle/right exceptional cell | Full analytic tail/future rows replaced by finite word and pulse | Cofinal critical-band or row-scale escape; later consumers make this explicit |
| Fixed-tail rewind | Common coefficient list (cs), carry interval ([1,B]), offset, phase | `rewind_eq_closedForm`; width at most (2^{|cs|}) gives at most two ancestors | Phase fit gives singleton (`rewind_endpoint_eq_iff_phase_fit`) | Phase overflow gives exact adjacent seam pair; width alone never gives singleton | Live coefficient agreement and future feedback | Prove phase fit/common-divisor agreement or control seam |
| Selected suffix cylinder | Common prefix, suffix numeral, terminal carry (k), endpoint (E) | `HasSuffixCylinderAt`; successor appends bit and updates (E'=2E-C) | Preserve prefix and endpoint cover; `SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit` | Feedback can break common coefficient, leaving two sheets/one-hole seam | Individual representatives and pulse outside common prefix | Cofinal selected windows or surviving sheet at every feedback row |
| Pre-feedback windows | Depth-18 base and propagated common depth-13 cylinder | `SelectedSuffixCylinderPreFeedback.Stage.step`; exact stages (18\le N\le27) | Full selected windows through first feedback; depth-27 cover is proved | First genuine feedback row is beyond the common-prefix argument | Later feedback history | Feedback theorem plus cofinal successor producer |
| Terminal-only strip | Finite word, normalized bits, terminal integer carry only | `HalfTerminalOnlyStripWitness`; error at most ((4M+12)/2^M) | Cofinal witnesses imply half-membership by closedness | Blind to every intermediate row; no coherence required | All intermediate carries, endpoint cylinders, support history | Cofinal terminal witnesses; consumer only |
| Scaled-terminal sequence | Terminal word and (|K_M|/2^M\to0) | `dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail` | `HalfTerminalOnlyScaledVanishingSequence` gives convergence and membership | No local fatality visible; unrelated terminal words may pass | All prefix legality | Construct sequence from original orbit |
| Binary coefficient-tail window | Coefficient (f), natural state (u), recurrence, tail envelope | Zero window doubles (u) exactly (`state_eq_pow_mul_of_coeffZeroWindow`); subpower envelope absorbed logarithmically | Supply lower-tail certificate and upper envelope | Zero window is only a hypothesis; transfer theorem produces none | Support coefficients, divisors, rational state | Arithmetic producer supplying both certificates; module says no frontier strengthening |
## 3. Strong equivalences already proved

Several apparently different walls are exact translations of the same boundary event.

1. `mem_mersenneAchievementSet_iff_holeFree` translates all-level greedy survival into avoidance of the moving open holes.
2. For rational targets, `rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally` translates membership into cofinal crossings of the lower separatrix. The (1/21) theorem `one_div_twentyOne_mem_iff_scaledLowerBranchCofinally` is an instance, not a proof of either side.
3. `greedyHalf_mem_nextMersenneDyadicSliver_iff_excess` translates a half-orbit fatal gap into the exact integer window (0<E_n) and (2E_n<p_n).
4. `greedyHalfRemainder_le_twoChannelCap_iff_excess` translates the two-channel cap into one integer inequality. The cap route and sliver route are therefore the same state under different inequalities; the cap does not add divisor information.
5. The cylinder route likewise reduces to exact integer branch inequalities: `nextRemainder_trichotomy`, `QuarterBandEscapeAt`, and the critical-band identities in `HalfUpperResetCriticalBand.lean` describe the same adjacent-cut state rather than independent mechanisms.
6. `half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse`, `half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle`, and `half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip` identify terminal-false, upper/middle, and no-last-skip forms. They prove that the eventual-right seam tail is the complementary fatal configuration.
7. A full selected cylinder implies a terminal-only witness by `SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness`. The latter is strictly weaker: it deliberately forgets endpoint, cylinder, and history. At feedback, the bridge preserves only that one of two sheets survives.

These equivalences explain why repeated attempts reach the same wall. They are not themselves a reduction to a solved statement: each remaining producer asks for a new cofinal fact about the original orbit.

## 4. Testing the supercontractive fixed-point interpretation

The attachment's fixed-point picture is useful, but it needs two qualifications.

### 4.1 Exact part

The channel identity and gap estimates in `GreedyAchievementSet.lean` show that changing a support bit at exponent (N) changes the first binary channel at scale (2^{-N}), while the correction begins at scale (4^{-N}). The cylinder and correction-window theorems make this delayed boundary exact.

The actual forward sliver map is not contracting. The theorem `mersenneSliverCoordinateRat_selected_step` gives
[
 \rho_{n+1}=\left(4+\frac{2}{2^n-1}\right)\rho_n-1,
]
and the doubled coordinate has the corresponding `4ρ-2` law plus its finite correction. The scaled residual has factor `2` on both branches by `scaledGreedyRemainder_succ`. Thus “supercontractive” is valid only for prefix-to-correction dependence in a suitable product/ultrametric description; it is false if read as forward contraction of the greedy orbit.

More precisely, the contracting direction is inverse and prefix-based: after
a common prefix of depth \(N\), the unresolved correction is at \(4^{-N}\)-scale
while the binary cylinder has width \(2^{-N}\). The half-correction equation
is exact: `halfCorrectionValue` and `halfComplementValue`, with
`halfComplementValue_eq_tsum_complement`, feed
`positiveMersenneSupportValue_eq_half_iff_correction_eq_complement`.
`HalfPrefixForcingChain.correction_eq_complement` proves equality when
compatible correction intervals lie in nested cylinders of unbounded depth.
The target-parametric analogue is supplied by the correction/complement
theorem and `TargetPrefixForcingChain` in `BooleanMobiusCarry.lean`.
These are inverse prefix-forcing consumers, not a claim that the forward
residual map contracts.

The rewind formulation makes the seam obstruction explicit: inverse rewinding
can contract a common coefficient block, but
`rewind_singleton_or_isSeamPair` leaves either one ancestor or the adjacent
binary seam pair; `rewind_endpoint_eq_iff_phase_fit` identifies the additional
phase-fit condition needed for the singleton case. Contraction therefore
does not itself choose the boundary side.

### 4.2 Exact discontinuity set

The discontinuity is exact, not metaphorical:

* in scalar coordinates it is `GreedyMersenneHoleAt`;
* in integer prefix coordinates it is (0<E_n) and (2E_n<p_n);
* in fixed-coefficient rewind it is phase overflow, producing a seam pair;
* in cylinder coordinates it is the branch trichotomy and its quarter/critical bands.

The interpretation is too strong if it says that this discontinuity is automatically avoided. The corpus has exact counterexamples to scalar avoidance:

* `safeBracket_and_numeratorMonotone_not_inductive_fixture` starts at (7/(2\cdot17)), takes rank (3), then skips rank (4) with excess (1).
* `lcmSaturated_safeBracket_not_inductive_fixture` retains full initial Mersenne-denominator LCM saturation, safe bracketing, positive cancellation, and numerator increase, yet after rank (8) rank (10) is skipped with excess (1013).
* `rankThree_rawSafe_but_seamNotEscaped` in `HalfCylinderFiniteShadow.lean` shows that raw two-channel safety does not imply seam escape.

Hence compressed-coordinate contraction does not control omitted phase or divisor ancestry. A theorem ruling out alignment must combine binary phase with multiplicative coefficient history; no cited theorem currently supplies that cofinal joint law.

## 5. What the map says about information loss

The projections form a descending chain of state strength:
[
\text{support }A
\to R_n
\to y_n=2^nR_n
\to (p,D,E)
\to \text{cap/band inequality}
\to \text{finite seam word and carry}
\to \text{terminal-only carry}.
]

The first arrow is lossless on genuine support values. The later scalar and
finite projections are generally many-to-one; the full quotient/carry state is
an exception that must be treated separately.

That last sentence needs an important qualification. The full greedy remainder
on a genuine support is lossless, by
`greedyMersenneRemainder_supportValue` and
`greedySupport_supportValue_eq`; it should not be grouped with scalar cap or
excess coordinates. Likewise, the full quotient/divisor-support/carry state
in `BooleanMobiusCarry.lean` retains the Boolean support together with the
Möbius/divisor coefficients and carry recurrence. Under its Boolean/Möbius and
boundary hypotheses it can retain both sides of a seam and recover the target;
its remaining difficulty is proving those hypotheses, not information loss
from the state itself.

The genuinely lossy arrows are the scalar and finite projections below:

* A scalar residual forgets which divisors produced the higher channels.
* An integer excess forgets future pulse history.
* A cap forgets the exact positive higher-channel correction.
* Fixed-coefficient rewind forgets whether common coefficient remains valid at the next feedback row.
* A suffix cylinder forgets individual representatives once prefix and endpoint agree.
* A terminal-only witness forgets all prefix legality.
* A coefficient-tail window forgets the support altogether.

The strongest exact bridges restore only selected pieces. The suffix-cylinder theorem restores divisor agreement before the first feedback row; `HalfUpperResetCriticalBand` restores an exact pulse/critical-gap identity for an actual upper/right run; and `HalfCarryRewindPhase` restores the suffix-numeral/phase relation. None restores the full pair (binary phase, multiplicative ancestry) cofinally.

The missing global datum is consequently not simply “more state”. It is a
cofinal boundary-compatibility condition tying the forward divisor/carry
evolution to the inverse prefix cylinders: at sufficiently late feedback rows,
the actual correction cell must be identified with the actual forcing state,
and the chosen side of every dyadic seam (or the exact harmless seam-pair
alternative) must persist cofinally. `HalfPrefixForcingChain` and
`TargetPrefixForcingChain` consume this kind of datum; `FixedCoeffRewind` shows
why contraction without phase fit does not supply it. The corpus currently has
no theorem establishing that global compatibility for the live rational cases.

The precise common wall is therefore:

> establish a cofinal theorem about the original Boolean support which is stable under the next divisor-feedback pulse and simultaneously excludes the strict binary boundary window.

Every current consumer is proved once such a theorem is supplied. The missing statement is not another equivalent normal form; it is the first cross-representation assertion absent from the current map.

## 6. Boundary of the present corpus

The following are proved consumers, not supplied producers:

* a cofinal lower-separatrix crossing proves rational membership;
* a cofinal no-hole orbit proves rational membership;
* a cofinal terminal-only or scaled-vanishing sequence proves the half target;
* a cofinal selected-cylinder or critical-band construction proves the half target;
* a binary coefficient zero-window certificate transfers to a logarithmic bound under an independent envelope.

The corpus does not prove any of those cofinal hypotheses for (1/2), (1/21), (1/9), or (1/20). Nor does the fixed-point interpretation decide whether a rational target eventually enters a discontinuity window. The exact open object is the joint binary–divisor transition law at feedback, not the validity of any individual representation.
## 7. Source index for the map

The principal binary/additive authorities consulted are:

* `Erdos257PeriodNoncollapse/GreedyAchievementSet.lean`: weights, tails, cylinders, greedy residual, support recovery, sliver coordinates, caps, and survival.
* `Erdos257PeriodNoncollapse/GreedyHoleNormalForm.lean`: the exact hole definition and hole-free normal form.
* `Erdos257PeriodNoncollapse/GreedyTrapDynamics.lean`: scaled nearly-doubling law, lower separatrix, exponential escape, and trapping criteria.
* `Erdos257PeriodNoncollapse/HalfGapMass.lean`, `HalfGreedyFatalGap.lean`, `HalfGreedyTwoThirdsBand.lean`, and `HalfGreedyDyadicSafe.lean`: gap mass, sharp three-channel safety, two-thirds localization, and dyadic-safe consequences.
* `Erdos257PeriodNoncollapse/HalfCutLocator.lean`: finite correction windows, straddles, deterministic half steps, and the exact fatal-gap dichotomy.
* `Erdos257PeriodNoncollapse/HalfCylinderIntegerGreedy.lean`: truncated divisor weights, gap-dominating integer greedy, row pulses, affine defect, and branch trichotomy.
* `Erdos257PeriodNoncollapse/HalfCylinderFiniteShadow.lean`: finite-shadow factorization, future-skip capacity, feedback, and the rank-three raw-safe/seam-not-escaped fixture.
* `Erdos257PeriodNoncollapse/HalfCylinderFatalGapRightTail.lean` and `HalfCylinderHalfMembershipClassification.lean`: eventual-right classification and its equivalent upper/middle, terminal-false, and no-last-skip forms.
* `Erdos257PeriodNoncollapse/HalfCylinderFalseBitSupply.lean`, `HalfCylinderFinalMiddleCellEscape.lean`, `HalfCylinderFinalMiddleTailSocket.lean`, `HalfCylinderFixedTailSocket.lean`, `HalfCylinderProducerCarrySocket.lean`, `HalfCylinderResetDeficitEscape.lean`, `HalfCylinderSeamProducerAlignment.lean`, `HalfCylinderSkippedEndpointClassifier.lean`, `HalfCylinderSkippedRankLimit.lean`, and `HalfCylinderQuarterBandEndpoints.lean`: the terminal-false, middle/right, reset, endpoint, and rank-limit consumers and their remaining producer hypotheses.
* `Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean`: exact pulse/critical-gap identities and the conditional critical-band consumer.
* `Erdos257PeriodNoncollapse/HalfCarryCeilParentContraction.lean` and `HalfCarryRewindPhase.lean`: exact rewind, phase fit, seam pair, and suffix-phase identities.
* `Erdos257PeriodNoncollapse/SelectedSuffixCylinder.lean` and `SelectedSuffixCylinderPreFeedback.lean`: suffix-cylinder endpoint invariant and the depth-18 through depth-27 pre-feedback construction.
* `Erdos257PeriodNoncollapse/SuffixCylinderTerminalOnlyBridge.lean`, `TerminalOnlyCofinal.lean`, and `TerminalOnlyScaledVanishing.lean`: the explicit information-losing projection from cylinders to terminal-only convergence.
* `Erdos257PeriodNoncollapse/DyadicPrefixCompression.lean`: exact integer excess, block compression, reciprocal-floor obstruction, and falsifying fixtures.
* `Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean`: the full quotient/divisor-support carry state, target-parametric correction/complement equation, and `TargetPrefixForcingChain`.
* `Erdos257PeriodNoncollapse/BinaryTailWindowTransfer.lean`: support-free zero-window transfer and logarithmic absorption. Its module header explicitly records that it is an interface refactor and does not strengthen the theorem frontier.

The draft does not treat finite certificates or conditional producers as proofs of
the unresolved cofinal hypotheses.
