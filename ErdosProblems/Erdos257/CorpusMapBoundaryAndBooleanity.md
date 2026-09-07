# Erdős 257: boundary conditions and Boolean ancestry

Status: source audit. This note records theorem-level interfaces and the exact
information lost at their present endpoints. It introduces no new invariant and
does not claim a solution of Erdős 257.

## Claim discipline

“Lean-checked” below means that the exact source builds from its declared
imports and the cited declaration's axiom audit does not contain `sorryAx`.
Occurrence of a theorem-shaped declaration in a worktree file is not proof
authority. “Deduction” means an elementary consequence of named Lean-checked
statements but is not itself cited as a packaged theorem. “Interpretation”
identifies useful language from the supplied fixed-point analysis that is not
yet a formal object in the corpus.

The audit concerns the source object

\[
  A\subseteq\mathbb N,\qquad
  b_n=\mathbf 1_A(n),\qquad
  c_m=\sum_{d\mid m}b_d,
\]

and the exact identity

\[
  \sum_{n\in A}\frac1{2^n-1}=\sum_{m\ge1}c_m2^{-m}.
\]

The full object has two logically different kinds of data:

1. a boundary condition at infinity, such as a tempered carry, a vanishing
   normalized terminal state, or a cofinal closed return; and
2. Boolean/multiplicative ancestry: the assertion that the forcing is the
   divisor convolution of one Boolean support, with the same support governing
   every row.

The principal conclusion of this audit is qualified. Those two data are indeed
the common missing pair in the **live global reconstruction routes**. They are
not a universal explanation of every obstruction in the corpus. In particular,
`AdelicHeightObstruction` is a finite scalar-localisation obstruction with no
boundary at infinity, and the eventual fatal `1/21` quotient orbit is a smooth
homogeneous escape after its Boolean branching has ended. These are substantive
limits on the proposed common picture.

## Comparative map

| Formulation | State retained | Exact law | Success event | Fatal or blind configuration | Information discarded | Exact original-object fact still needed |
|---|---|---|---|---|---|---|
| Generic tail orbit | Coefficients `c`, scalar multiplier `v`, integer orbit `u` | `u (N+1)=2u N-v*c (N+1)` together with `u N/2^N -> 0` | Existence of the tempered orbit is equivalent to rationality of the binary coefficient series | Arbitrarily large fresh fan-out can follow the same finite prehistory; an untempered homogeneous `2^N` mode survives every local recurrence | The condition `c=1*b` with Boolean `b`, unless imposed separately; a finite prehistory also loses the terminal boundary | Prove simultaneously that the forcing has Boolean Möbius ancestry and that the canonical orbit is tempered |
| Cofinal strip return | The actual half greedy carry and its normalized scalar value | The normalized uncentred carry is antitone | Cofinal returns below the square-root strip force the whole normalized carry to zero and give an infinite support of value `1/2` | No cofinal return; the scalar state may stay above every subexponential strip | All divisor labels and almost all finite-word history | Produce arbitrarily late strip returns from the actual greedy support |
| Scalar localisation / adelic height | A rational `x`, a scalar `c`, and one surviving denominator channel `H` | The complementary reduced denominator `x.den/H` divides `|c|`; after clearing `H`, the result is a multiple of the original numerator | A separately supplied small real tail and large numerator divisor yield a height contradiction | The omitted denominator is paid by the scalar; every rational-linear descender through scalar equality is rank one | Independent denominator coordinates | A support-aware, non-scalar relation retaining independent denominator ancestry; no boundary-at-infinity hypothesis is involved |
| Half upper-reset critical band | Reset row, dyadic critical index, exact gap, actual subsequent right-run pulse, and aggregate charge | `remainder + charge = 4^k * criticalGap`; no-stall is equivalent to pulse charge plus row cost fitting that gap | `SeamUpperResetCriticalBandEscape` implies half-membership | The nearest dyadic gap is too small for the actual accumulated support pulse | At the final predicate, the divisor history has been compressed to one charge | Prove the critical-gap inequality at every actual sufficiently late upper reset from the same greedy support |
| `1/21` quotient compactness | A finite support at depth `M`, exact quotient target/defect, and its real prefix value | Exact quotient error identity and an explicit error bound | Any unbounded sequence of rows with normalized defect tending to zero gives `1/21` by closedness | No such cofinal small rows | Which divisors produced the quotient defect; cross-depth support coherence is intentionally absent | Produce arbitrarily deep Boolean quotient rows with `(defect + card + 1)/2^M -> 0`; coherence is not required |
| `1/21` quotient greedy | Canonical support `D_R`, scalar remainder `s_R`, periodic target pulse, and support pulse | On the only fatal branch, eventually `s_R>2^R`, the next support bit is always selected, and one affine recurrence remains | Any cofinal closed/subexponential return, or the preterminal next-coin bound, gives `1/21` | A positive homogeneous base-`4` escape persists after all residual Boolean choices cease | The recurrence forcing does not determine the homogeneous boundary amplitude | Derive a cofinal return or show that the actual initial/fatal gap makes the homogeneous amplitude zero; local pulse laws alone cannot do this |
| One-step quotient borrow | Exact quotient row, doubled suffix reservoir, target bit, next divisor contribution | Exact cocycle: next prefix quotient plus reservoir/bit equals next target plus divisor contribution | Cofinal failed borrows give real prefixes converging to `1/21` | Under nonmembership every sufficiently deep exact retained-prefix row borrows successfully | Quotient exactness does not imply the real prefix is below the target | Produce cofinal failures, or relate perpetual successful borrowing to a forbidden original greedy gap |
| Affine endpoint-pulse cocycle | Base-`4` state, endpoint divisor forcing, correction sequence, rational anchor | Division by `4^(R+1)` is an exact coboundary; temperedness pins the weighted forcing to the negative anchor | A rationally anchored tempered branch forces its weighted correction to be irrational | The fatal branch has a positive normalized boundary charge (deduction in §7), so the tempered hypothesis fails | Local/eventually periodic forcing does not determine the boundary charge | Prove temperedness or an equivalent vanishing boundary statement for the actual branch |
| Endpoint divisor signal | The full-window endpoint divisor count | The endpoint pulse equals `2*tau(2R+1)+tau(2R+2)-7` | Factorial rays give arbitrarily long simultaneous divisibility windows | A large pulse can arrive when the binary state is already far into supercapacity | Divisor identities, earlier support roles, and the radix cell into which the pulse lands | Synchronize a divisor-rich row with a small actual suffix/carry state, or bound that state from the same support |
| Moving hole / fatal gap | Scalar greedy remainder, next weight, and remaining tail | Hole avoidance at every level is exactly achievement-set membership | No hole at any level | Entry into the open interval between the take and skip images | Divisor ancestry and all future word data | Prove that the original rational orbit never enters a hole; the equivalence itself supplies no mechanism |
| Suffix cylinder / seam / recut | Common prefix, suffix numeral, endpoint carry, and sometimes a two-sheet profiled gap | Endpoint transport is affine; crossing sheets are recylindrified, while an in-strip one-hole seam is exposed exactly | Cofinal cylinders, or merely cofinal terminal-only witnesses, give membership | A protected one-hole seam can remain inside the next strip | Passing to a terminal witness forgets cylinder history; promotion forgets no gap but does not force its eventual exit | Produce cofinally many terminal witnesses or show every actual protected seam eventually exits; compatible histories are stronger than necessary |
| Preterminal quotient bound | The canonical quotient greedy state just before its terminal coin | Every preterminal remainder is required to lie below the next quotient coin | The bound implies cofinal normalized decay and hence `1/21` | A preterminal state larger than the next coin | The statement is scalar and does not explain the divisor pulse creating the state | Prove the next-coin inequality for every canonical preterminal row from its Boolean/divisor ancestry |

## 1. Generic tail-orbit rigidity: the two missing data are explicit

`IsTemperedBinaryOrbit` stores both the affine recurrence and the terminal
condition

\[
  u_{N+1}=2u_N-vc_{N+1},\qquad u_N/2^N\longrightarrow0
\]

([GenericTailOrbitRigidity.lean:67](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean)).
The equivalence
`binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`
([line 426](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean))
and the identity `temperedBinaryOrbit_eq_scaledTail`
([line 339](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean))
show that the boundary condition is part of the exact rationality
certificate, not an optional estimate.

The same file proves two independent no-go statements.
`balancedPulse_no_autonomous_decoder`
([line 247](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean))
allows unbounded fresh successor fan-out after a fixed finite prehistory.
`affineBinaryOrbit_sub` and `doublingOrbit_eq_zero_of_tempered`
([lines 289 and 315](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean))
identify the other ambiguity: two locally valid orbits differ by a homogeneous
doubling mode, and only temperedness kills it.

There is also a direct ancestry counterexample. `globalBalancedCoeff_value`
and `globalBalancedOrbit_even_payload`
([lines 545 and 557](../../Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean))
embed an arbitrary bounded Boolean payload in generic coefficients while
preserving the same rational value. Thus local affine evolution plus rational
value cannot reconstruct the multiplicative source. This module gives the
cleanest formal support for the qualified common diagnosis: a global argument
needs both admissible forcing and a terminal condition.

## 2. Boundary consumers do not require coherent finite histories

The corpus repeatedly proves that cross-depth coherence is unnecessary at the
last analytic step.

### Half carry

`scaled_integerHalfCarry_antitone`
([CofinalStripReturn.lean:23](../../Erdos257PeriodNoncollapse/CofinalStripReturn.lean))
shows that the normalized uncentred half carry is antitone for every support.
`GreedyHalfCarryCofinalStripReturn` asks only for arbitrarily late visits to a
subexponential strip ([line 76](../../Erdos257PeriodNoncollapse/CofinalStripReturn.lean)).
Theorems
`greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn`,
`greedy_half_infinite_of_cofinalStripReturn`, and
`half_mem_mersenneAchievementSet_of_cofinalStripReturn`
([lines 84, 130, and 157](../../Erdos257PeriodNoncollapse/CofinalStripReturn.lean))
then force the complete boundary limit and membership.

### Terminal-only half words

`HalfTerminalOnlyScaledVanishingSequence` permits unrelated finite words whose
depths tend to infinity and whose normalized terminal carries tend to zero
([TerminalOnlyScaledVanishing.lean:117](../../Erdos257PeriodNoncollapse/TerminalOnlyScaledVanishing.lean)).
`half_mem_mersenneAchievementSet_of_terminalScaledVanishing`
([line 165](../../Erdos257PeriodNoncollapse/TerminalOnlyScaledVanishing.lean))
uses only those terminal data.

### Quotient rows and borrows

`TwentyOneEvenQuotientWindowSupply` explicitly permits a new finite support at
each even depth
([TwentyOneQuotientCompactness.lean:130](../../Erdos257PeriodNoncollapse/TwentyOneQuotientCompactness.lean)).
The exact error identity and bound are
`scaled_localMersennePrefixValue_sub_one_div_twenty_one` and
`abs_localMersennePrefixValue_sub_one_div_twenty_one_le`
([lines 65 and 88](../../Erdos257PeriodNoncollapse/TwentyOneQuotientCompactness.lean));
`one_div_twenty_one_mem_mersenneAchievementSet_of_evenQuotientWindow`
([line 186](../../Erdos257PeriodNoncollapse/TwentyOneQuotientCompactness.lean))
then applies closedness.

The worktree borrow module proposes an even more explicit interface:
`TwentyOneCofinalFailedBorrows` permits unrelated finite supports, its intended
consumer would make cofinal failures imply membership, and an intended
contrapositive would make nonmembership force eventual successful borrowing.
These statements are not Lean-checked.  The focused build of
`TwentyOneOneStepPropagation.lean` on 2026-08-22 exits `1` with multiple proof
errors, and the printed declarations contain `sorryAx`.  They may guide a
future repair but cannot support a theorem-level conclusion here.

Therefore coherence is not the common missing datum. Some finite producers need
coherence to propagate their chosen state, but the endpoint theorems do not.
Replacing a cofinal existence problem by a compatible-chain problem makes the
hypothesis stronger without addressing the proved obstruction.

## 3. The fixed-point and “supercontraction” picture

### Exact part

The corpus defines

\[
 E(A)=\operatorname{MersenneValue}(A)-\operatorname{DyadicValue}(A),
 \qquad C_x(A)=x-\operatorname{DyadicValue}(A),
\]

as `supportDyadicCorrectionValue` and `targetDyadicComplementValue`
([BooleanMobiusCarry.lean:3059-3067](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).
The theorem
`positiveMersenneSupportValue_eq_target_iff_correction_eq_complement`
([lines 3069-3076](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean))
is the exact equivalence

\[
  \operatorname{MersenneValue}(A)=x
  \quad\Longleftrightarrow\quad
  E(A)=x-\operatorname{DyadicValue}(A).
\]

The correction suffix is nonnegative and at most the complete correction tail
by `supportDyadicCorrectionSuffix_nonneg` and
`supportDyadicCorrectionSuffix_le_tail`
([lines 3636-3650](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).
The correction itself splits into prefix and suffix in
`supportDyadicCorrectionValue_eq_prefix_add_suffix`
([line 3682](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).
Finally,
`mersenneCorrectionTail_lt_doubleDepth` and
`doubleDepth_succ_lt_mersenneCorrectionTail`
([HalfCutLocator.lean:55 and 80](../../Erdos257PeriodNoncollapse/HalfCutLocator.lean))
give the sharp scale

\[
  2^{-(2m+2)}<\eta_m<2^{-(2m+1)}\qquad(m>0
  \text{ for the upper inequality}).
\]

**Deduction.** If two supports agree through depth `m`, their correction values
differ by less than `2^(-(2m+1))`. This is a rigorous ultrametric modulus for
the correction coordinate: `m` fixed support digits determine roughly `2m`
binary places of the correction, away from a dyadic boundary.

`TargetCorrectionImageForcingChain.correctionImage_eq_dyadic` and
`target_mem_mersenneAchievementSet_of_correctionImageForcingChain`
([BooleanMobiusCarry.lean:3834 and 3872](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean))
make the cylinder consequence exact. The cofinal forms
`one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalTrapping` and
`one_div_twenty_one_mem_mersenneAchievementSet_of_trappingCofinally`
([lines 4084 and 4120](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean))
also prove that the trapping cells need not be compatible. A single still-open
local assertion, `TwentyOneCorrectionImageAmplifiesOnDoublingBlockHit`, would
imply membership by
`one_div_twenty_one_mem_mersenneAchievementSet_of_amplifiesOnHit`
([lines 4131-4154](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).

### What remains interpretation rather than a formal equivalence

The corpus does not define a canonical total function

\[
  A\longmapsto \operatorname{BinaryDigits}(x-E(A))
\]

on support sequences, choose a convention at dyadic rationals, or prove that
this digit-valued map is a contraction. The exact scalar fixed-point relation
and its correction-tail modulus are proved; the global discontinuous
supercontractive self-map is an interpretation of those statements. It becomes
an exact local cylinder statement only after one supplies a cell that avoids or
controls the dyadic boundary.

There is a second necessary qualification. The exact forward laws
`mersenneSliverCoordinateRat_selected_step` and
`scaledGreedyRemainder_succ`
([GreedyAchievementSet.lean:1080](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean)
and [GreedyTrapDynamics.lean:72](../../Erdos257PeriodNoncollapse/GreedyTrapDynamics.lean))
are expanding, not contracting. More decisively, the fatal `1/21` theorem below
shows that after a finite time there need be no digit-choice discontinuity at
all. Therefore “the only instability is the discontinuity hierarchy” is false
as a description of the full forward orbit.

## 4. The exact `1/21` fatal branch and the surviving boundary charge

`TwentyOneFatalAlignedBranch` stores an actual fatal greedy witness, finite
skipped support, cofinite subsequent selection, eventual quotient/rational
alignment, and eventual hits in every doubling block
([TwentyOneQuotientGreedy.lean:3379](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
It is exactly nonmembership by
`twentyOneFatalAlignedBranch_iff_not_mem`
([line 3494](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).

The one-third suffix-density phenomenon has already been composed with
ancestry in one genuine junction.
`twentyOneFatalAlignedBranch_eventually_saturated_socket`
([line 3397](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
uses quotient/rational alignment and cofinite selection to fill both ancestor
digits forced by a bad saturated transition, contradicting the one-third-scale
hole theorem. Thus that local Boolean branch is closed; repeating the same
density statement cannot address the remaining regime.

The remaining regime is described exactly by two later theorems:

* `twentyOneFatalAlignedBranch_eventually_strict_supercapacity`
  ([line 5625](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
  proves `2^R < s_R` at every sufficiently late row.
* `twentyOneFatalAlignedBranch_eventually_affine_supercapacity`
  ([line 5658](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
  proves that the next support bit is then always appended and

  \[
    s_{R+1}=4s_R+t_R-p_R-(2^{R+1}+1),
  \]

  with no residual Boolean branch.

**Deduction.** Combine eventual full alignment in
`TwentyOneFatalAlignedBranch`, the exact scaled quotient-error identity
`scaled_localMersennePrefixValue_sub_one_div_twenty_one`, and the positive
fatal interval in `twentyOne_not_mem_forces_erdosBorwein_fatalInterval`
([TwentyOneQuotientGreedy.lean:4451](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
The fractional-mass and support-cardinality errors are `O(R/4^R)`, while the
aligned finite prefixes converge to the cofinite actual greedy support. Hence
`s_R/4^R` tends to the strictly positive final greedy gap. This normalized
limit is not packaged as a theorem in the inspected files; it is the precise
sense in which the eventual affine branch has a positive homogeneous boundary
amplitude. The strict-supercapacity theorem alone proves only `s_R>2^R` and
would not by itself imply failure of base-`4` temperedness.

This theorem is the clearest falsifier of the **strong** discontinuity picture.
Fatality does not require recurrent alignment with binary digit boundaries. It
can become an open, deterministic, homogeneous escape after the boundaries have
ceased to affect the choice. In boundary/ancestry language, the local ancestry
is already as rigid as the corpus currently makes it, but the untempered
homogeneous amplitude remains free.

The actual endpoint hypotheses are correspondingly global.
`TwentyOneCofinalEvenQuotientGreedyDecay` and
`one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay`
([lines 5425 and 5458](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
require only normalized decay along one unbounded sequence.
`one_div_twenty_one_mem_mersenneAchievementSet_of_preterminalNextCoin`
([line 5739](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
uses the still-unproved canonical preterminal next-coin bound. Neither theorem
asks for compatible finite supports.

## 5. Moving holes and borrow failure have different logical roles

`GreedyMersenneHoleAt` is the exact open interval between the take and skip
images ([GreedyHoleNormalForm.lean:25](../../Erdos257PeriodNoncollapse/GreedyHoleNormalForm.lean)).
`mem_mersenneAchievementSet_iff_holeFree`
([line 58](../../Erdos257PeriodNoncollapse/GreedyHoleNormalForm.lean))
proves that avoiding every such hole is equivalent to membership. This is an
exact reformulation of all-level greedy survival, but it retains only the scalar
remainder and supplies no divisor mechanism that forces avoidance.

The proposed borrow-failure interface has the opposite intended logical role,
but it is not yet proof authority.

In the worktree source, the attempted statement
`twentyOne_qRow_cocycle`
([TwentyOneOneStepPropagation.lean:65](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean))
has the intended form

\[
 Q_{M+1}(D)+(2s+\text{targetBit}_M)
 =T_{M+1}+\text{endpointContribution}_M(D).
\]

The same file attempts to derive real-prefix borrow safety in
`twentyOne_borrowContribution_le_reservoir_add_bit_of_prefix_le`
([line 80](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean)).
It also attempts the one-way overshoot bound
`twentyOne_failedBorrow_prefix_interval`
([line 108](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean))
whose target conclusion places the real prefix just above `1/21` in a shrinking
interval.  Until the module builds without `sorryAx`, neither the bound nor its
cofinal membership consumer may be used.  If repaired, the intended polarity
would differ from the fatal gap: failed borrow would be an approximation event
for closedness, while perpetual successful borrowing would be the surviving
escape branch.  At present this is programme-level interpretation, not a
checked separation theorem.

## 6. Critical bands and suffix cylinders: exact local coupling, global producer absent

The half critical-band module already retains both sides of the proposed
coupling. `CriticalDyadicBandIndex` and `DyadicBandEscape`
([HalfUpperResetCriticalBand.lean:33-42](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
locate the dyadic boundary. The equivalences
`dyadicBandEscape_iff_exists_critical` and
`seamUpperResetBand_iff_exists_critical`
([lines 108 and 141](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
collapse quantifiers but do not supply an escape.
`seamAdjacentCut_belowPulse_eq_pairedSupportCoeff`
([line 175](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
identifies the local pulse with the paired support coefficient. The main exact
coupling is
`seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap`
([line 253](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean)),
and
`seamUpperThenRightRun_row_le_remainder_iff_exactCriticalGap`
([line 610](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
turns no-stall into the corresponding pulse-charge/gap inequality.
`SeamUpperResetCriticalBandEscape`
([line 958](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
is therefore an exact conditional endpoint, not a proved cofinal producer;
`half_mem_mersenneAchievementSet_of_upperResetCriticalBandEscape`
([line 981](../../Erdos257PeriodNoncollapse/HalfUpperResetCriticalBand.lean))
is its membership consumer.

The suffix-cylinder corpus reaches the same boundary locally. At an exact
feedback horizon,
`CylinderStage.feedbackAdvance_or_protectedSeam_inStrip`
([SuffixCylinderFeedbackFanIn.lean:62](../../Erdos257PeriodNoncollapse/SuffixCylinderFeedbackFanIn.lean))
proves that low, high, below-hole, and above-hole cases all advance; the only
non-advancing output is a realized protected seam whose integer hole lies in
the next strip. `ProfiledGapStage.promoteCutoff`
([SuffixCylinderProfiledPromotion.lean:168](../../Erdos257PeriodNoncollapse/SuffixCylinderProfiledPromotion.lean))
recuts both live sheets at the odd feedback boundary while leaving the gap and
selected families unchanged.

This makes “cylinder recut” a change of coordinates, not a new obstruction.
The terminal projection is deliberately weaker: a cylinder stage gives a
terminal-only strip witness by
`CylinderStage.halfTerminalOnlyStripWitness`
([SuffixCylinderTerminalOnlyBridge.lean:63](../../Erdos257PeriodNoncollapse/SuffixCylinderTerminalOnlyBridge.lean)).
Even a realized localized seam supplies such a witness, and an adjacent
singleton profiled gap cannot kill the next one, by
`halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt` and
`ProfiledGapStage.halfTerminalOnlyStripWitness_after_singletonGap`
([lines 74 and 217](../../Erdos257PeriodNoncollapse/SuffixCylinderTerminalOnlyBridge.lean)).
Cofinal cylinder stages suffice for an infinite half support by
`exists_infinite_support_half_of_cofinalCylinderStages`
([line 302](../../Erdos257PeriodNoncollapse/SuffixCylinderTerminalOnlyBridge.lean)).
Consequently, perpetual compatibility of the recut cylinders is not the exact
original-object fact needed. The exact missing fact is cofinal production of
small terminal states, or an eventual exit theorem for every actual protected
in-strip seam.

## 7. Endpoint divisor signal and affine cocycle

The endpoint pulse is not merely a numerical correlation. Theorems
`card_divisors_Icc_odd`, `card_divisors_Icc_even`, and
`endpointPulse_eq_divisorSignal`
([EndpointDivisorSignal.lean:51, 94, and 144](EndpointDivisorSignal.lean))
prove its exact divisor formula. The factorial-ray theorem
`endpointDivisorSignal_unbounded_on_factorial_ray`
([line 158](EndpointDivisorSignal.lean)) proves simultaneous divisibility on
arbitrarily long windows. Its literal conclusion is the divisibility window;
growth of the displayed signal is a deduction using the preceding formulas,
not the stated theorem conclusion.

The signal's global weighted class is also exact.
`endpointPulseTerm_eq` and
`tsum_endpointPulseTerm_eq_erdosBorwein`
([AffineCocycleObstruction.lean:145 and 186](AffineCocycleObstruction.lean))
identify its base-`4` sum with the Erdős--Borwein constant, and
`irrational_tsum_endpointPulseTerm`
([line 211](AffineCocycleObstruction.lean)) proves irrationality.
For any affine recurrence, `affine_cocycle_telescope` and
`affine_cocycle_tsum_eq_neg_anchor`
([lines 84 and 97](AffineCocycleObstruction.lean)) show that temperedness pins
the weighted forcing to the anchor.
`irrational_tsum_correction_of_tempered_branch`
([line 223](AffineCocycleObstruction.lean)) consequently forces the correction
sum to be irrational on a tempered rationally anchored branch.

**Deduction.** On `TwentyOneFatalAlignedBranch`, the skipped support is finite,
so a correction built from those skipped divisors is eventually periodic in
the row index and has a rational base-`4` weighted sum. The affine obstruction
does not close the branch because the normalized quotient state tends to the
positive fatal gap, as deduced in §4; the actual orbit therefore violates its
tempered hypothesis. The irrational charge has moved into the homogeneous
boundary amplitude.

Thus an LCM or factorial pulse theorem without a simultaneous state bound
cannot close the route. The exact missing original-object statement must put a
divisor-rich pulse and a small carry/suffix state at the same row, or else prove
that the actual homogeneous amplitude vanishes.

## 8. Scalar localisation limits the scope of the common diagnosis

`scalarLocalization_complement_dvd`
([AdelicHeightObstruction.lean:23](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean))
proves that if `H | x.den` and the denominator of `c*x` divides `H`, then
`x.den/H | |c|`. `scalarLocalization_integer_eq_mul_num`
([line 56](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean))
states the same conservation as an equality: clearing the retained channel
makes the result an integer multiple of the original reduced numerator.
`positiveRat_mersenne_height`
([line 103](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean))
is the finite Archimedean/2-adic inequality, and
`linearDescender_eq_smul_eval`
([line 120](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean))
shows that any rational-linear channel killing scalar relations factors through
the one-dimensional evaluation map.

This module falsifies an overbroad version of the common picture. Its obstruction
is finite and algebraic: scalar equality cannot retain independent denominator
coordinates. There is no omitted terminal limit. The boundary/ancestry pair is
therefore the right audit for global orbit reconstructions, not a theorem that
classifies every failed approach in the corpus.

## 9. Verdict on the proposed common wall

### Supported, in a precise restricted form

For the global carry, quotient, correction-image, and suffix-cylinder routes,
every proved endpoint needs a vanishing/cofinal boundary fact. Every generic
local recurrence that forgets Boolean/divisor ancestry admits formal
counterexamples. Conversely, divisor/LCM pulses and Boolean quotient laws do
not determine the homogeneous boundary amplitude. In that restricted class,
the wall is accurately stated as:

> the corpus does not yet control a terminal boundary condition and the
> Boolean/multiplicative ancestry of its forcing in the same cofinal state.

This is an information-loss diagnosis, not a reduction or a new lemma.

### Coherence is a red herring at the endpoint

The terminal-only, quotient-compactness, cofinal-borrow, and correction-trapping
consumers all accept unrelated finite stages. Coherence may be needed to build a
particular sequence of stages, but no existing endpoint theorem makes it the
universal missing condition.

### The discontinuous supercontraction is only partly an exact reformulation

The scalar correction fixed-point equation and the approximately doubled prefix
modulus are exact theorem-level consequences. Cylinder trapping packages their
local consequence. A canonical global `BinaryDigits` self-map, including dyadic
ambiguity and a contraction theorem, is absent. Moreover, eventual affine
supercapacity is a formal counterexample to the claim that all fatal behavior
is continued contact with discontinuity surfaces.

### Exact original-object statements that would change the frontier

No new invariant is proposed here. The smallest already-consumed facts are:

1. cofinal square-root-strip returns for the actual half greedy carry;
2. the actual upper-reset pulse-charge inequality at every sufficiently late
   half critical band;
3. cofinal normalized decay, or the canonical preterminal next-coin bound, for
   the `1/21` quotient greedy orbit;
4. correction-image amplification on every sufficiently late hit doubling
   block for `1/21`;
5. a simultaneous theorem locating a divisor-rich endpoint pulse in a small
   actual carry/suffix state; or
6. direct elimination of the positive homogeneous amplitude in the eventual
   affine fatal branch.

Each item is stated in the coordinates consumed by an existing theorem. None is
supplied by the current corpus, and replacing any of them by a compatible-chain
or equivalent normal-form statement would not advance the theorem frontier.
