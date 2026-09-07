# Arithmetic dynamics and information loss in the Erdős #257 corpus

This note records the arithmetic half of the corpus-wide information-loss map. It does not propose an invariant or a proof route. Every named result below is a current Lean theorem (including the finite `{2,6}` fixture, which is formally proved by `norm_num` and `decide`, not empirical computation). No numerical experiment is used as evidence here. A statement marked **open** or **conjectural** is not promoted by this note.

## The common arithmetic object

For a support `A ⊆ ℕ`, write

```
f_A(m) = #{d ∈ A : d ∣ m}.
```

The development proves that `f_A` is the support indicator convolved with `ζ`, and that Möbius inversion recovers the Boolean indicator: `positiveSupportBitAF_mul_zeta` and `moebius_mul_supportCoeffAF` in [BooleanMobiusCarry.lean:75-128](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean). It also proves

```
sum_{d in A} 1/(2^d-1) = sum_{m>=1} f_A(m)/2^m
```

as `erdosSupportSeries_two_eq_binaryCoeffSeries` ([BooleanMobiusCarry.lean:375-390](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)). Thus the divisor convolution in the supplied attachment is an exact theorem-level coordinate change.

The next change of coordinates is a tempered integer carry orbit: `erdosSupportSeries_rational_iff_exists_temperedCarry` ([BooleanMobiusCarry.lean:382-389](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)). The inspected source does not prove that the canonical eventually periodic binary digit expansion of a rational value is a symbolic factor of the Boolean support. The attachment's phrase “Dirichlet convolution followed by radix carrying produces eventually periodic output” is therefore a useful standard heuristic, but not a currently formalized transport law in this corpus.

| Coordinate or projection | Retained state | Lost state |
|---|---|---|
| full `A <-> f_A` | the entire support, recoverable by Möbius inversion | none: the coordinate change is lossless |
| full `(f_A,q,U)` carry certificate | the entire support, recoverable from the quotient and Möbius inversion | none, once the full sequences and `q` are retained |
| one coefficient, count, or carry difference | a single aggregate value | the contributing divisor labels at that index |
| finite suffix -> integer | one radix value | factorization of the coordinates realizing it |
| finite LCM sample | simultaneous divisibility of a chosen set | the binary cylinder at the sampled index |

The distinction is essential. `f_A(m)` does not display its contributors at one
index, but the *whole* function `f_A` recovers `A`; similarly a full tempered
carry certificate recovers `f_A` and then `A`. Information loss below always
means a named estimate, scalar, finite window, average, or difference, not the
global coordinate change unless explicitly stated otherwise.

## Möbius carries and Boolean repair

### Carry certificate

**Retained state.** A coefficient sequence, integer carry `U`, denominator `q`, and quotient `(2 U_N-U_(N+1))/q`.

**Exact transport law.** `temperedCarry_quotient_eq_supportCoeff` identifies the quotient with `f_A`; `mobius_carryQuotient_boolean` proves that its Möbius transform is Boolean ([BooleanMobiusCarry.lean:663-820](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)). Conversely, `support_fraction_of_booleanMobiusCarry` reconstructs a Boolean support from initial value, positivity, square-root bound, divisibility, and Boolean Möbius quotient ([BooleanMobiusCarry.lean:774-891](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).

**Success event.** `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry` is an exact existence equivalence ([BooleanMobiusCarry.lean:944-965](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)). The support `{2,3}` gives a checked period-six example with value `10/21`, not an infinite Boolean support ([BooleanMobiusCarry.lean:1055-1158](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean)).

**Fatal or blind configuration.** Rationality gives a carry after the support has already been supplied. The certificate does not construct a new infinite Boolean quotient from signed Lambert data or from a local radix repair.

**Information discarded.** Nothing is discarded by the *full* certificate:
its quotient recovers `f_A`, then Möbius inversion recovers the support. A
single carry difference records only `f_A(N+1)`, however, and omits the
contributors at that index.

**Original-object datum needed.** The missing ingredient is not recovery of the
support from a completed certificate. It is a global existence or exclusion
theorem for an infinite admissible Boolean carry trajectory.

### Local and global repair

**Retained state.** A lower support `D`, endpoint divisor count, binary suffix value, and repair integer `H = 2*suffix + 1 - endpointDivisorContribution`.

**Exact transport law.** `localRepairInteger_eq_two_mul_suffix_add_one_sub_endpoint` gives the formula ([BooleanMobiusLocalRepair.lean:440-458](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean)). `exists_boolean_replacement_of_signedDyadicValue` replaces a signed dyadic word by a Boolean word of the same value when that value fits its window ([BooleanMobiusLocalRepair.lean:500-557](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean)). The upper-half result additionally requires rational undershoot, endpoint count at least two, and exact suffix capacity ([BooleanMobiusLocalRepair.lean:656-819](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean)).

**Success event.** A stable trajectory satisfying `GlobalBooleanMobiusRepairFeasible` yields an infinite support of value `1/2`, by `infinite_support_half_of_globalBooleanMobiusRepair` ([BooleanMobiusGlobalRepair.lean:452-480](../../Erdos257PeriodNoncollapse/BooleanMobiusGlobalRepair.lean)). This theorem is conditional. Feasibility includes `GlobalEndpointExponentialBound`, exact word realization, capacity, and quotient-row equality ([BooleanMobiusGlobalRepair.lean:136-198](../../Erdos257PeriodNoncollapse/BooleanMobiusGlobalRepair.lean)).

**Fatal or blind configuration.** A finite Boolean replacement preserves one dyadic value but can alter future divisor incidences at every common multiple. Capacity alone neither gives bit stability nor the successive quotient equalities.

**Information discarded.** The scalar repair value forgets which factors label the coordinates changed by the repair.

**Original-object datum needed.** The limiting construction needs compatible Boolean bits on overlapping windows, including the changing divisor incidences of those bits.

## Signed Lambert coordinates

**Retained state.** An integer or nonnegative arithmetic weight and its divisor sum, rather than a Boolean support.

**Exact transport law.** `tsum_lambert_linear_weight` regroups a signed linear-growth Lambert series by divisor antidiagonals ([MersenneLambertLadder.lean:107-188](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean)). At base two, the source proves `sum mu(d)/(2^d-1)=1/2` and `sum phi(d)/(2^d-1)=2` in `tsum_moebius_div_two_pow_sub_one_eq_half` and `tsum_totient_div_two_pow_sub_one_eq_two` ([MersenneLambertLadder.lean:572-595](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean)). The primitive weight `phi*mu` has divisor sum `phi` ([MersenneLambertLadder.lean:248-305](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean)).

**Success event.** These are exact rational identities of convergent signed or multiplicity-weighted series.

**Fatal or blind configuration.** The weights are not Boolean. The primitive weight is unbounded on primes (`primWeight_unbounded_on_primes`, [MersenneLambertLadder.lean:307-325](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean)). The negative-Möbius support is not a half representation: it equals one half plus the positive-Möbius tail and exceeds half by at least `1/63` ([MobiusSignSupportNoGo.lean:109-168](../../Erdos257PeriodNoncollapse/MobiusSignSupportNoGo.lean)).

**Information discarded.** Signed cancellation and multiplicity retain net mass but lose the locations where a Boolean replacement must occur.

**Original-object datum needed.** A Booleanisation must lift the signed identity to compatible binary corrections while preserving a Boolean Möbius quotient. No inspected theorem supplies this lift.

## Rational tails, reciprocal mass, and common multiples

**Retained state.** Denominator doubling residues, wrap counts, and a scaled tail state.

**Exact transport law.** Rationality yields positive integer states with recurrence `u(n+1)+v*f_A(c+n+1)=2*u(n)`, residue congruence, and a common-multiple lower bound; see `exists_shifted_odd_tail_nat_state_with_common_multiple_bound_of_support_fraction` ([RationalSupportCarrySkeleton.lean:2300-2322](../../Erdos257PeriodNoncollapse/RationalSupportCarrySkeleton.lean)). `sum_supportCoeff_range_eq_sum_div` is exact double counting, and reciprocal summability makes its Cesàro limit equal reciprocal mass ([RationalSupportCarrySkeleton.lean:807-971](../../Erdos257PeriodNoncollapse/RationalSupportCarrySkeleton.lean)).

**Success event.** An infinite rational support has an unbounded positive shifted tail state (`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`, [RationalSupportCarrySkeleton.lean:2381-2402](../../Erdos257PeriodNoncollapse/RationalSupportCarrySkeleton.lean)). Odd-order wraps impose reciprocal-mass lower bounds ([RationalSupportCarrySkeleton.lean:1456-1525](../../Erdos257PeriodNoncollapse/RationalSupportCarrySkeleton.lean)).

**Fatal or blind configuration.** Unbounded state is compatible with rationality. Cesàro and wrap transports average away the precise binary location of an LCM pulse.

**Information discarded.** This compressed residue/wrap statistic does not
identify the individual support elements causing a coefficient, or the radix
cylinder containing the sampled state. This does not contradict losslessness
of the full carry certificate.

**Original-object datum needed.** A common-multiple argument needs a simultaneous upper or exclusion bound for the carry at that same multiple, retaining the corresponding binary prefix or suffix.

### Reciprocal-summable close returns

**Retained state.** Shifted atom sums for a complete binary tail.

**Exact transport law.** `binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom` decomposes the tail ([ReciprocalSupportIrrationality.lean:820-832](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean)). An infinite support makes shift zero a strict minimum ([ReciprocalSupportIrrationality.lean:868-892](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean)). Under reciprocal summability, period-LCM averaging produces arbitrarily close positive returns ([ReciprocalSupportIrrationality.lean:953-1009](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean)).

**Success event.** `irrational_erdosSupportSeries_two_of_summable_reciprocal` proves irrationality for every infinite reciprocal-summable support ([ReciprocalSupportIrrationality.lean:1011-1020](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean)).

**Fatal or blind configuration.** Dense supports need not satisfy the summability hypothesis. The averaging step loses exceptional LCM shifts and their radix phase.

**Information discarded.** The LCM average retains an average shifted-atom mass, but discards the exceptional shift, its divisor profile, and the radix phase at which it would be carried.

**Original-object datum needed.** A dense-case replacement must retain an exceptional shift together with its divisor ancestry and its binary cell, rather than only an average.

## Dilation, valuation, and shell projections

### Prime dilation

**Retained state.** Coefficient differences under multiplication by chosen primes and a pullback support.

**Exact transport law.** At a coprime argument, `f_A(pn)-f_A(n)` is the coefficient of `p`-pullback, by `dilationDifference_supportCoeffInt` ([SupportDilationDifferences.lean:112-139](../../Erdos257PeriodNoncollapse/SupportDilationDifferences.lean)). Iterated distinct-prime differences equal iterated pullback ([SupportDilationDifferences.lean:160-199](../../Erdos257PeriodNoncollapse/SupportDilationDifferences.lean)).

**Success event.** A support bounded in `Omega` is annihilated after more prime pullbacks than its bound (`iteratedDilationDifference_eq_zero_of_cardFactors_le`, [SupportDilationDifferences.lean:222-261](../../Erdos257PeriodNoncollapse/SupportDilationDifferences.lean)).

**Fatal or blind configuration.** The operator requires a coprime sample and only controls a selected multiplicative projection. It gives no transport of a rational radix carry through that operator.

**Information discarded.** The difference suppresses the undifferenced coefficient and keeps only support elements divisible by the selected prime product.

**Original-object datum needed.** Any use against #257 must retain the binary phase of the original carry while applying the same prime projection.

### Composite defects and valuation layers

**Retained state.** A composite dilation defect or a specified prime-power layer.

**Exact transport law.** `supportCoeff_mul_eq_add_defect` isolates the composite defect ([CompositeDilationDefect.lean:27-98](../../Erdos257PeriodNoncollapse/CompositeDilationDefect.lean)); the formally proved `{2,6}` fixture shows the defect can be nonzero ([CompositeDilationDefect.lean:216-231](../../Erdos257PeriodNoncollapse/CompositeDilationDefect.lean)). `supportCoeff_prime_power_layer` extracts one exact valuation pullback, and `mixedPrimePowerLayerTwo_supportCoeffInt` extracts two commuting distinct layers ([SupportSunflowerDichotomy.lean:652-713](../../Erdos257PeriodNoncollapse/SupportSunflowerDichotomy.lean); [MaximalOmegaLayer.lean:18-74](../../Erdos257PeriodNoncollapse/MaximalOmegaLayer.lean)).

**Success event.** The bouquet estimate bounds composite defect by finite exceptional core plus a petal coefficient ([CompositeDilationDefect.lean:128-214](../../Erdos257PeriodNoncollapse/CompositeDilationDefect.lean)).

**Fatal or blind configuration.** The clean prime model fails for composites. A valuation layer sees one signature but not interactions among signatures after radix carrying.

**Information discarded.** A composite defect keeps aggregate change under multiplication, and a valuation layer keeps one prime-power signature; together they still lose source indices, signs, overlaps, and binary digit positions.

**Original-object datum needed.** A joint state would have to contain several valuation layers and the carry simultaneously. The current theorems are finite coefficient algebra only.

### Primitive shell

**Retained state.** A prefix through `X`, a residual support above `X`, and a cross-carry.

**Exact transport law.** Prefix and residual split both coefficient and binary tail ([PrimitiveSupportBridge.lean:97-153](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean)). The cross-carry equals the scaled residual tail, and on the first shell `(X,2X]` evolves by the primitive Boolean bit ([PrimitiveSupportBridge.lean:170-205](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean)).

**Success event.** On the first shell, the residual coefficient equals the primitive support bit ([PrimitiveSupportBridge.lean:63-95](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean)). The denominator-pressure lemmas convert independently supplied analytic bounds into explicit power bounds ([PrimitiveSupportBridge.lean:209-251](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean)).

**Fatal or blind configuration.** Later shells contain proper residual divisors, so the primitive-bit recurrence stops. The pressure estimates are conditional and do not supply their analytic premises.

**Information discarded.** Shell splitting retains prefix and residual masses but suppresses the individual residual divisor ancestry and where its contributions land in the binary word.

**Original-object datum needed.** A multi-shell state must record residual divisor ancestry as well as the binary carry.

## Structured supports and endpoint pulses

### Sunflower structure

**Retained state.** An orthogonal-petal decomposition, finite exceptional core, and selected divisibility slot.

**Exact transport law.** `SunflowerForcedSlotTailSelection` is the explicit *hypothesis* combining a divisible weighted block with a bounded binary coefficient tail. From it, the theorem `forcedSlotCarrySelection_of_tailSelection` yields finite carry selection ([SupportSunflowerDichotomy.lean:406-483](../../Erdos257PeriodNoncollapse/SupportSunflowerDichotomy.lean)). With this hypothesis, `irrational_erdosSupportSeries_of_orthogonalPetalBouquet` gives irrationality ([SupportSunflowerDichotomy.lean:528-545](../../Erdos257PeriodNoncollapse/SupportSunflowerDichotomy.lean)).

**Success event.** Once the tail-selection premise is supplied, a selected divisible frame forces a carry choice; the orthogonal-petal theorem then proves irrationality. Both are conditional success statements, not a source of the selector.

**Fatal or blind configuration.** This is conditional on the tail selector. The decomposition separates rays but does not prove that a divisible block occurs in the same binary phase as a bounded tail.

**Information discarded.** Ray labels and a finite core do not retain the full binary word at the selected shift.

**Original-object datum needed.** One actual frame must be located with both its divisibility condition and its binary tail bound.

### Endpoint divisor pulse

**Retained state.** The two endpoint divisor counts for the selected support in
`[2,R]`; this is a pulse statistic, not the full selected support.

**Exact transport law.** `card_divisors_Icc_odd`, `card_divisors_Icc_even`, and `endpointPulse_eq_divisorSignal` identify the full-window pulse with `2*tau(2R+1)+tau(2R+2)-7` ([EndpointDivisorSignal.lean:49-151](EndpointDivisorSignal.lean)).

**Success event.** The factorial-ray theorem gives arbitrarily long synchronized divisor windows (`endpointDivisorSignal_unbounded_on_factorial_ray`, [EndpointDivisorSignal.lean:153-165](EndpointDivisorSignal.lean)).

**Fatal or blind configuration.** Pulse size does not determine the quotient remainder or binary suffix capacity; suffix capacity does not determine which old divisors contribute to the pulse.

**Information discarded.** The count forgets divisor identities, their previous support roles, and the current radix cylinder.

**Original-object datum needed.** The relevant joint state must retain the contributing selected divisors and the carry interval into which their pulse is inserted.

## Lossy estimates versus lossless states

The preceding failures have two different logical forms. They must not be
merged into the assertion that the available state is always too compressed.

1. **Lossy estimate projections.** Endpoint counts, finite suffix values,
   dilation differences, valuation layers, shell masses, and LCM/Cesàro
   averages deliberately forget coordinates. Their unresolved task is to
   retain enough of the omitted divisor/radix data to make the estimate
   decisive at one common index.
2. **Lossless full states.** The complete `A <-> f_A` coordinate and a complete
   Boolean--Möbius carry certificate are reversible. Their unresolved task is
   different: prove that an infinite globally admissible trajectory exists or
   cannot remain in the unresolved boundary regime. No recovery of hidden
   ancestry is missing once that state is given.

### The exact `1/21` objection to compression as the whole wall

For the canonical denominator-`21` rows, full quotient/rational alignment
identifies the finite lower support `D_R` exactly with the rational greedy
prefix through `R`, not merely with its coefficient counts
(`twentyOneEvenQuotientGreedySupport_eq_greedyMersennePrefixRat_of_fullAlignment`,
[`TwentyOneQuotientGreedy.lean:4856-4895`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)). Thus the state `(D_R,s_R)`, with `s_R` the canonical quotient remainder, retains the complete finite support ancestry and its matching radix remainder.

Under the fatal aligned branch, the source proves an exact eventual transition
for both `D_R` and `s_R`
(`twentyOneFatalAlignedBranch_eventually_canonical_transition`,
[`5282-5315`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5282)). It also proves that nonmembership is exactly this fatal/cofinite/aligned
branch (`twentyOneFatalAlignedBranch_iff_not_mem`,
[`3492-3510`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L3492)),
and forces permanent strict supercapacity `2^R < s_R`
(`twentyOneFatalAlignedBranch_eventually_strict_supercapacity`,
[`5617-5651`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5617)).

This is an exact counterexample to the claim that information loss alone is
the common wall. The formal obstruction is a global boundary/admissible-
trajectory question: exclude (or realize) the exact eventual supercapacity
orbit. The affine normal form records that surviving regime without a residual
Boolean choice (`twentyOneFatalAlignedBranch_eventually_affine_supercapacity`,
[`5653-5668`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5653)).

## Carry-law dictionary: what is the same event, and what is not

All six constructions have an affine carry shape, but they are not equivalent
without their own hypotheses.

* **Exact one-step `1/21` law.** For a `TwentyOneQRowExact D M s` whose
  members are at least two, `twentyOne_qRow_cocycle` gives an equality between
  the next prefix quotient, reservoir `2s`, target bit, and endpoint divisor
  contribution ([`TwentyOneOneStepPropagation.lean:62-76`](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean#L62)). With the additional real-prefix inequality
  `localMersennePrefixValue D <= 1/21`,
  `twentyOne_borrowContribution_le_reservoir_add_bit_of_prefix_le` proves the
  next borrow is nonnegative ([`78-90`](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean#L78)). Thus a pulse cannot exceed this *particular* reservoir-plus-bit under exact-row and real-undershoot hypotheses.
* **Borrow failure is a one-way boundary certificate.** Under the stricter
  range condition `2 <= d < M`, a failed borrow implies a strict real prefix
  overshoot, with the stated `O(M 2^-M)` upper interval
  (`twentyOne_failedBorrow_prefix_interval`,
  [`106-117`](../../Erdos257PeriodNoncollapse/TwentyOneOneStepPropagation.lean#L106)). The converse is not asserted. Hence failed borrow is not definitionally the same event as a seam crossing or a negative repair; it is a sign event which, in this exact row, certifies one kind of real-cell exit.
* **Local repair is the same algebra, not the same state.**
  `localRepairInteger_eq_two_mul_suffix_add_one_sub_endpoint` is exactly
  `H = 2A + 1 - S` ([`BooleanMobiusLocalRepair.lean:438-458`](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean#L438)). Its nonnegativity theorem needs the separate cutoff-undershoot hypothesis, `k<n`, and support containment in `[2,n/2]` ([`273-390`](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean#L273)). It specializes to the same signed balance only after identifying its suffix, target digit, and endpoint contribution with a quotient row; Lean does not state a global equivalence with `twentyOne` borrow failure.
* **Suffix-cylinder and seam steps preserve a cell, rather than decide a
  borrow.** `SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit` propagates
  a certified endpoint by `E' = 2E-C` and proves coverage of the new carry
  interval, but requires a selected-window buffer, a common coefficient
  profile, an existing cylinder, and `R <= E`
  ([`SelectedSuffixCylinder.lean:133-167`](../../Erdos257PeriodNoncollapse/SelectedSuffixCylinder.lean#L133)). A seam/crossing or preterminal-window assertion is therefore a cell-location statement under cylinder hypotheses; it is not equivalent to the `1/21` sign inequality.
* **Two-step quotient law.** On the fatal aligned branch only, the exact
  quotient state has the base-four affine update
  `s_(R+1) = 4s_R + targetPulse - prefixPulse - (2^(R+1)+1)` and appends
  `R+1` ([`TwentyOneQuotientGreedy.lean:5653-5668`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5653)). It is the two-row aggregate of the local affine balance after fatal-branch alignment and strict supercapacity; it is not available for an arbitrary repair or cylinder state.

**Answer to the central question.** For the exact aligned `1/21` lower rows,
yes: real prefix undershoot proves next-carry nonnegativity
([`TwentyOneQuotientGreedy.lean:4897-4966`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L4897)). Thus the fatal aligned branch has no eventual borrow/sign obstruction. Within that branch, the only formal survivor is the legal homogeneous supercapacity escape. This does **not** prove that generic borrow failure, negative local repair, seam crossing, and preterminal capacity failure are one event, nor that this is the only wall in the dense-support problem outside the `1/21` branch.

## Test of the supplied fixed-point picture

The supplied picture has two theorem-level components and two conjectural components.

* **Proved:** Boolean support becomes a divisor convolution, and rationality becomes a tempered integer carry. The citations in the first section establish both assertions.
* **Proved:** Large multiplicative synchronization occurs at common multiples and factorial endpoint windows, while binary tail and suffix theorems use a separate radix coordinate.
* **Not formalized here:** the supercontractive map `b -> BinaryDigits(r-E(b))`, its contraction property, and identification of its discontinuities with greedy gaps, seams, borrows, or endpoint pulses.
* **Open:** a theorem that either forbids or constructs simultaneous multiplicative resonance and a fatal binary cell.

The inspected corpus supports a qualified information-loss diagnosis:
averaging, dilation differences, valuation layers, and scalar carries each
preserve one arithmetic coordinate while losing another. But the exact `1/21`
state already retains finite support ancestry and radix state. The remaining
wall there is a global boundary/admissible-trajectory theorem, not a missing
coordinate reconstruction.
