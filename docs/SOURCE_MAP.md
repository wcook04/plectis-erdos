<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Source map

## Bounded reader route

Start from one mathematical question rather than decoding the complete import
graph:

1. Read `docs/orientation.json`, or its human projection
   `docs/ORIENTATION.md`, and select one programme, claim, or exact remaining
   open proposition.
2. Run one bounded lookup:
   `python3 scripts/query_corpus.py --route <programme_id>`,
   `python3 scripts/query_corpus.py --claim <claim_id>`, or
   `python3 scripts/query_corpus.py --open <remaining_open.id>`.
3. Follow the returned paper label into the authored exposition and its
   declaration or source handles into the modules grouped below.
4. Read `Erdos249257.lean` or `ErdosProblems.lean` only when package topology
   itself is the question. Read `docs/WAVE_INDEX.md` for chronology, not as the
   recommended mathematical reading order.

Lean source checked by the pinned Lean kernel is proof authority. This map is
authored navigation: it does not strengthen a claim, replace
`docs/claims.json`, or close an exact remaining-open proposition. Erdős #249
and the universal form of #257 remain open.

## #1041 / source-current frontier

Problem #1041 has a second, source-only navigation route in addition to the
Lean-backed Newton-flow note. Start with the dated [frontier delta](../research_corpus/Erdos1041/FRONTIER.md),
then use the [strongest-result map](../research_corpus/Erdos1041/STRONGEST_RESULTS.json)
and the [corpus manifest](../research_corpus/Erdos1041/CORPUS_MANIFEST.json).
The frontier delta is the authority for rows refuted after the activation map
was generated; do not rebuild those rows merely because they remain in the
machine map.

The high-signal reading routes are:

- [hub selection and generic closure](../research_corpus/Erdos1041/AttachmentAwareReeb.md)
  → [GenericSufficiencyClosure](../research_corpus/Erdos1041/GenericSufficiencyClosure.md):
  the surviving parent carrier is `min_c L(c) <= 2` on the ray-separated locus,
  followed by lower-semicontinuity closure.
- [quantitative Fekete stability and radial/angular reduction](../research_corpus/Erdos1041/NearFeketeRadialAngularSplit.md)
  → [degree-five sharpened cuts](../research_corpus/Erdos1041/Degree5AssemblyAndSharpenedCuts.md):
  the new tools localise the residual, but do not prove the degree-five or
  unrestricted theorem.
- [partial-cluster perimeter identity](../research_corpus/Erdos1041/PartialClusterPreimagePerimeterIdentity.md)
  → [tied-fibre moment hierarchy](../research_corpus/Erdos1041/TiedNewtonFaceFibreProduct.md):
  these are exact geometric/algebraic premises for future selection work, not
  a completed compatible-root selector.
- [new exterior-root product covering](../research_corpus/Erdos1041/ExteriorRootProductCovering.md)
  and [separatrix aggregate reduction](../research_corpus/Erdos1041/SeparatrixAggregateReduction.md):
  read their explicit hypotheses and refutations before treating either as a
  parent route.

The [earlier paper note](papers/full-text/erdos-1041-lemniscate-newton-flow.md)
remains the paper-facing route to the checked declarations in
`ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean`. The research corpus is
not part of `docs/claims.json`'s reviewed claim authority: its files preserve
source-level premises, computations, no-go results, and open boundaries.
Nothing in this route settles #1041; the exact continuation boundary is in
`FRONTIER.md` and must be read before any new proof search.

## Expansion-problem source routes

The per-problem [machine index](problems.json) is the source for the complete
module and note inventories below. Use the paper note for the mathematical
exposition, the principal Lean file for checked propositions, and the stated
open boundary for resumable work. These expansion roots are exact Lean source
under `ErdosProblems.lean`, not reviewed claim-registry entries.

| Problem | Paper-facing exposition | Principal checked source | Exact open boundary |
|---|---|---|---|
| #68 | [`erdos-68-factorial-denominator-irrationality.md`](papers/full-text/erdos-68-factorial-denominator-irrationality.md) | [`FactorialZeroPlateau.lean`](../ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1090) | Produce cofinally many non-unit carries; the finite denominator exclusion is not cofinal. |
| #243 | [`erdos-243-reciprocal-tail-rigidity.md`](papers/full-text/erdos-243-reciprocal-tail-rigidity.md) | [`ReciprocalTailRigidity.lean`](../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L897) | Exclude the unbounded mixed-sign/negative-excursion regime after the conditional bounded case. |
| #251 | [`erdos-251-prime-gap-dyadic-series.md`](papers/full-text/erdos-251-prime-gap-dyadic-series.md) | [`PrimeGapDyadicTail.lean`](../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360) | Obtain cofinally many adjacent small tail shifts at indices where the prime gaps differ. |
| #269 | [`erdos-269-three-prime-running-lcm.md`](papers/full-text/erdos-269-three-prime-running-lcm.md) | [`ThreePrimeRunningLcm.lean`](../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L123) | Supply the rationality-to-carry bridge and cofinal window escape for three-prime instances. |
| #1049 | [`erdos-1049-rational-base-lambert.md`](papers/full-text/erdos-1049-rational-base-lambert.md) | [`RationalBaseLambert.lean`](../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155) | Prove or refute irrationality at `3/2`; current obstructions do not supply a method-wide construction or analytic remainder bound. |

For #249 and #257, use the reviewed routes above and the registered paper
labels returned by `query_corpus.py`; this table deliberately covers only the
five expansion roots that are not represented in the reviewed module map.
Every row remains open at the problem level, and a checked local proposition
does not upgrade that status.

## Reviewed problem return routes

The two reviewed problems also have problem-owned registry routes. Use the
registry route to return from a problem number, the reviewed route to recover
the strongest registered claim spine, and the exact open handles to resume
work. The paper notes are exposition; the reviewed route's claim and source
packets retain their own authority boundaries.

| Problem | Problem-owned return | Reviewed result route and paper note | Exact open frontier |
|---|---|---|---|
| #249 | `python3 scripts/query_corpus.py --route erdos_249` | `python3 scripts/query_corpus.py --route erdos249_certificate_story`; [problem note](papers/full-text/erdos-249-binary-totient-series.md) | `remaining_open.erdos_249_irrationality`; `remaining_open.unbounded_certificate_supply` |
| #257 | `python3 scripts/query_corpus.py --route erdos_257` | `python3 scripts/query_corpus.py --route erdos257_half_story`; [problem note](papers/full-text/erdos-257-mersenne-support-subseries.md) | `remaining_open.half_value_membership`; `remaining_open.twenty_one_permanent_affine_supercapacity`; `remaining_open.universal_257_all_infinite_supports` |

From either reviewed route, use the registered claim or paper-anchor query
to travel back to exact Lean declarations; use the open query for the
unresolved boundary rather than treating a checked special case as a solution:

```sh
python3 scripts/query_corpus.py --claim <claim_id>
python3 scripts/query_corpus.py --paper-anchor <TeX_label_or_source_ref>
python3 scripts/query_corpus.py --open <remaining_open.id>
```

## Build entrypoint

- `Erdos249257.lean`
- `ErdosProblems.lean`
- Lake package: `erdos249257`
- Lean libraries / stable root imports: `Erdos249257`, `ErdosProblems`

`Erdos249257` is the reviewed #249/#257 corpus. `ErdosProblems` is the
problem-owned expansion surface; unregistered declarations there remain exact
Lean propositions rather than reviewed public mathematical claims.

## #257 / Erdős–Borwein families

- `Erdos249257.CertificateKernel`
- Relevant declarations include: `irrational_erdosSum_full_support`,
  `irrational_erdosBorwein_series`, `irrational_erdosSum_factorial_support`,
  `irrational_erdosSum_two_pow_support`, and
  `irrational_erdosSupportSeries_eventuallyPeriodic`.

## Periodic weighted Lambert series

- `Erdos249257.CertificateKernel`
- Nonnegative weights:
  `irrational_weightedErdosSeries_periodic`,
  `irrational_weightedErdosSeries_eventuallyPeriodic`, and
  `irrational_ratWeightSeries_eventuallyPeriodic`.
- Signed weights:
  `irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic` gives
  the irrational-or-base-terminating dichotomy, while
  `irrational_intWeightedErdosSeries_periodic_of_bpow_mul_ne_intCast`
  consumes an explicit nontermination hypothesis.
- `intWeightedCoeff_periodFourSignWeight_eq_zero_of_mod_four_eq_three` is the
  residue-selection obstruction explaining why the signed endpoint is not
  unconditional irrationality.

## #249 / totient denominator exclusions

- `Erdos249257.GapFareyBound`
- `Erdos249257.CertificateKernel`

## #249 / certificate reductions

- `Erdos249257.TotientTailPeriodKiller`
- `Erdos249257.CarrySurvivorExtinction`
- `Erdos249257.LcmDiagonalReduction`
- `Erdos249257.LcmConeFlatness`
- `Erdos249257.LcmConeNonflat`

Supporting ladder modules:

- `Erdos249257.MersenneLambertLadder`
- `Erdos249257.GeometricCoprimality`
- `Erdos249257.GcdMomentCalculus`

## #249 / diagonal pincer frontier

Read this band after the certificate reductions above.  It sharpens the same
open obligation; it does not prove the required unbounded supply.

- `Erdos249257.DiagonalPincerDecomposition` — exact full-target interval
  characterisation and the target-avoidance-to-irrationality reduction.
- `Erdos249257.SquaredMersenneDiagonalEnclosure` — Lambert-projected centre,
  exact signed square tail, and a sharp separation criterion.
- `Erdos249257.DiagonalFreshLossBridge` — exact fresh-loss projection and
  stronger adjacent-suffix supply interfaces.
- `Erdos249257.DiagonalPincerCertificates` and
  `Erdos249257.DiagonalPincerCertificatesT*`, followed by
  `ErdosProblems.Lift` and `ErdosProblems.Skip` — the finite diagonal segment
  supplies a checked working depth for every
  natural `t ≤ 82`; it supplies nothing at `t = 83`. This is finite source
  extraction, not a cofinal or asymptotic result.
- `Erdos249257.DiagonalPincerPrimeCertificates.*` — finite prime certificate
  shards used by that assembled segment; read the aggregators first.

Algebraic support for the same band:

- `MersenneShadowCyclotomicNoncollapse → MersenneShadowDenominatorGrowth`
- `RadicalMobiusShadow → RepunitMobiusNumerator → CyclicTensorMobiusShadow`
- `CyclotomicProjectionOfShadow → PrimePowerJumpDynamics`
- `RationalDenominatorSurvival`, `LambertDiagonalEnclosure`,
  and `FullTargetPrimeAdjunctionNoGo`

Exploratory exact interfaces with explicit conditional boundaries live in
`PrimitiveRationalGapSupply`, `PrimitiveSupportBridge`,
`ActualForeignResidueProjection`, `SternBrocotRunGeometry`, and
`SupportDilationDifferences`.

### Transport and curvature companion band

Read `CurvatureCarry → ExponentOnlyTransport → JointExponentTransport` for the
main proof spine, then `PrimeJumpMigration → PrimeJumpWindow` and
`ThreeTransportBoundary` for the new-prime and balanced finite consumers.
For the harmonic route, read
`FirstHarmonicGap → FirstHarmonicPivot → AdjacentPhaseSeparation`.
`FirstHarmonicGap` turns a constant-saving cosine bound into a direct
certificate. `FirstHarmonicPivot` decomposes the complex harmonic sum exactly
into centred supplier-fibre, fibre-mean, bad-supplier, and non-supplier terms;
the one-sided budgets `14X/25`, `X/100`, `X/100`, and `8X/25` give the required
`9X/10` saving. `AdjacentPhaseSeparation` gives a pairwise alternative. No
cofinal harmonic, prime-distribution, or decorrelation estimate is proved.
`TropicalCurvatureCarry` is a proved negative result showing that bounded
valuation–unit precision alone cannot exclude all centred completions.

- `CurvatureCarry` — exact curvature window, sharp radius, recurrence, and
  conditional unbounded-supply endpoints.
- `ExponentOnlyTransport` — squarefree support stability and the exact
  periodic affine slope/intercept state.
- `JointExponentTransport` — universal two-moment old-channel annihilation and
  the anchored `(3,5)` four-vertex consumer.
- `PrimeJumpMigration` / `PrimeJumpWindow` — migrated-channel correction,
  sharp direct radius, and the finite `(12,5,15)` certificate.
- `ThreeTransportBoundary` — balanced `(1,2,3,6)` consumer and the finite
  `(60,12)` certificate.
- `FirstHarmonicGap` — deterministic conversion of a blockwise harmonic gap
  into a direct certificate.
- `FirstHarmonicPivot` — exact four-term complex pivot decomposition and a
  conditional cofinal budget-to-irrationality socket.
- `TropicalCurvatureCarry` — fixed-precision local-signature no-go theorem.

The former one-sided transport companion is retired.  Its exact Lean results
remain available through the claim registry and source routes; no separate
active manuscript or rendered companion is part of this release.

### Paper-curation boundary

The paper treats `GcdMomentCalculus` as supporting mathematical exposition: its
squared Lambert transform, gcd moments, reduced-direction law, and cylinder
recursion explain the representation containing the #249 Möbius-square atom.
`FullTargetPrimeAdjunctionNoGo` is included as a proved negative result because
it closes a recurring prime-adjunction strategy without changing the open
claim. `SternBrocotRunGeometry` is registered as a source-level supporting
claim: its continuant/Fibonacci stability theorems are stated in the Lambert
complements, but no endpoint argument currently consumes them. It therefore
remains outside the paper's principal result spine; the cylinder law is owned
by `GcdMomentCalculus`, while `SternBrocotRunGeometry` owns the induced-run
stability package.

## Binary-carry trunk (post-wave carry layer)

Builds on `Erdos249257.CertificateKernel`; not part of the wave chronology.
Reading order:
`GenericTailOrbitRigidity → GreedyAchievementSet → CampbellShiftSynchronization → BooleanMobiusCarry → RationalSupportCarrySkeleton → DyadicPrefixCompression → SublogDivisorCoverage`.

- `Erdos249257.GenericTailOrbitRigidity`
- Relevant declarations include: `temperedBinaryOrbit_eq_scaledTail`, `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`, `balancedPulse_fanout_unbounded`, `balancedPulse_no_autonomous_decoder`

- `Erdos249257.GreedyAchievementSet`
- Relevant declarations include: `volume_mersenneAchievementSet`, `perfect_mersenneAchievementSet`, `isNowhereDense_mersenneAchievementSet`, `mem_mersenneAchievementSet_iff_greedy_survival`, `certifiedGreedyMersenneDeath_not_mem`, `three_fourths_not_mem_mersenneAchievementSet`, `rational_member_support_bit_iff`, `half_mem_mersenneAchievementSet_of_prefixForcingChain` (conditional interface only)

- `Erdos249257.CampbellShiftSynchronization`
- Relevant declarations include:
  `campbellQuarterExponent_periodFreeze_noSync`,
  `campbellPhaseFreeze_parameters_impossible`,
  `shiftWindowZero_iff_greedyMersenneSkippedSupport_infinite`, and
  `shiftWindowZero_iff_half_mem_mersenneAchievementSet`. These are a
  synchronization no-go and an exact endpoint re-expression, not an
  independent half-membership producer.

- `Erdos249257.BooleanMobiusCarry`
- Relevant declarations include: `erdosSupportSeries_rational_iff_exists_temperedCarry`, `support_fraction_iff_exists_temperedCarry`, `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`, `mobius_carryQuotient_recovers_support`, `support_half_iff_affineBinaryOrbit_tempered`

- `Erdos249257.RationalSupportCarrySkeleton`
- Relevant declarations include: `sum_doublingResidue_eq_mul_wrapCount`, `one_div_oddOrder_le_reciprocalMass_of_support_fraction`, `reciprocalMass_eq_residueMean_add_excessMean`, `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`, `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`

- `Erdos249257.DyadicPrefixCompression`
- This is #257 support, not part of the #249 diagonal band. It gives exact
  finite-fragment dyadic compression inside a hypothetical dyadic-rational
  support value, reduced/raw block-safety coordinates, primitive-lattice and
  support-tail-gap equivalences, conditional half-membership consumers, and
  checked failures of naive induction.
  Start with `finiteFragment_dyadicPrefixCompression`,
  `halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound`,
  `greedyHalf_badSkipCapViolation_iff_primitiveLattice`,
  `halfGreedyPrefixSupportTailGap_eq_excess_div_denominator`, and
  `unsafeSkipGcdOvershootSupply_iff_primitive`. No cofinal witness supply is
  proved.

- `Erdos249257.SublogDivisorCoverage`
- Relevant declarations include: `supportCoeffZeroWindow_length_le_eps_logb_add`

## Half-value finite-prefix and boundary analysis

This band studies the test value `1/2` in ordinary finite-prefix language.
A greedy prefix is the first `n` include/skip decisions. A seam is a pair of
finite words whose values bracket `1/2`. A cylinder is the set of infinite
extensions of one fixed prefix. A producer is an unproved hypothesis that
supplies the required seams or return configurations arbitrarily far out.

Read the band in four layers:

1. `GreedyAchievementSet → HalfCutLocator` defines the achievement set, greedy
   coding, and the finite cut around `1/2`.
2. `HalfCarryReachability → HalfCylinderFiniteShadow` translates finite
   prefixes into integer carry and finite-shadow coordinates.
3. `HalfCylinderIntegerGreedy → HalfCylinderConcreteSeamAdapter →
   HalfCylinderFullShellSeamBridge → HalfCylinderSkippedEndpointClassifier →
   HalfCylinderFloorErrorReset → HalfCylinderSeamLimit` develops the exact
   boundary arithmetic and limiting seam interface.
4. `HalfCylinderFatalGapRightTail → HalfCylinderHalfMembershipClassification →
   HalfCylinderLastProducerContradiction → HalfCylinderMiddleCarryLowerBound`
   gives the endpoint classification, eliminates the upper and `-3` middle
   cases, and isolates the remaining carry-tail inequality for `-2` and `-1`.

The floor-error and shell modules are supporting arithmetic layers, not
separate endpoint theorems. The last layer remains conditional: no producer
supplying the required configurations cofinally is proved.

## Claim registry

- `docs/claims.json` — the single owner of release identity, claim statuses, and declaration coordinates (file and line), cross-checked by `scripts/check_release.py`

## Generated finite certificates

- `Erdos249257.GeneratedCertificates`
- `Erdos249257.GeneratedCertificates.*`

The complete import graph and every declaration are generated in
`docs/claims.json::machine_readable_paper.module_graph` and
`docs/declaration_atlas.json`; use those surfaces when a grouped route above is
not specific enough. Current corpus counts live in the generated
`docs/ORIENTATION.md`, not in this authored route map.
