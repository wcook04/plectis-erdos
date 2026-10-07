<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Source map

Use this page to locate evidence. [Results and limits](../RESULTS.md) explain
what the results establish; [claims.json](../claims.json) owns current public
status, exact statements and declaration coordinates. This authored lookup
map supplies no additional proof or status.
Lean source checked by the pinned Lean kernel is proof authority.

## Bounded reader route

1. Choose a programme or claim from [orientation](ORIENTATION.md), its
   machine owner `docs/orientation.json`, or
   [results and limits](../RESULTS.md).
2. Run one bounded lookup from the repository root:
   `python3 scripts/query_corpus.py --route <programme_id>`,
   `python3 scripts/query_corpus.py --claim <claim_id>`, or
   `python3 scripts/query_corpus.py --open <remaining_open.id>`.
3. Follow its paper label and declaration/source handles. Use the
   [problem library](../problem_library.json) for transitive source dependencies.
4. Read `Erdos249257.lean` or `ErdosProblems.lean` only when package topology
   itself is the question. The [first root](../../lean/Erdos249257.lean) and
   [second root](../../lean/ErdosProblems.lean) live under `lean/`. [Wave history](WAVE_INDEX.md) gives chronology rather than reading order.

## Complete eight-problem return matrix

The [machine index](../problems.json) owns the full programme lookup, including
`what_is_checked`, `what_is_not_checked` and
`claim_registration.registered_claim_ids`. Expand those fields and return to
the named claim before interpreting a module as a result or a remaining
obligation. The table locates entry points and exposition, not strongest-result
rankings or an independently maintained list of open problems.

| Problem | Query from repository root | Lean entry points | Paper and source record |
|---|---|---|---|
| #68 | `python3 scripts/query_corpus.py --route erdos_68` | [`FactorialGapPlateauCore.lean`](../../lean/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean) · [`FactorialZeroPlateau.lean`](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateau.lean) | [paper note](../papers/full-text/erdos-68-factorial-denominator-irrationality.md) · [TeX source](../../paper/68/erdos-68-factorial-denominator-irrationality.tex) |
| #243 | `python3 scripts/query_corpus.py --route erdos_243` | [`ReciprocalTailRigidity.lean`](../../lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean) · [`SquareSpecialisationUnconditional.lean`](../../lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70) | [paper note](../papers/full-text/erdos-243-reciprocal-tail-rigidity.md) · [TeX source](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex) |
| #249 | `python3 scripts/query_corpus.py --route erdos_249` | [`TotientStrictPrimeEscape.lean`](../../lean/ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean) · [`GcdMomentCalculus.lean`](../../lean/Erdos249257/GcdMomentCalculus.lean#L235) · [`SternBrocotRunGeometry.lean`](../../lean/Erdos249257/SternBrocotRunGeometry.lean#L343) | [paper note](../papers/full-text/erdos-249-binary-totient-series.md) · [TeX source](../../paper/249/erdos-249-binary-totient-series.tex) |
| #251 | `python3 scripts/query_corpus.py --route erdos_251` | [`PrimeGapDyadicTail.lean`](../../lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean) | [paper note](../papers/full-text/erdos-251-prime-gap-dyadic-series.md) · [TeX source](../../paper/251/erdos-251-prime-gap-dyadic-series.tex) |
| #257 | `python3 scripts/query_corpus.py --route erdos_257` | [`WeightedReturn.lean`](../../lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean) · [`MersenneSubseriesRigidity.lean`](../../lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean) | [paper note](../papers/full-text/erdos-257-mersenne-support-subseries.md) · [TeX source](../../paper/257/erdos-257-mersenne-support-subseries.tex) |
| #269 | `python3 scripts/query_corpus.py --route erdos_269` | [`RestrictedFloorSum.lean`](../../lean/ErdosProblems/Erdos269/RestrictedFloorSum.lean) · [`WeightedPhaseCarry.lean`](../../lean/ErdosProblems/Erdos269/WeightedPhaseCarry.lean) · [`ThreePrimeRunningLcm.lean`](../../lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean) | [paper note](../papers/full-text/erdos-269-three-prime-running-lcm.md) · [TeX source](../../paper/269/erdos-269-three-prime-running-lcm.tex) |
| #1041 | `python3 scripts/query_corpus.py --route erdos_1041` | [`HausdorffLength.lean`](../../lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean) · [`CatalogueAdapter.lean`](../../lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean) · [`NewtonFlowRaySeparation.lean`](../../lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean) | [dated frontier](../../research_corpus/Erdos1041/FRONTIER.md) → [paper note](../papers/full-text/erdos-1041-lemniscate-newton-flow.md) · [TeX source](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex) |
| #1049 | `python3 scripts/query_corpus.py --route erdos_1049` | [`RationalBaseThreshold.lean`](../../lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean) · [`RationalBaseLambert.lean`](../../lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean) · [`FinitePencilProposition.lean`](../../lean/ErdosProblems/Erdos1049/PaperR20/FinitePencilProposition.lean#L43) | [paper note](../papers/full-text/erdos-1049-rational-base-lambert.md) · [TeX source](../../paper/1049/erdos-1049-rational-base-lambert.tex) |

For the reviewed #249 and #257 core routes, use
`python3 scripts/query_corpus.py --route erdos249_certificate_story` and
`python3 scripts/query_corpus.py --route erdos257_half_story`.
The probability and cylinder source route is
`python3 scripts/query_corpus.py --route probabilistic_gcd_geometry`.
For authored family relations, use
`python3 scripts/query_semantic.py family-relations <family_id>`.

## Specialist module lookup

The following groups locate implementations without restating their theorem
inventories. Names in the first four rows are relative to
`lean/Erdos249257/`; the declaration atlas and source query return exact files
and current declaration coordinates.

| Source group | Modules to inspect |
|---|---|
| Certificate and diagonal machinery | `CertificateKernel`, `SquaredMersenneDiagonalEnclosure`, `DiagonalFreshLossBridge`, `DiagonalPincerCertificates`; inspect aggregators before `DiagonalPincerPrimeCertificates.*` shards. |
| Transport and harmonic machinery | `CurvatureCarry`, `ExponentOnlyTransport`, `JointExponentTransport`, `PrimeJumpMigration`, `PrimeJumpWindow`, `ThreeTransportBoundary`, `FirstHarmonicGap`, `FirstHarmonicPivot`, `AdjacentPhaseSeparation`, `TropicalCurvatureCarry`. |
| Binary-carry coordinates | `GenericTailOrbitRigidity`, `GreedyAchievementSet`, `CampbellShiftSynchronization`, `BooleanMobiusCarry`, `RationalSupportCarrySkeleton`, `DyadicPrefixCompression`, `SublogDivisorCoverage`. |
| Half-value boundary machinery | `HalfCutLocator`, `HalfCarryReachability`, `HalfCylinderFiniteShadow`, `HalfCylinderIntegerGreedy`, `HalfCylinderConcreteSeamAdapter`, `HalfCylinderFullShellSeamBridge`, `HalfCylinderSkippedEndpointClassifier`, `HalfCylinderFloorErrorReset`, `HalfCylinderSeamLimit`, `HalfCylinderFatalGapRightTail`, `HalfCylinderHalfMembershipClassification`, `HalfCylinderLastProducerContradiction`, `HalfCylinderMiddleCarryLowerBound`. |
| #1049 arithmetic | Under `lean/ErdosProblems/Erdos1049/`: `RationalBaseLambert`, `ZudilinHeightRegion`, `RationalPadeArithmetic`, `HermitePadeNoGo`, `QAperyDiagonalNonEquivalence`, `ZudilinConeArithmetic`. |
| Generated finite certificates | `lean/Erdos249257/GeneratedCertificates.lean` and its shards; [certificate manifest](../generated_certificate_manifest.json) owns their grouping. |

The complete topology is in
`claims.json::machine_readable_paper.module_graph`; the
[declaration atlas](../declaration_atlas.json) supplies every indexed declaration.
Use these machine owners when the grouped lookup is insufficient. Counts live
in [orientation](ORIENTATION.md).

## Research records and verification

For #1041 research provenance, use the dated
[frontier](../../research_corpus/Erdos1041/FRONTIER.md),
[result map](../../research_corpus/Erdos1041/STRONGEST_RESULTS.json) and
[manifest](../../research_corpus/Erdos1041/CORPUS_MANIFEST.json).
These research records do not override reviewed claim status. The current
counterexample sources are included in the matrix above; historical continuation
questions have their own scope.

The [selection record](../PALOMAR_RESULT_SHOWCASE.json) owns authored
`source_result_spine` and `candidate_ranking` reading orders. [External verification](../EXTERNAL_VERIFICATION.md) explains selected
interfaces and receipt boundaries. [Reproducibility](../REPRODUCIBILITY.md)
distinguishes recorded evidence, computations and Lean builds; follow
[replay instructions](../verification/EXTERNAL_VERIFICATION_REPLAY.md) for an
external check. Query and projection checks do not compile proofs.
