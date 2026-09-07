# Problem-centric formalization map

New formal mathematics is organized by the actual problem and proof object.
The legacy `Erdos257PeriodNoncollapse` library remains available as a large
shared infrastructure and compatibility surface; it is no longer the default
naming scheme for unrelated problems.

## Working in this tree

[`WORKING_GUIDE.md`](WORKING_GUIDE.md) is the operational front door: use it
to select a problem, distinguish source-of-truth status from derived evidence,
inspect a module's local import plan, and choose a safe focused build. It does
not duplicate the live status data held by packets and the manifest.

## Corpus map before a problem is selected

For orientation or organizational work, run this from the repository root
before browsing all owner directories:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \
  --entry --json
```

The resulting `recommended_routes` map distinguishes a compact frontier
chooser, source topology, corpus-wide declared computation routes, and a
bounded source inventory for one selected problem. It performs no computation
and does not open a research packet or infer mathematical progress. After an
exact problem id is chosen, use its cockpit for papers, comparator corpora,
and research handoffs before inspecting a large evidence tree:

```sh
./repo-python -m system.lib.mathematical_working_memory \
  --query "Erdos #<number>" --problem-cockpit --context-budget 12000
```

| Problem | Lean module | Assimilation packet | Live mathematical throat |
|---|---|---|---|
| Erdős #68 | `Erdos68.FactorialZeroPlateau` and companion modules | `Erdos68/research_packet.json` | prove cofinally many failures of $m\mid Z_m$; the one-kernel log constraint is saturated at its sharp constant |
| Erdős #243 | `Erdos243.ReciprocalTailRigidity` and `Erdos243.CleanRecoveryLengthCounterexample` | `Erdos243/research_packet.json` | the unbounded normalized-return family ends in one rigid quotient class whose next step is forced `11→12`, eliminating immediate clean-cylinder switching; control the resulting expanding excursion using unbounded prefix arithmetic or cross-recovery coherence |
| Erdős #249 | `Erdos249.TotientStrictPrimeEscape`, `Erdos249.FullDepthRayAmplifier`, `Erdos249.PeriodMultipleEscape` | `Erdos249/research_packet.json` | exclude inhomogeneous fixed-quotient boundary words using actual consecutive-totient correlations; the homogeneous constant-two mode is now killed at every shift |
| Erdős #251 | `Erdos251.PrimeGapDyadicTail` and `Erdos251.AffineCylinderCollapse` | `Erdos251/research_packet.json` | genuinely external control of actual prime-tail fractional parts; adaptive and fixed-lattice block pullbacks are checked circular |
| Erdős #257 | `Erdos257.MersenneSubseriesRigidity` | `Erdos257/research_packet.json` | turn hereditary unique coding into arithmetic rigidity of every individual infinite-support value |
| Erdős #269 | `Erdos269.DyadicOrderedTailRecurrence` and `Erdos269.DyadicShellSummability` | `Erdos269/research_packet.json` | the genuine infinite shell tail now either reaches an exact integral state or returns cofinally `1/31`-far from every integer; exclude the integral branch |
| Erdős #1041 | `Erdos1041.NewtonFlowRaySeparation`, `Erdos1041.LevelSeparation`, `Erdos1041.CassiniTreeBudget`, `Erdos1041.CubicCriticalHub`, `Erdos1041.NearFeketeHubOrbit`, `Erdos1041.CriticalTwoRootProximity`, `Erdos1041.BarycentricEnvelope`, `Erdos1041.BarycentricTargetDisc`, `Erdos1041.ConnectedClusterAreaForcing`, `Erdos1041.CriticalEllipseMinimaxStationarity`, and `Erdos1041.GenericSufficiencyClosure` | `Erdos1041/research_packet.json` | prove the compact ray-cut/Reeb decomposition, then find a metric consumer that avoids the Cassini positive attachment deficit |
| Erdős #1049 | `Erdos1049.RationalBaseLambert`, `Erdos1049.BezoutPluckerJets` | `Erdos1049/research_packet.json` | the normalized Hankel q-order is exactly sharp at every rank, and the source scalar content is all-rank but provably far below the required charge; extract additional primitive residual-matrix divisibility or close the q-Apéry all-start quantitative escape at base `3/2` |

The supported root `ErdosProblems` imports `ErdosProblems.Root`, which in turn
imports the current problem modules. Each module
must keep its remaining open hypothesis visible and must not promote finite
evidence, a representation change, or a failed strategy into closure of the
original open problem.

`assimilation_manifest.json` is the machine-readable root index. Its
`received_return_index` is the aggregate inventory of every assimilated
research return, while each problem-owned packet preserves source hashes,
authority bands, negative results, surviving producers, and the honest claim
ceiling.
`AxiomAudit.lean` is executable assumption documentation and is included by
the supported root.

The legacy #249/#257 library and `erdos249-257-main-paper` remain the unlimited
integration surfaces. Problem-owned modules and papers are self-contained
views, not replacements: they may deliberately repeat definitions, proof
chains, countermodels, and open obligations from the monolith.

Public release is a separate change class: focused Lean validation comes first,
then mathematical review of hypotheses and non-claims, then a problem-owned
claim-registry row and generated public navigation. Exact copies enter the
public corpus only from a source-current identity with collision-free target
paths.
