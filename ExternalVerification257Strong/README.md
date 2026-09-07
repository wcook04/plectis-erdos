# `ExternalVerification257Strong/` in the private authoring tree

Copied 2026-09-06 from the release candidate at
`public-source-redacted://release-final-20260905`, branch
`release/final-20260905`, HEAD `8a28b2521e`. Byte-identical copies, made by the
Erdős #257 corrective-integration pass so that private memory is not behind the
candidate.

This package exists in the release candidate and existed nowhere in this tree.
It is the only comparator package that carries the uniform square-root repair
criterion, and it is the only #257 package with five files rather than two.

| file | contents |
|---|---|
| `Statements.lean` | the source-independent definitions, including `mersenneAchievementSet` at line 34 and `binaryCoeffPrefixNumerator` at line 79 |
| `Challenge.lean` | the three compared statements: `irrational_erdosSupportSeries_of_summable_reciprocal` at line 90, `irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase` at line 96, and `mem_iff_greedyBinaryDefect_sqrt_windows` at line 101 |
| `Solution.lean` | the transports, importing `Erdos249257.BouquetReciprocalIrrationality` and `ErdosProblems.Erdos257.GreedyRepairCriterion` |
| `NegativeSolution.lean` | the deliberate-negative pair |
| `AxiomAudit.lean` | the axiom print |

## Why it is inert here

The modules carry the release tree's namespace `Erdos249257.ExternalVerification.Strong257`
and import `Erdos249257.BouquetReciprocalIrrationality`, which this tree spells
`Erdos257PeriodNoncollapse` and which was itself only copied here today. This
directory is not a `lean_lib` in `lakefile.toml` and nothing imports it, so
`lake` does not build these files and they cannot break this tree's build. They
are preserved source, not a live target.

## Obligation for the next cycle

Do not re-author this package from a private inventory. It exists, it is
complete, and it carries `mem_iff_greedyBinaryDefect_sqrt_windows`, which is the
only exact membership criterion valid at every real target. Two things are
outstanding and neither is a mathematical gap: the package appears nowhere in
`docs/formal_math/palomar/launch_selection_v1.json`, so it is in no launch list,
and it is absent from the Palomar cut. Its execution status in
`palomar-entry-catalog.json` is `not_run_not_asserted`, as for every other
`ExternalVerification257` entry, so nothing here claims a replay.
