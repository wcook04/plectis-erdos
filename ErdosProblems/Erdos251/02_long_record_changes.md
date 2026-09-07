# Long-record changes and preservation map

The long record is a prior published assembly; the round-6 short note and Lean slice govern current statements. Locations below use the supplied files and authored labels, not a guessed current public branch.

## `reasoning-parts/erdos251/extended_record.tex`

### `sec:xr-divisorhit`, lines 93–106

Replace the heading `A weaker recurrence-level target` with `A divisor-hitting formulation`. Replace the paragraph after `xr:divisor-hit` with:

> The divisor-hitting condition is equivalent to irrationality within an integer-digit dyadic recurrence. Irrationality gives nonintegrality of every positive shift. Conversely, a rational initial value gives one eventually integral positive shift; the cocycle identity makes all its positive multiples eventually integral as well. Applying the proposed condition to that shift gives a contradiction. The quantifier organisation may be useful for a producer, but the equivalence alone is not an analytic saving.

The existing current short note already contains the relevant classifier. Do not present this as a new theorem from this return.

### `sec:xr-compression`, state-compression paragraph, lines 114–123

Retain the valid conditional pigeonhole observation, but replace the claim of a finite-state real tail by:

> After the rational transient, the tails lie in one fixed lattice. A dyadic first-moment bound gives a positive proportion of indices with `T_N ≤ C_1 log X`, for a fixed sufficiently large `C_1`. On that restricted set only `O_d(log X)` lattice values occur, so one value is repeated `≫_d X/log X` times. The bound on the number of states grows with the scale. Fractional parts are eventually periodic; the full real tails need not have a fixed finite state space. These repeated values give integral differences, whereas the desired producer needs a nonintegral difference.

Do not delete this valid bounded-scale counting argument merely because rationality alone does not force repeated real tails.

## `02_long_record.tex`, free-pair discussion, lines 661–669

Use the same scale-dependent qualification. The free-pair and fixed-shift conditions are alternative exact criteria after all their quantifiers are imposed. A single nonintegral pair is not the full free-pair criterion.

## `02_long_record.tex`, paragraph following `prob:smallpair`, lines 1317–1330

The sentence about density-zero events being produced on a sparse set is already compatible with sparse averaging. Do not label it as a newly discovered error. Narrow the broad claim about fixed patterns to:

> The cited isolated-gap and fixed-cluster statements do not themselves give the residue-sensitive weighted continuation estimate used here. A future argument can combine a sparse configuration count with a global tail budget; density zero alone does not rule out that route.

## `family_catalogue.tex`, Actual real prime gap tail, lines 71–90

This entry already correctly records the actual bridge and its conditional endpoint. Leave the mathematical scope intact. The general handoff obligation still requesting that bridge is stale metadata, not a missing theorem.

## New ordinary research appendix

Place `proofs/SharpSparseFeedback.md` after `SparseRationalisation.md` as a separate ordinary result. Keep the old paired construction: it works below an arbitrary divergent envelope and remains a useful transparent constraint-separation example. The new theorem optimises the regular polylogarithmic regime and adds the exact dimension law. It does not replace every part of the old theorem.

The principal failure map is in `00_IDEA.md`. Preserve the old bounded-alphabet sparse obstruction, the adaptive-support entropy argument, the polynomial complete-tail example, the sparse irrational phase-concentration example, and the failed affine escape identity. Their roles are distinct.

## Generated metadata rather than mathematical source

`03_research_packet.json` retains an early row describing free pairs as a strict weakening, and an older `structural_reading` sentence inferring a producer from finite observations. Later additive corrections in that same file give the correct boundaries. Consolidate the producer description instead of publishing both accounts. Keep the finite observations as observations. The corrected finite-continued-fraction boundary at line 430 already says that finite data do not determine an irrationality exponent; do not undo it.

No new numerical prime computation or denominator exclusion was attempted in this return.
