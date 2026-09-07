# Erdős #269: exact rank of the sampled cut family

## Statement

Fix a field `F` and a scalar `c` with `c ≠ 0` and `c ≠ 1`. For `0 ≤ k ≤ m`, let
`v_k` be the length-`m` column carrying `1` in each of its first `k` coordinates
and `c` in the remaining ones. Let `E` be a finite set of cuts, each at most `m`,
and let `A` be a matrix whose set of columns is exactly `{v_k : k ∈ E}`. Then

```text
rank A = |E| - [ 0 ∈ E and m ∈ E ]
```

The compared theorem is stated over an arbitrary field, not only over the
rationals, and the column hypothesis is an equality of column ranges, so
repeated and permuted columns are covered with no ordering assumption on `E`.

## Mechanism

Consecutive cut columns differ by `(1 - c)` times the indicator of a half-open
block of coordinates. For cuts strictly inside the range those blocks are
nonempty and pairwise disjoint, so a linear relation among the columns has zero
coefficient at every interior cut. The two extreme cuts are the only source of
degeneracy: `v_0 = c · v_m`, so `0` and `m` together contribute one relation and
nothing else does. Removing cut `0` when both extremes occur leaves an
independent family whose span is unchanged, which gives the displayed formula
through `Matrix.rank_eq_finrank_span_cols`.

## Boundary

This is a finite linear-algebra theorem about the sampled cut family. It is a
rank computation for one explicitly described matrix family. It makes no
assertion about the running least common multiple of `{2,3,5}`-smooth numbers,
it supplies no irrationality argument, and it does not settle Erdős Problem 269,
which remains open. The parent problem is untouched by this package.

`Challenge.lean` is Mathlib-only and carries one deliberate specification
`sorry`. `Solution.lean` is sorry-free and transports the theorem from
`ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean`. No Comparator replay and no
Palomar submission has been performed for this package.
