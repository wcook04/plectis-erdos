# Cassini attachment-deficit lab

## Question

Can a ray-cut decomposition be consumed metrically by choosing an
average-short Newton trajectory in each strip and joining the chosen
trajectories inside arbitrarily small saddle neighbourhoods, without losing
the coefficient `1 / (2π)`?

## Discriminating probe

For the Cassini polynomial

\[
f_a(z)=z^2-a^2,
\]

the Newton trajectories are lifts of oriented rays under `f_a`.  The saddle is
`z=0`, with critical value `-a²`.  Consequently only the lift of the negative
real critical-value ray reaches the saddle.  A trajectory selected from the
strip average at any other value argument misses every sufficiently small
saddle neighbourhood.  Shrinking the neighbourhood therefore does not make
the attachment mismatch local.

An independent numerical quadrature of the exact Cassini level
parametrisation was used only to discriminate between two conflicting
mechanism predictions.  It confirmed that the coarea integral can sit below
the root distance, directing the durable proof to the already exact arithmetic
certificate rather than to a new finite approximation.  No numerical value is
used as proof authority.

## Exact result

At `a = 9/10`, the two roots are `9/5` apart.  The checked Cassini coarea
majorant is more than `4/25` below that distance.  Therefore every connected
root-spanning object of length `len` satisfies

\[
  \text{coareaBudget}+4/25 < \operatorname{len}.
\]

Lean declaration:

- `ErdosProblems.Erdos1041.CassiniTreeBudget.cassini_nine_tenths_forces_attachment_overhead`

The proof consumes
`cassini_nine_tenths_slack` and the unavoidable root-distance lower bound; it
does not depend on raster resolution or floating-point quadrature.

## Source-linked dual-draft falsifier

The exact estimate is not merely a generic warning about strip averaging.  It
directly refutes the load-bearing spanning-tree statement printed in both
local unrestricted proof drafts:

- Proposition 12 of `erdos1041-general-candidate-draft-main`;
- Proposition 7 of `erdos1041-general-candidate-draft-revised`.

Each proposition asserts that every positive `ε` admits a finite embedded tree
through all roots whose length is at most the level-length tail divided by
`2π`, plus `ε`.  The Cassini component at `a=9/10` satisfies the stated Morse
and distinct-critical-value hypotheses.  Its true tail budget is strictly
below `41/25`, while every connected root-spanning set has length at least
`9/5`; the gap is strictly greater than `4/25`.  Therefore no choice of local
saddle neighborhoods or strip representatives can make either printed
proposition true.

The source anchors, source digests, exact rational replay, Lean consumers, and
claim ceiling are bound by:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_candidate_tree_budget_source_audit.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_candidate_tree_budget_source_audit.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_candidate_tree_budget_source_audit_receipt.json`.

## One-way consequence

The additive-error strip-length fan-in with the unchanged `1 / (2π)`
coefficient is eliminated in both unrestricted drafts.  A perfect compact
Reeb decomposition would not repair this metric consumer: the necessary
attachment overhead is bounded below by a fixed positive number in the
Cassini witness.

This does **not** refute the Reeb decomposition, curved descending paths, or
Erdős #1041.  The surviving routes must either:

- use a different global selection inequality that pays for attachment;
- select a single short root pair rather than span every root; or
- bypass Newton-strip averaging with another geometric mechanism.
