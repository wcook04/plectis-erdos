# Erdős #257: positive half-greedy skip equivalence

This package exposes the exact boundary of the cofinal skipped-core route.
Every finite rational greedy residual for one half is strictly positive, and
cofinal strict skips occur if and only if one half belongs to the Mersenne
achievement set.

The equivalence is a nontrivial route-identification theorem: the proposed
skip supply is not a weaker sufficient condition waiting to be proved by
local estimates. It is another form of the open endpoint itself. This does
not prove half-membership, non-membership, or Erdős Problem #257.

`Challenge.lean` imports only Mathlib and repeats the exact definitions used
in the two theorem types. `Solution.lean` transports the source-current
declarations from
`Erdos257PeriodNoncollapse/BooleanMobiusSkipRowCofinal.lean`. The deliberate
negative adds an unused `True` argument to the equivalence, so Comparator must
reject it.
