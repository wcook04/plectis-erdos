# ExternalVerification68GapGcd

Two finite factorial-gap statements from the Erdős #68 programme, restated in
Mathlib-only vocabulary and transported from the project source.

## Statements

`factorial_gap_gcd`. For `2 ≤ i < j`,

```
gcd (i! - 1) (j! - 1) ∣ j!/i! - 1,
gcd (i! - 1) (j! - 1) ≤ j!/i! - 1,
j!/i! - 1 < j ^ (j - i).
```

`segment_inequality`. For `2 ≤ k ≤ N - 1`,

```
∑_{n = N-k+1}^{N} log (n! - 1)
  ≤ log (lcm_{2 ≤ d ≤ N} (d! - 1)) + binom(k+1, 3) · log N.
```

## Mechanism

The gcd statement rests on the quotient identity `j!/i! = j.descFactorial (j - i)`
together with the divisibility `gcd (i! - 1) (j! - 1) ∣ j!/i! - 1`, which comes
from reducing `j! - 1` modulo `i! - 1`. The upper bound follows because the
quotient minus one is positive, and the strict bound from
`Nat.descFactorial_le_pow`.

The segment inequality is the logarithm of the integer product bound: the
product of the moduli over a terminal block of length `k` divides the common
denominator times a collision factor `N ^ binom(k+1, 3)`, one factor for each
pair of the block whose gcd is nontrivial. The transport proves the interval
identity between the recursive block product and the `Finset.Icc` sum of
logarithms rather than assuming it.

## Boundary

Both theorems are finite arithmetic facts about factorial gaps. They bound the
common denominator of a prefix; they say nothing about the denominator of the
reduced prefix, and they do not decide the rationality of
`∑_{n ≥ 2} (n! - 1)^{-1}`. Erdős Problem 68 remains open. Novelty against the
literature is unassessed.

## Files

- `Challenge.lean` — Mathlib-only statements with intentional Comparator sorries.
- `Solution.lean` — transport from `ErdosProblems.Erdos68.PaperCompleteGcdSegment`.
- `comparator.json` — compared theorem names and the permitted axiom budget.
- `formalization.yaml` — metadata, scope, boundary, sources.
- `AxiomAudit.lean` — `#print axioms` for both compared theorems.
