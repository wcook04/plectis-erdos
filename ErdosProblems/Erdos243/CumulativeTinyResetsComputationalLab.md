# Cumulative tiny-reset lab

## Analytic question

The exact reset payments have a subexponential multiplicative upper budget.
The previous one-reset witness rules out charging one clean negative run
directly to its next payment. A distinct possible repair is to aggregate
several successive resets and hope that their payment product eventually
recovers the total clean-run length.

This probe tests only that raw-reset aggregation. It does not identify raw
resets with the complete aligned recoveries used by the surviving global
producer.

## Exact bounded probe

`scripts/check_erdos243_cumulative_tiny_resets.py` constructs the canonical
seed `(tail_start, guaranteed_height, scale) = (26, 4, 1)` and runs the exact
primitive rational cocycle. The declared stop boundary is the first of:

- the second reset;
- 12 exact transitions;
- a state exceeding 50,000 bits.

The bit bound is machine-readable in the shared experiment contract. It keeps
exact-state growth from turning a discriminating probe into an unbounded
computation while preserving the full integer witness.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_cumulative_tiny_resets.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos243_cumulative_tiny_resets_receipt.json
```

## One-way result

The first reset is preceded by seven negative `h=1` steps and has payment 2.
After it, one further negative `h=1` step precedes a second reset of payment 2.
Thus

```text
product of payments = 2 * 2 = 4
total clean length = 7 + 1 = 8
exponential clean-length charge = 2^8 = 256.
```

Hence the cumulative raw-reset inequalities `product(h_j) >= sum(L_j)` and
`product(h_j) >= 2^(sum(L_j))` are both false. No longer horizon can restore
either universal claim.

This does not refute a lower bound that uses complete-recovery alignment,
prefix CRT coherence, or source-specific prime multiplicity. It eliminates
raw reset lengths—even cumulatively—as the missing lower-cost mechanism.
