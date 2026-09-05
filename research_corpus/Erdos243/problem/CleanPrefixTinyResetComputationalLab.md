# Clean-prefix tiny-reset lab

## Analytic question

The exact excursion payments telescope into a subexponential global budget,
but that upper bound becomes contradictory only if repairs have a matching
lower cost.  A tempting local bridge is to charge the length `L` of a negative,
cancellation-free block directly to the next reset, for example by demanding
that its payment satisfy `h >= 2^L`.

The existing finite `E=-1` fixtures show that long clean blocks exist.  They do
not, by themselves, say how costly the first reset after such a block must be.

## Discriminating probe

`scripts/check_erdos243_clean_prefix_tiny_reset.py` starts from the exact
canonical seed `(tail_start, guaranteed_height, scale) = (16, 5, 1)` and keeps
running the actual primitive rational cocycle rather than stopping at the
declared `E=-1` horizon.  Every transition is checked with integer arithmetic:

- the state pair is primitive;
- `2 |e| < u`;
- `h = gcd(a^2, u-e)`;
- the successor is the exact content-reduced pair.

The stop condition is the first step with `h > 1`.  The sharp falsifier is a
prefix of `L` negative `h=1` steps followed by payment smaller than `2^L`.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_clean_prefix_tiny_reset.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos243_clean_prefix_tiny_reset_receipt.json
```

## One-way result

The exact centred errors before the first reset are

`[-1, -1, -1, -1, -1, -1, -1, -4]`,

and all eight corresponding payments are `1`.  The next step has centred error
`-7` and payment `h=2`, so `h < 2^8 = 256`.  This is an exact counterexample to
the universal block-length-only inequality `h >= 2^L`; no larger search horizon
can restore that statement.

The result does not refute a cumulative lower bound across complete recoveries.
It narrows the remaining producer: payment must be charged to global
prefix/residue coherence, or to a product spanning a properly aligned recovery
family, rather than to the length of the immediately preceding clean negative
prefix alone.  It is finite mechanism elimination, not an infinite orbit or a
solution of Erdős #243.
