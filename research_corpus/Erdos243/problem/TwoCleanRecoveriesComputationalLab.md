# Two consecutive clean recoveries still underpay length

The remaining #243 payment route needs a global lower bound across aligned
reset recoveries.  The first sharp finite question is whether passing from one
clean recovery to two already repairs the failed length charge.

It does not.  Starting from the exact primitive pair `(u,v)=(19,14684)`, the
centered reduced cocycle has

- heights `19,11,13,19,13,17,19`;
- centered errors `-3,-2,-6,-7,-4,-2`;
- payments `2,1,1,2,1,1`.

Thus `[19,11,13,19]` and `[19,13,17,19]` are consecutive clean first-return
intervals of length three.  Their reset payments are two and two, so the
cumulative payment is `4 < 6 < 2^6`.  This is a complete exact counterexample
to any universal lower bound using only the lengths and payments of two clean
recoveries.  It does not rule out an unbounded-prefix theorem using changing
CRT residues, prime identities, or overlap data across the recoveries.

The result sharpens the analytic target: “relations between several
recoveries” is too broad.  A viable relation must consume source-specific
arithmetic information not determined by the two recovery lengths and reset
payments.

Replay:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_two_clean_recoveries.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_two_clean_recoveries.py --check
```

The durable receipt is
`state/formal_math/erdos257_period_noncollapse/erdos243_two_clean_recoveries_receipt.json`.
