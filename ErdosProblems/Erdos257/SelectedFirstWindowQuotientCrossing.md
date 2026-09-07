# Selected first-window quotient-crossing anatomy

## Status

This note records a targeted exact discriminator for the logarithmic
first-window producer at the half target.  It does not prove the all-depth
producer or Erdős #257.

The companion Lean module `SelectedFirstWindowQuotientLift.lean` proves, for
the actual frozen half-greedy prefix `P_n`,

\[
 \operatorname{greedyHalfFrozenMargin}(n-1,J)
 =Q_{P_n}(n+J)-2^J(2^{n-1}-1).
\]

Thus first nonnegative frozen margin is literally first crossing of one
integer Mersenne quotient row.  The audit below inspects the last deficient
row at that crossing; it is not another survival-horizon census.

## Exact audit

`scripts/selected_first_window_quotient_crossing_audit.py` replays the
canonical greedy orbit for `1/2` using a fixed dyadic integer enclosure.  An
ambiguous take/skip comparison aborts.  It then iterates, at every actual
skipped `n`, the exact recurrence

\[
 M_{n,0}=-(K_n-1),\qquad
 M_{n,J+1}=2M_{n,J}+f_{P_n}(n+J+1).
\]

For a bounded independent check it also evaluates

\[
 Q_{P_n}(n+J)=\sum_{d\in P_n}
   \left\lfloor\frac{2^{n+J}}{2^d-1}\right\rfloor
\]

directly and asserts that its target gap equals the recurrence margin.  The
checked receipt has 456 such direct quotient comparisons through `n=384`,
with zero failures.  It also independently reconstructs the already-proved
future-skip-capacity factorization, again with zero failures.  That
factorization is not claimed as a new theorem here; it already lives in
`HalfCylinderFiniteShadow.lean`.

The durable run covers all skipped starts through `n=100000`:

- skipped starts analysed: `49785`;
- first-crossing failures by `2*ceil(log2 n)`: `0`;
- largest minimal crossing length: `19`, at `n=55127` (binary length `16`);
- branch at the crossing endpoint: `27451` skips and `22334` takes;
- exact orbit trace:
  `cc1559e310bf7bc75aa7f85deae5914e02fadf9cde02716d1d60226f06378f84`.

This extends the earlier logarithmic audit from `10000` to `100000` only
because it tests new named endpoint mechanisms.  It remains finite evidence.

## What the last deficient row actually looks like

If the pre-crossing margin is negative, elementary integer order forces

\[
 f_{P_n}(n+J)\ge -2M_{n,J-1}\ge2.
\]

The data show that this necessary inequality is essentially the only uniform
small statement visible at the final row:

- pre-crossing margins range from `0` down through `-32` in the receipt;
- closing divisor pulses range from `0` through `65`;
- every residue class modulo six occurs among crossing endpoints;
- crossings occur on both actual takes and actual skips;
- the second-smallest selected divisor needed at a closing endpoint reaches
  `49778` at endpoint `99556`.

Consequently none of the following proposed proofs survives: universal
pre-margin `-1`, universal closing pulse `2`, a closing multiple of six,
closure at an actual skip, or payment by two bounded small selected divisors.
The large second-divisor example is especially decisive against replacing
the global frozen prefix by a fixed finite divisor basis.

## Bounded future-skip supply is also false

Using the exact identity

\[
 M_{n,J}
 =\operatorname{futureSkipCapacity}(n,J)
  -\bigl(K_{n+J}-1\bigr),
\]

the number of actual future skips encountered before crossing is distributed
as follows:

| future skips | 0 | 1 | 2 | 3 | 4 | 5 |
|---:|---:|---:|---:|---:|---:|---:|
| starts | 83 | 16782 | 25098 | 7179 | 624 | 19 |

The claim that four future skips always suffice survives through `10000` but
fails first at `n=24473`.  Its minimal crossing is at endpoint `24480`, after
the five consecutive skips `24476,...,24480`; the future-skip capacity is
`31`, the terminal centred carry is `0`, and the closing divisor pulse is
`33`.  This exact late falsifier is why the longer targeted run was needed.

There is no evidence here for a universal bound of five.  More importantly,
even such a bound would still require an all-depth arrival theorem and would
not by itself control the coupled endpoint carry.  The proof target remains
the ordered incidence inequality, not a bounded count of skip events.

## Frontier effect

The quotient lift and the audit leave one honest logarithmic producer:

> At every actual skipped `n`, prove that some
> `J <= 2*ceil(log2 n)` has
> `Q_(P_n)(n+J) >= 2^J(2^(n-1)-1)`.

The audit closes several attractive local payer mechanisms but does not
weaken this producer.  Any continuation must retain either the complete
ordered selected-divisor incidence in those `O(log n)` rows or a genuinely
coupled capacity/carry potential.  Replacing that information by a fixed
small divisor basis, a bounded number of future skips, endpoint congruence,
or the raw rational remainder loses information already falsified here or
structurally excluded by the denominator-cancellation result.

## Reproduction

```text
./repo-python \
  formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/selected_first_window_quotient_crossing_audit.py \
  --max-n 100000 --quotient-check-max-n 384 \
  --json-out state/formal_math/erdos257_period_noncollapse/selected_first_window_quotient_crossing_receipt.json
```

The proof-bearing coordinate source is
`SelectedFirstWindowQuotientLift.lean`; the exact finite receipt is
`state/formal_math/erdos257_period_noncollapse/selected_first_window_quotient_crossing_receipt.json`.
