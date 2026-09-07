# Prime-record compensation: a bounded-recovery homogeneous-mode throat

## Scope

This computation is target-neutral in the sense relevant to the programme: it
does not privilege `1/21`, one-half, four-ninths, or any previously named
construction.  It audits the exact greedy carries of hundreds of distinct
rational tail states and asks a one-way question forced by any escaping orbit:

> when the carry first exceeds every earlier height, how long can it avoid
> returning below the old record?

The answer is not asserted as a theorem.  The exact computation kills recovery
bounds one, two, and three, while an exhaustive finite census leaves a bound of
four whose proof would construct a rational infinite Mersenne support.

## Exact state

Let `A` be the certified greedy word for a rational target `p/q` in `(0,1)`, let

    f_A(m) = #{d | m : d in A},

and let `epsilon_m` be the `m`th binary digit of `p/q`.  The integer carry used
by the audit satisfies

    C_m = 2 C_(m-1) + epsilon_m - f_A(m).                 (1)

For `P<R`, exact iteration gives

    C_R = 2^(R-P) C_P
          + sum_(j=P+1..R) 2^(R-j) epsilon_j
          - sum_(j=P+1..R) 2^(R-j) f_A(j).               (2)

The script checks (1), checks (2) at every recorded recovery, and independently
cross-checks the carry against

    floor(2^m p/q) - sum_(j<=m) 2^(m-j) f_A(j)

through rank 512 for every target.  It uses bounded rational remainders after
that point, not floating point.

## Why bounded record recovery would solve a rational construction

Write

    M_(N-1) = max_{m<N} C_m,

and suppose `C_N > M_(N-1)` is a new record.  Assume that for some fixed `H`
there is always an `ell` with `1 <= ell <= H` and

    C_(N+ell) <= M_(N-1).                                (3)

Because the carries are integers, `M_(N-1) <= C_N-1`.  Combining (2) and (3),
and using nonnegativity of the binary digit block, forces

    sum_(j=1..ell) 2^(ell-j) f_A(N+j)
      >= (2^ell-1) C_N + 1.                              (4)

But `f_A(m) <= tau(m) <= 2 sqrt(m)`.  Hence the left side of (4) is at most

    (2^ell-1) 2 sqrt(N+H),

so every record obeys

    C_N < 2 sqrt(N+H).                                   (5)

Every non-record carry lies below an earlier record, so (5) bounds the whole
orbit polynomially.  The denominator-`q` carry is `q C_N` plus the bounded
remainder of `2^N p` modulo `q`; it is therefore tempered.  The existing
`support_fraction_of_temperedCarry` consumer then identifies the Mersenne
support sum with `p/q`.  Choosing an even-denominator target makes infinitude
automatic: every finite Mersenne subsum has odd reduced denominator.  In
particular, the exact distance-four witness `71/182` is also a valid disposable
construction target.  An all-depth bounded-recovery proof for it would give an
admissible infinite rational support and refute Erdős #257.

This is not another normalization of membership: (3) is a concrete local
arithmetic statement about record creation, and (4) turns it into a divisor
bound without assuming convergence of the support sum.

## Selected-tail breadth result

Command:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/prime_record_compensation.py \
  --depth 10000 --target-limit 512
```

The 512 targets are exact quotient-distinct tail states from the broad rational
funnel.  Across 5,830 new-record events:

- every event returned below its preceding record within two ranks;
- 5,826 returned in one rank;
- four events falsified the one-rank law;
- the first and worst one-rank failure is target `31/1238` at rank 118:
  `M=3`, `C_118=4`, `C_119=5`, and `C_120=1`;
- all 5,830 record-recovery block identities passed;
- all direct floor/prefix cross-checks through rank 512 passed.

The most frequent record successors were not random-looking ranks.  They were
divisor-rich scales: `5040` (333 targets), `2520` (320), `7560` (210), `720`
(198), `1680` (197), `360` (196), and `1260` (183).  This is a structural clue:
record spikes appear immediately before a support-divisor pulse, and the rare
failure of the one-step law is repaired by the next pulse.

Canonical receipt:

```text
state/formal_math/erdos257_period_noncollapse/prime_record_compensation_receipt.json
```

## Selected-tail depth result

The depth cohort contains the first sixteen funnel leaders, every earlier
prime-gap extreme, and the breadth outliers at source ranks 134 and 487.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/prime_record_compensation.py \
  --depth 200000 \
  --source-ranks 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,49,71,84,118,125,134,487 \
  --output state/formal_math/erdos257_period_noncollapse/prime_record_compensation_deep_receipt.json
```

Across 23 exact targets and 545 record events through rank 200,000:

- every record again recovered within two ranks;
- 544 recovered immediately;
- the sole delayed event was the already known rank-118 witness;
- maximum observed record height was 49;
- zero carry-recurrence, direct-floor, or block-identity violations occurred.

The dominant late record successors were again divisor-rich:
`2520`, `5040`, `27720`, `10080`, `55440`, `166320`, `83160`, `15120`, and
`20160`.

Deep receipt:

```text
state/formal_math/erdos257_period_noncollapse/prime_record_compensation_deep_receipt.json
```

These two selected-tail runs initially made `H=2` look viable.  They are not the
final mechanism decision: the exhaustive denominator census below supplies
exact distance-three and distance-four witnesses.

## Exhaustive rational census

The adversarial census scans every reduced `p/q` in `(0,1)` with `q<=500`,
classifies the greedy word through rank 5,000, and audits every new record on
every certified survivor.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/prime_record_recovery_census.py \
  --max-denominator 500 --depth 5000
```

It classified 76,115 reduced targets: 38,045 alive, 38,036 dead, and 34 exact
precision-boundary cases.  Across 343,251 record events:

- `H=1` fails first for `1/27` at rank 142; recovery occurs at 144;
- `H=2` fails first for `32/85` at rank 67; recovery occurs at 70;
- `H=3` fails for `71/182` at rank 74; recovery occurs at 78;
- no event required more than four ranks;
- every direct floor/prefix cross-check and every unrolled block identity passed.

Thus `H=4` is the exact surviving finite-census bound.  The canonical receipt is

```text
state/formal_math/erdos257_period_noncollapse/prime_record_recovery_census_receipt.json
```

## Large-denominator falsifier

To test whether `H=4` was an artefact of the small-denominator census, a
predeclared deterministic sample used seed 257, 10,000 reduced targets with
denominators between 501 and 1,000,000, and depth 5,000:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/prime_record_recovery_random.py
```

It certified 5,059 targets alive and 4,941 dead, and audited 45,731 record
events.  The worst recovery distance was only three, attained by `625/46396`
from rank 97 to rank 100.  No distance-five witness occurred, and all direct
carry and block-identity checks passed.  This is reproducible finite evidence,
not a substitute for the all-depth theorem.  Receipt:

```text
state/formal_math/erdos257_period_noncollapse/prime_record_recovery_random_receipt.json
```

## Mechanism decision and claim ceiling

The laws with recovery bounds one, two, or three are false and must not be used.
The surviving finite-census statement is:

> **Four-rank record compensation.** For the actual greedy carry of a suitable
> rational target, every new record `C_N` returns below the preceding record by
> rank `N+4`.

If proved from the actual support/divisor ancestry, it gives (5), kills the
expanding homogeneous mode, and constructs a rational support.  For `71/182`,
the even reduced denominator would force that support to be infinite.  The computation
does not prove the all-depth statement, does not select a privileged target, and
does not decide Erdős #257.  Its one-way contribution is to replace the failed
pointwise prime-gap laws by one exact, falsifiable, solution-producing
record-recovery throat with a surviving finite bound `H=4`.
