# Erdős 68: the threshold failures have an unexplained parity cutoff

## Exact finite finding

The tail-free predecessor-gap threshold is exactly

```text
D_m + A_m >= 2/m.
```

It fails outright when `D_m = -1`, holds outright when `D_m >= 1`, and has a
separate thin boundary case `A_m >= 2/m` when `D_m = 0`.  The source-bound
scalar-spectrum receipt lists all eleven `D_m=-1` events through `m = 300000`:

```text
5, 9, 23, 60, 470, 3026, 19222, 27472, 30324, 35366, 65768.
```

Therefore:

* the only odd `D_m=-1` events are `5, 9, 23`;
* the only prime `D_m=-1` events are `5, 23`;
* every `D_m=-1` event after `23` is even.

The certified unit carries `D_m=0` occur at

```text
52, 591, 1030, 1407, 1438, 2164, 4258, 10991, 21236.
```

The digit-law receipt checks the successor-digit lower bound at every one of
them, and every row certifies `A_m >= 2/m`.  In particular the odd unit carries
`591, 1407, 10991` do not create hidden threshold failures.  Combining the two
branches, there is no full threshold failure at an odd index from 25 through
300000.

`erdos68_prime_threshold_parity.py` independently recomputes the correctly
indexed exact `Fraction` recurrence on a prefix before filtering the complete
certified list.  This also explains why a checker which stopped at the first
prime failure discarded the strongest visible pattern.

## Target-producing conjecture

The exact theorem suggested by the computation is

```text
Odd m and 25 <= m  ->  D_m + A_m >= 2/m.
```

Equivalently, every odd `m >= 25` would satisfy the pure integer predecessor
threshold already consumed by `PrimeZeroBranch.lean`.  Its two proof
obligations are

```text
D_m != -1,
D_m = 0 -> A_m >= 2/m.
```

This is not merely a classification result: every prime `p >= 29` is odd, so
the full theorem plus Euclid would give cofinally many threshold certificates
and hence prove the irrationality of

```text
sum_(n>=2) 1/(n!-1).
```

The odd-index threshold theorem is not proved here.  No local expanding-map argument can
prove it for arbitrary rational seeds; any proof must use the arithmetic of
the distinguished factorial-gap prefix.  The next discriminating step is to
write `D_m = -1` in the carry-congruence normal form and reduce it modulo the
odd denominator of the prefix at odd `m`, looking for the obstruction that
disappears at even indices.

`PrimeThresholdParity.lean` packages the exact consumer.  It proves that a
carry at least one meets the threshold automatically unless it is a unit
carry, in which case the successor-gap margin is sufficient.  It then proves
that these two obligations at all sufficiently large odd indices imply
irrationality directly; cofinal odd indices make a prime-supply theorem
unnecessary.

There is also a completely discrete sufficient interface:

```text
Odd m, 25 <= m -> b_m >= 1,
Odd m, 25 <= m, b_m = 1 -> b_(m+1) >= 3.
```

The second implication gives
`A_m > b_(m+1)/(m+1) >= 3/(m+1) >= 2/m`.  Every certified
odd unit carry satisfies it with a wide margin.  This adjacent-carry form is
the preferred congruence/finite-state proof target.

## Replay

```sh
./repo-python formal_math/probes/erdos68_prime_threshold_parity.py
./repo-python formal_math/probes/erdos68_prime_threshold_parity.py --check
```

The receipt is finite evidence through `300000`, not a cofinal parity theorem
and not an irrationality proof.

Focused replay: `lean_fast_build.py --jobs 2
ErdosProblems.Erdos68.PrimeThresholdParity`, exit `0` on 2026-08-24.

## Correction, 2026-09-06 (corrective-integration desk, Erdős #68)

Scope note, appended without changing anything above.

The eleven `D_m = -1` events listed here are certified only through
`m = 300000`, and the odd-index cutoff after `23` is a finite pattern over
that range. It is not evidence for the eventual odd-index threshold, and the
Lean module says so in the release candidate: at release-final HEAD
`8a28b2521e` the header of `ErdosProblems/Erdos68/PrimeThresholdParity.lean`
reads "the conditional odd-threshold producer interface" and adds that the
eventual odd-index threshold is a conjectural hypothesis and that the file
does not record a finite computation as evidence for an eventual statement.
The copy of that module in this tree still reads "the exact odd-threshold
producer interface". The candidate tree carries the honest label and this tree
is behind; the sync is recorded in
`docs/strategy/staging/rapid_breakout/audit/patches/reconcile_68.json` under
`conflicting_variants`.

Precise label for the finite pattern: `empirical_deprioritisation`. It ranks
odd indices below even ones as a search target through the certified horizon,
and it excludes nothing beyond `m = 300000`. The Lean consumer
`irrational_factorialGapSeries_of_eventual_odd_threshold`
(`PrimeThresholdParity.lean:100`) is the only kernel-checked object here, and
it is an implication whose hypothesis is unproved.
