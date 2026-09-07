# Erdős 251 polynomial-gap tail countermodel

## Mechanism question

The live `h=1` adjacent-small-mismatch consumer asks for two adjacent tail
shifts in `(-1,1)` with unequal gap digits.  Parity then forces the adjacent
gap difference to be exactly `+2` or `-2`.  Can positivity, evenness,
polynomial growth, unboundedness, and nonperiodicity of the gap word force
such certificates?

## Exact infinite countermodel

Define

```text
g_n = 2(n^2 + 4n + 2),
T_n = 2(n+4)^2.
```

Direct expansion gives

```text
T_(n+1) = 2*T_n - g_(n+1),
g_(n+1) - g_n = 4n + 10.
```

Thus `g_n` is positive, even, polynomially growing, strictly increasing,
unbounded, and nonperiodic.  The orbit `T_n` is integral at every index, so it
is a rational dyadic-tail orbit and all of its fixed tail shifts are integral.
But every adjacent gap difference is at least 10, hence never `±2`; the
`h=1` small-mismatch producer is absent at every index.

The finite telescoping identity for any dyadic tail recurrence gives

```text
T_0 = sum_(1 <= j <= N) g_j / 2^j + T_N / 2^N.
```

Here `T_N/2^N -> 0`, so the positive even gap series itself has the rational
value `T_0=32`.  This is an infinite countermodel, not a finite horizon.

## One-way consequence

No argument based only on positivity, parity, polynomial growth,
unboundedness, nonperiodicity, or the dyadic recurrence can supply the actual
prime-gap small-mismatch producer.  A successful #251 proof must use finer
arithmetic of consecutive primes or a genuinely external fractional-tail
theorem.  The countermodel is not the actual prime-gap word and does not
settle Erdős #251.

## Complementary obstruction (r2 revision, 2026-09-06)

The bounded rationalising perturbation of the *actual* prime gaps
(`BoundedPerturbationCountermodel.lean`) is not a rival word. It shows that
prefix, residue modulo `M`, and prime-number-theorem-scale cumulative growth
can coexist with a rational dyadic value. This polynomial orbit is the
explicit word that kills positivity, parity, polynomial growth, unboundedness,
and nonperiodicity as a force for the adjacent-small-mismatch producer.
Together they constrain arithmetic packages; neither is the actual prime-gap
series. Palomar headline remains
`ExternalVerification251PolynomialShiftCountermodel`.

`PrimeGapDyadicTail.lean` states exact declarations for the recurrence,
positivity, parity, strict monotonicity, integral tail states, and the global
absence of adjacent `±2` digits.

## Lean value of the series

`PolynomialGapSeriesValue.lean` proves the series value in Lean:

```text
hasSum_polynomialGapDyadicTerm : HasSum (fun n => g_(n+1) / 2^(n+1)) 32
tsum_polynomialGapDyadicTerm_eq : ∑' n, g_(n+1) / 2^(n+1) = 32
not_irrational_tsum_polynomialGapDyadicTerm
```

The proof is the exact rational telescope
`Σ_(j ≤ N) g_j / 2^j = 32 - T_N / 2^N` (`polynomialGap_partialSum_eq`) plus
`2(N+4)^2 / 2^N → 0` from Mathlib's polynomial-against-exponential limit; the
terms are nonnegative, so the partial-sum limit is the sum.  The `25/32` ratio
bound below is no longer load-bearing for the value.

## Executable symbolic receipt (superseded for the value)

The problem-local checker
`scripts/erdos251_polynomial_gap_countermodel.py` verifies the identities as
integer polynomial identities, not by sampling indices.  It also certifies
the exact terminal domination

```text
a_n = T_n/2^n,
a_(n+1)/a_n <= 25/32 < 1,
25(n+4)^2 - 16(n+5)^2 = n(9n+40) >= 0.
```

Thus `T_N/2^N -> 0`, closing the infinite telescope and giving the rational
series value `32`.  The durable machine receipt is
`state/formal_math/erdos257_period_noncollapse/erdos251_polynomial_gap_countermodel_receipt.json`;
it records hashes of this analysis, the checker, the research packet, and the
current Lean source.  Regenerate and verify it with:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/erdos251_polynomial_gap_countermodel.py --write
./repo-python formal_math/erdos257_period_noncollapse/scripts/erdos251_polynomial_gap_countermodel.py --check
```

## Correction, 2026-09-06 (appended; nothing above is rewritten)

**Priority and presentation.** The telescoping mechanism used here is the same
species as the construction Vjeko Kovač published on 15 April 2026 against the
variable-denominator conjecture printed under Erdős #251
(`On the Erdős problem #251`, Theorem 1;
`https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf`).
`docs/formal_math/palomar/prior_art_adjudication_2026_09_02.md:1508-1511` records
the adjudication verbatim: the `tsum = 32` countermodel "carries no priority
claim and must never be presented as a result about #251", and its role is
internal, namely that it kills our own `h = 1` adjacent-small-mismatch producer
as a consequence of coarse gap properties alone. Any presentation of a
telescoping countermodel as novel must cite Kovač.

**What it is and what it is not.** It is a counterexample to a proposal: the
proposal that positivity, evenness, strict growth, unboundedness and
non-eventual-periodicity of the gap word suffice to force the adjacent
small-mismatch certificates. The correct negative-knowledge label is
`counterexample_to_proposal`, never `closed` and never `dead`. It closes no
route on the actual primes, and `AdjacentMismatchDensityLab.md` measures the
event occurring at every tested offset over 6,841,648 actual primes, so the
countermodel does not transfer to them.

**Lean status.** The value is no longer a Python receipt. `HasSum` and the
`tsum` are Lean theorems, `PolynomialGapSeriesValue.lean:77, :89` with
`not_irrational_tsum_polynomialGapDyadicTerm` at `:106` in the release tree and
`:109` in this tree, and the superseded `25/32` ratio-bound receipt is recorded
in `claim_frontier_v1.json` as
`erdos251.polynomial_gap_countermodel_ratio_bound_receipt`, superseded by
`erdos251.polynomial_gap_countermodel_series_value_32`.
