# Möbius-sign Lambert Booleanisation: exact no-go

This audit tests the proposed subtraction

```
N_mu = 1/2 + P_mu,
```

where `N_mu = {d >= 2 : μ(d) = -1}` and
`P_mu = {d >= 2 : μ(d) = 1}`. The proposed construction asked whether a set
`R ⊆ N_mu` could have Mersenne value equal to `P_mu`, so that `N_mu \ R`
would have value `1/2`.

## Verdict

**Falsified as stated.** `P_mu` already is a normalized Boolean Mersenne
support with precisely that value. Global support coding is injective, whereas
`P_mu` and `N_mu` are disjoint and `6 ∈ P_mu`. Therefore no subset of
`N_mu` can have the value of `P_mu`.

This is not a failure of an implementation or a finite search. It rules out
every possible infinite `R` in the proposed support-restricted achievement
set.

## Exact formal proof of the no-go

Lean proves the sign-separated identity

```
sum(N_mu) = 1/2 + sum(P_mu)
```

as `tsum_negativeMobius_eq_half_add_positiveMobiusTail`
([`MobiusSignSupportNoGo.lean:109-140`](../../Erdos257PeriodNoncollapse/MobiusSignSupportNoGo.lean#L109)); the underlying signed identity is
`tsum_moebius_div_two_pow_sub_one_eq_half`
([`MersenneLambertLadder.lean:586-595`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L586)). The same module proves the positive tail has the nonzero term at
`d=6` ([`142-168`](../../Erdos257PeriodNoncollapse/MobiusSignSupportNoGo.lean#L142)).

Suppose `R ⊆ N_mu` and

```
erdosSupportSeries 2 R = erdosSupportSeries 2 P_mu.
```

Both supports omit `0`. The exact injectivity theorem
`erdosSupportSeries_injective_normalized` gives `R = P_mu`
([`GreedyAchievementSet.lean:1547-1562`](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L1547)). But a number cannot have both Möbius signs `-1` and `1`, while `6 ∈ P_mu`; hence `P_mu` is not a subset of `N_mu`. Contradiction.

This also exposes the error in calling `R` “the unique representing subset of
the negative support”: uniqueness is global, and identifies the only Boolean
representation as `P_mu` itself, which is forbidden by the restriction.

## Restricted greedy criterion

The restricted computation is still useful as an independent finite fatal-gap
receipt. Let `S` be any allowed set of exponents, with
`w_n = 1/(2^n-1)`, and let `y >= 0`. Process allowed exponents in increasing
order, taking `n ∈ S` exactly when the current residual is at least `w_n`.
For the selected prefix through `m`, write its residual as `r_m`, and set

```
T_S(m) = sum_{n in S, n>m} w_n.
```

Strict superincreasingness, formalized by `mersenneTail_lt_weight`
([`GreedyAchievementSet.lean:178-181`](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L178)), yields the exact restricted criterion:

```
y is a Boolean S-subsum  <=>  r_m <= T_S(m) for every m.       (G)
```

The forward implication is the usual greedy-prefix comparison. Conversely,
the inequalities give `0 <= r_m <= T_S(m)`, and `T_S(m) -> 0`; the selected
partial sums therefore converge to `y`. A strict violation `r_m > T_S(m)` is
a fatal gap. This criterion is a mathematical derivation from the cited
superincreasing theorem; it is not separately formalized for arbitrary `S`.

## Exact computation receipt

The audit script is
[`lambert_booleanisation_audit.py`](../../scripts/lambert_booleanisation_audit.py).
It uses a linear Möbius sieve and Python `Fraction` only—no floating point.
At a target enclosure horizon `32` and restricted decision depth `16`, run:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/lambert_booleanisation_audit.py --horizon 32 --depth 16
```

The receipt reports:

* `mu_6 = 1` and disjoint sign classes;
* forced negative-sign restricted choices `{7,11,13}` through depth `16`;
* no ambiguous comparison; and
* `fatal_gap_certified = true`.

The exact enclosure used is

```
P_32 <= P_mu <= P_32 + 2^-31,
T_N(16) <= sum_{17 <= n <= 32, mu(n)=-1} w_n + 2^-31.
```

The script compares these rational quantities exactly and certifies that the
lower residual after `{7,11,13}` exceeds the displayed upper bound for the
remaining negative-sign tail. A deeper independent run at `--horizon 256
--depth 128` again reports a forced, ambiguity-free fatal gap. Large fractions
are emitted as canonical SHA-256/bit-length receipts to keep the JSON small;
the script is the exact reproducible source of each fraction.

The computation is corroboration only. The injectivity proof above is the
complete infinite no-go.

## Symmetric and adjacent variants

### Reverse sign swap

Trying to represent `N_mu` by a subset of `P_mu` is immediately impossible by
mass. `N_mu` contains `2` and `3`, so its mass is at least
`1/3 + 1/7 = 10/21`. Every member of `P_mu` is at least `6`, hence its entire
mass is strictly below the full Mersenne tail after `5`, which is strictly
below `w_5 = 1/31` by the same superincreasing theorem. Thus the allowed
positive-sign reservoir is far too small even before injectivity is used.

### Other Lambert rungs

The sign-support subtraction mechanism is therefore dead, not merely stalled.
The remaining Lambert directions do not reduce to equality of two Boolean
Mersenne subseries:

* The primitive rung `primWeight = phi * mu` has divisor sum `phi`, but is
  unbounded on primes ([`MersenneLambertLadder.lean:248-325`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L248)); it is a multiplicity/carry problem, not a sign-subset problem.
* The totient rung has positive multiplicities and value `2`, not Boolean
  coefficients ([`572-585`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L572)).
* The squared Möbius lens changes the denominator to squared Mersenne factors
  ([`663-678`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L663)); it is not a Boolean #257 support identity.

These routes remain logically open only if they use a genuine carry or
multiplicity Booleanisation that does **not** assert equality between two
distinct Boolean Mersenne supports. No such Booleanisation is constructed or
certified here.
