# Forced-doubling charge at a hypothetical final `1/21` skip

Status: exact conditional identity plus finite adversarial audit.  No Lean
file is changed here.  This note starts from the exact actual-prefix bridge
`S_R = Q_(2R) + H_R`.  Here `Q` uses the divisor-count word
`supportCoeff A`, not the Boolean membership word; repeated lower-rank
geometric terms are already present on both sides of that bridge.

## 1. The block charge

Let `A` be the actual greedy support for `1/21`, and assume that `L` is a
final greedy skip.  Thus every index in `(L,2L]` is selected.  Set

```text
D_L = A intersect {2,...,L},
B_L = floor(2^(2L)/21) - 2^L floor(2^L/21),
J_L = sum_(L<n<=2L) 2^(2L-n) supportCoeff(D_L,n).
```

The finite quotient and fractional-mass objects are defined in
[`BooleanMobiusLocalRepair.lean:78-86`](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean#L78),
and their exact scaled decomposition is proved at lines 217--232.  The
denominator-21 defect `Q_N` is defined in
[`BooleanMobiusCarry.lean:1717-1757`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1717).

The target lift is exactly

```text
B_L = floor(2^L (2^L mod 21)/21).                          (1)
```

For `L<n<=2L`, a selected proper divisor of `n` cannot itself lie in
`(L,n)`: it would exceed `n/2`.  Since `n` itself is selected, this gives

```text
supportCoeff(A,n) = 1 + supportCoeff(D_L,n).                (2)
```

Expanding the dyadic prefix numerator from `L` to `2L` now gives the exact
doubling-scale identity

```text
Q_(2L) = 2^L (Q_L-1) + B_L + 1 - J_L.                      (3)
```

This is independent of the existing one- and six-step recurrences: the only
new load is the old-divisor incidence inside the forced selected block.  The
all-selected contribution is `2^L-1`; the target splits into its old prefix
plus `B_L`; the remaining contribution is exactly `J_L`.

## 2. Exact consequences and limits

The actual-prefix boundary bridge requires `Q_(2L)>=1` at a final skip.
Applying it to (3) gives the necessary integer budget

```text
J_L <= 2^L(Q_L-1)+B_L.                                    (4)
```

Equation (4) isolates the exact missing theorem: a lower bound on an
old-divisor charge, derived from the actual skipped-prefix condition.  In
particular, if `Q_L=1`, finality forces `J_L<=B_L`.

There is no residue-only parity law.  From (3), for `L>0`,

```text
Q_(2L) = B_L + 1 - J_L (mod 2).                            (6)
```

The denominator period controls `B_L`, but not `J_L`.  Nor does
`localFractionMass(D_L,2L)` determine `J_L`: the former is a sum of the
fractional parts of the quotient terms, while `J_L` is an integer weighted
count of their divisor incidences in one specified block.  Therefore neither
a period-six residue nor fractional mass alone closes (4).

## 3. Exact adversarial audit

[`actual_prefix_forced_block_audit.py`](../../scripts/actual_prefix_forced_block_audit.py)
computes the rational greedy word with `Fraction`.  For every actual skipped
rank `L<=384`, it preserves the real greedy prefix through `L`, forces all
ranks `(L,2L]` selected, and checks (3) with integer arithmetic.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/actual_prefix_forced_block_audit.py --max-l 384
```

Among 192 actual skipped ranks, none has a forced continuation with
`Q_(2L)>=1`.  The only nonnegative forced defect is

```text
L=6, Q_L=1, B_L=3, J_L=4, Q_(12)=0.
```

Every other checked actual skip already makes the forced prefix defect at
`2L` negative, so it cannot be final.  This is finite evidence, not a proof:
the remaining global task is precisely to prove a uniform violation of (4),
rather than to infer one from target residue, parity, or fractional mass
after divisor labels have been discarded.
