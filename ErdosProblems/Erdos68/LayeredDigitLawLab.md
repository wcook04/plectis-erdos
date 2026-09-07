# Erdős 68: the corrected second-layer coordinate

## Claim boundary

The finite second-layer identity is Lean-checked. The infinite-floor comparison
is certified exactly through `m = 500`, but no cofinal theorem has been proved.
Erdős #68 remains open.

This replaces the earlier version of this lab, which used the noncanonical
“eventually maximal” boundary for rational factorial expansions. With the floor
convention used by `CanonicalFactorialDigits.lean`, every rational number has an
eventually **zero** digit tail.

## The exact finite identity

Write

```text
P_m  = Σ_{2≤n≤m} 1/(n!−1),
P²_m = Σ_{2≤n≤m} 1/(n!(n!−1)),
E_m  = Σ_{2≤n≤m} m!/n!,
N_m  = ⌊m!P_m⌋+1,
b_m  = mN_(m−1)+1−N_m.
```

The elementary split

```text
1/(n!−1) = 1/n! + 1/(n!(n!−1))
```

gives `m!P_m = E_m + m!P²_m`, with integral `E_m` and
`E_m = mE_(m−1)+1`. Therefore

```text
⌊m!P²_m⌋ − m⌊(m−1)!P²_(m−1)⌋ = m−1−b_m.       (∗)
```

`SecondLayerDigit.lean` proves this exactly. It also proves that a rational
number cannot have an eventually maximal canonical factorial-digit tail.

The theorem is about finite prefixes. To replace `P²_m` by

```text
S₂ = Σ_{n≥2} 1/(n!(n!−1))
```

one must prove that the positive scaled tail does not cross the next integer at
both scales `m!` and `(m−1)!`. The returned desk-6 argument only established
“scaled tail `< 1`”; that is insufficient when the finite scaled prefix lies
within the tail length of its next integer.

## Exact no-crossing computation

The repaired probe compares the exact distance

```text
A_m = (⌊m!P²_m⌋+1) − m!P²_m
```

with the strict elementary tail bound

```text
m! Σ_{n>m} 1/(n!(n!−1)) < 1/m!.
```

Using exact `Fraction` arithmetic for every prefix through `m = 500`:

- `(∗)` has zero failures;
- no negative strict-successor carry occurs;
- every no-crossing comparison succeeds;
- the smallest ratio `A_m / (1/m!)` is `2`, at `m = 2`;
- the only unit carry in this range is `m = 52`, and `(∗)` gives the
  second-layer digit `50 = m−2` there.

Thus the formula returned by desk 6 survives a stronger falsifier, but the
missing cofinal floor-stability theorem is real and is now explicit rather than
hidden in a floor inference.

## Correct rational boundary

Rationality of the original series forces `b_m = 1` eventually. Wherever the
second-layer floors are stable at two consecutive scales, `(∗)` then gives

```text
d_m(S₂) = m−2.
```

So `d_m(S₂) ≠ m−2` cofinally is a valid sufficient target once the necessary
floor comparison is supplied; `m−2−c_(m+1)` from the old backwards finite-carry
convention is not the canonical rational boundary.

The finite addition identity

```text
d_m(S) = (1 + d_m(S₂) + c_(m+1)) mod m
```

still checks digitwise. Its backwards carry was initialized at a finite cutoff,
so it is a diagnostic of the computed digit block, not an infinite-tail
rationality criterion.

## Continued-fraction control

The independent continued-fraction measurement is unchanged: 2,899 partial
quotients inside the validated precision horizon give Gauss–Kuzmin `χ² = 1.9`
on nine degrees of freedom and Khinchin geometric mean `2.6777` versus
`2.6854520`. This remains finite genericity evidence only.

## Replay

```sh
./repo-python formal_math/probes/erdos68_layered_digits_and_continued_fraction.py
```

The probe exits nonzero on any finite-prefix identity failure, negative carry,
floor-stability failure, digit-range failure, addition failure, or predeclared
continued-fraction statistic failure.
