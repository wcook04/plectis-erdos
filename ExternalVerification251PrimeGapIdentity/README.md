# Erdős #251: unconditional prime-gap identity

This package exposes the exact analytic reduction from the normalized prime
series to the consecutive-prime-gap series. Lean proves the elementary bound
`p_n ≤ 1250(n+1)^4`, uses it to establish unconditional summability of both
series, and checks

```text
sum p_n / 2^(n+1) = 2 + sum (p_(n+1)-p_n) / 2^(n+1).
```

Consequently the two sums have exactly the same irrationality status. This is
an unconditional identity and exact reduction, not a proof that either sum is
irrational. The actual #251 obligation remains a prime-specific nonintegrality
or equivalent fractional-tail producer.

`Challenge.lean` imports only Mathlib and reproduces the four definitions
literally. `Solution.lean` transports the source summability and identity
theorems and assembles the unconditional irrationality equivalence. The
deliberate negative shifts the identity by the wrong integer and omits the
other endpoints, so Comparator must reject it.
