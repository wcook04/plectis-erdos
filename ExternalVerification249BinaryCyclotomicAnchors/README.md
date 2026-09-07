# Erdős #249: clean binary cyclotomic anchors

For every positive ray multiplier `h` and every threshold, the binary
cyclotomic layers `|Φ_(h*q)(2)|` contain a remote prime factor `p` at a prime
index `q` such that

```text
gcd(p, h*q) = 1,   p ∣ |Φ_(h*q)(2)|,   h*q ∣ p - 1.
```

The same arithmetic gives unbounded prime-divisor support on every positive
ray.  These are unconditional source-backed theorems.

The exact claim ceiling is also included: cofinal clean anchors carrying a
finite tail-discrepancy certificate are equivalent to irrationality of the
binary totient series.  The clean prime factors are unconditional; the
certificate field is the missing producer, so the equivalence is not a proof
of irrationality.

The final declaration fixes the support-only limitation.  If the binary totient
series were rational, some positive period ray would have eventually integral
tail differences while the binary cyclotomic layers on that same ray would
still have unbounded prime divisors.  Thus unbounded support alone cannot
contradict the rational period law; a carry- or phase-escape bridge is still
needed.  This conditional implication neither constructs a rational example
nor proves Erdős Problem #249.

`Challenge.lean` imports only Mathlib and gives literal definitions.
`Solution.lean` transports the four exact source theorems from
`ErdosProblems.Erdos249.CyclotomicAnchoredKill`.  The deliberate-negative
solution adds an extra hypothesis to the clean-anchor theorem and must be
rejected.

The positive configuration permits exactly `propext`, `Quot.sound`, and
`Classical.choice`, and enables NanoDa.  Comparator replay, public source
promotion, Palomar review, and submission are separate gates and are not
claimed here.
