# Erdős #251: the actual prime-gap rational-tail bridge

This package exposes the exact chain that begins if the actual consecutive
prime-gap dyadic series is not irrational.

First, non-irrationality produces a rational value `S` whose algebraic state

```text
T_S(N) = 2^(N+1) (S - the first N+1 prime-gap terms)
```

is exactly the corresponding scaled real tail at every depth.  Independently
of that hypothesis, `T_S` satisfies the actual prime-gap recurrence.

The denominator of every rational `S` then selects one positive fixed shift
`h` whose differences `T_S(N+h)-T_S(N)` are integral for all sufficiently
large `N`.  Actual prime-gap nonperiodicity proves that this same shift cannot
remain in the open interval `(-1,1)` eventually.  This is an exact
denominator-collapse and obstruction theorem for the actual gap word, not an
abstract recurrence surrogate.

The boundary is equally exact.  The package does not prove eventual smallness
for the denominator-selected shift, so it does not contradict the obstruction
or prove the prime-gap series irrational.  The authoritative #251 paper treats
this bridge and identifies the missing input as genuinely finer control of
actual consecutive-prime tail fractional parts.

The deliberate negative changes the open interval to a closed one and omits
the other three endpoints, so Comparator must reject it.
