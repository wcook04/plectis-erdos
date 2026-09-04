# Erdős #251: exact dyadic-tail classifier and one-schedule criterion

The package now starts from the complete rationality classifier for any real
integer-digit dyadic orbit.  One positive integral tail difference is already
equivalent to rationality of the initial state:

```text
not Irrational (T 0)
  iff
there exist h > 0 and N with T(N+h) - T(N) integral.
```

Negating and propagating this statement gives the exact cofinal form:
irrationality is equivalent to finding a nonintegral tail difference beyond
every basepoint for every fixed positive shift length.  These two endpoints
are the structural source of the order-lattice and diagonal compressions
below; they were previously explained in the paper but not exposed to
Comparator.

For a rational integer-digit dyadic recurrence, the first compared theorem
classifies every integral shift length exactly:

```text
tailShift T h N is integral
  iff orderOf (2 mod denominator(T N)) divides h.
```

Thus Euler's totient is only a possibly nonminimal witness; the true invariant
is the multiplicative-order lattice.

The order theorem then proves the general quantifier-compression mechanism. Any
positive schedule which eventually exceeds every basepoint and is eventually
divisible by every positive shift length decides irrationality using only its
diagonal points.

For a real orbit satisfying

```text
T(N+1) = 2 T(N) - g(N+1),  with g(N) integral,
```

the complete rationality obstruction can be tested on one predetermined
sequence. Let `L_j = lcm(1,...,j)`, with `L_0 = 1`. The compared theorem proves

```text
Irrational (T 0)
  iff
for every j, T(2 L_j) - T(L_j) is nonintegral.
```

The final theorem selects the smallest canonical schedule used in the paper.
Thus a double quantifier over all positive shift lengths and all basepoints is
replaced by the single diagonal `(N,h)=(L_j,L_j)`. The result is an exact
abstract criterion; it does not prove the required nonintegrality for the
actual consecutive-prime-gap orbit and therefore does not solve Erdős #251.

The factorial diagonal is a valid but pointwise larger corollary of the generic
schedule theorem, so it is not duplicated as a positive endpoint. The
deliberate negative substitutes it for the LCM theorem and omits the order and
generic-schedule declarations, so Comparator must reject the package.
