# Canonical Mersenne residue computational lab

## Exact frontier

`CyclotomicAnchoredKill.lean` reduces Erdős 249 to a fixed-basepoint arithmetic
normal form.  Write a prospective rational denominator as `2^c v`, with `v`
odd.  At a height `H` divisible by `phi(v)`, set

`M = (2^H - 1) / v`,

`Q(H,c) = sum_{j=0}^{H-1} phi(c+1+j) 2^(H-1-j)`,

`r = (-Q(H,c)) mod M`.

The exact remaining producer asks for an `H` with

`c + H + 1 < r < M - (c + H + 1)`.

There is no floating-point tail, free basepoint, prime-factor choice, or carry
trajectory left in this predicate.

## Discriminating probe

`scripts/check_canonical_mersenne_residue.py` scans odd `v`, dyadic exponents
`c`, and successive Euler multiples `H=t phi(v)`.  It separates the first
multiplier where the central interval is geometrically nonempty from the first
multiplier where the residue actually enters it.  This avoids mistaking the
trivial size obstruction `M <= 2(c+H+1)` for residue anti-concentration.  The
falsifier is an exact post-geometry-clear delay above the proposed threshold.

Canonical receipt command:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_canonical_mersenne_residue.py \
  --max-odd-denominator 200 \
  --max-dyadic-exponent 30 \
  --max-euler-multiplier 12 \
  --residue-delay-threshold 4 \
  --output state/formal_math/erdos257_period_noncollapse/erdos249_canonical_mersenne_residue_receipt.json
```

## Exact results

The canonical grid `1 <= v <= 200` odd and `0 <= c <= 30` tests 3,100
denominators through twelve Euler multiples.  Every pair reaches a central
residue, but `(c,v)=(27,1)` is an exact counterexample to post-clearance delay
at most four: the interval first becomes nonempty at `H=7`, while the residue
does not enter it until `H=12`.

The structurally targeted pure-dyadic extension `v=1`, `0 <= c <= 2000`
through `H=30` goes further.  All 2,001 pairs escape, but 61 have residue delay
above five and the maximum delay is twelve, attained at `c=349`: geometry
clears at `H=10`, while the endpoint trap survives through `H=21` and escapes
at `H=22`.  Thus the uniform constants four and five are both decisively
eliminated after the trivial empty-interval phase has been removed.  The next
question is not whether to try a slightly larger constant; it is whether the
pure-dyadic delay is unbounded and which binary-totient words create the nested
endpoint traps.

Durable no-go receipt:

`state/formal_math/erdos257_period_noncollapse/erdos249_pure_dyadic_residue_delay_nogo_receipt.json`

## Analytic consequence

A universal bounded post-clearance delay theorem, combined with deterministic
Mersenne growth, would feed the Lean equivalence and prove irrationality.
Finite success only supports such a theorem.  An exact delay violation
permanently eliminates that particular residue constant and identifies a
denominator-specific endpoint trap whose genealogy must be explained.

## Divisor centrality is strictly one-way

There is a tempting shortcut from the pure-dyadic axis to the full odd
denominator problem: prove that the residue is central modulo `2^H-1`, then
reduce it modulo `M=(2^H-1)/v`.  Exact modular geometry points in the opposite
direction.  If positive `M` divides `N` and

`B < z mod M < M-B`,

then `B < z mod N < N-B`.  Indeed, write
`z mod N = jM + (z mod M)` with `0 <= j < N/M`.  The lower endpoint is
immediate and the upper endpoint is at most
`(N/M-1)M + (M-B-1) < N-B`.

The converse fails on the actual totient block at the first small witness
found by `scripts/check_mersenne_divisor_centrality.py`.  For
`(c,v,H)=(0,3,6)`, one has `Q(6,0)=82`, `B=7`, `N=63`, and `M=21`:

```text
(-82) mod 63 = 44   (central: 7 < 44 < 56)
(-82) mod 21 = 2    (endpoint trapped)
```

Thus quotient-modulus escape is a genuinely stronger certificate and always
implies pure-dyadic escape at the same height, while pure-dyadic escape cannot
be projected down to arbitrary odd denominators.  Any proof of the full
Mersenne residue supply must retain `v`-specific arithmetic.
