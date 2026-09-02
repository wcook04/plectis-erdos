# Erdős 249 pointwise-totient countermodel lab

## Mechanism question

The actual pure-dyadic throat is fixed-quotient anti-shadowing for the word
`phi(c+1), phi(c+2), ...`.  Before extending the million-basepoint scan, this
probe asks which arithmetic information an analytic proof must genuinely use.
Could positivity, evenness, the elementary bound `phi(n) <= n`, and the fact
that every letter is itself a totient value force endpoint escape?

## Infinite countermodel

No.  Take the constant word `a_H=2`.  It is pointwise totient-valued because
`phi(3)=2`; it is positive and even; and for every `c>=2` it obeys
`a_H <= c+H+1`.  Its exact binary block is

`B_H = 2(2^H-1)`.

Thus the fixed quotient `k=2` gives signed endpoint error

`E_H = B_H-k(2^H-1) = 0`

for every depth.  The expanding homogeneous mode is cancelled forever while
all pointwise conditions survive.  Lean proves the all-depth statement as
`exists_pointwiseTotientValued_permanent_endpointTrap`; the finite checker is
only a source-linked coordinate regression.

## One-way consequence

This permanently eliminates every anti-shadowing route that treats the
totient letters independently and uses only:

- membership in the image of Euler's totient;
- positivity and evenness;
- an individual upper envelope depending on the moving index.

The missing ingredient must couple the letters to their actual consecutive
arguments.  Candidate inputs therefore have to involve correlations such as
prime-factor changes across `c+H`, residue-class structure of consecutive
integers, or another genuinely multi-letter arithmetic obstruction.  A larger
endpoint scan or a sharper pointwise bound is not licensed as progress by this
result.

## Actual consecutive-word correction

The countermodel is legal only because `phi(3)=2` is reused independently at
every position.  It is not an admissible shifted tail of the actual sequence.
For every basepoint `c`, choose a prime

`p >= max(c+1,5)`

and set `H=p-(c+1)`.  Then the actual letter at that position is
`phi(c+H+1)=phi(p)=p-1>=4`, not `2`.  Lean checks both the existence of such a
letter (`exists_actualTotientLetter_ne_two`) and the resulting function-level
inequality (`actualTotientWord_ne_const_two`).

This is a genuine one-way narrowing: the expanding homogeneous constant-two
boundary mode is impossible for the actual consecutive-totient word at every
shift, not merely absent from a finite scan.  It does **not** exclude
inhomogeneous fixed-quotient boundary words; those are now the exact surviving
correlation-sensitive obstruction.

## Replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_pure_dyadic_pointwise_countermodel.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_pure_dyadic_pointwise_countermodel.py --check
```

The durable receipt is
`state/formal_math/erdos257_period_noncollapse/erdos249_pure_dyadic_pointwise_countermodel_receipt.json`.
It hashes the checker, reusable affine-word utility, Lean source, and this
analysis, and names the exact Lean declarations in its analytic bridge.
