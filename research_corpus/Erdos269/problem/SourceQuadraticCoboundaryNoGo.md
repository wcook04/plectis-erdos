# Source-quadratic coboundary probe for Erdős #269

## The specified nonlinear class

An exact integral normalized tail would give integer states satisfying

`d_a=b_a C_a-C_(a+1)`.

The landed source-linear checker eliminates every phase-conditioned rational
linear functional of the nine direct source coordinates.  The next
mathematically specified enlargement is the full polynomial class of total
degree at most two in the eight nonconstant coordinates:

- scale and scale squared;
- the three cumulative pair counts;
- the three boundary pair counts.

The constant, every linear coordinate, every square, and every cross term are
included.  Coefficients may depend independently on the actual radix phase
`2`, `6`, `10`, or `30`.  This is a closed 180-parameter class, not a feature
list enlarged until it interpolates a chosen prefix.

## Exact decision protocol

The checker constructs the actual radix and digit word, substitutes the
phase-conditioned quadratic potential into the coboundary equation, and forms
an integer linear system.  The reusable certificate layer compares the exact
coefficient and augmented ranks.  If they differ, it extracts a primitive
integer left-null vector `lambda` and independently checks

`lambda^T M=0`,  `lambda^T d != 0`.

Such a separator eliminates the whole declared quadratic class.  Consistency
of a finite system would not establish an all-scale potential and would be
reported only as survival evidence.

## Exact obstruction

There are 45 distinct monomials before phase splitting and 180 independent
phase-conditioned coefficients.  On the actual initial source word, the first
116 equations have coefficient rank 115 and augmented rank 116.  The checker
extracts a primitive integer left-null vector supported on all 116 equations;
its largest coefficient has 788 bits.  Exact replay gives zero against every
one of the 180 coefficient columns and a nonzero pairing against the actual
digit word.

Therefore no potential in the full declared total-degree-two class satisfies
the source coboundary equation.  The modular rank pass used to locate equation
116 is discovery only; the stored certificate and rational replay carry the
claim.

## Claim boundary

This exact no-go cannot exclude cubic or nonpolynomial source
potentials, unbounded phase memory, or an integral carry beginning only after
a later state.  It is useful precisely because it decides the first natural
nonlinear extension without confusing a longer orbit scan with a theorem.
