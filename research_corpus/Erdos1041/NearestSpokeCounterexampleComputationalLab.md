# Erdős 1041: unique-nearest straight-spoke counterexample

## Claim boundary

`exists_two_roots_dist_sum_le_two_mul_geomMean` selects a nearest root and a
second-nearest root at a logarithmic critical point and proves that their two
distances have the sharp total bound `2r`. It does not prove that the straight
segments from the critical point to those roots remain in the strict unit
lemniscate.

The earlier quintic in `CriticalTwoRootProximity.lean` has one unsafe spoke, but
all five roots have the same modulus. A selection rule could therefore avoid
the bad spoke by resolving the distance tie differently. The computation here
tests that loophole, not the Erdős conjecture.

## Exact construction

Set

\[
p=\frac{999}{1000},\qquad
a=\frac{901}{902}p=\frac{900099}{902000},\qquad
u_\pm=\frac{-451\pm780i}{901}.
\]

Take the five roots

\[
a,\quad ip,\quad -ip,\quad pu_+,\quad pu_-.
\]

The identity `451²+780²=901²` gives `|u±|=1`. The last four roots have
modulus `p`, while `a<p`; hence `a` is the unique nearest root to the origin.
All five roots lie strictly inside the unit disk.

The reciprocal balance is exact:

\[
\frac1a+\frac1{ip}+\frac1{-ip}+\frac1{pu_+}+\frac1{pu_-}
=\frac{902}{901p}-\frac{902}{901p}=0.
\]

Thus the origin is a logarithmic critical point of the monic polynomial with
these roots.

At `z=a/10`, direct factored evaluation gives

\[
|f(a/10)|=
\frac{59875209312258922123673577759296931}
     {59708022487203200000000000000000000}
>1.
\]

So the straight segment from the critical point to the unique nearest root
leaves the strict unit lemniscate. Any broken straight line through the origin
that uses the nearest/second-nearest pair selected by the metric proof includes
this unsafe segment.

## Consequence

This is an exact counterexample to the proposed completion

> choose the two nearest roots supplied by the critical-point metric proof and
> join each to the critical point by a straight segment.

It is not a counterexample to Erdős 1041. It does not exclude curved descending
branches, a different critical point, component/collar stability, or a
Morse/Reeb strip construction. Its one-way effect is to make a curved or
topological containment producer essential; the metric theorem cannot close by
straight-spoke selection alone.

## Durable replay

```bash
./repo-python source-provenance://private-authoring-project/scripts/check_erdos1041_nearest_spoke.py
./repo-python source-provenance://private-authoring-project/scripts/check_erdos1041_nearest_spoke.py --check
```

The receipt
`source-provenance://private-authoring-project/receipts/erdos1041_nearest_spoke_counterexample_receipt.json`
records every rational root coordinate, squared norm, reciprocal sum, spoke
point, polynomial value, analytic falsifier, Lean consumer, and source digest.
Lean separately checks the reciprocal balance, unique-nearest squared-norm
comparison, and exact escape inequality.
