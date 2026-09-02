# Erdős 1041: all straight root-pair segments can fail

## Discriminating question

The earlier exact quintic shows that the two roots selected by the
critical-point metric theorem cannot always be joined to that critical point
by straight spokes. It leaves open a simpler fallback:

> Must some pair of roots have its direct straight segment inside
> `|f| < 1`?

This is a genuinely different mechanism from the Newton/Reeb route. If true,
the path problem would reduce to a root-pair selection inequality. If false,
every general proof needs curved or topological containment.

## Computation that exposed the structure

A pair-product search first maximized the elementary segment majorant

\[
 |z-z_i|\,|z-z_j|\prod_{k\ne i,j}
   \max(|z_i-z_k|,|z_j-z_k|).
\]

The first obstruction was already the nearly unit equilateral triple. That
numerical observation was used only to select an exact algebraic family; it is
not proof evidence.

Put

\[
  r=\frac{99}{100},\qquad f(z)=z^3-r^3,
\]

and write the roots as `r`, `rω`, `rω²`, where
`ω²+ω+1=0`. All roots have modulus `r<1`.

For any two distinct cube roots of unity `u,v`, the missing third root `w`
satisfies `u+v=-w`. Their midpoint is therefore `-rw/2`, and

\[
 f\!\left(\frac{ru+rv}{2}\right)
 =\left(-\frac{rw}{2}\right)^3-r^3
 =-\frac98r^3.
\]

The exact integer inequality

\[
 9\cdot99^3>8\cdot100^3
\]

gives `9r³/8>1`. Hence the midpoint of every distinct root pair is outside
the strict unit lemniscate. Every straight segment between roots fails.

## One-way consequence

This eliminates the entire proof geometry

> select two roots and use their Euclidean chord.

It is stronger than the prior unique-nearest-spoke counterexample: it does not
depend on a critical point, a nearest-root rule, or a particular spoke. It
forces any successful proof to leave the single-chord geometry, but it does
not by itself force curvature.

It does **not** refute Erdős #1041. The same cubic has an explicit short
two-segment root connection inside `|f|<1`.

## The surviving critical-point hub is visible in the same cubic

The chord failure is not a near-counterexample to the conjecture. Join `r` to
`rω` by the two radial segments `r → 0 → rω`. On either segment, write
`z=sr` or `z=srω`, with `0≤s≤1`. In both cases

\[
 |f(z)|=r^3(1-s^3)<1
\]

away from the root endpoint, and the total length is `2r=99/50<2`.
Rotation gives the same connection for every root pair. Thus the exact
counterexample simultaneously kills the direct-chord mechanism and opens a
**critical-point hub** mechanism: a short path may enter a protected critical
point along one safe spoke and exit along another. The contrast is exact:
one straight segment can fail while a broken line of two straight segments
succeeds. Generalizing the existence and metric budget of such hubs is a
concrete alternative to global direct-chord selection.

This is a robust family, not an isolated rational accident. For every
`0<r<1` with `r³>8/9`, all three root chords of `z³-r³` fail at their
midpoints. Nevertheless, the critical-point hub has length `2r<2` and stays
inside the strict lemniscate for every `0<r<1`. The exact radius `99/100` was
selected only to make the strict midpoint escape inequality rational and
kernel-cheap.

This hub construction is an ordinary exact algebraic argument recorded by
the checker; it is not yet a Lean declaration and is not promoted to proof
authority in the research packet.

## Durable authority and replay

Lean checks the root locations, the root equations, and all three midpoint
escapes in
`ErdosProblems.Erdos1041.CriticalTwoRootProximity`:

- `allStraightCubic_roots_in_unitDisk`;
- `allStraightCubic_roots`;
- `allStraightCubic_every_pair_midpoint_escapes`.

The independent exact checker works in
`Q(ω)=Q[x]/(x²+x+1)` and records all three pair certificates:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos1041_all_straight_segments.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos1041_all_straight_segments.py --check
```

Its canonical output is
`state/formal_math/erdos257_period_noncollapse/erdos1041_all_straight_segments_counterexample_receipt.json`.
