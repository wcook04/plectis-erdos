# Adjacent asymptotic directions have no metric defect

## Status

This is an all-degree Euclidean theorem for the tied Newton-face programme.
Once a hub `c` lies in the radius-`R` disk and two **adjacent** `n`-th-root
directions bracketing `arg c` have contained arms to their radius-`R` points,
the broken line already has length at most `2R`.  No separate scattering-length
estimate is needed.

The ellipse algebra is Lean checked in `TiedNewtonFaceAdjacentEllipse.lean`.
What remains open is containment of one such adjacent arm pair and its outward
tails.  This theorem does not prove that containment and does not solve Erdős
#1041.

## 1. The regular-polygon ellipse cover

Scale first to `R=1`.  Let two adjacent `n`-th roots of unity have arguments
`-delta,+delta`, where

```text
delta=pi/n <= pi/3.                                      (1)
```

Their midpoint is `(cos delta,0)` and their displacement from that midpoint is
vertical with length `sin delta`.  The ellipse with these foci and major axis
`2` therefore has semiaxes

```text
vertical: 1,                 horizontal: cos delta,
```

and equation

```text
(x-cos delta)^2/cos^2(delta) + y^2 <= 1.                 (2)
```

Take a point `z=rho exp(i theta)` in the intervening sector, so
`0<=rho<=1` and `|theta|<=delta`.  The left side of (2) is a convex quadratic
in `rho`, so it is at most the larger endpoint value.  At `rho=0` it equals
one.  At `rho=1`, because `cos theta>=cos delta>=1/2`, (2) reduces to

```text
cos(theta)-cos(delta) <= cos(delta) cos(theta),           (3)
```

and (3) follows from

```text
cos(theta)(1-cos(delta)) <= 1-cos(delta) <= cos(delta).
```

Thus the whole closed unit-disk sector lies in the adjacent-focus ellipse.
Restoring scale gives the exact theorem:

> If `|c|<=R` and `omega_j,omega_(j+1)` bracket the argument of `c`, then for
> every `n>=3`,
>
> ```text
> |R omega_j-c| + |R omega_(j+1)-c| <= 2R.                (4)
> ```

The origin spends equality.  Away from the ellipse boundary the inequality is
strict.

## 2. Lean kernel

The formal proof avoids trigonometric normalization.  Put the foci at
`(b,+f)` and `(b,-f)`, with

```text
R^2=b^2+f^2,                  R<=2b.                      (5)
```

For a sector point `(rho u,rho v)`, `u^2+v^2=1` and the angular bracket is
`b<=Ru`.  The inequality `R<=2b` implies

```text
0 <= Ru-b <= bu.                                        (6)
```

Squaring (6), using `rho<=R`, and expanding yields

```text
R^2(rho u-b)^2+b^2(rho v)^2 <= R^2 b^2,                 (7)
```

which is exactly ellipse membership without division.

For completeness, if `d_1,d_2` are the focal distances and
`X=rho u-b`, `Y=rho v`, then

```text
d_1^2=X^2+(Y-f)^2,            d_2^2=X^2+(Y+f)^2.
```

The difference between the square of the remaining product budget and
`(d_1d_2)^2` is

```text
(2R^2-X^2-Y^2-f^2)^2-(d_1d_2)^2
 =4(R^2b^2-R^2X^2-b^2Y^2),                              (8)
```

nonnegative by (7).  Hence `d_1d_2` fits the remaining budget, and expanding
`(d_1+d_2)^2` proves (4).  Lean checks (6)--(8) and their composition in:

```text
sector_ellipse_quadratic
bracket_right_inequality
ellipse_distance_sum_le_two_mul
adjacent_sector_distance_sum_le_two_mul
```

## 3. Consequence for the tied-face residual

The preceding trace checkpoints force a lexicographically negative critical
saddle and a two-ended safe component.  Their remaining metric statement had
been written as

```text
L(R)-2R<=0.                                               (9)
```

For the adjacent straight-arm mechanism, (4) proves (9) automatically as soon
as three containment facts are established:

1. a selected critical point satisfies `|c|<=R`;
2. both segments from `c` to the adjacent radius-`R` vertices lie in
   `{Re Q<=0}`;
3. the two outward root-direction tails from radius `R` lie in
   `{Re Q<=0}`.

Thus the local frontier is no longer a coupled length-and-containment problem.
It is the pure adjacent-arm containment theorem.  In particular, trying to
estimate a curved scattering excess before establishing adjacent containment
is unnecessary for this mechanism.

## 4. Why finite truncation is still essential

There is an exact discrete average behind the computation.  For every `c`,
`s>=0`, and the `n` roots of unity,

```text
(1/n) sum_j Re Q(c+s omega_j) = Re Q(c)-s^n.              (10)
```

So a translated direction is safe at every fixed radius on average.  But the
same direction need not remain safe for all radii.  The stationary-polynomial
probe already sees the stronger complete translated-ray selector fail on the
pure first-mode sextic `Q(z)=z-z^6`: each negative critical point has only one
sampled complete safe translated sixth-root ray.  That is deterministic
numerical evidence, not yet an exact no-go theorem, but it explains why the
radius-`R` truncation in the surviving statement is load-bearing.

The adjacent finite-segment selector survives stationary-point maximization,
not mere sampling.  Random normalized faces in the checked degrees return
negative scores, and the sharp quintic equality chart returns score zero
exactly at its zero leading critical value; the disk-forced paired trace from
the preceding checkpoint then supplies the strict next-order sign.  These rows
motivate the analytic containment theorem but are not promoted to proof.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_tied_newton_face_adjacent_hub.py
```

