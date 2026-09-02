# Exact no-go for universal adjacent pairing on a tied Newton face

## Result

The unique two-ended negative component of a tied-face model need not join
adjacent asymptotic sectors.  A small symmetric quintic already proves this:

```text
Q(z)=-(65/27)z+(100/27)z^2-z^5,       H(z)=Re Q(z).          (1)
```

Nevertheless the same nonadjacent pair has an exact strict two-arm connector.
Thus adjacency is not the invariant.  The corrected selector must allow any
two negative asymptotic directions and verify the direct two-focus metric
budget.

## Critical topology

Exact factorization gives

```text
Q'(z)=-5(z-1)(z-1/3)(z+2/3-i)(z+2/3+i).                    (2)
```

The four critical heights are

```text
H(1)=8/27,       H(1/3)=-32/81,
H(-2/3+i)=H(-2/3-i)=4/81.                                  (3)
```

Zero is regular and exactly one critical point lies below zero.  The standard
Morse/component-count argument for a harmonic polynomial with simple critical
points therefore gives four components of `{H<0}` for the five negative ends:
three one-ended components and one two-ended component.

## Exact identification of the nonadjacent pair

Set

```text
h=1/3,       R=1/2,
u=(5+12i)/13,       v=(5-12i)/13.                            (4)
```

Both are unit directions and

```text
Re(u^5)=Re(v^5)=341525/371293 > 0,
```

so the rays lie in negative sectors `E1` and `E4`, which are nonadjacent in
cyclic order.  On each central arm from `h` to `Ru` or `Rv`, the degree-five
Bernstein controls for `H` are

```text
-32/81, -32/81, -25157/54756, -2553583/4270968,
-3400915/4112784, -366892775/320797152.                      (5)
```

For `s=R/T`, the reciprocal-tail polynomial `s^5 H(Ru/s)` (and its conjugate)
has controls

```text
-341525/11881376, -341525/11881376, -341525/11881376,
-30136615/320797152, -40862125/106932384,
-366892775/320797152.                                       (6)
```

Every control in (5)--(6) is strictly negative.  Hence both arms and both
tails lie in `{H<0}`.  They identify the unique two-ended component as the one
joining `E1` to `E4`; no adjacent pair lies in a common component.

## Strict metric budget

The two arm lengths are equal and

```text
|Ru-h|^2=|Rv-h|^2=1417/6084 < R^2,
R^2-|Ru-h|^2=2/117.                                         (7)
```

Their sum is therefore strictly below `2R=1`.  This is simultaneously an
adjacency no-go and a positive free-pair chart.

## A quantitative four-real-dimensional solved chart

The strict certificate is robust on an explicit coefficient box; no appeal to
qualitative continuity is needed.  Put

```text
Q_(da,ea,db,eb)(z)=Az+Bz^2-z^5,
A=-65/27+da+i ea,             B=100/27+db+i eb,             (8)
```

and assume

```text
max(|da|,|ea|,|db|,|eb|) <= 2/3.                            (9)
```

Keep exactly the same `h,R,u,v` from (4).  Every arm and reciprocal-tail
Bernstein control is affine in the four perturbation coordinates.  Replacing
each signed perturbation by its worst possible contribution under (9) gives,
on either arm, the six strict upper controls

```text
-8/81, -29/1053, -5783/136890, -3166193/21354840,
-1103867/4112784, -151446167/320797152,                    (10)
```

and, on either reciprocal tail,

```text
-341525/11881376, -341525/11881376, -341525/11881376,
-112877099/1603985760, -21458221/106932384,
-151446167/320797152.                                      (11)
```

Thus all four curves remain strictly in `{Re Q_(da,ea,db,eb)<0}`.  The
geometry does not depend on the coefficients, so the squared metric margin is
still exactly `2/117`.  Equations (8)--(11) therefore prove a closed
four-dimensional coefficient box of strict model certificates, and hence an
open neighbourhood of that box, rather than merely a single calibration
point.  The smallest upper-control margin is the rational number `29/1053`.

This is the useful strengthening of a qualitative adjacency return: the
topological no-go is needed only at the centre to retire adjacency, whereas
the surviving arbitrary-pair mechanism now comes with explicit perturbation
room that a finite Newton-weight transfer can spend.

## Corrected producer

For an arbitrary tied Newton face, it is enough to produce:

1. a negative component (with a critical or noncritical hub),
2. any two negative asymptotic directions in that component,
3. a cutoff whose two arm and reciprocal-tail Bernstein controls are
   nonpositive, and
4. the direct inequality `|h-Ru|+|h-Rv|<=2R`.

Adjacent sector labels play no role in this free-pair ellipse statement.
`TiedNewtonFaceNonAdjacentNoGo.lean` checks (1)--(7), the Bernstein consumers,
tail transport, the strict metric kernel, and the coefficient-box domination
behind (10)--(11).  The symbolic checker reconstructs every perturbed control
before taking its exact `l1` sensitivity.  The harmonic-polynomial component
count and end classification remain ordinary mathematics.

This result does not prove the all-degree selector or Erdős #1041.  It removes
one false universal mechanism while leaving a strictly stronger exact chart
than the returned large witness.
