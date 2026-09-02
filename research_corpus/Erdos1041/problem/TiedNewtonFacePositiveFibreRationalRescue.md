# Rational rescue of the positive leftmost-fibre quintic

## Result

The exact quintic

```text
Q(z)=15z+5z^2-z^5                                         (1)
```

has positive renormalized defect at its unique leftmost critical fibre, but
the face itself has a strict rational finite connector.  Take

```text
h=-8/5,       R=7/5,
u=(-3+4i)/5,  v=(-3-4i)/5.                                 (2)
```

The two segments from `h` to `Ru,Rv` and the two outward rays from those
points lie strictly in `{Re Q<0}`, while their central length is strictly less
than `2R`.

This is the exact constructive answer to the false Leftmost-Fibre selector on
its counterexample: the selected curved fibre is bad, not the tied face.

## Arm certificate

Write `H=Re Q`.  Along the segment

```text
z(t)=(1-t)h+tRu,                  0<=t<=1,
```

the degree-five Bernstein controls of `H(z(t))` are

```text
-2232/3125,
-91359/15625,
-2201607/156250,
-15036143/781250,
-37150741/1953125,
-153827009/9765625.                                 (3)
```

All are strictly negative.  The conjugate arm has the same real profile.

## Reciprocal-tail certificate

The direction is unit and

```text
Re(u^5)=Re(v^5)=237/3125>0.                              (4)
```

Thus the leading term is in a negative asymptotic sector.  Put `s=R/T` on
the outward ray, so `0<s<=1`.  The degree-five Bernstein controls of
`s^5 H(Ru/s)` are

```text
-3983259/9765625,
-3983259/9765625,
-3983259/9765625,
-13325893/19531250,
-39311384/9765625,
-153827009/9765625.                                      (5)
```

Again all are strictly negative, and conjugation gives the second tail.

## Metric certificate

The arms have equal length and

```text
|Ru-h|^2=229/125,
R^2-|Ru-h|^2=16/125>0.                                   (6)
```

Therefore their total length is `2 sqrt(229/125)<2R=14/5`.

## Quantitative coefficient box

The strict certificate is not isolated.  Keep the same `h,R,u,v` and set

```text
Q_delta(z)=(15+da+i ea)z+(5+db+i eb)z^2-z^5.             (7)
```

On the closed four-real-dimensional box

```text
max(|da|,|ea|,|db|,|eb|) <= 1/6,                         (8)
```

affinity of Bernstein conversion gives the following coordinatewise upper
bounds for the six controls on either finite arm:

```text
-196/9375,
-478429/93750,
-4167439/312500,
-86815733/4687500,
-215205071/11718750,
-440043527/29296875.                                     (9)
```

The corresponding upper bounds for either reciprocal tail are

```text
-3983259/9765625,
-3983259/9765625,
-3983259/9765625,
-75208483/117187500,
-74182143/19531250,
-440043527/29296875.                                    (10)
```

Every number in (9)--(10) is strictly negative.  The smallest certified
Bernstein margin is therefore `196/9375`, while the geometry is unchanged
and retains the squared metric margin `16/125`.  Thus (8) is one explicit
resolved finite-transfer chart, rather than an appeal to qualitative
continuity.  The exact maximal uniform `l_infinity` radius admitted by these
affine controls is `279/1625`; the smaller radius `1/6` leaves strict room on
the closed box.

## Consequence

Equations (3)--(10) give both a strict model certificate and an explicit
four-real-dimensional coefficient chart with rational margin.

This sharpens the returned transfer picture in two ways:

1. the proposed LF inequality is not the pointwise tied-face obligation;
2. a finite atlas may need charts whose hubs and curves are unrelated to the
   canonical critical fibre, exactly as its own RSCT hypotheses permit.

`TiedNewtonFacePositiveFibreRationalRescue.lean` checks the rational arm and
tail Bernstein identities, their nonpositive consumers, reciprocal transport,
strict metric budget, and the coefficient-box affine inequalities.  The
symbolic checker independently reconstructs all controls and verifies their
strict signs.  This closes one quintic face and a coefficient neighbourhood
of it, not the all-degree face cover, compact-away forcing, or unrestricted
Erdős #1041.
