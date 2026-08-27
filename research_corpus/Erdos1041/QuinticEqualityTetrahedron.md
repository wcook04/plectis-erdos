# Erdős #1041: the sharp quintic equality chart has a centred contact tetrahedron

Status: complete analytic four-connector equality atlas and local stability
theorem, with exact symbolic replay and Lean formalization of the decisive
first-order selector, 2026-08-25. This proves a genuine open neighbourhood of
the formerly dangerous equality chart. It does **not** yet cover the whole
mixed coefficient space or unrestricted Erdős #1041.

## 1. The result

Consider the normalized mixed quintic model

```text
H_{A,beta}(z) = Re(Az + i exp(i beta) z^2 - z^5).          (1)
```

Let `u_*^3=27/320`. There is an open neighbourhood `U` of `(A,beta)=(u_*,0)`
such that every parameter in `U` has a fifth-root-pair truncated connector on
which (1) is nonpositive. At the centre, four explicit connectors are active;
for every nonzero tangent perturbation, at least one becomes strictly negative
to first order.

Thus the exact equality chart is not a failure of uniform stability. It is a
finite four-way transition whose contact gradients surround the origin.

## 2. The two additional equality connectors

The canonical-slice theorem already supplied the tangent connectors on root
pairs `(0,1)` and `(2,3)`. Two more occur on `(1,3)` and `(3,4)`, crossing the
positive and negative imaginary axes. Put

```text
w = sqrt(10+2 sqrt(5)),          h = sqrt(3),
Q_+ = w^3(3h-5)/160,
Q_- = w(3h+5)(3w^2-40)/160.                              (2)
```

Their truncation radii are `Q_+^(1/3)` and `Q_-^(1/3)`. Numerically,

```text
Q_+ = 0.06749516206750685...,
Q_- = 0.82823268698256268... .                            (3)
```

At the axis-crossing parameters

```text
t_+ = 1-w^2/20,                    t_- = w^2/20,           (4)
```

the value and first chord derivative vanish. After division by the squared
radius, exact expansion factors each chord as

```text
(t-t_±)^2 (q_2 t^2+q_1 t+q_0).                       (5)
```

For `(1,3)`, with `Q=Q_+`,

```text
q_2 = -25Q(w^2-8)/8,
q_1 = 5Q(3w^2-20)/4,
q_0 = -(10Qw^2+40Q+w^3)/16.                              (6)
```

Here `q_2<0` and the exact discriminant is negative, so the residual
quadratic is strictly negative on the entire real line. For `(3,4)`, with
`Q=Q_-`,

```text
q_2 = 25Q(w^2-12)/8,
q_1 = -5Q(3w^2-40)/4,
q_0 = (10Qw^2-240Q+3w^3-40w)/16.                         (7)
```

Here `q_2>0`, while `q_0<0` and `q_2+q_1+q_0<0`; convexity makes the residual
strictly negative on `[0,1]`. The four associated outward rays are strict:
three use endpoint power domination, and the lone positive-quadratic ray uses
the decreasing-quartic criterion from `QuinticCanonicalMixedSlice`.

All identities reduce exactly modulo

```text
w^4-20w^2+80=0,                    h^2-3=0.               (8)
```

Rational isolating intervals for `w,h` certify every displayed strict sign.

## 3. The contact geometry collapses to four simple points

Let `y>0` be the imaginary coordinate of the `(0,1)` double contact. Exact
cyclotomic reduction shows that the four contact points are

```text
z_L = y( sqrt(5)+i),
z_+ = i y( sqrt(3)-1),
z_R = y(-sqrt(5)+i),
z_- =-i y( sqrt(3)+1).                                  (9)
```

The apparently unrelated radii in the numerical optimizer are therefore one
rigid configuration. The identities behind (9) are cubic and exact; for
example

```text
Q_+ Im(v_+)^3 = (sqrt(3)-1)^3 r_L^3 Im(v_L)^3,           (10)
```

and similarly for the other three contacts. Positivity selects the stated
real cube roots.

## 4. The centred tetrahedron

Write a tangent perturbation as

```text
A = u_* + a + i b + O(||(a,b,beta)||^2),
i exp(i beta) = i-beta+O(beta^2).                         (11)
```

At a contact `z=x+iy`, its first value variation is

```text
Re((a+ib)z-beta z^2).                                    (12)
```

After factoring the harmless common powers of `y`, the four gradient rows are

```text
g_L = ( sqrt(5), -(1),       -4),
g_+ = (       0, -(sqrt(3)-1), (sqrt(3)-1)^2),
g_R = (-sqrt(5), -(1),       -4),
g_- = (       0,  sqrt(3)+1,  (sqrt(3)+1)^2).             (13)
```

They satisfy

```text
g_L+g_++g_R+g_-=0,                                       (14)
det [g_L 1; g_+ 1; g_R 1; g_- 1] = 16 sqrt(15) != 0.     (15)
```

So the origin is the strict barycentre of an affinely independent
tetrahedron. Equivalently, for every nonzero tangent vector `v`,

```text
min_j g_j dot v < 0.                                     (16)
```

There is an elementary proof avoiding convex-geometry terminology. If all
four dot products were nonnegative, (14) would force all four to vanish.
Subtracting the left and right equations gives `a=0`. The two axis equations
then give simultaneously

```text
b = y(sqrt(3)-1) beta,
b =-y(sqrt(3)+1) beta,
```

hence `beta=b=0`; therefore the perturbation was zero. Lean checks this as
`tetrahedral_strict_selector`.

## 5. From first order to an actual open neighbourhood

On each centre connector the chord has one nondegenerate double zero and is
strictly negative elsewhere; both ray tails are strict. Compactness separates
the contact from the strict region. In a local chord coordinate `s`, Taylor's
theorem gives uniformly

```text
H_j(s;v) <= g_j dot v - kappa s^2
             + C(||v|| |s| + ||v||^2).                   (17)
```

Completing the square absorbs the mixed term and yields

```text
max_s H_j(s;v) <= g_j dot v + C' ||v||^2.                (18)
```

Because the unit sphere is compact and (16) is strict, some `c>0` satisfies

```text
min_j g_j dot v <= -c ||v||.                             (19)
```

Choose the minimizing connector. For `0<||v||<c/C'`, (18) is negative.
The strict away-from-contact chord pieces and ray tails persist by continuity.
This proves the claimed open neighbourhood. Lean's
`linearMargin_absorbs_quadratic` checks the final scale comparison.

## 6. Exact boundary and next handoff

Closed here: all perturbation directions at the sharp canonical equality
chart, including the phase directions that defeated a single-connector
remainder estimate. The first arrow

```text
model equality  ->  uniform finite-parameter negativity
```

is now proved on an actual open neighbourhood of the equality orbit.

Still required: certify that outside symmetry copies of this neighbourhood,
the compact normalized mixed parameter space has a uniform negative margin.
That is now a separated compact-away-from-equality problem. The next owner
should construct a finite rational box cover with analytic Bernstein or
interval certificates, not revisit the transition asymptotics.
