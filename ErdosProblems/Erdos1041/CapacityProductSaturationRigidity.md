# Erdős 1041: rigidity at capacity-product saturation

## Status

This note proves an exact endpoint theorem for the exterior finite-Blaschke
model.  It strengthens the equality discussion in
`ExteriorBlaschkeFibreCapacityGap.md`: saturation of the product bound under
the **non-strict** boundary-speed hypothesis forces the regular exterior
polygon.  The strict admissible hypothesis cannot attain the endpoint.

This is not the conjectural symmetric merge envelope.  In particular it does
not compare subcritical merge heights for unequal radii.

## Theorem

Let `B` be a finite Blaschke product of degree `m`, let `n>m`, and assume

```text
|B'(zeta)| <= n                    for every |zeta|=1.   (1)
```

Put `p=|B(0)|`.  If

```text
p=(n-m)/(n+m),                                         (2)
```

then, after rotations of source and range,

```text
B(z)=(exp(i phi) z^m-p)/(1-p exp(i phi) z^m).           (3)
```

Equivalently, the zeros of `B` have one common modulus and regular
`m`-gon arguments.  If (1) is strict at every boundary point, then equality
in (2) is impossible and `p<(n-m)/(n+m)`.

## Proof

Rotate the range so that `B(0)=-p`, and use the fibre `B(zeta)=1`.  The Clark
fibre identity is

```text
sum_(B(zeta)=1) 1/|B'(zeta)|
  =(1-|B(0)|^2)/|1-B(0)|^2
  =(1-p)/(1+p)=m/n.                                    (4)
```

There are `m` fibre points, counted with multiplicity.  Assumption (1) makes
every summand at least `1/n`; hence equality in (4) forces

```text
|B'(zeta)|=n                                            (5)
```

at every point of this fibre.

On the unit circle the angular derivative is positive and real:

```text
zeta B'(zeta)/B(zeta)=|B'(zeta)|.
```

Consequently

```text
H(z)=n-z B'(z)/B(z)                                    (6)
```

is nonnegative on the circle.  Equations (5)-(6) give a zero at each point
of the fibre `B=1`.  A zero of a real-analytic nonnegative boundary function
has even order, so these are `m` boundary double zeros.

Write `B=P/Q`, with `P,Q` of degree at most `m` and `Q` zero-free on the
closed disk.  The cleared numerator of

```text
B H=nB-zB'
```

has degree at most `2m`.  The `m` double zeros just found exhaust that degree,
and the fibre polynomial is `P-Q`.  Therefore, for a constant `C`,

```text
nB-zB'=C(B-1)^2,
H=C(B-1)^2/B.                                           (7)
```

At zero, `H(0)=n` and `B(0)=-p`, so

```text
C=-np/(1+p)^2.                                          (8)
```

Substitution into (7) gives the separable equation

```text
zB'=A(B+p)(B+1/p),       A=np/(1+p)^2.                 (9)
```

The endpoint relation (2) is exactly

```text
A(1/p-p)=n(1-p)/(1+p)=m.                               (10)
```

Thus

```text
z d/dz log((B+p)/(B+1/p))=m,
(B+p)/(B+1/p)=c z^m.                                   (11)
```

Solving for `B` yields

```text
B(z)=(c z^m/p-p)/(1-c z^m).                            (12)
```

Because `B` is inner, the two sides of (12) have equal modulus on the unit
circle.  For `y=c z^m`, direct subtraction gives

```text
|y/p-p|^2-|1-y|^2
  =(1-p^2)(|c|^2/p^2-1).                               (13)
```

Hence `|c|=p`; writing `c=p exp(i phi)` turns (12) into (3).

Finally, under the strict condition `|B'|<n`, every summand in (4) is
strictly larger than `1/n`.  The endpoint value `(1-p)/(1+p)=m/n` is then
impossible, proving the strict product gap. ∎

## Consequence and boundary

The capacity endpoint is rigid: a sequence approaching product saturation can
only converge (after rotations and subsequences) to the regular exterior
polygon.  This supplies the exact equality object needed by compactness or
local-stability arguments.

It does **not** prove that the regular polygon maximizes the first merge level
at a fixed subcritical product.  The coupled irregular-angle/irregular-radius
`m=3` selector or mountain-pass inequality remains open.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_capacity_product_saturation_rigidity.py
```

The checker verifies the endpoint algebra, ODE factorization and integration,
the inner-boundary modulus identity, and rational regular-model regressions.
The Clark identity and the boundary zero-order argument are ordinary complex
analysis, not a finite-arithmetic or Lean claim.
