# Erdős 1041: connected negative ordered-parameter chain past `-0.0012`

Date: 2026-08-30.  Exact replay:
`scripts/check_erdos1041_quintic_double_tight_negative_gradient_chain.py`.
Reusable engine: `scripts/lib_erdos1041_affine_tcell_engine.py`.

## 1. Result

On the weak upper-half-plane ordered double-tight carrier, the macroscopic
seed cell and four new affine-predictor cells form one rigorously identified
analytic branch.  Their connected union is

```text
-121/100000 <= t <= -89/90000.                      (NGCH1)
```

In particular it contains `t=-3/2500=-0.0012` in its interior.  Everywhere on
the union the paired inverse-ray excess satisfies the exact uniform bound

```text
mathcal E(t)<-3/50.                                  (NGCH2)
```

Thus the negative atlas has moved from a microscopic point-attached seed to a
connected interval of width `199/900000`, over twenty thousand times the
original `2*10^-8` support-seed width.

## 2. The four outward cells

Beyond the already-proved seed `[-91/90000,-89/90000]`, the new cells are

```text
[-53/50000, -1/1000],
[-111/100000, -21/20000],
[-29/25000, -11/10000],
[-121/100000, -23/20000].                           (NGCH3)
```

Each has radius `3/100000`.  At their respective exact rational centres, the
two-complex-variable affine Krawczyk ratios are

```text
K_a/rho_a  < 0.281, 0.268, 0.257, 0.246,
K_mu/rho_mu< 0.184, 0.175, 0.167, 0.160.            (NGCH4)
```

The interval Jacobian determinant lower bounds are respectively

```text
10144.00, 10720.60, 11303.76, 11893.49,             (NGCH5)
```

and all wall-orientation margins exceed `1752.63`.  Hence every cell carries
one unique regular branch in the same strict wall chamber.

## 3. Direct centre signs and exact transport

The exact centre excess upper bounds are

```text
-0.117961252392,
-0.118812268844,
-0.119635737655,
-0.120433675616.                                    (NGCH6)
```

On the four complete carrier tubes, exact integration of the nonnegative
parameter-gradient densities gives

```text
G_mu  < 0.362800, 0.358881, 0.354450, 0.350629,
G_phi < 8.973625, 8.917545, 8.853056, 8.799985.      (NGCH7)
```

After exact implicit differentiation of the two carrier equations and the
wall direction, the chain-rule Lipschitz bounds are

```text
L < 1834.348, 1759.267, 1688.314, 1625.057.         (NGCH8)
```

Multiplying by the common radius `3/100000` gives the whole-cell excess upper
bounds

```text
-0.062930816595,
-0.066034263974,
-0.068986330293,
-0.071681991483,                                    (NGCH9)
```

all strictly below `-3/50`.  The seed cell already has the stronger bound
`mathcal E<-1/10`, proving (NGCH2) on the connected union.

## 4. Exact gluing

Successive cells overlap at the rational parameters

```text
-201/200000, -211/200000, -221/200000, -231/200000. (NGCH10)
```

At each parameter an additional exact two-variable Krawczyk box contains the
zeros delivered by both adjacent cells and contains a unique carrier zero.
This proves the boxes describe one analytic branch; numerical proximity alone
is not used.

All decimal values above are readable outward approximations.  Carrier
substitution, Krawczyk inclusion, wall separation, point arclengths, gradient
integrals, transport, and overlap uniqueness use exact rational complex-ball
arithmetic.

## 5. Boundary

This closes one connected negative-side weak-branch segment through
`t=-0.0012`.  It does not cover the other four simultaneous carrier branches,
continue to the next event, close the remaining regular domains or cusp
collar, or by itself prove the complete double-tight atlas, `EX-W`, `EX-U`,
degree five, or unrestricted Erdős 1041.
