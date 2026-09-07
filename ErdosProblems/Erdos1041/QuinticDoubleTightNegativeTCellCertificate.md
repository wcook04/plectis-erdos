# Erdős 1041: exact negative ordered-parameter seed cell

Date: 2026-08-30.  Exact replay:
`scripts/check_erdos1041_quintic_double_tight_negative_tcell.py`.

## 1. The certified cell

Write the two ordered tight critical gaps as `a` and `t a`.  On the complete
rational interval

```text
-100001/100000000 <= t <= -99999/100000000,          (NTC1)
```

there is one unique regular analytic carrier branch continuing the Newton
centre

```text
a  = 32.612244055311... + 43.090878126976... i,
mu = -12.476212477852... +  2.472960355017... i.     (NTC2)
```

The branch stays in one strict wall chamber and the canonical paired inverse-
ray excess obeys the uniform exact inequality

```text
mathcal E < -1/50.                                   (NTC3)
```

This is a whole-tube estimate.  It is not a point certificate transported by
an imported gradient bound.

## 2. Exact continuation mechanism

For

```text
A=4(mu+4),
B=-(12/25)(3mu^3-5mu^2-100mu-200),
C=(4/3125)(mu+10)^3(27mu^2+140mu+200),
```

the ordered carrier is the two-complex-equation system

```text
E1=(1+t+t^2)a^2+(1+t)A a+B=0,
E2=t(1+t)a^3+t A a^2-C=0.                            (NTC4)
```

The checker substitutes affine predictors for `a(t)` and `mu(t)` into these
polynomials before interval evaluation, so the exactly cancelled linear term
is not reintroduced as interval dependency.  The correction polydisc has
radii

```text
rho_a=10^-9,  rho_mu=1/(8*10^9),
```

and the outward Krawczyk radii satisfy

```text
K_a  < 3.001e-10,
K_mu < 4.045e-11,
|det d(E1,E2)/d(a,mu)| > 11080.93.                   (NTC5)
```

Thus the map is a strict self-map and the interval Jacobian is nonsingular.

## 3. Wall direction, anchor overlap, and direct sign

Put `p=(1+t)a` and let the third gap be `h=-A-p`.  On the entire box,

```text
|Im(conj(p)h)| > 1781.78,                            (NTC6)
```

so the wall sign cannot change.  The normalized ray direction reconstructed
from `p` remains strictly in the fourth quadrant.

The old complete-fibre anchor was expressed in the unordered coordinate
`kappa=-1/1000`.  Since `kappa(t)=t/(1+t^2)` is strictly increasing for
`|t|<1`, the exact comparisons

```text
kappa(-100001/100000000) < -1/1000 < kappa(-1/1000) (NTC7)
```

put its unique ordered preimage inside (NTC1).  Hence this seed is attached to,
not merely numerically near, that certified fibre.

Finally the checker feeds the whole `mu`- and ray-discs to the compact
support--Stieltjes engine.  Each arm is partitioned into 2048 exact rational
cells; monotone cells use the half-angle support inequality and the remaining
cells use the nonnegative direct defect density.  Their outward sum is

```text
mathcal E < -0.020846693870... < -1/50.              (NTC8)
```

All floating values are scouts only.  Polynomial substitution, Krawczyk
inclusion, determinant separation, wall orientation, anchor overlap, root
tubes, support sums, tail bounds, and the final sign comparison use exact
rational complex-ball arithmetic.

## 4. Boundary

This closes a nonzero-width negative ordered cell on the weak branch and gives
a sound seed for an adaptive negative-`t` atlas.  It does not cover the other
four branches throughout this cell, extend the seed to the adjacent singular
event, close the cusp collar, or by itself prove the complete double-tight
atlas, `EX-W`, `EX-U`, degree five, or unrestricted Erdős 1041.
