# Erdős 1041: a macroscopic affine/gradient double-tight cell

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_large_gradient_cell.py`.
Consumes `QuinticDoubleTightCriticalValueCarrier.md`,
`QuinticSupportDefectEngine.md`, and the affine-predictor cell engine.

## 1. Result

On the complete rational interval

```text
99/100000 <= t <= 101/100000,                       (LG1)
```

the weak upper-half-plane double-tight carrier branch through `t=1/1000`
is unique, regular, stays in one strict wall chamber, and has paired
inverse-ray excess

```text
mathcal E(t) < -1/10.                                (LG2)
```

The width of (LG1) is `1/50000=2*10^-5`: fifty times the first direct
interval cell and one thousand times the original affine seed cell.

## 2. Exact carrier enclosure

The checker substitutes exact affine predictors for `(a(t),mu(t))` into the
two polynomial carrier equations before interval evaluation.  The cancelled
linear residual therefore remains cancelled.  A two-complex-variable
Krawczyk map on (LG1) gives

```text
K_a  < 0.000334752 < 1/2500,
K_mu < 0.000045645 < 1/20000,
|det d(E1,E2)/d(a,mu)| > 12924.19,
wall cross margin > 1983.41.                         (LG3)
```

The reconstructed parameter tubes obey

```text
rad(mu)<0.014744,  rad(e^{-i phi})<0.003513.          (LG4)
```

All displayed comparisons are exact rational ball inequalities.  Decimal
centres are used only to scout the branch.

## 3. Gradient transport

At the exact centre `t=1/1000`, equivalently
`kappa=1000/1000001`, the point engine proves

```text
mathcal E(t_0)<-0.1169876625.                        (LG5)
```

Exact implicit differentiation over the whole carrier tube yields

```text
|a_t|<10222.85,  |mu_t|<1534.64,  |phi_t|<90.951.    (LG6)
```

A gradient-only wall march integrates nonnegative parameter-gradient
densities over validated arc tubes and proves

```text
G_mu<0.302591,  G_phi<7.533180,
G_mu |mu_t| + G_phi |phi_t| < 1149.515.              (LG7)
```

The exact mean-value bound from (LG5)--(LG7), with
`|t-t_0|<=1/100000`, is

```text
mathcal E(t)<-0.1054925219<-1/10,                    (LG8)
```

which proves (LG2).

## 4. Boundary

This is a rigorous scale gain for one regular carrier branch and supplies a
practical cell size for an adaptive double-tight atlas.  It does not yet
certify the other simultaneous carrier branches, cross a singular/event
cell, cover the complete ordered `t` interval, or prove `EX-W`, `EX-U`,
degree five, or unrestricted Erdős 1041.
