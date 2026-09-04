# Erdős 1041: an affine-predictor regular double-tight chain

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_affine_tcell_chain.py`.
Reusable engine: `scripts/lib_erdos1041_affine_tcell_engine.py`.

## 1. Result

On the weak upper-half-plane ordered double-tight carrier branch, the two
overlapping rational cells

```text
99999/10^8       <= t <= 100001/10^8,
200001/(2*10^8) <= t <= 40001/(4*10^7)              (ATC1)
```

form one rigorously identified analytic branch.  Their union is exactly

```text
[99999/10^8, 40001/(4*10^7)],  width 7/(2*10^8).    (ATC2)
```

This is a connected outward advance of width `3.5*10^-8`, 175 times the
width of the first fixed-centre cell.  On every point of the union the direct
support--Stieltjes certificate proves

```text
mathcal E < -7/200.                                  (ATC3)
```

No arm-gradient bound or floating transport estimate is used in (ATC3).

## 2. Affine-predictor Krawczyk mechanism

The ordered carrier equations are

```text
E1=(1+t+t^2)a^2+(1+t)A a+B=0,
E2=t(1+t)a^3+t A a^2-C=0,                            (ATC4)
```

where

```text
A=4(mu+4),
B=-(12/25)(3mu^3-5mu^2-100mu-200),
C=(4/3125)(mu+10)^3(27mu^2+140mu+200).
```

At each rational centre the engine scouts `(a0,mu0)` and the implicit
tangent `(a1,mu1)`, then substitutes

```text
a=a0+a1 tau+delta_a,  mu=mu0+mu1 tau+delta_mu,
|tau|<=10^-8.
```

Crucially, it carries the predictor through the exact polynomial ring in
`tau`; ordinary interval substitution would destroy the cancelled linear
term.  With

```text
|delta_a| <= 10^-9,  |delta_mu| <= 10^-10,
```

the two exact parametric Krawczyk radii are respectively bounded by

```text
cell 0:  K_a < 3.033532*10^-10, K_mu < 4.159746*10^-11,
cell 1:  K_a < 3.033465*10^-10, K_mu < 4.159648*10^-11.   (ATC5)
```

The corresponding interval Jacobian determinant lower bounds exceed
`13397.21`, and the wall-orientation margins exceed `1998.02`.

## 3. Direct sign and exact gluing

For each complete parameter tube, put `p=(1+t)a`, reconstruct the fixed wall
direction `d=i p/|p|`, and pass the resulting exact `(mu,d)` balls directly to
the compact support--Stieltjes engine.  The exact outward paired endpoints are

```text
cell 0: mathcal E < -0.0353033456...,
cell 1: mathcal E < -0.0353036524....                 (ATC6)
```

Each arm uses 2048 rational compact cells, Krawczyk root isolation, monotone
half-angle support where available, the nonnegative defect density at turns,
and an exact terminal tail bound.

The parameter overlap has width `1/(2*10^8)`.  At

```text
t=400003/(4*10^8),                                   (ATC7)
```

a third exact two-variable Krawczyk box contains the roots supplied by both
cells and contains a unique carrier zero.  Therefore the two certified cells
are not merely adjacent negative boxes: they are the same analytic branch.

## 4. Boundary

This proves a reusable quadratic-defect continuation mechanism and a first
connected chain materially wider than the fixed-centre seed.  It does not yet
cover the remainder of the four regular rational `t` domains, the other
carrier branches, the cusp collar, the complete double-tight atlas, `EX-W`,
`EX-U`, degree five, or unrestricted Erdős 1041.
