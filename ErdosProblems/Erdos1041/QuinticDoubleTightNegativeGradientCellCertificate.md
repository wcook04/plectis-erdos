# Erdős 1041: a macroscopic negative ordered-parameter cell

Date: 2026-08-30.  Exact replay:
`scripts/check_erdos1041_quintic_double_tight_negative_gradient_cell.py`.
Consumes the affine-predictor cell engine and the compact wall-arclength
engine.

## 1. Result

On the complete rational interval

```text
-91/90000 <= t <= -89/90000,                        (NGC1)
```

the weak upper-half-plane ordered double-tight carrier branch through
`t=-1/1000` is unique, regular, stays in one strict wall chamber, and has
paired inverse-ray excess

```text
mathcal E(t) < -1/10.                                (NGC2)
```

The interval has width `1/45000=2.222...*10^-5`; its left endpoint is
strictly below `-0.00101`.  It strictly contains the direct support seed

```text
[-100001/10^8,-99999/10^8],                         (NGC3)
```

so analytic-branch identity is automatic from uniqueness on the larger box.

## 2. Exact carrier enclosure

With the ordered gaps `a` and `ta`, the carrier equations are

```text
E1=(1+t+t^2)a^2+(1+t)A a+B=0,
E2=t(1+t)a^3+t A a^2-C=0,                            (NGC4)
```

where

```text
A=4(mu+4),
B=-(12/25)(3mu^3-5mu^2-100mu-200),
C=(4/3125)(mu+10)^3(27mu^2+140mu+200).
```

The exact affine-predictor Krawczyk map on (NGC1) has outward radii

```text
K_a  < 0.000406436 < 0.001,
K_mu < 0.000054539 < 0.0001,
|det d(E1,E2)/d(a,mu)| > 10639.66,                   (NGC5)
```

and the wall cross-product margin exceeds `1766.68`.  The reconstructed tubes
obey

```text
rad(mu)<0.015765,  rad(e^{-i phi})<0.004055.         (NGC6)
```

All these are exact rational ball comparisons; the displayed decimals are
readable outward approximations.

## 3. Exact centre and gradient transport

At the exact centre

```text
t_0=-1/1000,  kappa_0=-1000/1000001,
```

the oriented arclength engine proves

```text
mathcal E(t_0)<-0.117436414945....                    (NGC7)
```

Implicit differentiation of the carrier on the entire affine tube gives

```text
|a_t|<10243.62,  |mu_t|<1487.35,  |phi_t|<120.57.   (NGC8)
```

The same validated root tubes, now integrated with their nonnegative
parameter-gradient densities, give

```text
G_mu<0.315107,  G_phi<7.617693,
G_mu|mu_t|+G_phi|phi_t|<1387.103.                    (NGC9)
```

Therefore the exact mean-value estimate on `|t-t_0|<=1/90000` is

```text
mathcal E(t)<-0.102024168563...<-1/10,               (NGC10)
```

proving (NGC2).  Floating values are used only as root scouts.  Carrier
inclusion, wall separation, centre excess, parameter gradients, and the final
transport comparison are exact outward rational-ball inequalities.

## 4. Boundary

This turns the attached negative support seed into one macroscopic certified
cell and supplies a practical negative-side atlas scale.  It covers only this
one carrier branch.  It does not certify the other four simultaneous branches,
cross an event fibre, close the remaining regular domains or cusp collar, or
by itself prove the complete double-tight atlas, `EX-W`, `EX-U`, degree five,
or unrestricted Erdős 1041.
