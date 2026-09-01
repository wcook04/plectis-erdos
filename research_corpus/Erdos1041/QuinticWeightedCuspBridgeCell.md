# Erdős 1041: a full five-sheet weighted-cusp bridge cell

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_weighted_cusp_bridge_cell.py`.
Consumes `QuinticDoubleTightSupportStieltjesReduction.md`,
`QuinticDoubleTightCriticalValueCarrier.md`, and the exact wall engine.

## 1. Result

Put

```text
kappa=u^3.
```

> **Theorem WCB (first full weighted-cusp bridge cell).** On the complete
> rational interval
>
> ```text
> 1/10000 <= u <= 1001/10000000,                    (WCB1)
> ```
>
> all five upper-half-plane sheets of the double-tight carrier are regular,
> remain in fixed wall chambers, and satisfy
>
> ```text
> mathcal E < -1/20.                                 (WCB2)
> ```
>
> On the same tubes, the exact arm-gradient integrals satisfy
>
> ```text
> G_mu < 1/2,       G_phi < 13/2                    (WCB3)
> ```
>
> on the three `mu=-10` sheets, and
>
> ```text
> G_mu < 2/5,       G_phi < 13/2                    (WCB4)
> ```
>
> on the two `mu_*` sheets.  In particular every sheet satisfies the earlier
> sufficient cusp inequalities `G_mu<2`, `G_phi<8`.

This is a genuine nonzero-width parameter certificate, not a collection of
point samples or a floating transport estimate.

## 2. The three weighted `mu=-10` sheets

Use the already proved weighted chart

```text
kappa=u^3,   mu=-10+uz,
H(u,z)=u^-6 K_{u^3}(-10+uz).                        (WCB5)
```

The checker replays exactly that `H` is polynomial and

```text
H(0,z)=(2304/625)(z^6+16200z^3+590490000).          (WCB6)
```

Rouché's theorem on `|z|=30`, with the exact limiting lower bound

```text
(2304/625) 2700^2,
```

proves that all six roots remain inside the circle on (WCB1).  Three
parametric Krawczyk discs isolate the upper roots; conjugation supplies the
lower roots, so the three upper tubes are exhaustive.  The rational active
pair reconstruction stays nonzero and its chamber cross product has a
strict sign on every tube.

Passing the resulting exact `(mu,d)` balls to the oriented wall engine gives
the following outward upper endpoints and gradient bounds (decimals are
only readable projections of exact rational inequalities):

```text
sheet        mathcal E upper     G_mu upper    G_phi upper
  0          -0.9143651          0.411973      5.754785
  1          -0.0533034          0.480403      6.451091
  2          -1.1263561          0.372112      5.508420.       (WCB7)
```

The weak sheet therefore still has more than the rational margin `1/20` at
the outer face of the bridge cell.

## 3. The two `mu_*` sheets are a different regular germ

The `mu_*` branches must not be forced through the singular weighted chart.
Write the selected gaps as `a` and `ta`.  The exact carrier system is

```text
E1=(1+t+t^2)a^2+(1+t)A(mu)a+B(mu)=0,
E2=t(1+t)a^3+tA(mu)a^2-C(mu)=0.                     (WCB8)
```

For `kappa=t/(1+t^2)` and the interval (WCB1), the elementary identity

```text
t-kappa=kappa t^2
```

places the unique positive preimage inside

```text
u_min^3 <= t <= u_max^3+4u_max^9.                   (WCB9)
```

At `t=0`, `mu=mu_*=(-70+10i sqrt(5))/27`, the two roots of
`a^2+A(mu_*)a+B(mu_*)` give two distinct regular germs.  A two-complex-
variable parametric Krawczyk calculation on (WCB9) isolates both.  Their
`a`-tubes are disjoint even though their `mu`-coordinates coalesce at the
endpoint.  Direct exact wall integration then gives

```text
sheet        mathcal E upper     G_mu upper    G_phi upper
  3          -1.2651086          0.244043      5.558223
  4          -1.0245800          0.393305      6.031939.       (WCB10)
```

Thus the `mu=-10` cubic cusp and the `mu_*` linear germs are certified in
their natural coordinates and fan into one five-sheet conclusion only after
their separate regularity checks.

## 4. Exactness and boundary

All accepted inclusions, chamber signs, inverse-arm tubes, arclength bounds,
tail estimates, gradient integrals, and final comparisons use rational
outward complex-ball arithmetic.  Newton values from `mpmath` only choose
centres; every centre is subsequently enclosed by an exact Krawczyk
self-map.

Theorem WCB advances the proved cusp collar from the limiting fibre to a
full five-sheet nonzero interval.  It does not fill the still-open gap

```text
10^-4 < u < 0.1,
```

nor certify the remaining regular double-tight atlas.  Consequently it does
not by itself prove the compact double-tight sign theorem, `EX-W`, `EX-U`,
degree five, or unrestricted Erdős 1041.
