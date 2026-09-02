# Erdős 1041: connected negative ordered continuation through `-0.002`

Date: 2026-08-30.  Exact replay:
`scripts/check_erdos1041_quintic_double_tight_negative_gradient_continuation.py`.
Reusable engine: `scripts/lib_erdos1041_affine_tcell_engine.py`.

## 1. Result

The weak upper-half-plane ordered double-tight branch certified on the prior
negative chain continues through ten new overlapping rational cells.  The new
continuation union is

```text
-101/50000 <= t <= -23/20000,                       (NGCO1)
```

and overlaps the prior cell `[-121/100000,-23/20000]`.  Combining the two
certificates therefore gives one connected analytic branch on

```text
-101/50000 <= t <= -89/90000.                       (NGCO2)
```

In particular `t=-1/500=-0.002` is an interior point.  On every new cell the
paired inverse-ray excess satisfies the exact uniform inequality

```text
mathcal E(t)<-1/100.                                 (NGCO3)
```

The prior chain has the stronger bound `mathcal E<-3/50`, so (NGCO3) holds on
the combined union (NGCO2).

## 2. Ten rational cells

The new cells, each of radius `1/20000`, are

```text
[-13/10000,  -3/2500],
[-69/50000,  -4/3125],
[-73/50000, -17/12500],
[-77/50000,  -9/6250],
[-81/50000, -19/12500],
[-17/10000,  -1/625],
[-89/50000, -21/12500],
[-93/50000, -11/6250],
[-97/50000, -23/12500],
[-101/50000, -6/3125].                              (NGCO4)
```

The exact affine-predictor Krawczyk ratios decrease along the chain:

```text
K_a/rho_a   < 0.344, 0.327, ..., 0.241,
K_mu/rho_mu < 0.221, 0.209, ..., 0.151.             (NGCO5)
```

The interval Jacobian determinant lower bound increases from `11664.44` to
`20667.09`, and all wall-orientation margins exceed `1823.46`.  Thus each cell
contains one unique regular carrier branch in a fixed wall chamber.

## 3. Recentered exact signs

Cumulative transport is deliberately not used.  Each cell is recentered at
its own exact rational `t`, its own exact `kappa=t/(1+t^2)` carrier fibre is
isolated, and its centre arclength is independently certified.  The ten centre
upper bounds are

```text
-0.121511136546, -0.122691131517, -0.123821331516,
-0.124906648910, -0.125950913059, -0.126957681008,
-0.127930040645, -0.128870463074, -0.129781473814,
-0.130665103801.                                    (NGCO6)
```

On the full parameter tubes the exact chain-rule Lipschitz bounds decrease
from `2217.967` to `1337.289`.  After multiplication by the radius `1/20000`,
the whole-cell excess upper bounds are

```text
-0.010612785666, -0.019017216434, -0.026404015150,
-0.033257891746, -0.039990791780, -0.047956209284,
-0.052427534538, -0.056494665547, -0.060311344203,
-0.063800632301.                                    (NGCO7)
```

All lie strictly below `-1/100`, proving (NGCO3).  This recentering is the
load-bearing reason a macroscopic chain remains rigorous: the first large
cell nearly spends its centre margin, whereas later cells become easier.

## 4. Exact gluing

The first new cell is glued to the last old cell at `t=-241/200000`.  The nine
new-new matching parameters are

```text
-129/100000, -137/100000, -29/20000,
-153/100000, -161/100000, -169/100000,
-177/100000, -37/20000, -193/100000.                (NGCO8)
```

At every matching parameter an additional exact two-variable Krawczyk box
contains both adjacent carrier zeros and contains a unique zero.  Hence all
cells lie on one analytic branch, rather than merely tracking nearby numerical
solutions.

All decimal displays are readable outward approximations.  Polynomial
substitution, Krawczyk maps, determinant and wall separation, centre
arclengths, gradient integrals, transport, and overlap uniqueness are exact
rational complex-ball calculations.

## 5. Boundary

This closes the connected weak negative branch only through `t=-0.00202`.
It does not cover the other four simultaneous carrier branches, continue to
the next event, close the remaining regular domains or cusp collar, or by
itself prove the complete double-tight atlas, `EX-W`, `EX-U`, degree five, or
unrestricted Erdős 1041.
