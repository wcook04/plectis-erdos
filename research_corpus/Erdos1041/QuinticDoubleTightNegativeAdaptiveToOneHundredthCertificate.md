# Erdős 1041: connected negative ordered atlas through `-0.01`

Date: 2026-08-30.  Exact replay:
`scripts/check_erdos1041_quintic_double_tight_negative_adaptive_to_one_hundredth.py`.
Reusable engine: `scripts/lib_erdos1041_affine_tcell_engine.py`.

## 1. Result

The weak upper-half-plane ordered double-tight carrier branch previously
certified through `t=-0.00202` continues across forty-seven new overlapping
rational cells.  The new continuation union is

```text
-127/12500 <= t <= -6/3125,                         (NGA1)
```

and overlaps the preceding cell.  Combining the exact overlap-uniqueness
certificates gives one connected analytic branch on

```text
-127/12500 <= t <= -89/90000.                       (NGA2)
```

In particular `t=-1/100=-0.01` lies in the interior.  On every new cell the
canonical paired inverse-ray excess satisfies

```text
mathcal E(t)<0.                                      (NGA3)
```

The smallest displayed outward margin is still more than `0.0169`.

## 2. Adaptive exact cells

The cells use four scales:

```text
10 cells of radius  6/100000,
 7 cells of radius  8/100000,
11 cells of radius 10/100000,
19 cells of radius 12/100000.                       (NGA4)
```

Successive centre spacings are respectively `10`, `14`, `18`, and `22` over
`100000`, strictly below the sums of adjacent radii.  The three scale changes
also have positive overlap.  This gives a connected cover without paying the
small cusp-collar radius throughout the regular domain.

On all forty-seven cells, the exact affine-predictor Krawczyk ratios obey

```text
K_a/rho_a<0.371,  K_mu/rho_mu<0.215,                (NGA5)
```

the interval Jacobian determinant lower bound exceeds `20976`, and the strict
wall-orientation margin exceeds `2132`.  The reconstructed ray-direction ball
has radius below `0.0224`.  Thus each box contains one unique regular carrier
branch in the same wall chamber.

## 3. Recentring and exact sign

No cumulative transport estimate is used.  Every cell is recentered at its
own exact rational `t`; the exact fibre

```text
kappa=t/(1+t^2)
```

is independently isolated, and its centre excess is independently integrated.
The centre upper bounds decrease from

```text
-0.131733950611... to -0.174265863635....            (NGA6)
```

Each complete carrier tube then receives its own exact nonnegative
parameter-gradient integration and implicit carrier/wall derivative bound.
The resulting whole-cell upper endpoints are all negative.  At the four scale
starts they are

```text
radius  6/100000: -0.035804052757...,
radius  8/100000: -0.030116705870...,
radius 10/100000: -0.016911671599...,
radius 12/100000: -0.023550848705....                (NGA7)
```

The final cell has upper endpoint `-0.092107499941...`.  The scale-start
values are the local minima because increasing a radius widens the exact tube;
recentring restores and then improves the margin within each block.

The expensive arclength and gradient integrations are independent exact
computations.  The checker evaluates them in a fixed four-process pool.  This
changes wall time only: every acceptance comparison remains an exact rational
complex-ball inequality.

## 4. Exact branch identity

For the old-new join, every within-block overlap, and all three scale changes,
the checker chooses a rational parameter in the strict intersection and builds
an additional two-variable Krawczyk box containing both adjacent carrier
zeros.  All forty-seven matching boxes contain a unique zero.  Consequently
the atlas follows one analytic branch; it does not rely on nearest-root
heuristics or floating continuation.

All decimal displays are readable outward approximations.  Polynomial
substitution, carrier Krawczyk maps, determinant and wall separation, exact
centre arclengths, parameter-gradient integrals, mean-value transport, and
overlap uniqueness are rational-ball computations.

## 5. Boundary

This closes the connected weak negative branch only through `t=-0.01016`.
It does not cover the other four simultaneous carrier branches, continue to
the next event, close the remaining regular domains, or by itself prove the
complete double-tight atlas, `EX-W`, `EX-U`, degree five, or unrestricted
Erdős 1041.
