# Erdős 1041: a positive-width stationary bridge from the collapse face

## Status

In the ordered chart `u=r s w`, `v=s w`, the stationary GP3 residual is
strictly positive on

```text
0<=t<=1,
0<=r<=1/8,
1/4<=s,w<=3/8.                                        (1)
```

This is stronger than a local collar: it reaches the collapse face `r=0`
with a fixed positive width.  Together with
`ThreeExteriorStationaryLowerProjectiveBlock.md` and
`ThreeExteriorStationaryCompactInteriorBlock.md`, it proves

```text
S_stat>0 for 0<=t<=1, 0<=r<=3/8, 1/4<=s,w<=3/8.       (2)
```

It does not cover the complement of (2), prove GP3, or prove Erdős 1041.

## Certificate

The checker pins and reuses the rigorous outward-rounded binary64 interval
engine from the first compact block.  A 32-by-16-by-16-by-16 coarse
partition gives 119,630 green cells and 11,442 dependency-red cells.  Each
red cell is bisected in all four variables.  All

```text
16*11442 = 183072
```

children are green.  The weakest accepted lower endpoint is

```text
0x1.807c2d7f4ffffp-21 = 7.161592491602974e-7 > 0,
```

and the deterministic accepted-endpoint digest is

```text
4bae2574c0764401c8cbdb13f8b77505f9ee8fb9a27ff32bb75ab728d832995c.
```

The cell union is exactly (1), so this is an exhaustive interval proof, not
a sample or optimizer report.

## Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_collapse_bridge_block.py
```

The strongest surviving stationary boundary is now outside the full bridge
(2): either `s` or `w` leaves `[1/4,3/8]`, or `r>3/8`.  The proved isosceles
slices and local collapse collars still apply there, but a wider finite atlas
or a global analytic inequality is required to finish the ordered cone.
