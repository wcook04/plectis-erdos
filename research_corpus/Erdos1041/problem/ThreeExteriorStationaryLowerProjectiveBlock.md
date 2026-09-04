# Erdős 1041: an adjoining lower-projective stationary block

## Status

In the ordered chart `u=r s w`, `v=s w`, the stationary GP3 residual is
strictly positive on

```text
0<=t<=1,
1/8<=r<=1/4,
1/4<=s,w<=3/8.                                        (1)
```

This block adjoins `ThreeExteriorStationaryCompactInteriorBlock.md` along
`r=1/4`.  Their union therefore proves positivity on

```text
0<=t<=1,  1/8<=r<=3/8,  1/4<=s,w<=3/8.                (2)
```

It advances toward the locally covered collapse face `r=0`; it is not a
uniform bridge all the way to that face and does not prove GP3 or Erdős 1041.

## Certificate

The replay imports and pins by SHA-256 the outward-rounded binary64 interval
engine from the adjoining-block checker.  All cell endpoints are dyadic.
The coarse partition uses 32 cells in `t` and 16 in each of `r,s,w`, for
131,072 cells.  Exactly 114,286 are green immediately.  Each of the 16,786
dependency-red cells is bisected in all four directions.  All

```text
16*16786 = 268576
```

children are green; none remains red.  The weakest accepted lower endpoint
is

```text
0x1.7edfd8ef4ffffp-21 = 7.131591512124501e-7 > 0.
```

The deterministic stream of accepted lower endpoints has digest

```text
b50911869c93e6344124169fd7d21ea6f2775ec688655e79c26fdd00329b52b8.
```

Thus the cell union proves (1), and composition with the previous block
proves (2).  There is no sampling or optimizer claim.

## Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_lower_projective_block.py
```

The exact remaining stationary region is the complement of (2), the proved
collapse-face neighborhoods, and the proved isosceles slices.  A further
adaptive atlas or a global analytic inequality is still required.
