# Erdős 1041: a high-scale extension of the stationary collapse bridge

## Status

The stationary GP3 surplus is strictly positive in the ordered chart on

```text
0<=t<=1,  0<=r<=1/8,  1/4<=s<=3/8,  3/8<=w<=1/2.     (1)
```

This block adjoins the fixed-width collapse bridge along `w=3/8`.  Their
union proves positivity for

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<=1/2.        (2)
```

## Certificate

The checker pins and reuses the rigorous outward-rounded binary64 interval
engine from the first compact block.  A uniform `32*16^3=131072`-cell
partition proves (1) without refinement: every cell is green.  The weakest
lower endpoint is

```text
0x1.2617fddfebc51p-4 = 0.07180022401620191 > 0,
```

and the accepted-endpoint digest is

```text
2daa67235965f35a919c2c965d6ae6b5dcf68142b46957101f0d2b8e6fad44a6.
```

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_high_scale_collapse_block.py
```

This is an exhaustive interval theorem, not sampling.  It widens the
collapse-side atlas to (2), but does not cover the rest of the ordered cone,
prove GP3, or prove Erdős 1041.
