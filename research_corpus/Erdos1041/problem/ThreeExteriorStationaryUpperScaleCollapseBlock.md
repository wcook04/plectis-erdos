# Erdős 1041: an upper-scale extension of the stationary collapse atlas

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/2<=w<=3/4.
```

Together with the two lower scale slabs, this proves positivity for the fixed
collapse-side prism

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<=3/4.
```

The checker pins the rigorous outward-rounded binary64 engine and exhausts
`32*16^3=131072` cells. Every coarse cell is green; no refinement is needed.
The weakest lower endpoint and deterministic digest are

```text
0x1.eced4c2b1f62ap-3 = 0.24068698412513473,
bf2a5d558c4e23b7983e1dea72a719b98a84b82b9f26efcdf70dc5ff7689a9a6.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_upper_scale_collapse_block.py
```

This is an exhaustive interval theorem, not sampling. It does not cover the
ordered-cone complement, prove GP3, or prove Erdős 1041.
