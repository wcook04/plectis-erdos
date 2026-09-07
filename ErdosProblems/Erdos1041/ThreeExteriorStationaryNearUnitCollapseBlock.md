# Erdős 1041: a near-unit extension of the stationary collapse atlas

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 3/4<=w<=7/8.
```

Together with the three adjoining lower-scale slabs, this proves positivity on
the fixed collapse-side prism

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<=7/8.
```

The checker pins the rigorous outward-rounded binary64 engine and exhausts
`32*16*16*8=65536` cells. Every coarse cell is green; no refinement is needed.
The weakest lower endpoint and deterministic digest are

```text
0x1.d6440a63206e3p+0 = 1.8369757167824268,
bbe08e266c6797df44e102990ffa88fdb50ad76bda034934e4e942dd276d62d2.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_near_unit_collapse_block.py
```

This is an exhaustive interval theorem, not sampling. It does not cover the
ordered-cone complement, prove GP3, or prove Erdős 1041.
