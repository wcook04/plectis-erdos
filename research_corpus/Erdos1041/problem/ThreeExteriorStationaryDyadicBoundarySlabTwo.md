# Erdős 1041: second dyadic stationary boundary slab

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 15/16<=w<=31/32.
```

Together with the five adjoining slabs already certified, this proves
positivity on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<=31/32.
```

The checker pins the rigorous outward-rounded binary64 engine and exhausts
`32*16*16*8=65536` cells. Every coarse cell is green. The weakest lower
endpoint and deterministic digest are

```text
0x1.b2af126931e60p+3 = 13.583871083697147,
53fa94acac96745932ed931da59eb5fa7146abbe13e11859f47ec5803c72577e.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_dyadic_boundary_slab_two.py
```

This is an exhaustive interval theorem, not sampling. It does not include
`w=1`, cover the ordered-cone complement, prove GP3, or prove Erdős 1041.
