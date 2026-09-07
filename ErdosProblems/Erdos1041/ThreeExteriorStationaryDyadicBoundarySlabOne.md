# Erdős 1041: first dyadic stationary boundary slab

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 7/8<=w<=15/16.
```

Together with the four adjoining slabs already certified, this proves
positivity on

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<=15/16.
```

The checker pins the rigorous outward-rounded binary64 engine and exhausts
`32*16*16*8=65536` cells. Every coarse cell is green. The weakest lower
endpoint and deterministic digest are

```text
0x1.6ad821bab65bbp+2 = 5.669441635452524,
b7e5bbae6ec896953e677aa5da3deffcfc68d431b772090a266ba12e6edeceb4.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_dyadic_boundary_slab_one.py
```

This is an exhaustive interval theorem, not sampling. It does not include
`w=1`, cover the ordered-cone complement, prove GP3, or prove Erdős 1041.
