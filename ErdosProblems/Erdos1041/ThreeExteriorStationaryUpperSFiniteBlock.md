# Erdős 1041: a finite upper-`s` stationary block

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 3/8<=s<=1/2, 1/4<=w<=1/2.
```

This positive-volume block adjoins the earlier full lower-`s` prism along
`s=3/8` and the analytic upper-`s` high-`w` tail in the same ordered chart.

The checker pins the rigorous outward-rounded binary64 engine. On
`w in [1/4,3/8]`, it checks 131072 coarse cells: 107143 are immediately green,
and all 382864 four-coordinate dyadic children of the 23929 dependency-red
cells are green. On `w in [3/8,1/2]`, all 131072 coarse cells are green. The
weakest accepted lower endpoint is

```text
0x1.50a67975affffp-21 = 6.270600311983342e-7.
```

The deterministic accepted-lower-bound digests are

```text
d0553d434a6048b79f2743119f0327c747d486bfccc9a038d5447043ac3b74d7,
35597198cc68a1f049b0d7d183cbe15256bdfeb58325a6c8a0998f1e44286e8f.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_upper_s_finite_block.py
```

This is an exhaustive interval theorem, not sampling. It does not yet cover
`1/2<w<31/32` on this upper-`s` slab, prove GP3, or prove Erdős 1041.
