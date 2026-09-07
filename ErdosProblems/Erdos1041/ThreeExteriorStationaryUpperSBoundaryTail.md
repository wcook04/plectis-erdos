# Erdős 1041: analytic high-`w` tail on the upper-`s` slab

On the ordered chart `u=r s w`, `v=s w`, the stationary surplus is strictly
positive throughout

```text
0<=t<=1, 0<=r<=1/8, 3/8<=s<=1/2, 31/32<=w<1.
```

This adjoins the previously closed `s<=3/8` prism along the full `s=3/8`
face.

## Proof

Let

```text
ell(x)=(1-x^2)/(1+x+x^2)^2.
```

As in the lower-`s` boundary-tail theorem, `ell` decreases on `[0,1]` and the
stationary kernel satisfies `ell(x)<=L_t(x)<=2`. Here

```text
u<=1/16, v<=1/2,
L_t(u)>=lu=ell(1/16)=21760/24843,
L_t(v)>=lv=ell(1/2)=12/49.
```

The positive `w` self term is at least `31`. Dropping all other positive terms,
the six ordered pair losses total at most

```text
3(uv+uw+vw)<=57/32.
```

Since `p=uvw<=1/32` and `u+v+w<=25/16`, the two global charge losses are at
most

```text
150/31, 75/496.
```

The negative tangent correction is at most

```text
8[(1/16)^2/lv+(1/2)^2/lu+1/(lu+lv)]
=1084769987/113603520.
```

Thus the total negative budget is

```text
C=57473958467/3521709120<31,
```

and the stationary surplus has the exact uniform lower bound

```text
31-C=51699024253/3521709120>0.
```

Replay all rational identities and comparisons with

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_upper_s_boundary_tail.py
```

This theorem closes only the high-`w` tail of the stated upper-`s` slab. It
does not cover its finite-`w` part, prove GP3, or prove Erdős 1041.
