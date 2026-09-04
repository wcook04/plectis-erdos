# Erdős 1041: the adjoining upper-scale strong-gain endpoint block

The centered-form strong-curvature certificate extends across the adjoining
ordered-chart block

```text
0<=t<=1,
1/8<=r<=1/4,
1/2<=s<=5/8,
1/2<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Here `u=rsw`, `v=sw`, and `a,b,c` are the three tangent weights with the
endpoint branch active at `a`.  With

```text
mu=4uv[v J_t(v)+u J_t(u)],
nu=b^2c^2/(b+c)^3,
```

the strong curvature theorem gives

```text
S_true >= S_end+9mu nu/[8(mu+nu)].                     (2)
```

The checker evaluates the right side by rigorous centered binary64 interval
automatic differentiation on a `16*8^3=8192` dyadic partition of (1).  All
`8192` boxes are green without refinement.  The weakest lower endpoint is

```text
0x1.738de557cd736p-3 = 0.18142298864557355 > 0,
```

and the ordered digest is

```text
c7a7f6679a117b2a33748a39d35f4377559e0dc1e18d06eac9e9e62528ba1f13.
```

Together with `ThreeExteriorEndpointStrongGainCompactBlock.md`, this closes
the same `r,s` rectangle for `1/4<=w<=3/4`.  It does not cover the remaining
ordered cone, prove GP3, or prove Erdős 1041.
