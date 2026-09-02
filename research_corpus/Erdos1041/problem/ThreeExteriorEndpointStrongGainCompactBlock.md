# Erdős 1041: a compact active-endpoint block from the strict curvature gain

In the ordered chart

```text
u=r s w,  v=s w,
```

consider the endpoint cone active at the `uv` weight:

```text
a=uv(L_u+L_v), b=uw(L_u+L_w), c=vw(L_v+L_w),
F=bc-a(b+c)>=0.                                          (1)
```

The true, unlinearized GP3 surplus is strictly positive on the compact block

```text
0<=t<=1,  1/8<=r<=1/4,  1/2<=s<=5/8,  1/4<=w<=1/2.     (2)
```

## Certified lower bound

Write `R` for the angle-independent radial term.  The tangent endpoint
residual is evaluated in the cancellation-free endpoint branch form

```text
S_end=R+(3a-b-c)/2.                                     (3)
```

For the active pair, exact differentiation in normalized variables gives

```text
mu=4uv[v J_t(v)+u J_t(u)],
J_t(x)=(1-x)/(1+x)^5+t^2(1-tx)/(1+tx)^5.               (4)
```

Put `nu=b^2c^2/(b+c)^3`.  The strong endpoint-curvature theorem proves on the
whole active cone that

```text
S_true >= S_end + 9mu nu/[8(mu+nu)].                    (5)
```

The checker certifies the right side of (5) directly.  It first partitions
(2) into `16*8^3=8192` dyadic boxes.  On each box it uses the rigorous
first-order centered form

```text
B(m)+sum_j (partial_j B)(box_j)(box_j-m_j),             (6)
```

with binary64 interval automatic differentiation and one-ulp outward
rounding after every primitive operation.  Of the coarse boxes, `6020` are
green.  Each of the remaining `2172` dependency-red boxes is bisected in all
four coordinates; all `34752` children are green.  The weakest accepted
lower endpoint is

```text
0x1.e3ea730897fffp-17 = 1.4421815209775256e-5 > 0.       (7)
```

The SHA-256 digest of the accepted lower endpoints, in deterministic cell
order, is

```text
13f0965f34498e29e80c4f18a5e32ae1a49e91ad8730ad635de49e6dd7b2303c.
```

Replay with

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_strong_gain_compact_block.py
```

This is a positive-volume block of the active endpoint cone.  It does not
cover the remaining ordered chart, prove GP3, or prove Erdős 1041.
