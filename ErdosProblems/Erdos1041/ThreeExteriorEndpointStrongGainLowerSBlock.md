# Erdős 1041: a lower-`s` strong-gain endpoint block

After closing the `r`-direction on the central `s,w` rectangle, the centered
strict-curvature certificate crosses the adjacent lower-`s` face on

```text
0<=t<=1,
1/8<=r<=1/4,
3/8<=s<=1/2,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Here `u=rsw`, `v=sw`, and the endpoint branch has active weight `a`.  The
checker uses the exact switch payment

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3.
```

The gain is increasing in `kappa=bc/(b+c)-a` on the active cone.  Two
adjoining `w` subcertificates cover the block:

| `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---:|---:|---:|---|
| `[1/4,1/2]` | `6572/1620` | `25920/0` | `0x1.7bcd1b61d9bffp-15` | `a27d81d3...e3703c` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.c2405ac076c38p-3` | `1e880924...dfb4f` |

There are no inactive cells and no unresolved cells.  This is a
positive-volume extension across `s=1/2` on the full central `w`-range.  It
does not cover the rest of the lower-`s` face, the outer `w` faces, the other
GP3 branch, or Erdős 1041.
