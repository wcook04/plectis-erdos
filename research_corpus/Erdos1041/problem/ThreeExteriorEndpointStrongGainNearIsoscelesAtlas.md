# Erdős 1041: the near-isosceles strong-gain endpoint atlas

The centered strict-curvature certificate extends the active endpoint region
through the two dyadic `r` slabs

```text
0<=t<=1,
3/4<=r<=15/16,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Here `u=rsw`, `v=sw`, and the endpoint branch has active weight `a`.  The
checker uses the exact lower bound

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3,
```

from the strong endpoint curvature theorem.  The gain is increasing in
`kappa=bc/(b+c)-a` on the active cone, so its value at `kappa=0` is a valid
uniform payment.  Cells proved to satisfy `bc-a(b+c)<0` are discarded because
the chosen endpoint branch is inactive; all other cells are rigorously
positive.

## Slab `3/4<=r<=7/8`

| `s` | `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `1529/6663` | `105454/1154` | `0x1.5b98310de7fffp-16` | `202643a3...a85aa` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8067/125` | `1395/605` | `0x1.eba3675b457ffp-12` | `2f96e1d3...d8953` |
| `[5/8,3/4]` | `[1/4,1/2]` | `653/7539` | `53195/67429` | `0x1.27b1eaeafbfffp-17` | `4fc7e4c2...7f6eb` |
| `[5/8,3/4]` | `[1/2,3/4]` | `7127/1065` | `78/16962` | `0x1.04822a2cdffffp-17` | `53ce24f4...fc118` |

## Slab `7/8<=r<=15/16`

| `s` | `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `1483/6709` | `99057/8287` | `0x1.40699d4947fffp-16` | `df370fa0...37305` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8032/160` | `660/1900` | `0x1.36bc7f61a8fffp-14` | `c7ed4525...f4401` |
| `[5/8,3/4]` | `[1/4,1/2]` | `536/7656` | `25939/96557` | `0x1.90b4f2545dfffp-13` | `a6d61a09...41c8b` |
| `[5/8,3/4]` | `[1/2,3/4]` | `6854/1338` | `0/21408` | `0x1.7d1dd829597ffp-14` | `25e3ded4...6c68d` |

No unresolved active cell remains.  Together with the preceding blocks, the
exact connected active-endpoint compact rectangle is now

```text
1/8<=r<=15/16, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  The isosceles face `r=1` is known by a separate analytic
theorem, but this certificate does not claim the intervening open collar
`15/16<r<1`.  The remaining ordered-cone complements are also open; neither
GP3 nor Erdős 1041 is claimed.
