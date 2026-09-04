# Erdős 1041: a near-isosceles dyadic endpoint collar

The centered strict-curvature certificate proves the active endpoint surplus
through the next dyadic collar

```text
0<=t<=1,
15/16<=r<=31/32,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Here `u=rsw`, `v=sw`, and the endpoint branch has active weight `a`.  The
checker uses

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3,
```

which is the strong endpoint-curvature gain at the switch `kappa=0`; the gain
is increasing in `kappa=bc/(b+c)-a` on the active cone.  Cells proved to have
`bc-a(b+c)<0` are discarded as inactive.  Every remaining cell is rigorously
positive.

| `s` | `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `1462/6730` | `92812/14868` | `0x1.08db88afc4bffp-14` | `d8bb44dd...5b090` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8006/186` | `399/2577` | `0x1.786f586c3b9ffp-13` | `9cd097d9...176e2` |
| `[5/8,3/4]` | `[1/4,1/2]` | `486/7706` | `16699/106597` | `0x1.1d92a32c7ffffp-22` | `6d295b25...55b4` |
| `[5/8,3/4]` | `[1/2,3/4]` | `6719/1473` | `0/23568` | `0x1.f5352abed9fffp-14` | `e31588b5...6fa` |

No unresolved active cell remains.  Together with the preceding blocks, the
exact connected active-endpoint compact rectangle is now

```text
1/8<=r<=31/32, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  The isosceles face `r=1` is known separately, but this note
does not claim the intervening collar `31/32<r<1`, the ordered-cone
complements, GP3, or Erdős 1041.
