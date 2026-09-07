# Erdős 1041: the high-`r` strong-gain endpoint block

The centered strict-curvature certificate extends the active endpoint region
through

```text
0<=t<=1,
5/8<=r<=3/4,
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

which follows from the strong endpoint curvature theorem because its gain is
increasing in `kappa=bc/(b+c)-a` on the active cone.  Four dyadic
subcertificates cover the rectangle.  Cells proved to satisfy
`bc-a(b+c)<0` are discarded because the chosen endpoint branch is inactive;
every remaining cell is rigorously positive.

| `s` | `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `2112/6080` | `97280/0` | `0x1.dbc49a70bcfffp-16` | `81950be6...02d1e` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8174/18` | `288/0` | `0x1.428e74af5247fp-11` | `e64cfd44...f7a9` |
| `[5/8,3/4]` | `[1/4,1/2]` | `1287/6905` | `85617/24863` | `0x1.227e99b657fffp-14` | `10395aa7...d6c8` |
| `[5/8,3/4]` | `[1/2,3/4]` | `7792/400` | `666/5734` | `0x1.f5af578fea1ffp-13` | `038b4a09...8455` |

No unresolved active cell remains.  Together with the preceding blocks, the
exact connected active-endpoint compact rectangle is now

```text
1/8<=r<=3/4, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  The remaining cone is open; neither GP3 nor Erdős 1041 is
claimed.
