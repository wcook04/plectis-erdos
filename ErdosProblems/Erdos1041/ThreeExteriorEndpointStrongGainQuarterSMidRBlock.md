# Erdős 1041: the middle-`r` quarter-`s` endpoint block

The exact strong-gain endpoint atlas extends through

```text
0<=t<=1,
1/4<=r<=1/2,
1/4<=s<=3/8,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

The centered interval checker applies

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3,
```

and obtains:

| `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---:|---:|---:|---|
| `[1/4,1/2]` | `4608/3584` | `57344/0` | `0x1.2de3700f867ffp-15` | `cb1240c1...318ee` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.15d7fe98304d7p-3` | `861fad56...29a7d` |

Every active cell is strictly positive.  There are no inactive cells and no
unresolved active cells.  Together with
`ThreeExteriorEndpointStrongGainQuarterSBlock.md`, this gives connected exact
coverage through `r=1/2` on the quarter-`s` slab.  Its terminal `r>1/2` part,
the region `s<1/4`, outer `w` faces, the other GP3 branch, and Erdős 1041
remain open.
