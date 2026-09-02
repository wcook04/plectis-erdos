# Erdős 1041: the middle-`r` eighth-`s` endpoint block

The exact strong-gain endpoint atlas extends through

```text
0<=t<=1,
1/4<=r<=1/2,
1/8<=s<=1/4,
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
| `[1/4,1/2]` | `5362/2830` | `45280/0` | `0x1.c979048f77fffp-15` | `2d2c2f4a...b16dd8` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.8a43630bd80ccp-3` | `4a5678ec...6144c` |

Every active cell is strictly positive.  There are no inactive cells and no
unresolved active cells.  Together with
`ThreeExteriorEndpointStrongGainEighthSBlock.md`, this gives connected exact
coverage through `r=1/2` on the eighth-`s` slab.  Its terminal `r>1/2` part,
the simultaneous-collapse region `s<1/8`, the remaining `r<1/8` and
outer-`w` slabs, the other GP3 branch, and Erdős 1041 remain open.
