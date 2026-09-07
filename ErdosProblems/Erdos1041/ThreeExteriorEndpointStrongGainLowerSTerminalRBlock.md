# Erdős 1041: the terminal-`r` lower-`s` endpoint block

The strong-gain endpoint atlas closes the remaining terminal part of the
lower-`s` strip:

```text
0<=t<=1,
1/2<=r<=1,
3/8<=s<=1/2,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

The checker uses the exact strong-convexity lower bound

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3,
```

with outward-rounded binary64 intervals and centered automatic
differentiation.  Two adjoining `w` certificates give:

| `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---:|---:|---:|---|
| `[1/4,1/2]` | `783/7409` | `118544/0` | `0x1.2cf6f6fe167ffp-14` | `5160646a...af272` |
| `[1/2,3/4]` | `7792/400` | `6400/0` | `0x1.d65dbebb75fffp-16` | `8b65e67b...2cb7d` |

Every active cell is strictly positive.  There are no inactive cells and no
unresolved active cells.  Composing this block with
`ThreeExteriorEndpointStrongGainLowerSBlock.md` and
`ThreeExteriorEndpointStrongGainLowerSMidRBlock.md` proves the maximal
connected lower-`s` theorem

```text
0<=t<=1,
1/8<=r<=1,
3/8<=s<=1/2,
1/4<=w<=3/4,
bc-a(b+c)>=0  ==>  S_true>0.                            (2)
```

The region `s<3/8`, the outer `w` faces, the other GP3 branch, and Erdős 1041
remain open.
