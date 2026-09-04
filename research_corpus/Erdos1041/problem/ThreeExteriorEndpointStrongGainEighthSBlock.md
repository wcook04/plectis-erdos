# Erdős 1041: the first eighth-`s` endpoint block

The exact strong-gain endpoint atlas descends into the next slab:

```text
0<=t<=1,
1/8<=r<=1/4,
1/8<=s<=1/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

The centered interval checker proves

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)) > 0,
nu=b^2*c^2/(b+c)^3.
```

The two exact `w` certificates are:

| `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---:|---:|---:|---|
| `[1/4,1/2]` | `7755/437` | `6992/0` | `0x1.577d63323ffffp-20` | `aeb30a77...b49c7` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.3e747f0fccc7fp-2` | `de49c12a...9ee40` |

All active cells are strictly positive; there are no inactive cells and no
unresolved active cells.  This block overlaps the central rectangle along
`s=1/4`.  Its continuation through `r>1/4`, the lower slab `s<1/8`, the
remaining `r<1/8` and outer-`w` slabs, the other GP3 branch, and Erdős 1041
remain open.
