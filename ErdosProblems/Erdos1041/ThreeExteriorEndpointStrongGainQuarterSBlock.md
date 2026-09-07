# Erdős 1041: the first quarter-`s` endpoint block

The exact strong-gain atlas descends across the next adjoining `s` slab on

```text
0<=t<=1,
1/8<=r<=1/4,
1/4<=s<=3/8,
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
| `[1/4,1/2]` | `7193/999` | `15984/0` | `0x1.14b0644679fffp-16` | `b83d29f5...9140c` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.0d4c9fa258a42p-2` | `135a90be...166b8` |

All active cells are strictly positive; there are no inactive cells and no
unresolved active cells.  This overlaps the already proved lower-`s` theorem
along `s=3/8`.  The remaining `r>1/4` portion of this new slab, the region
`s<1/4`, outer `w` faces, the other GP3 branch, and Erdős 1041 remain open.
