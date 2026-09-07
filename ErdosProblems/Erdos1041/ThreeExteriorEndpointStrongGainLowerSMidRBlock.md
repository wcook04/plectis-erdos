# Erdős 1041: the middle-`r` lower-`s` endpoint block

The lower-`s` strong-gain atlas extends through

```text
0<=t<=1,
1/4<=r<=1/2,
3/8<=s<=1/2,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

As in the preceding block, the centered checker applies the switch payment

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3.
```

Two adjoining `w` certificates cover the full central range:

| `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---:|---:|---:|---|
| `[1/4,1/2]` | `3768/4424` | `70784/0` | `0x1.5290e5071a7ffp-15` | `a20144e5...65443` |
| `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.1ab505a607fa3p-4` | `7ff0c479...97802` |

All active cells are strictly positive.  There are no inactive cells and no
unresolved cells.  Together with `ThreeExteriorEndpointStrongGainLowerSBlock.md`,
this proves the connected lower-`s` region through `r=1/2`.  The remaining
`r>1/2` part of this lower-`s` strip, outer `w` faces, other GP3 branch, and
Erdős 1041 remain open.
