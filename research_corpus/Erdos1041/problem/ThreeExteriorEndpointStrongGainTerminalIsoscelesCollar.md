# Erdős 1041: the terminal isosceles endpoint collar

The centered strict-curvature certificate closes the entire remaining
`r`-tail of the active endpoint region:

```text
0<=t<=1,
31/32<=r<=1,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Here `u=rsw`, `v=sw`, and the endpoint branch has active weight `a`.  Since
`s<=3/4<1`, the terminal face `r=1` is an off-diagonal isosceles slice rather
than the regular equality locus.  The checker proves the whole collar at
once using

```text
S_true >= S_end + 9*mu*nu/(8*(mu+nu)),
nu=b^2*c^2/(b+c)^3.
```

This is the strong endpoint-curvature gain at the switch `kappa=0`; the gain
is increasing in `kappa=bc/(b+c)-a` on the active cone.

The replay keeps the two logical outcomes separate.  A cell is counted
**inactive** only after interval arithmetic proves `bc-a(b+c)<0`.  Otherwise
it is counted **green** only after the centered lower bound for the true
endpoint surplus is strictly positive.  Inactive cells are not treated as
sign proofs.

| `s` | `w` | coarse green/red | refined green/inactive | weakest active lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `1360/6832` | `89339/19973` | `0x1.ad0c036292fffp-15` | `7253ff89...3556a` |
| `[1/2,5/8]` | `[1/2,3/4]` | `7932/260` | `440/3720` | `0x1.1bc2a1d795bffp-14` | `e1000e7e...5b80` |
| `[5/8,3/4]` | `[1/4,1/2]` | `380/7812` | `12633/112359` | `0x1.cab2e828defffp-14` | `8d6b4b83...f033` |
| `[5/8,3/4]` | `[1/2,3/4]` | `6511/1681` | `0/26896` | `0x1.41b7d369d83ffp-13` | `79619f06...a6c2` |

There are zero unresolved cells.  Composing this terminal collar with
`ThreeExteriorEndpointStrongGainNearIsoscelesDyadicCollar.md` and the earlier
connected endpoint atlas proves the full `r`-direction on the compact
ordered rectangle:

```text
0<=t<=1,
1/8<=r<=1,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (2)
```

Thus the near-isosceles `r` face is no longer an open boundary for the active
endpoint branch on this `s,w` block.  The complements in `r<1/8`,
`s` outside `[1/2,3/4]`, or `w` outside `[1/4,3/4]` remain open, as do the
other GP3 branch and the parent Erdős 1041 theorem.
