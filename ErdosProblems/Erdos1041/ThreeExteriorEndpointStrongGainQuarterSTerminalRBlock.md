# Erdős 1041: terminal `r` and the central endpoint rectangle

The exact strong-gain endpoint atlas closes the terminal part of the
quarter-`s` slab:

```text
0<=t<=1,
1/2<=r<=1,
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
| `[1/4,1/2]` | `1603/6589` | `105424/0` | `0x1.1952a5818cbffp-13` | `0dbcd02b...e4eb8f` |
| `[1/2,3/4]` | `8151/41` | `656/0` | `0x1.351ea34ce1fffp-13` | `25549e34...28a8c` |

Every active cell is strictly positive.  There are no inactive cells and no
unresolved active cells.

## Composed central-rectangle theorem

Together with the source-current lower-`s`, quarter-`s`, and upper endpoint
blocks, this proves

```text
0<=t<=1,
1/8<=r<=1,
1/4<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0  ==>  S_true>0.                            (2)
```

The displayed rectangle has raw `(r,s,w)` chart volume

```text
(1-1/8)*(3/4-1/4)*(3/4-1/4)=7/32.
```

This is only a transparent coordinate-volume statement; it is not a measure
claim about the nonlinear active cone.  Outside this rectangle the remaining
parameter slabs are `r<1/8`, `s<1/4`, `s>3/4`, `w<1/4`, and `w>3/4`, with
overlaps among them.  Existing face and collapse collars cover parts of those
slabs, but not their whole active interiors.  The other GP3 branch and Erdős
1041 also remain open.
