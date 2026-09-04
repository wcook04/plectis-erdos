# Erdős 1041: the upper-`r` strong-gain endpoint block

Four centered-form certificates extend the active-endpoint rectangle to

```text
0<=t<=1,
1/4<=r<=3/8,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Each certificate evaluates the strict-curvature lower bound

```text
S_true >= S_end+9mu nu/[8(mu+nu)]
```

on a `16*8^3` dyadic partition.  Splitting both `s` and `w` at their
midpoints gives the following exact replay data:

| `s` | `w` | coarse green/red | refined green | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `4573/3619` | `57904` | `0x1.a35be13c627ffp-15` | `ab929b08...ac46a2` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8192/0` | `0` | `0x1.e296def52e22fp-4` | `46e7b759...7be8c` |
| `[5/8,3/4]` | `[1/4,1/2]` | `4104/4088` | `65408` | `0x1.4f220d90993ffp-14` | `0c92bf11...50766c` |
| `[5/8,3/4]` | `[1/2,3/4]` | `8192/0` | `0` | `0x1.2beb10b70cdffp-4` | `023babaa...3a91cd` |

All refined children are green and no cell remains red.  Together with the
previous strong-gain blocks, positivity is now proved on the full active
endpoint compact rectangle

```text
1/8<=r<=3/8, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  This does not cover the remaining ordered cone, prove GP3, or
prove Erdős 1041.
