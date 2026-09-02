# Erdős 1041: the middle-`r` strong-gain endpoint block

The centered strict-curvature certificate extends the active endpoint
rectangle through

```text
0<=t<=1,
3/8<=r<=1/2,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

The four exact dyadic subcertificates, split at `s=5/8` and `w=1/2`, are:

| `s` | `w` | coarse green/red | refined green | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `3595/4597` | `73552` | `0x1.c71b65f35dfffp-17` | `ca20a1f0...7b092` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8192/0` | `0` | `0x1.05508a9118a13p-4` | `ab9cda52...ba3d0` |
| `[5/8,3/4]` | `[1/4,1/2]` | `3016/5176` | `82816` | `0x1.11b62c00ab7ffp-15` | `dbd132ce...ed5d7` |
| `[5/8,3/4]` | `[1/2,3/4]` | `8192/0` | `0` | `0x1.0c3558b31ed9fp-8` | `89af2c11...eafeb` |

Every refined child is green.  With the preceding blocks, the certified
active-endpoint compact rectangle is now

```text
1/8<=r<=1/2, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for all `t`.  The complement remains open; GP3 and Erdős 1041 are not
claimed.
