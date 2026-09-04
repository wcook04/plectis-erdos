# Erdős 1041: the upper-middle-`r` strong-gain endpoint block

The centered strict-curvature certificate extends the active endpoint region
through

```text
0<=t<=1,
1/2<=r<=5/8,
1/2<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

Four dyadic subcertificates cover the rectangle.  Cells proved to satisfy
`bc-a(b+c)<0` are discarded because the chosen endpoint branch is inactive;
every remaining cell is rigorously positive.

| `s` | `w` | coarse green/red | refined green/inactive | weakest lower bound | digest |
|---|---|---:|---:|---:|---|
| `[1/2,5/8]` | `[1/4,1/2]` | `2807/5385` | `86160/0` | `0x1.f9710babaffffp-18` | `53d4c04b...a1ed0` |
| `[1/2,5/8]` | `[1/2,3/4]` | `8192/0` | `0/0` | `0x1.a924fdd904aefp-7` | `0272e3f3...b5670` |
| `[5/8,3/4]` | `[1/4,1/2]` | `2073/6119` | `96111/1793` | `0x1.e45335d816fffp-15` | `cbb39272...a20bb` |
| `[5/8,3/4]` | `[1/2,3/4]` | `8137/55` | `399/481` | `0x1.e170f919ac3ffp-13` | `dc0e1ff3...9f290` |

No unresolved cell remains.  Together with the preceding blocks, the exact
active-endpoint compact rectangle is now

```text
1/8<=r<=5/8, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  The remaining cone is open; GP3 and Erdős 1041 are not
claimed.
