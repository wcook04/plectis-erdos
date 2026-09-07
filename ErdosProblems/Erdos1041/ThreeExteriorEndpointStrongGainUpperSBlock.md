# Erdős 1041: the upper-`s` strong-gain endpoint block

The centered-form strict-curvature method closes the adjoining upper-`s`
rectangle of the active endpoint cone:

```text
0<=t<=1,
1/8<=r<=1/4,
5/8<=s<=3/4,
1/4<=w<=3/4,
bc-a(b+c)>=0.                                          (1)
```

The certificate evaluates the exact lower bound

```text
S_true >= S_end+9mu nu/[8(mu+nu)]
```

from the strong endpoint-curvature theorem, using centered interval automatic
differentiation.  It splits the `w` range at `1/2`.

On `1/4<=w<=1/2`, a `16*8^3` coarse partition has `5621` green and `2571`
dependency-red cells; all `41136` dyadic four-coordinate children are green.
The weakest lower endpoint and digest are

```text
0x1.67abdc12cffffp-19 = 2.6797602087624824e-6,
ca328f8d6115b5e6a83cf91260d06e7e67b12dcf1d99529670380025968e66f9.
```

On `1/2<=w<=3/4`, all `8192` coarse cells are green, with

```text
0x1.3388a897a6438p-3 = 0.15016299927518317,
2c8b1faaed55d21480f92a04867ab4fbddc6e9ba55d88293186cb5d18f4c3b8f.
```

Together with the preceding two strong-gain blocks, this proves positivity
on the active endpoint rectangle

```text
1/8<=r<=1/4, 1/2<=s<=3/4, 1/4<=w<=3/4
```

for every `t`.  The remaining ordered cone is not covered; GP3 and Erdős 1041
are not claimed.
