# Erdős #1041: the sextic null branch has a strict companion

Status, 2026-08-25: complete analytic companion-connector theorem, exact
symbolic replay, and Lean formalization of the mirror chord and ray
certificates. This repairs the temporary optimality overclaim in
`SexticNullBranch.md`: the zero-contact family is valid, but another connector
is strictly better for positive branch parameter. This is still a homogeneous
sextic model theorem, not finite transfer or unrestricted Erdős #1041.

## The mirror construction

Retain the null-branch parameters

```text
s=sqrt(3),  q0=(7+4s)/27,  beta*=(106+25s)/1221,
R^4=q0(1+(3/2)beta(s-1)),
c=beta/R,  u=3 beta R(2-s).
```

For `0<=beta<=beta*`, use the opposite adjacent pair `(0,5)` and the mirror
truncation radius

```text
rho^4=q0(1-(3/2)beta(s-1)).                              (1)
```

Then `R>=rho>0`. Put `L=R/rho>=1` and `M=rho/R<=1`.

After division by `rho^2/2`, the actual chord polynomial is

```text
C_beta(t)=P(t)(1-q(-beta)Q(t))
           -3s beta L(2-s)t+3s beta M t(1-t).            (2)
```

The mirror polynomial is the previously formalized affine chord evaluated at
the negative parameter:

```text
F_{-beta}(t)=P(t)(1-q(-beta)Q(t))
             -3s beta(2-s)t+3s beta t(1-t).              (3)
```

Since `L>=1`, `M<=1`, `0<=t<=1`, both coefficient corrections have the
favourable sign, so

```text
C_beta(t)<=F_{-beta}(t).                                 (4)
```

For `beta>0`, `L>1`, and `0<t<=1`, the first correction is strict.

## Exact mirror endpoint

The family `F_{-beta}` is affine in beta. At beta zero it is the canonical
nonpositive chord. At the other endpoint,

```text
F_{-beta*}(t)
=-(4943+2813s)/10989 (t-s+1)^2 Q_4(t),                  (5)
```

where the degree-four Bernstein coefficients of `Q_4` are

```text
(40775-17588s)/1706,
(46577-12145s)/3412,
(17575+4062s)/3412,
(-9721+15151s)/3412,
(-9041+5707s)/853.
```

They are all positive using only `50/29<sqrt(3)<2`. Hence (5) is
nonpositive, and convex interpolation proves `F_{-beta}<=0` throughout the
interval. Equation (4) proves the actual companion chord.

## Rays

The real ray is `-x^2-x^6<0`. On the lower non-real ray, write `x=rho y`,
`y>=1`. The actual value is bounded by

```text
G_{-beta}(y)=-3s beta(2-s)y+y^2-2q(-beta)y^6.            (6)
```

At `y=1`, the earlier exact factor is already nonpositive. Moreover

```text
q(-beta)>=q(-beta*)=0.4465947...>1/6,
y^6-1=(y^2-1)(y^4+y^2+1)>=3(y^2-1).
```

Therefore the positive growth `y^2-1` is absorbed by
`2q(-beta)(y^6-1)`, while the linear term only decreases. Thus every outward
ray point is nonpositive. The adjacent-pair path length is `2-rho<2`.

## Consequence

The unique first-order null direction is not an optimized equality edge. It
has a companion connector with a strict chord comparison for every positive
parameter. This converts the earlier apparent degeneracy into quantitative
slack and supplies the correct input for a finite neighbourhood theorem.
What remains is to extract an explicit uniform margin in coefficient space,
cover the other sextic faces, and transfer the atlas to actual polynomials.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_sextic_null_branch_companion.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems/Erdos1041/SexticNullBranchCompanion.lean
```
