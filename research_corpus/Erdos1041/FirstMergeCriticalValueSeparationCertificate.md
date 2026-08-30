# Erdős 1041: a critical-value separation certificate for the first merge

Status: ordinary exact analytic theorem with an exact symbolic checker.
2026-08-30.  This is a genuine all-degree sufficient regime, not the
unrestricted theorem.

## Theorem

The radius-four statement below is the uniform all-degree form of a more
general estimate.  If `S>1` and every other critical point satisfies

```text
|1-P(d)| >= S,
```

then the identical argument, with continuation radius `sqrt(S)`, gives

```text
integral_(-1)^1 |Z'(xi)| dxi
  <= 2 * (1+S)^(1/n) * sqrt(log(S/(S-1))).              (CVS-S)
```

Thus the connector is strictly shorter than two whenever

```text
(1+S)^(2/n) log(S/(S-1)) < 1.                           (T-S)
```

Three exact convenient thresholds are:

```text
n >= 3:  S=4;
n >= 4:  S=3;
n >= 7:  S=2.
```

The latter two substantially shrink the unresolved critical-value cluster in
higher degree; they are consequences of the same theorem, not computational
observations.

Let `P` be a degree-`n` polynomial, `n >= 3`, whose leading coefficient has
modulus one.  Suppose

```text
P(0)=1,    P'(0)=0,    P''(0) != 0,
```

and every other critical point `d != 0` of `P` satisfies

```text
|1-P(d)| >= 4.                                           (S4)
```

Let `Z` be either of the two local solutions at the saddle of

```text
P(Z(xi)) = 1-xi^2,    Z(0)=0.
```

Then `Z` continues holomorphically and injectively to `|xi|<2`, the two
points `Z(-1),Z(1)` are distinct roots of `P`, and their canonical resolved
inverse-ray connector satisfies

```text
integral_(-1)^1 |Z'(xi)| dxi
  <= 2 * 5^(1/n) * sqrt(log(4/3))
  < 2.                                                   (CVS)
```

Consequently, if `f` is monic, `c` is a simple critical point with
`v=f(c) != 0`, and

```text
|1-f(d)/f(c)| >= 4
```

for every other critical point `d`, then two roots are joined inside
`{|f|<=|v|}` by a path of length strictly below `2|v|^(1/n)`.  In particular,
when all roots of `f` lie in the open unit disk, this proves Erdős 1041 for
that polynomial: (S4) makes `c` the unique minimum-modulus critical point,
the Fekete chain gives `|v|<1`, and the connector has length below two inside
`{|f|<1}`.

## Proof

The simple critical point has local form

```text
P(z)=1+A z^2+O(z^3),    A != 0,
```

so the square substitution resolves it and supplies two local holomorphic
solutions, interchanged by `xi -> -xi`.  A finite branch point of their
algebraic continuation can occur only when `P'(d)=0` and

```text
xi^2=1-P(d).
```

The branch point belonging to `d=0` has already been resolved.  Assumption
(S4) puts every other branch point on or outside `|xi|=2`.  Properness of a
polynomial rules out escape to infinity over the bounded value set.  The
monodromy theorem therefore continues `Z` holomorphically through the open
disk `D_2`.

It is injective there.  Indeed, `Z(xi_1)=Z(xi_2)` implies
`xi_1^2=xi_2^2`.  If `xi_2=-xi_1 != 0`, the two inverse sheets meet at a
regular point of `P`, which is impossible by local inverse uniqueness; a
meeting could occur only at one of the excluded branch points.  Thus
`xi_1=xi_2`.

Write

```text
Z(xi)=sum_(k>=1) a_k xi^k.
```

More generally, under separation `S>1`, for every `1<R<sqrt(S)`, injectivity
and the area formula give

```text
pi sum_(k>=1) k |a_k|^2 R^(2k) = Area(Z(D_R)).           (1)
```

Since `P(Z(xi))=1-xi^2`, the image lies in
`{|P|<1+R^2}`.  Pólya's area--capacity inequality and the unit-modulus leading
coefficient give

```text
Area(Z(D_R)) <= Area{|P|<1+R^2}
              <= pi (1+R^2)^(2/n).                      (2)
```

Cauchy--Schwarz, (1), and (2) now yield

```text
sum_(k>=1) |a_k|
 <= (1+R^2)^(1/n)
    sqrt(sum_(k>=1) 1/(k R^(2k)))
 =  (1+R^2)^(1/n) sqrt(log(R^2/(R^2-1))).               (3)
```

Termwise integration of the absolutely convergent power series on
`[-1,1]` gives

```text
integral_(-1)^1 |Z'| <= 2 sum_(k>=1)|a_k|.
```

Letting `R` increase to `sqrt(S)` proves `(CVS-S)`.  Taking `S=4` proves the
first inequality in (CVS).  For the strict last inequality, square the
coefficient.  For `n>=3`,

```text
5^(2/n) log(4/3)
 <= 5^(2/3) log(1+1/3)
 <  5^(2/3)/3
 <  1,
```

where `log(1+x)<x` for `x>0` and `5^(2/3)<3` is exactly `25<27` after cubing.

For `S=3` and `n>=4`, the squared coefficient is strictly below

```text
4^(2/n) log(3/2) <= 2 log(1+1/2) < 1.
```

For `S=2` and `n>=7`, use `log 2 < 7/10`.  This logarithmic bound is exact from
the positive exponential series, since

```text
exp(7/10) > 1 + 7/10 + (7/10)^2/2 + (7/10)^3/6
          = 12013/6000 > 2.
```

The remaining radical inequality is exact because

```text
(3^(2/7) * 7/10)^7 = 9*7^7/10^7
                     = 7411887/10000000 < 1.
```

Finally normalize `f` by `z=c+rho e^(i theta)w`,
`rho=|f(c)|^(1/n)`, choosing the harmless rotation so the normalized leading
coefficient has modulus one.  Critical values become `f(d)/f(c)`, lengths
are multiplied by `rho`, and the real `xi` segment has
`f/f(c)=1-xi^2 in [0,1]`.  This proves the scaled conclusion and containment.

## Why this advances, but does not close, the frontier

The proof turns critical-value separation into an analytic-continuation disk
and then spends its extra radius through a coefficient/area estimate.  It is
precisely the regime in which the ordinary endpoint Bergman estimate was too
weak: the latter sees the merge point on the boundary and has a logarithmic
divergence, while (S4) exposes a larger disk on the resolved cover.

The surviving boundary is exact relative to `(T-S)`: this certificate says
nothing once another critical value enters the chosen separation disk.  The
convenient unresolved disks have squared resolved radii `4` in degree three,
`3` in degrees four through six, and `2` from degree seven onward.  In
particular the theorem does not handle the near-tie and multiple-saddle strata,
where several branch points approach the resolved origin.  Those strata
require a grouped critical-value contour, the partial-cluster identity, or
another argument.  No claim is made that these convenient thresholds are
sharp, and no unrestricted capacity-geodesic theorem, COVER theorem, or Erdős
1041 proof follows without covering the complementary critical-value cluster
regime.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_first_merge_critical_value_separation.py
```

The checker verifies the exact constant chain, the branch-value algebra, and
the nonempty boundary example `P(z)=1-3z^2+z^3`, whose other critical point is
`2` and satisfies `1-P(2)=4`.  The analytic continuation, univalence, area
formula, and Pólya inequality remain ordinary mathematics as proved above.
