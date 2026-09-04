# Minimum-real critical value plus angular bracketing is the wrong selector

## Status

This note gives an exact quintic no-go theorem for a natural selector in the
tied Newton-face programme.  Selecting the critical point at which `Re Q(c)`
is smallest does **not** guarantee that the adjacent root directions
bracketing `arg c` admit contained finite arms and outward tails.

This is a selector obstruction only.  In fact
`TiedNewtonFaceComponentSelector.md` proves that this same critical point is a
strict hub for the actual end pair of its negative component.  What fails is
angular bracketing, which mixes that component with the separate positive-real
end.  The barycentric-envelope route and Erdős #1041 are not refuted.

## The exact quintic

Let

```text
Q(z) = -(379/256) z + 3z^2 - z^5.
```

Its derivative factors exactly as

```text
Q'(z) = -(4z-1)(320z^3+80z^2+20z-379)/256.               (1)
```

Thus `c0=1/4` is critical, and

```text
Q(c0) = -47/256.                                           (2)
```

At any critical point `c`, the derivative equation eliminates `c^5` and
gives

```text
Q(c) = (9/5)c^2-(379/320)c.                               (3)
```

We now prove that `c0` uniquely minimizes the real part of the four critical
values.

Put

```text
p(r)=320r^3+80r^2+20r-379.
```

Since

```text
p'(r)=20(48r^2+8r+1)>0,
p(24/25)=-9239/3125<0,
p(1)=41>0,
```

`p` has a unique real root `r` in `(24/25,1)`.  Equation (3) then makes
`Q(r)>0`, so its critical value is larger than (2).

The remaining roots of `p` are `x+iy` and `x-iy`.  Viete gives

```text
2x+r=-1/4,                 x^2+y^2=379/(320r).
```

Substitution into the real part of (3) yields

```text
Re Q(x+iy)+47/256
  = (11520r^3+13340r^2+4965r-27288)/(12800r)
  = (10460r^2+4245r-13644)/(12800r).                       (4)
```

The second equality uses `p(r)=0`.  The numerator in the final expression is
strictly increasing for positive `r`, and at `r=24/25` it is `8892/125>0`.
Hence both conjugate critical values have real part strictly larger than
`-47/256`.  This proves the claimed uniqueness.

## Why this hub cannot support the adjacent certificate

The argument of `c0` is the positive real fifth-root direction.  Either
adjacent pair bracketing this boundary direction therefore contains that
direction.  But

```text
Q(2/3)=6677/31104>0.                                      (5)
```

For every radial cutoff `R`, there are only two cases:

- if `R<=2/3`, the outward positive-real tail contains `2/3`;
- if `R>=2/3`, the finite arm from `1/4` to `R` contains `2/3`.

Thus no cutoff makes both that arm and its tail lie in `{Re Q<=0}`.  Since
every adjacent bracketing pair uses this direction, the unique
minimum-real-critical-value hub cannot furnish the desired adjacent
arm-and-tail certificate.

The rational factorization, values, cutoff dichotomy, real-root comparison,
and Viete gap kernel are checked in
`TiedNewtonFaceMinimumRealSelectorNoGo.lean`.  The checker independently
replays all symbolic identities and isolates the four critical points.

## Corrected consequence

The paired critical trace theorem remains useful: it guarantees a strictly
negative critical saddle after the disk-forced correction.  What fails is the
composite rule “take the most negative saddle and bracket its argument by
adjacent asymptotic directions.”  The component-degree theorem instead selects
the whole end block carried by that saddle.  The remaining local target is a
pair inside that block with strict negative renormalized defect (or a direct
finite connector), followed by finite transfer.  Angular adjacency is not a
valid replacement for component membership.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_tied_newton_face_minimum_real_selector_no_go.py --json
```
