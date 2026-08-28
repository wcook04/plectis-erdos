# Erdős 1041: the symmetric merge envelope is exact for two exterior roots

## Status

This note proves the fixed-product symmetric-envelope conjecture from
`CapacitySaturationBridge.md` when the component has exactly two exterior
roots.  It is an ordinary exact proof, replayed by
`scripts/check_erdos1041_two_exterior_symmetric_envelope.py`.

The unrestricted parent theorem remains open.  The first unsupported case of
the envelope is now three exterior roots.

## Theorem

Let `U` be a proper regular component of `{|f|<t}` for a monic degree-`n`
polynomial, containing `n-2` roots.  In the exterior-disc coordinate write

```text
B(z)=(z-a)(z-b)/[(1-conj(a)z)(1-conj(b)z)],
W(z)=unit*t*z^n/B(z),
p=|ab|=cap(closure U)^n/t.
```

Let `b_next` be the first level at which `U` acquires an excluded root.  Put

```text
s=sqrt(p),
B_s(z)=(z^2-p)/(1-pz^2).
```

> **Theorem (two-exterior symmetric envelope).** One has
>
> ```text
> b_next/t <= max_(1<=x<=1/s) x^n(1-px^2)/(x^2-p).       (1)
> ```
>
> The right side is exactly the first exterior critical level of
> `t*z^n/B_s(z)`.  Equivalently, if `y>1` is the larger root of
>
> ```text
> y^2-[((n+2)p^2+(n-2))/(np)]y+1=0,                     (2)
> ```
>
> then
>
> ```text
> b_next/t <= y^(n/2)(1-py)/(y-p).                       (3)
> ```

Thus, among all two-zero exterior Blaschke products with fixed `|B(0)|=p`,
the equal-radius antipodal configuration gives the sharp radial attachment
barrier.  Equality in the pointwise polarization away from the boundary
requires equal radii and antipodal arguments.

## Proof

Choose the exterior zero of larger modulus and rotate so it is `a=r>0`.
Write

```text
b=rho*exp(i phi),    r*rho=p,    r>=sqrt(p)=s.
```

Follow the actual radial attachment segment `z=x`, `1<=x<=1/r`, from the
boundary of `U` to the excluded root `1/r`.  On it,

```text
|W(x)|/t
 = x^n (1-rx)/(x-r)
   * sqrt[(1-2rho*x*cos(phi)+rho^2*x^2)
          /(x^2-2rho*x*cos(phi)+rho^2)].                 (4)
```

Put `c=cos(phi)` and call the quotient under the square root `Q(c)`.  Direct
differentiation gives

```text
Q'(c)=2rho*x(1-x^2)(1-rho^2)
      /(x^2-2rho*x*c+rho^2)^2 <= 0.                      (5)
```

Hence the spectator obstruction is largest at `c=-1`, i.e. when the zeros
are antipodal.  Therefore (4) is at most

```text
F_r(x)=x^n (1-rx)(1+rho*x)/[(x-r)(x+rho)].               (6)
```

The remaining radius polarization is pointwise and exact.  Since `rho=p/r`,

```text
F_s(x)/x^n - F_r(x)/x^n
 = x(x^2-1)(1+p)(r^2-p)
   /[(x^2-p)(p+rx)(x-r)] >= 0.                           (7)
```

All denominators are positive on `1<x<1/r`; the endpoints follow by
continuity.  Also `r>=s` implies `[1,1/r]` is contained in `[1,1/s]`.
Consequently the maximum of (4) on the actual attachment segment is at most
the right side of (1).  This proves the merge ceiling.

For the symmetric product, set `y=x^2`.  Differentiating the profile in (1)
gives the reciprocal quadratic (2), and its larger root gives (3).  The sharp
proper-component capacity gap supplies `p<(n-2)/(n+2)`, so the symmetric
profile has the asserted interior maximum. ∎

## Frontier effect

The conjectural inequality `b_next<=b_sym(n,m,p)` is now a theorem for
`m=1` (the last-lobe law) and `m=2` (this note).  The proof reveals two exact
polarization moves:

1. angular polarization sends a spectator opposite the selected zero;
2. radial polarization equalizes their moduli at fixed product.

For `m>=3`, iterating these pairwise moves changes the selected closest zero
and the attachment ray, so a genuine multi-spectator polarization or
mountain-pass monotonicity theorem is still required.  The first live case is
`m=3`, where computation converges to equal radii at `120`-degree spacing.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_two_exterior_symmetric_envelope.py
```

