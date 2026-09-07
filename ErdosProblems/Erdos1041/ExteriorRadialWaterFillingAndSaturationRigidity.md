# Erdős 1041: exterior radial water-filling and saturation rigidity

## Status

This note proves three exact consequences of the exterior finite-Blaschke
model:

1. a sharp radial attachment ceiling retaining both the zero product `p` and
   the largest zero radius `r`;
2. uniqueness of the regular finite-Blaschke product at equality in the sharp
   exterior product-capacity bound;
3. a derivative-range and conformal-port separation theorem obtained from the
   Kovalev--Yang boundary-derivative inequality.

It then gives exact degree-two and degree-three obstructions showing why the
new scalar radial ceiling, even together with the Boolean boundary-speed
condition, does not prove the symmetric merge envelope.  The missing datum is
angular distribution.  No general symmetric envelope, terminal-block metric
theorem, or unrestricted Erdős 1041 result is claimed.

## 1. The `(p,r)` radial water-filling ceiling

Let `B` be a degree-`m` finite Blaschke product with nonzero zeros
`a_1,...,a_m`, and let

```text
W(z)=unit*t*z^n/B(z),       n>m>=2,
p=product_j |a_j|.
```

Choose a zero of largest modulus, rotate it to `a_1=r>0`, and put

```text
u=p/r^(m-1).                                             (1)
```

Then `0<u<=r<1`.  The radial segment `1<=x<=1/r` joins the component boundary
to the excluded root corresponding to `a_1`.

> **Theorem 1 (radial water-filling ceiling).**  Along this segment,
>
> ```text
> |W(x)|/t
>  <= E_(n,m,p,r)(x)
>  := x^n (1-rx)/(x-r)
>       * [(1+rx)/(x+r)]^(m-2)
>       * (1+ux)/(x+u).                                 (2)
> ```
>
> Consequently the component acquires an excluded root by level
>
> ```text
> b_next/t <= max_(1<=x<=1/r) E_(n,m,p,r)(x).           (3)
> ```

### Proof

Write a spectator zero as `a=rho exp(i phi)`.  Its factor in `|W(x)|/t` is

```text
S_x(rho,cos(phi))
 = sqrt[(1-2rho x cos(phi)+rho^2x^2)
        /(x^2-2rho x cos(phi)+rho^2)].                  (4)
```

The derivative of the quotient under the square root with respect to
`c=cos(phi)` is

```text
2rho x(1-x^2)(1-rho^2)/(x^2-2rho xc+rho^2)^2 <=0.      (5)
```

Thus every spectator is worst when antipodal to the selected zero, and

```text
S_x(rho,c) <= g_x(rho):=(1+rho x)/(x+rho).              (6)
```

Put `v=log rho`.  Exact differentiation gives

```text
d^2/dv^2 log g_x(exp(v))
 = -rho x(rho-1)(rho+1)(x-1)(x+1)
   /[(rho+x)^2(rho x+1)^2] >=0.                         (7)
```

The function is also increasing in `v`.  The spectator logarithmic radii are
at most `log r` and have sum `log(p/r)`.  Convex water-filling (equivalently,
Karamata after sorting) therefore puts `m-2` of them at `log r` and the last
at

```text
log(p/r)-(m-2)log r=log u.
```

Multiplying (6) in that endpoint configuration and restoring the selected
factor proves (2).  The actual radial curve proves (3).  The bound is sharp
given only `p`, `r`, and the selected radial direction: equality in the two
polarizations places all spectators antipodal, with `m-2` spectator moduli
equal to `r` and the last equal to `u`.  ∎

The theorem strictly improves the spectator-drop ceiling in
`CapacitySaturationBridge.md`: every retained factor in (2) is at most one,
and it keeps the full product `p`.  It is nevertheless not the symmetric
envelope; Section 4 identifies the exact loss.

## 2. Exact rigidity at capacity saturation

Now impose the closed boundary-speed condition

```text
g(z):=|B'(z)|<=n,             |z|=1,                    (8)
```

and write `d=n-m`.  The exterior fibre theorem gives

```text
p=|B(0)| <= p_0:=(n-m)/(n+m)=d/(n+m).                  (9)
```

> **Theorem 2 (saturation rigidity).**  Equality `p=p_0` in (9) is possible
> under (8) only for
>
> ```text
> B(z)=unit*(z^m-p_0)/(1-p_0 z^m),                      (11)
> ```
>
> up to a rotation of the variable.  Conversely (11) satisfies (8), with
> equality at its regular boundary fibre.

### Proof

Multiply `B` by a unimodular constant so that `B(0)=-p_0`, and use the
antipodal fibre `B(zeta)=1`.  The exact harmonic-measure identity says

```text
sum_(B(zeta)=1) 1/g(zeta)=(1-p_0)/(1+p_0)=m/n.          (12)
```

There are `m` fibre points counted with multiplicity, while (8) makes every
summand at least `1/n`.  Equality in (12) forces `g(zeta)=n` at every fibre
point.  The fibre is simple because these derivatives are nonzero.

Write `B=P/Q`, with `P,Q` the usual reciprocal denominator pair, and put

```text
C(z)=nP(z)Q(z)-z[P'(z)Q(z)-P(z)Q'(z)].                 (13)
```

On the circle, `C/(PQ)=n-g>=0`.  At each of the `m` roots of `P-Q`, this
nonnegative real-analytic function vanishes, hence it has even order.  Since
`deg C<=2m`,

```text
C=lambda(P-Q)^2.                                        (14)
```

Dividing by `Q^2` and evaluating at zero gives the Riccati equation

```text
nB-zB'=-np_0/(1+p_0)^2 * (B-1)^2.                      (15)
```

Apply the disk automorphism

```text
Y=(B+p_0)/(1+p_0 B).
```

Substitution of `p_0=(n-m)/(n+m)` into (15) reduces exactly to

```text
zY'=mY.                                                 (16)
```

Analyticity at zero gives `Y=c z^m`; because `Y` is a degree-`m` finite
Blaschke product, `|c|=1`.  Solving for `B` proves (11).  Direct substitution
shows that its maximum boundary derivative is
`m(1+p_0)/(1-p_0)=n`.  ∎

This upgrades the former statement that the product constant is sharp for the
abstract boundary-speed problem: the equality object itself is rigid.  It
also explains why the symmetric model is the only possible endpoint of a
near-saturation argument.

## 3. What the Kovalev--Yang derivative theorem genuinely gives

For a degree-`m` finite Blaschke product, write

```text
M=max_T |B'|,       mu=min_T |B'|.
```

Kovalev and Yang prove

```text
m/(M-m+1) <= mu                                     (KY)
```

as part of their sharp description of the possible pair `(M,mu)`; see
L. V. Kovalev and X. Yang, *Extreme values of the derivative of Blaschke
products and hypergeometric polynomials*, Bull. Sci. Math. 169 (2021),
102979, arXiv:2007.09760, Theorem 1.2.

> **Corollary 3 (speed range and port separation).**  Under the strict
> exterior condition `M<n=m+d`,
>
> ```text
> mu > m/(d+1),
> 0<h(theta):=n-|B'(exp(i theta))|
>   < d(n+1)/(d+1).                                     (17)
> ```
>
> The boundary map `z^n/B(z)` has degree `d`.  Consecutive points in any one
> of its boundary fibres have exterior angular separation strictly larger
> than
>
> ```text
> 2pi(d+1)/[d(n+1)].                                    (18)
> ```

The first line is `(KY)` and elementary algebra.  For (18), the boundary
phase derivative is `h`; its integral between consecutive fibre points is
`2pi`, while (17) bounds it pointwise.

The Kovalev--Yang theorem does not prove the merge envelope: its critical
equation concerns extrema of `|B'|`, whereas exterior merge saddles solve
`zB'/B=n` for the meromorphic quotient `z^n/B`.  Its sharp hypergeometric
objects also live far from capacity saturation.  For first-kind extremals
with `M` tending to `n`, their parameter tends to `nu=d` and

```text
|B(0)| -> p_K=d(d+1)/[n(n+1)].                          (19)
```

The exact gap from the capacity endpoint is

```text
p_0-p_K
 = d m(m-1)/[(n+m)n(n+1)],                              (20)
```

strict for `m>1`.  Thus the hypergeometric derivative extremals certify the
sharpness of (17), but they are not the high-capacity extremals required by
the remaining terminal-block problem.

## 4. Exact scalar obstruction in moved degrees two and three

The water-filling ceiling loses angular distribution before the boundary-speed
constraint can be spent.  This is not merely a concern about constants.

Take the regular triangle product

```text
B(z)=(z^3-1/8)/(1-z^3/8),       p=1/8,       r=1/2.     (21)
```

Its exact maximum boundary derivative is

```text
M=3(1+p)/(1-p)=27/7.                                    (22)
```

Hence it satisfies the strict exterior speed condition both for
`(n,m,d)=(5,3,2)` and `(6,3,3)`.  In Theorem 1, `u=1/2`; at `x=3/2` its
water-filling profile is

```text
E_(5,3,1/8,1/2)(3/2)=11907/8192 > 11/8,                (23)
E_(6,3,1/8,1/2)(3/2)=35721/16384 > 17/8.               (24)
```

But (21) is already the symmetric model.  Its true maxima are strictly below
those rational separators.  For `n=5`, if `Y_*=(17+3sqrt(21))/10`, cubing
the exact maximum gives

```text
b_sym^3=9059/6250 + (1431/6250)sqrt(21) < (11/8)^3;    (25)
```

the final comparison follows from
`1840271^2-21*366336^2=568353990625>0`.  For `n=6`,

```text
b_sym^3
 = 76623025309/17179869184
   +(3805648605/17179869184)sqrt(385) < (17/8)^3;       (26)
```

the squared comparison has positive remainder
`2208574994107097677824`.

Thus even on an exact admissible regular configuration, the `(p,r)` ceiling
lies above the symmetric answer in both low moved degrees.  The boundary-speed
condition is true, but (2) has already replaced the regular angular spread by
an impossible antipodal pile-up.  A closure theorem must retain an angular
speed-distribution statistic, a fibre-wise saturation defect, or the full
critical numerator (13); no scalar post-processing of (2) by the Boolean fact
`M<n` can recover the lost equality geometry.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_exterior_radial_waterfilling.py
```
