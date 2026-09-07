# Erdős 1041: the two-exterior symmetric envelope lifts to two regular exterior orbits

## Status

This note proves an exact all-degree family extension of
`TwoExteriorSymmetricEnvelope.md`.  The extension is an ordinary analytic
theorem, with its algebra replayed by
`scripts/check_erdos1041_qfold_two_orbit_symmetric_envelope.py`.

The result concerns exterior Blaschke products which are pullbacks of a
degree-two product under `z -> z^q`.  Equivalently, their exterior zeros are
the union of two regular `q`-orbits, with arbitrary radii and arbitrary
relative phase.  It proves the symmetric next-merge envelope on this family.
It does not assert that a general low-moved-degree component has this orbit
structure, and it does not prove unrestricted Erdős 1041.

## The real-exponent two-zero lemma

The proof of `TwoExteriorSymmetricEnvelope.md` does not use integrality of the
ambient exponent.  The precise real-exponent statement needed here is as
follows.

Let `N>2`, let `A,C` be nonzero points of the open unit disk, and put

```text
P=|AC|,             0<P<(N-2)/(N+2),
Bt(y)=(y-A)(y-C)/[(1-conj(A)y)(1-conj(C)y)].
```

For the exterior potential

```text
u(y)=N log|y|-log|Bt(y)|,        |y|>=1,
```

let `H(A,C)` be the first mountain-pass height from the unit circle to either
exterior zero of `exp(u)`.  Then

```text
H(A,C)
 <= max_(1<=x<=1/sqrt(P)) x^N (1-Px^2)/(x^2-P).       (1)
```

This remains meaningful for nonintegral `N`: only the real potential and its
radial restrictions are used.

### Audit of every polarization step

Choose the zero of larger modulus, rotate it to `A=r>0`, and write

```text
C=rho exp(i phi),       r rho=P,       r>=sqrt(P).
```

The radial segment `y=x`, `1<=x<=1/r`, is an actual curve from the unit
circle to the corresponding exterior zero.  On that segment the exponential
of the potential is

```text
x^N (1-rx)/(x-r)
 * sqrt[(1-2rho x cos(phi)+rho^2 x^2)
        /(x^2-2rho x cos(phi)+rho^2)].                 (2)
```

For fixed `x>=1`, differentiation of the quotient under the square root with
respect to `c=cos(phi)` gives

```text
2 rho x (1-x^2)(1-rho^2)
 /(x^2-2rho x c+rho^2)^2 <= 0.                         (3)
```

Thus the spectator factor is largest when `C` is antipodal to `A`.  In that
case (2) is at most

```text
F_r(x)=x^N (1-rx)(1+rho x)/[(x-r)(x+rho)].             (4)
```

Put `s=sqrt(P)`.  The radius-polarization identity is

```text
F_s(x)/x^N-F_r(x)/x^N
 = x(x^2-1)(1+P)(r^2-P)
   /[(x^2-P)(P+rx)(x-r)] >= 0.                         (5)
```

Every denominator is positive for `1<x<1/r`; the endpoints follow by
continuity.  Since `[1,1/r]` is contained in `[1,1/s]`, (5) proves (1).
Neither (3) nor (5) contains `N`; the only use of `N` is the common positive
factor `x^N`.  This is the promised real-exponent audit.

For the symmetric profile put `Y=x^2`.  Its unique interior maximum is at the
larger root `Y_*>1` of

```text
Y^2-[((N+2)P^2+(N-2))/(NP)]Y+1=0.                     (6)
```

Indeed logarithmic differentiation gives (6), while
`P<(N-2)/(N+2)` makes the logarithmic derivative positive at `x=1` and
negative near `x=1/s`.  Hence

```text
max x^N(1-Px^2)/(x^2-P)
 = Y_*^(N/2)(1-PY_*)/(Y_*-P).                          (7)
```

The inequalities in (3) and (5) are strict at every interior point unless
the two zeros have equal modulus and are antipodal.  Consequently equality
in (1) occurs only for the rotationally symmetric two-zero product.

## The q-fold lift

Let `q>=1` and `n>2q` be integers.  Suppose a proper regular component has
`2q` exterior roots and its exterior finite Blaschke product has the form

```text
B(z)=Bt(z^q),                                           (8)
```

where `Bt` is the degree-two product above.  Its zeros are exactly two regular
`q`-orbits.  Put

```text
m=2q,       d=n-m,       N=n/q,       P=|B(0)|=|Bt(0)|.
```

On the exterior disk, `z -> y=z^q` is an unbranched `q`-fold covering, and

```text
n-z B'(z)/B(z)
 = q [N-y Bt'(y)/Bt(y)],                               (9)

|z|^n/|B(z)|=|y|^N/|Bt(y)|.                            (10)
```

Thus the critical equations, critical-value moduli, attachment paths, and
mountain-pass levels downstairs lift exactly to the original exterior
problem.  The exterior-fibre capacity theorem supplies

```text
P < (n-m)/(n+m).
```

The threshold in the real-exponent lemma is exactly the same number:

```text
(N-2)/(N+2)=(n-2q)/(n+2q)=(n-m)/(n+m)=d/(2n-d).        (11)
```

Applying (1) therefore proves the following.

> **Theorem (q-fold two-orbit symmetric envelope).**  In the setup above,
> if `b_next` is the first level at which the component acquires an exterior
> root, then
>
> ```text
> b_next/t
>  <= max_(1<=x<=P^(-1/m)) x^n(1-Px^m)/(x^m-P).        (12)
> ```
>
> If `Y_*>1` is the larger root of
>
> ```text
> Y^2-[((n+m)P^2+(n-m))/(nP)]Y+1=0,                    (13)
> ```
>
> then the right side of (12) is
>
> ```text
> Y_*^(n/m)(1-PY_*)/(Y_*-P).                           (14)
> ```

The right side is exactly the symmetric model from
`CapacitySaturationBridge.md` equation (18).  Equality holds only when the
two `q`-orbits have equal radii and their phases interlace, so that their
union is one regular `2q`-orbit.  Hence the conjectural symmetric envelope is
now a theorem on the entire two-regular-orbit family, not only when there are
literally two exterior roots.

## Boundary and reuse

The same covering observation lifts any proved degree-`ell` exterior-envelope
slice through `z -> z^q`.  In particular, the equal-radius and regular-angle
three-exterior slices lift to corresponding three-orbit families.  This note
records only the complete degree-two lift, so it does not count those partial
slices as new theorems.

The remaining obstruction is genuinely symmetry-breaking: a general exterior
zero set need not be a union of two regular orbits.  No general symmetric
envelope, low-moved-degree terminal-block theorem, perimeter/access estimate,
or unrestricted Erdős 1041 result follows from (12).

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_qfold_two_orbit_symmetric_envelope.py
```
