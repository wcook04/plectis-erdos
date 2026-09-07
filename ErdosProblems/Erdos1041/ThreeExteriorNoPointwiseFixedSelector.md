# Erdős 1041: no pointwise fixed-ray selector for three unequal exterior zeros

## Status

This note gives an exact admissible `m=3`, `n=5` obstruction.  At a fixed
zero product, **every** root-attached radial profile exceeds the regular
triangle profile somewhere on its own attachment domain.  Thus the surviving
three-exterior theorem cannot be proved by selecting one actual ray and
showing that it is pointwise dominated by the symmetric ray at every radius.

The obstruction does not refute the optimized min-ray barrier or the genuine
mountain-pass envelope.  Different rays fail at different radii, and their
optimized barriers can still obey the conjectured symmetric ceiling.

## Exact witness

Take the three Blaschke zeros `a_j=r_j omega_j`, where

```text
(r_0,r_1,r_2)=(3/50, 9/160, 125/1728),
omega_0=(1,0),
omega_1=(7/25,24/25),
omega_2=(-117/125,-44/125).
```

All three `omega_j` are rational unit vectors.  Their pairwise cosines are

```text
c_01=7/25,       c_02=-117/125,       c_12=-3/5.       (1)
```

The radius product is

```text
r_0 r_1 r_2=1/4096=s^3,       s=1/16.                 (2)
```

For `x>=1`, put

```text
A_r(x)=(1-rx)/(x-r),
Q_r(x,c)=(1-2rxc+r^2x^2)/(x^2-2rxc+r^2).              (3)
```

On the ray attached to `a_j`, the normalized modulus profile is

```text
F_j(x)=x^n A_(r_j)(x)
       * product_(k != j) sqrt(Q_(r_k)(x,c_jk)),        (4)
```

for `1<=x<=1/r_j`.  The regular-triangle profile with the same product is

```text
F_sym(x)=x^n A_s(x) Q_s(x,-1/2),       1<=x<=1/s.      (5)
```

The factor `x^n` cancels from each squared comparison.  Exact substitution at
three rational points gives

```text
F_0(15)^2/F_sym(15)^2
 =172787754918790708715041/102525497999369526069153 >1,

F_1(15)^2/F_sym(15)^2
 =367494798077462739999625/102233383454364535848969 >1,

F_2(3)^2/F_sym(3)^2
 =7940052051703231440629/7665730371986326402005 >1.    (6)
```

The points are on the genuine common parts of the attachment domains:
`15<1/r_0,1/r_1,1/s`, and `3<1/r_2,1/s`.  Therefore no index `j` has

```text
F_j(x)<=F_sym(x) for every x in
[1,min(1/r_j,1/s)].                                    (7)
```

This failure is independent of the ambient exponent `n`; admissibility is
checked next at `n=5`.

## Exact boundary-speed certificate

On the unit circle,

```text
|B'(zeta)|=sum_j (1-r_j^2)/|zeta-a_j|^2.               (8)
```

Parametrize `zeta` by `t=tan(theta/2)`.  Clearing denominators gives

```text
5-|B'(zeta)|=4 P(t)/D(t),                              (9)
```

where

```text
P(t)=
 484587325002401 t^6 - 60656800485888 t^5
+1473437332595025 t^4 -175831243637760 t^3
+1452136601119935 t^2 - 96565790863872 t
+461871237111311,

D(t)=
 (2809t^2+2209)
 (132437t^2-27648t+124373)
 (2597257t^2+304128t+3405961).                         (10)
```

Each denominator quadratic has positive leading coefficient and negative
discriminant.  The exact Sturm count of `P` on the real line is zero; since
`P(0)>0`, one has `P(t)>0` for every real `t`.  The leading coefficient is
positive as well, so the omitted half-angle point `t=infinity` also has
positive margin.  Hence

```text
|B'(zeta)|<5                                            (11)
```

on the whole circle.  The witness is strictly admissible for the quintic
three-exterior model (and automatically for every larger ambient `n`).

## Frontier effect

The earlier closest-root obstruction rules out always choosing the largest
Blaschke radius.  This witness rules out the stronger fallback in which an
arbitrary but fixed actual ray is chosen and compared pointwise with the
regular profile.  A successful proof must instead use at least one of:

1. the optimized barriers `min_j max_x F_j(x)` directly;
2. a selector whose proof is allowed to change comparison inequalities across
   radial subintervals while retaining one final root;
3. the genuine exterior mountain-pass level, which may use curved paths.

No inequality between the three optimized barriers and the symmetric barrier
is disproved here.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_no_pointwise_fixed_selector.py
```

The checker uses exact rational arithmetic for (1)-(6), exact discriminants
and an exact Sturm count for (9)-(11).
