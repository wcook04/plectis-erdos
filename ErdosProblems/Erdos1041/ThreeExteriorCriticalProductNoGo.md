# Erdős 1041: the three-exterior critical-value product shortcut is false

## Status

This note gives an exact strictly admissible quintic witness for which the
product of the three interior saddle values of `R=B/z^5` is more than an order
of magnitude larger than the cube of the symmetric mountain-pass value at the
same zero product.

Thus the desired least-saddle inequality cannot be obtained by bounding the
geometric mean of all three saddle values.  The least saddle itself remains
small in this witness; the symmetric least-saddle/mountain-pass conjecture is
not refuted.

## Rational witness and strict boundary speed

Take the real Blaschke zeros

```text
(a_1,a_2,a_3)=(-9/16,-8/125,5/9),       p=a_1a_2a_3=1/50,
```

and put

```text
B(z)=P(z)/Q(z)=product_j (z-a_j)/(1-a_j z),
R(z)=B(z)/z^5.
```

For `u=cos(theta)`, exact reduction of the boundary speed gives

```text
5-|B'(exp(i theta))| = -5 C(u)/D(u),                   (1)

C(u)=25920000u^3+162872928u^2-28889659u-165922849,

D(u)=-(45u-53)(288u+337)(2000u+15689).                 (2)
```

Under `u=2t-1`, the degree-three Bernstein coefficients of `C` are

```text
-80262,  -553991816/3,  -767291134/3,  -6019580.       (3)
```

Hence `C<0` on `[-1,1]`.  Every factor in `D` has the displayed strict sign,
so `D>0` there.  Equation (1) proves `|B'|<5` on the whole unit circle.

## The three disk critical points

Away from the pole at zero, the critical points of `R` are the zeros of

```text
z(P'Q-PQ')-5PQ.
```

After multiplication by the positive constant `64800000`, the cleared
critical polynomial is

```text
Ccrit(z)=
 6480000z^6+81436464z^5-9449659z^4-168972770z^3
-9449659z^2+81436464z+6480000.                          (4)
```

It is reciprocal.  Exact Sturm counts isolate its six simple real roots, one
in each interval

```text
(-12.519,-12.518), (-1.025,-1.024),
(-0.977,-0.976), (-0.080,-0.079),
(0.836,0.837), (1.194,1.195).                           (5)
```

Consequently the third, fourth and fifth intervals contain exactly the three
disk critical points `c_1,c_2,c_3`.

Exact rational interval evaluation of `P(c)/(Q(c)c^5)` on those isolating
intervals yields the deliberately coarse lower bounds

```text
|R(c_1)|>99/100,       |R(c_2)|>1400,       |R(c_3)|>1.
```

Therefore

```text
product_(j=1)^3 |R(c_j)| > 1386.                        (6)
```

## The symmetric cube is below 100

For the regular three-exterior model with product `p=1/50`, write `y=x^3` at
its interior critical point.  The symmetric critical equation is

```text
y^2-(2504/125)y+1=0.                                   (7)
```

At `y=39/2` its left side is `-4687/500`, while at `y=20` it is `9/25`.
Thus the large root obeys `39/2<y<20`.  The symmetric saddle value satisfies

```text
M_sym^3=y^5(1-y/50)^3/(y-1/50)^3
       <20^5(1-(39/2)/50)^3/((39/2)-1/50)^3
       <100.                                            (8)
```

Combining (6)-(8),

```text
product_(j=1)^3 |R(c_j)| > 1386 > 100 > M_sym^3.        (9)
```

This is an exact failure with a large margin, not a floating-point search.

## Frontier effect

The three saddle values can have the shape `near 1, moderate, enormous`.
Their geometric mean therefore carries the wrong order statistic.  Any valid
global route must control the **least** relevant saddle directly, for example
through the stationary GP3 residual, a least-critical-value comparison, or a
topological minimax argument.  Neither a product nor an arithmetic average of
all saddle values can supply the sharp symmetric ceiling.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_critical_product_nogo.py
```

The checker uses exact rational arithmetic, Bernstein coefficients, Sturm
counts and rational interval evaluation only.
