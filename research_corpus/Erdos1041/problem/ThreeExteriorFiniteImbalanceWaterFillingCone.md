# Erdős 1041: the finite three-exterior imbalance cone is closed

## Theorem

Let (nin\{5,6\}), let (B) be a degree-three finite Blaschke product
with nonzero zeros (a_1,a_2,a_3), and assume the strict exterior-speed
condition

```text
max_|z|=1 |B'(z)| < n.
```

Put

```text
p=product_j |a_j|,       r=max_j |a_j|,
u=p/r^2,                 h=u/r,
d=n-3.
```

Let

```text
C_n=(3/d)(d/n)^(n/3),
M_n=max_(z>=1) (z-1)(z+1)^2/z^n,
T_n=(M_n/C_n)^(1/d).
```

If the normalized largest radius lies in the homogeneous imbalance cone,

```text
r/p^(1/3) >= T_n,                                      (1)
```

then the actual root-attached exterior ray at a largest-modulus zero has
barrier at most the regular three-point barrier (R_n(p)).  Equivalently,
the finite adaptive selector is proved on the whole outer-radial branch in
degrees five and six; no small-capacity limit is being taken.

This consumes the exact radial water-filling ceiling from
`ExteriorRadialWaterFillingAndSaturationRigidity.md`.  It does not prove the
remaining compact near-equal branch, GP3, the terminal-block theorem, or
unrestricted Erdős 1041.

## 1. Scalar form of the water-filling ray

Choose the largest zero and rotate it to the positive ray.  The water-filling
theorem gives, after the inversion (q=1/x),

```text
E_ray(q) <= q^(-n) A(q),             r<=q<=1,

A(q)=((q^2-r^2)(q+u))/((1-r^2q^2)(1+uq)).             (2)
```

The regular comparison factor is

```text
T_p(q)=(q^3-p)/(1-pq^3),
R_n(p)=max_(p^(1/3)<=q<=1) q^(-n) T_p(q).              (3)
```

Since (u\le r), the numerator in (2) obeys

```text
(q^2-r^2)(q+u) <= (q-r)(q+r)^2.                       (4)
```

Writing (q=rz), the right side of (4), after multiplication by
(q^{-n}), is at most (r^{-d}M_n).

The speed condition at the selected boundary direction implies

```text
r < (n-1)/(n+1).                                      (5)
```

In particular (p\le r^3<d/n) in both degrees.  Hence the homogeneous
regular maximizer (q^3=np/d) occurs below one, and (3) gives the useful
lower bound

```text
R_n(p) >= C_n p^(-d/3).                               (6)
```

Finally, (1) is exactly

```text
h <= h_n:=T_n^(-3),
M_n=C_n h_n^(-d/3).                                   (7)
```

## 2. Low-radius branch: the denominator pays itself

Put

```text
D(q)=(1-r^2q^2)(1+uq).
```

If

```text
h >= r/(1-r^2),                                       (8)
```

then (D(q)\ge1) for every (r\le q\le1), because

```text
D(q)-1
 =q[hr-r^2q-hr^3q^2]
 >=q[hr-r^2-hr^3] >=0.                               (9)
```

Equations (4), (6), and (7) immediately give

```text
max q^(-n)A(q) <= r^(-d)M_n <= C_n p^(-d/3) <= R_n(p).
```

If (8) fails, the universal bound (D(q)\ge1-r^2) gives instead

```text
 max q^(-n)A(q) / [C_n p^(-d/3)]
 <= (h/h_n)^(d/3)/(1-r^2)
 <  [r/(h_n(1-r^2))]^(d/3)/(1-r^2).                  (10)
```

Thus (10) is at most one whenever

```text
r/h_n <= (1-r^2)^(1+3/d).                             (11)
```

The left side of (11) increases with (r), while the right side decreases.
The exact enclosures

```text
13/20 < h_5 < 2/3,          3/4 < h_6 < 19/25         (12)
```

and the rational comparisons

```text
r=3/8, n=5:
  (1-r^2)^5-(r/(13/20))^2
   =24657081775/181462368256 >0,

r=5/12, n=6:
  (1-r^2)^2-r/(3/4)
   =2641/20736 >0                                      (13)
```

prove (11) throughout (r\le3/8) in degree five and (r\le5/12) in
degree six.

## 3. High-radius branch: pointwise comparison

Direct subtraction gives the exact identity

```text
T_p(q)-A(q)
 = q(q-1)(q+1) B(q)
   /[(qr-1)(qr+1)(qu+1)(pq^3-1)],                    (14)

B(q)=-r^2(1-u^2)(q^2+1)+qu(1-r^4).                   (15)
```

The denominator in (14) is positive and (q(q-1)(q+1)\le0).  Since
(q^2+1\ge2q), it is enough that

```text
u(1-r^4) <= 2r^2(1-u^2),
```

or, using (u=hr\le h_nr),

```text
F_n(r):=2r(1-h_n^2r^2)-h_n(1-r^4) >=0.               (16)
```

On the speed ranges (5), (F_n) is increasing.  This follows from

```text
F_n'(r)=2-6h_n^2r^2+4h_nr^3>0,
```

using (h_5<2/3,r<2/3) and (h_6<19/25,r<5/7).  The same upper
enclosures in (12) give the exact starting margins

```text
F_5(3/8) > F_(h=2/3)(3/8)=305/6144>0,
F_6(5/12)> F_(h=19/25)(5/12)=6571/518400>0.           (17)
```

Therefore (A(q)\le T_p(q)) pointwise for (r\ge3/8) in degree five and
for (r\ge5/12) in degree six.  Together with Sections 2 and 3, the two
rational branches overlap and exhaust the complete speed-admissible radius
range.

## Replay and exact boundary

Run

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_finite_imbalance_waterfilling.py
```

The replay checks the rational identities, the exact radical enclosures in
(12), every splice comparison, and the derivative margins.  The theorem
closes only the finite largest-radius branch (1).  The remaining finite
selector problem is the compact normalized box

```text
T_n^(-2)< |a_j|/p^(1/3) < T_n,
```

where the regular equality and coupled angles still require the adaptive
near-equal selector theorem.
