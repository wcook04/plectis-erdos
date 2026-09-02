# Erdős 1041: quantitative saturation stability for three exterior zeros

## Status

This note upgrades the equality statement in
`ExteriorRadialWaterFillingAndSaturationRigidity.md` to a quantitative
theorem.  For a degree-three finite Blaschke product whose boundary speed is
at most `n=5` or `n=6`, a product within `10^-16` of the sharp product
endpoint forces its three zeros into an explicit neighbourhood of the
regular endpoint triangle.

The proof is ordinary exact analysis.  The companion checker replays every
scalar identity and every rational inequality in the explicit corollary.
This is a saturation stability theorem, not yet the finite selected-ray
inequality at every capacity.

## 1. Exact Clark-fibre defect

Let

```text
B(z)=unit * product_(k=1)^3 (z-a_k)/(1-conj(a_k)z),
g(theta)=|B'(exp(i theta))|,
p=product_k |a_k|,
g(theta)<=n,                 n in {5,6},
p_0=(n-3)/(n+3).
```

Normalize the unimodular factor so that `B(0)=-p`.  Write the three points of
the fibre `B=1` as `zeta_j=exp(i theta_j)`, in cyclic order, and put

```text
lambda_j=1/g(theta_j),
D=sum_j (lambda_j-1/n).
```

The Clark harmonic-measure identity and the speed bound give the exact
defect formula

```text
D = (1-p)/(1+p)-3/n
  = (n+3)(p_0-p)/(n(1+p)),                 (1)
lambda_j-1/n >=0.                           (2)
```

Thus every individual fibre mass is already controlled by the product
deficit.  Equivalently, if `f=n-g`, then

```text
0<=f(theta_j)
 = n-1/lambda_j
 = n^2(lambda_j-1/n)/(1+n(lambda_j-1/n))
 <=n^2D.                                    (3)
```

This is the exact quantitative datum missing from bare saturation
compactness.

## 2. From mass defect to an almost regular fibre

We record completely explicit constants.  Put `d=n-3` and

```text
M_n=3[16((n+1)/2)^6+4((n+1)/2)^4],
Lambda_n=(d+1)/3,
H_n(D)=Lambda_n^2 n sqrt(2M_n D),
E_n(D)=2n[H_n(D)+4D].                       (4)
```

> **Theorem 1 (quantitative Clark-fibre stability).**  After a rotation and
> cyclic relabelling,
>
> ```text
> |theta_1|=0,
> |(theta_2-theta_1)-2pi/3| <= E_n(D),
> |(theta_3-theta_2)-2pi/3| <= E_n(D),
> |(2pi+theta_1-theta_3)-2pi/3| <= E_n(D),  (5)
> |zeta_j-exp(2pi i(j-1)/3)| <= 2E_n(D).    (6)
> ```

### Proof

The boundary speed is the sum of three Poisson kernels.  At the argument of
any zero `a_k`, its own kernel is `(1+|a_k|)/(1-|a_k|)`; hence `g<=n` implies

```text
|a_k| <= (n-1)/(n+1).                       (7)
```

Two differentiations of a Poisson kernel, using
`1-2r cos(theta)+r^2 >=(1-r)^2`, give the deliberately coarse uniform bound

```text
|g''(theta)| <= M_n.                         (8)
```

For a nonnegative twice differentiable function with `|f''|<=M`, the descent
estimate at `theta-f'(theta)/M` gives

```text
|f'(theta)|^2 <=2M f(theta).                 (9)
```

Apply this to `f=n-g` and use (3).  The Kovalev--Yang lower derivative bound
under `max g<=n` gives `g>=3/(d+1)`, so `lambda_j<=Lambda_n`.  Therefore

```text
|g'(theta_j)| <= n sqrt(2M_nD).              (10)
```

To spend (10), use the Clark representation

```text
(1+B(z))/(1-B(z))
 = sum_j lambda_j (zeta_j+z)/(zeta_j-z).     (11)
```

On the circle put

```text
y(theta)=sum_j lambda_j cot((theta-theta_j)/2).
```

Then `g=-2y'/(1+y^2)`.  Expansion at the pole `theta_j` gives the exact
first two coefficients

```text
g(theta_j)=1/lambda_j,
g'(theta_j)=-h_j/lambda_j^2,
h_j=sum_(k!=j) lambda_k
                 cot((theta_j-theta_k)/2).             (12)
```

Consequently `|h_j|<=H_n(D)`.

Let `alpha,beta,gamma` be the three consecutive angular gaps.  Since the
phase of `B` advances by `2pi` between consecutive points of the fibre and
`g<=n`, each gap is at least `2pi/n`.  Since the other two have the same
lower bound, every gap is at most `2pi-4pi/n`.  On this interval

```text
|cot(t/2)|<=cot(pi/n)<2,
|cot(s/2)-cot(t/2)| >= |s-t|/2.             (13)
```

For example, (12) at the first node reads

```text
h_1=lambda_3 cot(gamma/2)-lambda_2 cot(alpha/2).
```

Using `|lambda_j-1/n|<=D`, (13), and `|h_1|<=H_n(D)` yields

```text
|gamma-alpha|<=2n[H_n(D)+4D]=E_n(D).        (14)
```

The other two nodes give the other two pairwise gap estimates.  Their sum is
`2pi`, so each differs from `2pi/3` by at most `E_n(D)`.  Rotating the first
node to `1`, the second angle has error at most `E_n(D)` and the third at
most `2E_n(D)`.  The chord is no longer than the angular error, proving
(5)--(6).  ∎

## 3. Explicit zero stability

Put

```text
r_0=p_0^(1/3),
F_n(D)=24D+(12+36/n)*2E_n(D).                (15)
```

> **Theorem 2 (quantitative saturation stability).**  If
>
> ```text
> F_n(D) <= (n-3)/(4n),                      (16)
> 2nF_n(D)/[(n+3)r_0^2] <= 1-r_0,            (16b)
> ```
>
> then, after a rotation and a matching of the three zeros,
>
> ```text
> max_j |a_j-r_0 exp(2pi i(j-1)/3)|
>   <= 2n F_n(D)/[(n+3)r_0^2].               (17)
> ```

### Proof

Set

```text
A(z)=product_j(zeta_j-z),
N(z)=sum_j lambda_j(zeta_j+z)
                   product_(k!=j)(zeta_k-z),
F(z)=N(z)-A(z).                              (18)
```

Equation (11) says `B=0` exactly when `F=0`.  At the regular endpoint,

```text
A_0(z)=1-z^3,
N_0(z)=(3/n)(1+z^3),
F_0(z)=((n+3)/n)(z^3-p_0).                  (19)
```

For `|z|<=1`, every factor in (18) has modulus at most `2`.  Telescoping the
three factors, then using (2) and (6), gives

```text
|F(z)-F_0(z)|
 <=24D+(12+36/n) max_j|zeta_j-zeta_j^0|
 <=F_n(D).                                   (20)
```

Let

```text
s=2nF_n(D)/[(n+3)r_0^2].                    (21)
```

Condition (16), and `r_0^3=p_0=(n-3)/(n+3)`, say exactly that `s<=r_0/2`.
Condition (16b) keeps all three comparison circles in `|z|<=1`, where (20)
was proved.
On the circle of radius `s` about any one of the three regular zeros, the
distances to the other two regular zeros exceed `r_0`.  Hence

```text
|F_0(z)| > ((n+3)/n)s r_0^2=2F_n(D)
          >|F(z)-F_0(z)|.                   (22)
```

Rouché's theorem puts exactly one zero of `F` in each disk, proving (17).
∎

## 4. A rational endpoint collar for the two required degrees

> **Corollary 3 (bit-replayable collar).**  If
>
> ```text
> 0<=p_0-p<=10^-16,                          (23)
> ```
>
> then the conclusion of Theorem 2 holds.  More concretely, after rotation
> and matching,
>
> ```text
> n=5:  max_j |a_j-(1/4)^(1/3)omega^j| < 16/625,
> n=6:  max_j |a_j-(1/3)^(1/3)omega^j| <  3/40,        (24)
> omega=exp(2pi i/3).
> ```

### Exact rational audit

Since `1+p>=1`, (1) gives

```text
D <= ((n+3)/n)10^-16.                    (25)
```

The exact constants are

```text
M_5=35964,             M_6=180075/2.
```

Substitution in (4), with squared rational comparison, gives

```text
H_5(D)<1/50000,        H_6(D)<1/16000.    (26)
```

Using these upper bounds in (4)--(15) gives

```text
F_5(D)<0.007680000001 <1/10,
F_6(D)<0.027000000001 <1/8.               (27)
```

Thus (16) holds.  Moreover `r_0<3/4`, while the two claimed bounds in (24)
are less than `1/4`; hence (16b) also holds.  Finally

```text
(1/4)^(2/3)>39/100,    (1/3)^(2/3)>1201/2500,
```

and (17), (26)--(27) give respectively the rational bounds `16/625` and
`3/40`.  The companion checker verifies all comparisons as integer
inequalities.

## 5. Exact boundary

This theorem removes the qualitative ambiguity in the saturation branch of
`ThreeExteriorFiniteCapacityContinuationReduction.md`: a first-failure
sequence approaching `p_0` must approach the regular triangle at square-root
rate, and the last `10^-16` product slab lies in the explicit zero collars
(24).

It does **not** by itself prove that the finite adaptive selected-ray
inequality remains nonpositive throughout those collars.  The remaining
composition step is to compare the degenerating finite regular mixed-kernel
margin with the explicit rate (17), or to exclude a nonregular KKT contact in
the compact interval below (23).  No unrestricted Erdős 1041 conclusion is
claimed here.
