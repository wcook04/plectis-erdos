# Erdős 1041: one-row compression and an exact low-mode splice

## Status

This note strengthens the phase-moment spoke certificate in
`CriticalSpokePhaseMomentHybrid.md`.  At one critical point, every spoke is a
radial sample of a **single** reciprocal Taylor polynomial.  After absorbing
the terminal coefficient with the root endpoint identity, both nearest-root
hybrid envelopes are therefore dominated by the row belonging to the second
nearest root.  An exact finite coefficient/energy splice and a closed Young
bound follow.

This is an ordinary theorem with an exact symbolic checker.  It does not prove
that the second-nearest row passes at some critical point.  A deterministic
adversarial sweep of the admissible family `z^n+epsilon*z-r^n` shows that even
the sharper pointwise hybrid can exceed one at every critical point; those
floating-point values are an obstruction probe, not a proof of failure.

## 1. One reciprocal polynomial owns every spoke

Let

```text
P(z)=product_(j=1)^n(z-a_j),       P'(c)=0,       P(c)!=0,
d_j=a_j-c,                         r_j=|d_j|.
```

Order `r_1<=r_2<=...`.  The reciprocal Taylor polynomial at `c` is

```text
Q(w)=P(c+w)/P(c)=product_j(1-w/d_j)=sum_(k=0)^n A_k w^k.       (1)
```

Criticality says

```text
A_0=1,             A_1=-sum_j 1/d_j=0.                       (2)
```

The normalized polynomial on the `i`th root spoke is not an independent
object:

```text
C_i(t)=P(c+t d_i)/P(c)=Q(t d_i)=sum_k A_k d_i^k t^k.          (3)
```

Since `C_i(1)=0`,

```text
A_n d_i^n+1=-sum_(k=2)^(n-1) A_k d_i^k.                      (4)
```

Put

```text
x_(i,k)=|A_k| r_i^k,       D_i=sum_(k=2)^(n-1)x_(i,k),
K_i(t)=1-t^n+sum_(k=2)^(n-1)x_(i,k)(t^k+t^n).                (5)
```

The exact phase majorant `H_i` from the previous note and (4) give

```text
|C_i(t)| <= H_i(t) <= K_i(t).                                (6)
```

The loss in the second inequality is deliberate: it makes the selector
monotone.  Because `r_1<=r_2`,

```text
K_1(t)<=K_2(t)              for every 0<=t<=1.                (7)
```

The inverse-square energy rows are monotone as well.  If

```text
p_i=r_i^-2/sum_j r_j^-2,       S_i=(1-p_i)/p_i,
F_i(t)=(1-t)(1+(2t+S_i t^2)/(n-1))^((n-1)/2),                (8)
```

then `p_1>=p_2`, hence `S_1<=S_2` and `F_1(t)<=F_2(t)`.
Consequently the pointwise hybrid rows

```text
J_i=max_(0<=t<=1) min(F_i(t),K_i(t))                          (9)
```

satisfy

```text
J_1<=J_2.                                                     (10)
```

Thus the two-spoke test is a **one-row test**: if `mu=|P(c)|` and

```text
mu J_2<=1,                                                    (11)
```

then both nearest straight spokes lie in `{|P|<=1}`.  If also `mu<=1`, the
critical ellipse theorem gives `r_1+r_2<=2 mu^(1/n)<=2`.

Notice that (9) is `max_t min(F,K)`, not `min(max_t F,max_t K)`.  No common
maximizer is assumed or cancelled.

## 2. Exact phase/energy splice

For `0<=tau<=1`, define the energy tail

```text
E_n(S,tau)=max_(tau<=t<=1) F_(n,S)(t)                         (12)
```

and the phase-head scalar

```text
M_i(tau)=1+sum_(k=2)^(n-1)x_(i,k) tau^k
             +max(D_i-1,0) tau^n.                            (13)
```

Indeed, from (5),

```text
K_i(t)-1=sum_k x_(i,k)t^k+(D_i-1)t^n <= M_i(tau)-1           (14)
```

for `0<=t<=tau`; when `D_i<=1` the discarded terminal term is nonpositive.
Hence:

> **Theorem (finite low-mode splice).**  If for the second nearest root there
> is a `tau in [0,1]` such that
>
> ```text
> mu M_2(tau)<=1,              mu E_n(S_2,tau)<=1,            (15)
> ```
>
> then (11) holds, so both nearest spokes are contained.  When `mu<=1`, their
> total length is at most two.

This is a genuine splice: the retained reciprocal Taylor modes control the
phase head `0<=t<=tau`, while the inverse-square statistic controls the energy
tail `tau<=t<=1`.

## 3. Optimisation-free Young certificate

There is also a closed sufficient condition using the phase row alone.  Suppose
`D_2<1`, put `q=1-D_2`, and choose arbitrary positive rational allocations

```text
alpha_k>0,              sum_(k=2)^(n-1) alpha_k=q.             (16)
```

For `x>=0`, exact differentiation gives

```text
max_x [d x^k-alpha x^n]
 =Y_(n,k)(d,alpha)
 :=(n-k)/n * d * (k d/(n alpha))^(k/(n-k)).                   (17)
```

Since

```text
K_2(t)-1=sum_(k=2)^(n-1)[x_(2,k)t^k-alpha_k t^n],             (18)
```

we obtain

```text
J_2<=max_t K_2(t)<=1+sum_(k=2)^(n-1)Y_(n,k)(x_(2,k),alpha_k). (19)
```

Therefore

```text
mu [1+sum_k Y_(n,k)(x_(2,k),alpha_k)] <=1                    (20)
```

is an optimisation-free exact two-spoke certificate.  Formula (17) also
exposes the correct fractional powers of small phase moments; a linear norm
bound erases precisely this gain.

## 4. Computed boundary of the route

The companion checker replays (1)--(4), (14), and (17)--(19) symbolically and
tests (6)--(10) on deterministic exact-rational complex configurations.

For obstruction search only, it also evaluates the *sharper* row using the
original `H_i` rather than `K_i` on

```text
P_(r,epsilon)(z)=z^n+epsilon z-r^n,      r=0.999,
0<epsilon<1-r^n.                                             (21)
```

Rouché proves that every root of (21) is strictly in the unit disk, and its
critical points are explicit from `n z^(n-1)+epsilon=0`.  A grid refined around
the worst `epsilon` gave the following values of

```text
min_c |P(c)| max_(i=1,2) max_t min(F_i(t),H_i(t)):
```

| degree | largest sampled value |
|---:|---:|
| 5 | 1.0404 |
| 6 | 1.0854 |
| 7 | 1.1397 |
| 8 | 1.2009 |
| 9 | 1.2661 |
| 10 | 1.3358 |
| 11 | 1.4062 |
| 12 | 1.4764 |
| 13 | 1.5414 |

These are deterministic floating-point lower signals for failure of the
**certificate**, not interval-certified counterexamples and not
counterexamples to Erdős 1041.  The failing scale moves rapidly toward
`epsilon=0` as `n` grows, matching the hub-splitting scale
`epsilon^(1/(n-1))`.  This isolates the exact division of labour:

* the phase row closes the unsplit regular equality itself;
* the energy row closes concentrated reciprocal weights;
* the splice (15) covers overlap between them;
* the singular near-regular split can evade every straight-envelope row and
  still requires the already-developed curved near-Fekete connector.

No averaging or critical-value product principle forcing (11), (15), or (20)
at some critical point is proved here.  That global allocation is the exact
open boundary of this route.
