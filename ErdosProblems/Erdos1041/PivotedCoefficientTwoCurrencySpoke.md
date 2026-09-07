# Erdős 1041: pivoted coefficient partition with two slack currencies

## Status

This note proves an exact rootwise spoke certificate around an arbitrary
coefficient mode.  Unlike the regular-baseline collar, it is exact on every
centred trinomial and charges a multi-mode remainder to two different geometric
slacks.  A fractional-knapsack formula makes the best allocation finite and
explicit.

This is an ordinary analytic theorem with exact symbolic replay.  It is not a
universal two-root selector.  A quintic adversarial sweep finds multi-mode
angular perturbations for which no root passes this coefficient certificate;
that computed boundary is stated only as float evidence.

## 1. Pivot identity

Let

```text
P(z)=z^n+sum_(k=1)^(n-1)b_k z^k+c
```

have all roots in the open unit disk, and let `a` be a root.  Fix a pivot
`1<=m<n`.  Eliminating `b_m a^m` with `P(a)=0` gives

```text
P(t a)
 =c(1-t^m)+a^n(t^n-t^m)
   +sum_(k!=m)b_k a^k(t^k-t^m).                            (1)
```

The first two terms are the exact centred-trinomial model.  Their coefficient
partition is

```text
(1-t^m)+(t^m-t^n)=1-t^n.                                  (2)
```

Thus they leave two currencies:

```text
constant currency:  (1-|c|)(1-t^m),
root currency:      (1-|a|^n)(t^m-t^n).                    (3)
```

## 2. Sharp mode exchange rates

For `0<=t<=1`, exact differentiation gives

```text
t^k-t^m <= (m-k)/m (1-t^m),             k<m,              (4)
t^m-t^k <= (k-m)/m (1-t^m),             m<k<n,            (5)
t^m-t^k <= t^m-t^n,                     m<k<n.             (6)
```

The constants in (4)--(5) are sharp at `t=1`.  A high mode can therefore be
split fractionally between the two currencies.

Put `d_k=|b_k||a|^k`.  Choose any `theta_k in [0,1]` for `m<k<n` and define

```text
C_m(a,theta)
 =sum_(k<m)(m-k)/m d_k
   +sum_(k>m)theta_k (k-m)/m d_k,                         (7)

R_m(a,theta)=sum_(k>m)(1-theta_k)d_k.                     (8)
```

> **Theorem B (two-currency pivot certificate).**  If
>
> ```text
> C_m(a,theta)<=1-|c|,          R_m(a,theta)<=1-|a|^n,     (9)
> ```
>
> then the complete spoke `[0,a]` lies in `{|P|<1}`.

### Proof

Use (4) on low modes.  Split each high-mode term into `theta_k` and
`1-theta_k` pieces, then use (5) and (6), respectively.  The absolute value of
(1) is at most

```text
[|c|+C_m](1-t^m)+[|a|^n+R_m](t^m-t^n)
 <=1-t^n<1                                                     (10)
```

for `0<t<1`; the endpoints are strict because `|c|<1` and `P(a)=0`.  ∎

If two root occurrences pass (9), joining them through the origin has length
strictly below two and proves Erdős 1041 for that polynomial.

## 3. Exact optimal allocation

The existence of `theta` is a finite fractional-knapsack problem, not a
continuum optimization.  Let

```text
L=sum_(k<m)(m-k)/m d_k,
H=sum_(k>m)d_k,
E=max(H-(1-|a|^n),0).                                      (11)
```

At least mass `E` of the high modes must be transferred to the constant
currency.  Sort the high modes by their unit costs

```text
q_k=(k-m)/m.                                                (12)
```

Fill mass `E` from the smallest `q_k` upward, fractionally at the last mode,
and call the resulting minimum cost `F_m(E)`.  Then (9) is feasible **if and
only if**

```text
L+F_m(E)<=1-|c|.                                            (13)
```

This gives an exact finite rootwise selector.

For a genuine two-mode perturbation with nonzero modes `m<k<n`, (13) reduces
to the closed formula

```text
(k-m)/m * max(|b_k||a|^k-(1-|a|^n),0) <=1-|c|.             (14)
```

When only the pivot mode is present, the residual vanishes and (9) is
automatic.  Thus the theorem recovers the exact centred-trinomial boundary
without a smallness assumption.

## 4. Smallest adversarial face

Before treating (13) as a selector, the companion checker searches quintic
angular perturbations of a regular pentagon.  With all root moduli `0.999`, the
first deterministic tested scale producing no passing root was approximately

```text
angular scale = 0.00263027,
|c|           = 0.9950099900,

(b_4,b_3,b_2,b_1)
 =(0.00344730+0.00334302 i,
   -0.00082881-0.00656737 i,
    0.00081067-0.00656296 i,
   -0.00342817+0.00334205 i).                              (15)
```

Every root failed every pivot `m=1,2,3,4` under the optimized allocation.
This is a float obstruction to universality of the **certificate**, not an
interval theorem and not a counterexample to Erdős 1041.  It shows that two
competing higher modes can exhaust both currencies even arbitrarily near the
regular polygon.  Curved higher-tangent control remains genuinely necessary.

## 5. Exact boundary

Theorem B strictly enlarges the one-mode/cyclic-trinomial face and provides a
finite test for general multi-mode coefficients.  What it does not prove is
that two roots pass (13), or that failure forces the critical one-row hybrid.
The surviving near-Fekete obstruction is exactly the angular-dominated
multi-mode higher-tangent face isolated in
`GlobalSpokeCoefficientCuspDichotomy.md`.
