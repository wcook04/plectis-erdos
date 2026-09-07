# Erdős 1041: critical-spoke moments and the synchronized reciprocal sweep

Status, 2026-08-26: exact ordinary theorem with an independent numerical and
Gaussian-integer regression. It gives one safe sampled spoke point at every
synchronized reciprocal radius, but neither a persistent root index nor two
safe spokes. Erdős 1041 remains open.

## 1. Critical-centred spoke identity

Let `p(z)=product_i(z-a_i)`, let `c` be a non-root critical point, and put

```text
w_i=a_i-c,  u_i=1/w_i,  S_m=sum_i u_i^m.
```

Then `sum_i u_i=0` and

```text
p(c+t w_i)/p(c)=product_k(1-t w_i/w_k).                (M1)
```

For

```text
G_i(t)=log |p(c+t w_i)/p(c)|,
```

the convergent germ at zero gives

```text
G_i^(m)(0)=-(m-1)! Re(S_m/u_i^m),                      (M2)
sum_i |u_i|^(2m) G_i^(m)(0)=-(m-1)! |S_m|^2<=0.        (M3)
```

Thus at least one root ray initially enters the critical sublevel at the first
nonzero moment. This is correct, but one ray is the sharp conclusion.

## 2. New all-order synchronized sweep

For `r>=0` define the point on the `i`-th critical-to-root spoke by

```text
z_i(r)=c+r conjugate(u_i)=c+t_i(r)w_i,
t_i(r)=r|u_i|^2.
```

If `r max_i |u_i|^2<1`, then every `t_i(r)` lies in `[0,1)` and absolute
convergence permits summing all orders:

```text
sum_i log |p(z_i(r))/p(c)|
 = -sum_(m>=1) r^m |S_m|^2/m <=0.                     (M4)
```

Equivalently,

```text
product_i |p(c+r conjugate(u_i))/p(c)| <=1.            (M5)
```

Proof: factor

```text
p(c+r conjugate(u_i))/p(c)
 = product_k(1-r conjugate(u_i)u_k)
```

and use `log|1-z|=-sum_(m>=1)Re(z^m)/m`. Summing over
`i,k` turns the coefficient into
`Re((sum_k u_k^m)(sum_i conjugate(u_i)^m))=|S_m|^2`.

Therefore, for every synchronized reciprocal radius, at least one sampled
spoke point lies in `{|p|<=|p(c)|}`. This is an arbitrary-modulus,
critical-centred extension of the equal-radius orbit-balance identity in
`ConcyclicSpokeCalculus.md`.

## 3. Sharp scope: neither two rays nor a persistent ray follows

Take the Gaussian integers

```text
u_1=-3-2i,  u_2=3i,  u_3=3-i.
```

They satisfy `S_1=0` and `S_2=4+6i`, while

```text
Re(S_2/u_1^2)=92/169>0,
Re(S_2/u_2^2)=-4/9<0,
Re(S_2/u_3^2)=-1/25<0.
```

By `(M2)`, exactly one spoke initially descends at second order. Since
`w_i=1/u_i` and `sum_i1/w_i=0`, these data arise from an actual cubic with
critical point `c`. Hence no moment argument can universally select two
initially safe rays. Existing ONE-SPOKE counterexamples separately block the
quantifier exchange from “for every radius, some index” to “some index, for
every radius”.

The source-current conclusion is therefore `(M4)--(M5)`, not the returned
same-critical two-full-spoke allocation theorem. The latter is already
contradicted by the quartic straight-spoke authority, and curvature or a
component-aware allocation remains necessary.
