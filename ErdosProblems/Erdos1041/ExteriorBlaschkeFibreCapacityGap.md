# Erdős 1041: the exterior Blaschke fibre gives a sharp product capacity gap

## Status

This note strengthens `ProperComponentCapacityGap.md`.  The earlier theorem
bounded every excluded-root factor separately.  Here the boundary fibres are
coupled by harmonic measure, giving the sharper product estimate

```text
cap(closure(U))^n / t < k/(2n-k).
```

This is an exact theorem for every proper regular component.  It improves the
two existing Bergman/COVER consumers, but it does not yet force one merge node
through either consumer; unrestricted Erdős #1041 therefore remains open.

Let `f` be monic of degree `n>1`, let `t>0` be a regular value of `|f|`, and
let `U` be a component of `{|f|<t}` containing `k<n` roots, counted with
multiplicity.  Put `m=n-k`.  In the normalized exterior map from
`ProperComponentCapacityGap.md`, write

```text
a_j = 1/conj(xi_j),
B(z) = product_(j=1)^m (z-a_j)/(1-conj(a_j)z).
```

Thus `B` is a degree-`m` finite Blaschke product and

```text
p := |B(0)| = product_j |a_j| = product_j |xi_j|^(-1).
```

The exterior boundary-speed formula is

```text
h(theta)=n-|B'(exp(i theta))|>0.                         (1)
```

## 1. A finite-Blaschke fibre identity

> **Lemma 1 (harmonic-measure fibre identity).**  If `B` is a finite Blaschke
> product of degree `m`, `w` lies on the unit circle, and the boundary fibre
> `B(zeta)=w` is counted with multiplicity, then
>
> ```text
> sum_(B(zeta)=w) 1/|B'(zeta)|
>   = (1-|B(0)|^2)/|w-B(0)|^2.                            (2)
> ```

*Proof.*  Harmonic measure at `z` is conformally natural under the proper map
`B`.  Pulling the Poisson kernel at `B(z)` back through the `m` boundary
inverse branches gives

```text
P_(B(z))(w)
  = sum_(B(zeta)=w) P_z(zeta)/|B'(zeta)|.
```

Set `z=0`, for which `P_0=1`.  This is (2).  Equivalently, it follows by
partial fractions from the rational function `(w+B(z))/(w-B(z))`; its simple
boundary poles have residues `2/|B'(zeta)|`, and evaluation at zero gives the
same identity.  Multiple fibres follow by a limiting argument (or by counting
local degrees). ∎

Choose `w=-B(0)/|B(0)|` when `B(0) != 0`.  Then (2) becomes

```text
sum_(B(zeta)=w) 1/|B'(zeta)| = (1-p)/(1+p).              (3)
```

When `p=0`, all conclusions below are immediate.

## 2. Sharp product separation

> **Theorem 2 (exterior-fibre product gap).**  With the hypotheses above,
>
> ```text
> product_(a_j notin U) |xi_j|^(-1) < k/(2n-k).           (4)
> ```

*Proof.*  By (1), every boundary derivative in the fibre from (3) is strictly
less than `n`.  There are `m` fibre points counted with multiplicity, so

```text
m/n < sum_(B(zeta)=w) 1/|B'(zeta)| = (1-p)/(1+p).
```

All denominators are positive.  Clearing them gives
`p(n+m)<n-m`, hence

```text
p < (n-m)/(n+m) = k/(2n-k).
```

This proves (4). ∎

The constant is sharp for the boundary-speed problem: for
`B(z)=phi(z^m)` with the zero product tending radially to the extremal value,
the maximum boundary derivative tends to `n`.  Polynomial coupling may impose
additional restrictions, so no polynomial equality example is asserted.

## 3. Capacity, area, and metric consequences

The exterior leading-coefficient identity is

```text
cap(closure(U))^n/t = product_j |xi_j|^(-1).
```

Therefore:

> **Corollary 3 (fibre-coupled capacity and area gap).**
>
> ```text
> cap(closure(U)) < t^(1/n) (k/(2n-k))^(1/n),             (5)
> Area(U)/pi < t^(2/n) (k/(2n-k))^(2/n).                 (6)
> ```

The product constant improves the earlier independent-factor constant:

```text
k/(2n-k) <= ((n-1)/(n+1))^(n-k),                         (7)
```

with equality only when `n-k=1`.  One proof sets `m=n-k` and observes that
`x -> log((n-x)/(n+x))` is concave on `[0,n)`, hence its value at the integer
`m` is at most `m` times its value at `1`.

For `2<=k<n`, the actual connected-cluster theorem now gives a root-to-root
curve of length at most `2 t^(1/n)` whenever

```text
q_U <= tanh(((2n-k)/k)^(2/n))^(k/2).                     (8)
```

For a component born at critical modulus `mu` and observed at a regular level
`t` before the next merge, `q_U=mu/t`.

The first-merge geodesic theorem gives COVER whenever

```text
t^(2/n) (k/(2n-k))^(2/n)
  log(1/(1-(mu/t)^(2/k))) <= 1.                          (9)
```

Both thresholds strictly improve the corresponding criteria in
`ProperComponentCapacityGap.md` whenever at least two roots are excluded.

## 4. Exact remaining boundary

This theorem couples all exterior roots without crossing the conformal-welding
firewall: only boundary harmonic measure and the conformal invariant `B(0)`
are used.  The remaining target-deciding problem is now narrower: prove that
some proper merge node crosses (8) or (9), or combine failure of every such
crossing with one of the terminal/combined-charge/near-Fekete consumers.  A
pure abstract merge tree cannot force the crossing because adjacent critical
levels can coalesce; the required next input must retain polynomial geometry.
