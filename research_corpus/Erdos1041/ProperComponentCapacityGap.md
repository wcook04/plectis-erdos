# Erdős 1041: every proper regular component has a uniform capacity gap

## Status

This note proves a new exact consequence of the exterior Blaschke component
model and feeds it into two existing sufficient theorems for Erdős #1041.  It
closes every proper component satisfying the explicit merge-ratio criteria
below.  It does **not** prove that one of those criteria must occur, so the
unrestricted problem remains open.

Throughout, `f` is monic of degree `n > 1`, `t > 0` is a regular value of
`|f|`, and `U` is a component of `{|f| < t}` containing `k` roots, counted
with multiplicity.  We call `U` proper when `k < n` and put

```text
q_n := (n - 1)/(n + 1).
```

## 1. Exterior roots cannot approach the unit circle

Let

```text
psi : {|zeta| > 1} -> C-hat \ closure(U)
```

be the exterior Riemann map, normalized by
`psi(zeta) = cap(closure(U)) zeta + O(1)`.  For each root `a_j` outside `U`,
write `xi_j = psi^{-1}(a_j)`, so `r_j := |xi_j| > 1`.  The exterior component
model, applied to `f/t`, gives

```text
f(psi(zeta))/t
  = exp(i alpha) zeta^n product_{a_j notin U}
      (zeta-xi_j)/(1-conj(xi_j)zeta).                         (1)
```

On the unit circle its angular derivative is

```text
h(theta) = n - sum_{a_j notin U}
  P_{1/conj(xi_j)}(exp(i theta)) > 0.                         (2)
```

> **Theorem 1 (exterior-root separation).** For every root outside `U`,
>
> ```text
> |xi_j| > (n+1)/(n-1) = 1/q_n.                              (3)
> ```

*Proof.*  Fix `xi_j = r exp(i theta_j)`.  At `theta = theta_j`, its Poisson
kernel has its maximum value

```text
P_{1/conj(xi_j)}(exp(i theta_j))
  = (r^2-1)/(r-1)^2 = (r+1)/(r-1).
```

Every other Poisson summand is positive.  Equation (2) therefore implies
`(r+1)/(r-1) < n`.  Since `r>1` and `n>1`, clearing the positive denominators
gives `(n+1)/(n-1) < r`.  The scalar algebra is formalized in
`ProperComponentCapacityGap.lean`. ∎

This is a genuinely componentwise constraint.  It comes from global
polynomial degree `n`, not from an arbitrary degree-`k` proper map of a disk.

## 2. Uniform capacity and area loss

Comparison of the leading coefficients in (1) gives the exact identity

```text
cap(closure(U))^n / t
  = product_{a_j notin U} |xi_j|^{-1}.                        (4)
```

There are `n-k` factors, counted with multiplicity.  Theorem 1 gives:

> **Theorem 2 (proper-component capacity gap).** If `k<n`, then
>
> ```text
> cap(closure(U))
>   < t^(1/n) q_n^((n-k)/n),                                 (5)
> Area(U)/pi
>   < t^(2/n) q_n^(2(n-k)/n).                                (6)
> ```

*Proof.*  Apply (3) to every factor in (4), take the positive `n`th root,
and then use Pólya's inequality `Area(U) <= pi cap(closure(U))^2`. ∎

In the notation of `ComponentCapacityFormula.md`, this also gives the new
degree-only lower bound on the excluded-root Green defect

```text
Sigma_U > (n-k) log((n+1)/(n-1)).                            (7)
```

The strictness is useful: it turns equality at either sufficient threshold
below into a strict certificate.

## 3. Direct Bergman consumer

Assume `2 <= k < n`, and that `U` contains at least two distinct root
locations.  Put

```text
q_U := max {|f(c)|/t : c in U, f'(c)=0}.
```

`ConnectedClusterBergman.md` proves that two distinct roots in `U` have a
joining curve of length at most `2 t^(1/n)` whenever

```text
q_U <= tanh(1/kappa_U^2)^(k/2),
kappa_U := cap(closure(U))/t^(1/n).
```

Since (5) gives
`1/kappa_U^2 > q_n^(-2(n-k)/n)`, we obtain:

> **Corollary 3 (degree-only cluster threshold).** Such a curve exists if
>
> ```text
> q_U <= tanh(q_n^(-2(n-k)/n))^(k/2).                         (8)
> ```

For a component born at a first merge of critical modulus `mu`, and for a
regular `t` before its next merge, `q_U=mu/t`.  Hence (8) is the explicit
merge-gap condition

```text
mu/t <= tanh(q_n^(-2(n-k)/n))^(k/2).                         (9)
```

It strictly improves the capacity-blind threshold `tanh(1)^(k/2)` for every
proper component.

## 4. Visibility/COVER consumer

The first-merge geodesic theorem in `BergmanGeodesicInvariance.md` gives COVER
on the merge geodesic when

```text
(Area(U)/pi) log(1/(1-(mu/t)^(2/k))) <= 1.
```

Theorem 2 therefore gives the following source-free scalar sufficient
condition:

> **Corollary 4 (proper first-merge COVER threshold).** COVER holds if
>
> ```text
> t^(2/n) q_n^(2(n-k)/n)
>   log(1/(1-(mu/t)^(2/k))) <= 1.                             (10)
> ```

Because the area bound is strict, equality in (10) is harmless.

## 5. Conformal-welding firewall

Equation (2) lives in the **exterior** boundary parameter.  If `phi:D->U` is
an interior Riemann map, its boundary parameter is related to the exterior one
by a conformal welding `theta=tau(s)`.  The interior angular derivative is

```text
H(s) = h(tau(s)) tau'(s),
```

not `h(s)`.  Thus the pointwise exterior bound `h<n` does not imply a
pointwise bound on `H`, nor a radius bound for the zeros of the interior
degree-`k` Blaschke product.  Near a pinching boundary the welding derivative
is precisely where distortion can concentrate.  Any argument identifying the
two circle parameters without controlling `tau'` is invalid.

The capacity gap avoids this interface completely: leading coefficients are
conformal invariants, so (4)--(10) need no pointwise transfer through the
welding.

## 6. Exact remaining boundary

This theorem supplies a uniform loss whenever a candidate merge component is
proper.  To finish Erdős #1041 through this route one still must prove that
some proper merge component satisfies (8) or (10), or handle the terminal
all-root component by a different certificate.  The new information is that
the capacity term in those tests is no longer free to approach one at a proper
node: its deficit is at least the explicit degree/missing-root amount in
(5).
