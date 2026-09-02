# Augmented inverse-square target discs

## Theorem

Let

```text
f(z)=prod_j (z-a_j),              F(z)=|f(z)|^(2/n),
P(z)=sum_j 1/(z-a_j),             S(z)=sum_j 1/|z-a_j|^2,
B(z)=z-conjugate(P(z))/S(z).
```

At a nonroot point `z`, for every `T>=|f(z)|` the closed disc

```text
|y-B(z)|^2 <= |z-B(z)|^2 + n(T^(2/n)-F(z))/(F(z)S(z))       (1)
```

is contained in `{y: |f(y)|<=T}`.  At `T=|f(z)|` this is the
inverse-square descent disc in `BarycentricEnvelope.md`; the extra radial term
is exact and is useful when the target level is fixed in advance.

## Proof

Put `d_j=z-a_j` and apply AM--GM to

```text
|f(y)|^(2/n)/F(z) = (prod_j |1-(z-y)/d_j|^2)^(1/n).
```

The arithmetic mean of the factors is

```text
1 + (S|z-y|^2 - 2 Re((z-y)P))/n
= 1 + (S|y-B|^2-|P|^2/S)/n.                                (2)
```

Since `|z-B|^2=|P|^2/S^2`, condition (1) makes (2) at most
`T^(2/n)/F(z)`.  This proves the inclusion.  Equality in the completing-square
step is algebraic; no sampling is used.

## Exact ray reach and the endpoint obstruction

On a unit ray `y=z+s u`, write

```text
alpha = Re(conjugate(z-B) u),
sigma^2 = n(T^(2/n)-F)/(FS).
```

The maximal certified reach is

```text
s_max = alpha + sqrt(alpha^2+sigma^2).                      (3)
```

If `T>|f(z)|`, then `sigma^2>0`, so every direction has positive reach.  At
the boundary level `T=|f(z)|`, (3) stalls exactly when `alpha<=0`; equivalently
the endpoint KKT sign points out of the descent disc.  Thus target slack
removes the local directional obstruction, while a boundary proof must obtain
the correct one-sided sign or change hubs.

## Flow consequence and limitation

For the inverse-square barycentric flow `z'=B(z)-z`, direct differentiation
gives

```text
-dF/dt = 2F |P|^2/(nS),       |z'|^2=|P|^2/S^2,
```

and AM--GM gives `FS>=n`.  Hence

```text
-dF/dt >= 2 |z'|^2.                                         (4)
```

This controls quadratic action, not arclength: Cauchy--Schwarz still introduces
the elapsed time, which can diverge near a critical point.  The theorem is
therefore a rigorous local containment engine, not by itself the missing
global connector.

`BarycentricTargetDisc.lean` checks the completed-square transport, the exact
ray formula and stall dichotomy, and the scalar energy-to-action implication.
Weighted AM--GM and complex differentiation remain ordinary mathematics.

## Frontier use

The free-pair selector may choose noncritical hubs.  Formula (1) supplies a
correlated target-level disc at each candidate hub, while (3) gives an exact
finite test for whether both chosen directions have usable initial reach.
Any global disc-chain argument must additionally pay arclength; (4) alone does
not do so.
