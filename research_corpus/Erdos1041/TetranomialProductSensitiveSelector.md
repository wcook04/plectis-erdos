# Erdős #1041: the product-sensitive tetranomial selector

Status: analytic theorem proved on 2026-08-24; its finite product–sum kernel,
exact Vieta norm-product bridge, and signed selector are formalized in
`TetranomialProductSensitiveSelector.lean`.  Its exact canonical shared-cache
build passed on 2026-08-24.  This is a strict strengthening of the all-exponent
tetranomial L2 class, not an unrestricted solution.

## The theorem

Retain the notation and explicit Newton moment `N=p_s` from
`TetranomialL2Selector.md`.  If every root of

```text
g(w)=w^m+a w^r+b w^s+c,       m>r>s>=1,
```

lies in the open unit disk and

```text
m|c|^2+(m-1+|c|^(2s))|b|^2+2 Re(conj(c)b N)<m-1,       (P)
```

then two distinct roots have complete origin spokes in `{|g|<1}` and hence
are connected there by a broken line of length below two.  The conclusion
again survives every translated cyclic lift from the companion theorem.

## Proof

For `x_i=|w_i|^(2s)` we have `0<=x_i<1`.  The elementary inequality

```text
sum_i x_i <= m-1+product_i x_i                           (1)
```

follows by induction from `x+y<=1+xy`, equivalently
`(1-x)(1-y)>=0`.  Vieta gives

```text
product_i x_i
 = |product_i w_i|^(2s)
 = |c|^(2s).                                             (2)
```

The exact tail-energy identity is

```text
sum_i |c+b w_i^s|^2
 = m|c|^2+|b|^2 sum_i |w_i|^(2s)+2 Re(conj(c)b N).       (3)
```

Equations (1)–(3) and (P) put this energy below `m-1`; the sharp pigeonhole
lemma then forces two tails below one.  The Abel-tail theorem supplies both
safe spokes.

This strictly improves the previous coefficient majorant, replacing
`m|b|^2` by `(m-1+|c|^(2s))|b|^2`.  Since `|c|<1`, the replacement is strict
whenever `b!=0`.

The product-sensitive bound is itself sharp if only cardinality and product
are retained.  On the closed cube, `x_1=...=x_(m-1)=1` and `x_m=P` attain
equality `sum x_i=m-1+P`; points in the open cube approach this configuration.
Thus no uniformly smaller replacement can follow from `|c|` alone.  Any next
improvement must consume another symmetric statistic of the root radii or
abandon total-energy selection.

A deterministic coverage replay on `3,204` accepted open-disk tetranomials
certified `3,161` with the crude all-exponent signed bound and `3,187` with
(P), a strict gain of `26`.  The product-sensitive class included `113` cases
outside the earlier L1 diamond, and all `3,187` certified configurations had
at least two numerically safe tails.  The smallest measured gap between
`m-1` and the exact tail energy was `0.0594`.  These figures measure scope and
apply falsification pressure; they are not proof authority.

## Boundary and handoff

The remaining tetranomial region is where even (P) fails.  Its next useful
quantity is not another Newton moment—that is already explicit—but a sharper
upper bound on `sum_i |w_i|^(2s)` from additional coefficients, or a selector
that does not use total squared energy.

After exact Lean validation, the Refinery should place (P) above the crude L2
corollary, retain the no-priority boundary, and return failure of (P) to the
closure engine for a higher-symmetric-sum energy bound or counterexample.
