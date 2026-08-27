# Exact all-branch fibre product and moment constraints

## Result

The useful part of the returned leftmost-fibre argument is an exact algebraic
theorem, but its strongest form is not limited to a leftmost critical point.
Let `P` be any monic polynomial of degree `n`, let

```text
P(z_j(s))=s^n,                    j=1,...,n,                 (1)
```

be a simple fibre, and list the critical points `d_k` with multiplicity.  Then

```text
product_j |z_j'(s)|
  = product_k s^n/|s^n-P(d_k)|.                              (2)
```

If every critical value of `P` lies in the closed left half-plane, the product
in (2) is at most one, is nondecreasing in `s`, and tends to one.

There is also a stronger signed constraint omitted from the return.  For every
`ell=0,...,n-2`,

```text
sum_j z_j(s)^ell z_j'(s)=0,                                 (3)
```

and for `ell=n-1` the sum is `n s^(n-1)`.  Thus the fibre velocities form the
complete barycentric moment system, not merely a list of positive speeds.

## Product identity

Put `F_s=P-s^n`.  Since `P` is monic,

```text
P'(z)=n product_k (z-d_k).
```

Consequently

```text
product_j |P'(z_j)|
 = n^n product_k product_j |z_j-d_k|
 = n^n product_k |P(d_k)-s^n|.                              (4)
```

Differentiating (1) gives

```text
P'(z_j)z_j'=n s^(n-1).
```

Multiplication over `j` and (4) prove (2).  This is a resultant identity; it
does not depend on a branch ordering and extends through multiplicities as an
algebraic identity, though individual derivatives are used only on simple
fibres.

For `r>0` and `Re u<=0`,

```text
|r-u|^2-r^2=|u|^2-2r Re u >=0.                              (5)
```

Taking `r=s^n` in every factor proves the contraction.  Moreover

```text
d/dr log(r/|r-u|)
 = (|u|^2-r Re u)/(r|r-u|^2) >=0,                           (6)
```

and each factor tends to one.

For a tied Newton face `Q` and a critical point `c` minimizing `Re Q(d)`, put
`P=Q(c)-Q`.  Then `P` is monic and

```text
Re P(d)=Re Q(c)-Re Q(d)<=0,
```

so (2), (5), and (6) apply automatically.  No critical-value ray-avoidance or
branch labelling is required for this algebraic conclusion.

## Complete velocity moments

On a simple fibre, Lagrange interpolation gives the standard identities

```text
sum_j z_j^ell/F_s'(z_j) = 0,       0<=ell<=n-2,
sum_j z_j^(n-1)/F_s'(z_j) = 1.                              (7)
```

They are the coefficients of `z^(n-1)` in the Lagrange interpolation of
`z^ell`; equivalently they are the residue theorem at infinity for
`z^ell/F_s(z)`.  Since `F_s'=P'` and
`z_j'=n s^(n-1)/P'(z_j)`, equation (7) is exactly (3) and its final moment.

This hierarchy is a better invariant than the product alone.  In particular,
the velocities sum to zero, and all their polynomial moments through order
`n-2` cancel.  A future two-branch estimate should use the marked pair as a
local-monodromy block inside this barycentric system, rather than discard the
phases and retain only the geometric mean of all speeds.

## Sharp claim ceiling

Neither (2) nor the first cancellation `sum z_j'=0` controls the arithmetic
length of a marked pair.  Even abstractly, the five real velocities

```text
2, 2, -4, 1/10, -1/10
```

sum to zero and have product of norms `4/25<1`, while the first two norms sum
to `4>2`.  The higher moment identities in (3) are therefore essential if
this lane is to recover a pair estimate.

More decisively, `TiedNewtonFaceHorizontalFibreHubwiseNoGo.md` proves that for
`Q=15z+5z^2-z^5` the unique leftmost critical fibre itself has integrated
marked-pair defect at least `(sqrt(5)-1)/2>0`.  Hence the returned
Leftmost-Fibre Inequality is false despite (2)--(3).  The product theorem does
not close tied-face selection, RSCT's signed contacts, compact-away forcing,
or unrestricted Erdős #1041.

`TiedNewtonFaceFibreProduct.lean` checks the half-plane factor inequality, its
finite product consumer, and the exact zero-sum/product countermodel.  The
resultant identity and the Lagrange moment hierarchy are ordinary finite
algebra, replayed independently by the symbolic checker.
