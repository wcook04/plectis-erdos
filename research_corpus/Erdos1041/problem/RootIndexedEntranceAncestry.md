# Erdős 1041: root-indexed entrance ancestry

## Status

This note refines the global leaf-entrance product identity into identities
which retain the complete attachment ancestry of every root.  Unlike the
global product, these formulas do not erase mixed nodes of a comb.  They are
exact bookkeeping identities, not an allocation inequality, and unrestricted
Erdős 1041 remains open.

## 1. The pathwise factorization

Let

```text
f(z)=product_(i in I) (z-a_i)
```

be monic with distinct roots and let a separated binary lemniscate merge tree
be fixed.  For an internal node `v`, write its two leaf sets as `L_v,R_v`.
If the leaf `i` lies below `v`, let `S_v(i)` be the leaf set in the child of
`v` opposite to `i`.  Let `p(i)` be the first internal parent of `i`, put

```text
sigma_i=beta_(p(i)),        q_i=sigma_i/|f'(a_i)|,
d_ij=|a_i-a_j|.
```

### Theorem A (root-indexed ancestor product)

For every leaf `i`,

```text
|f'(a_i)|
  = product_(v ancestor of i) product_(j in S_v(i)) d_ij,

q_i
  = beta_(p(i))
      product_(v ancestor of i) product_(j in S_v(i)) d_ij^(-1).       (RIA1)
```

Indeed, for every `j != i`, the lowest common ancestor of `i,j` is the
unique node whose sibling set `S_v(i)` contains `j`.  Thus the sibling sets
along the path from `i` to the root partition `I\{i}`.  Multiplying their
distance factors gives `product_(j!=i)d_ij=|f'(a_i)|`.

On a comb, every later mixed merge contributes a new nonempty sibling set to
each old leaf and contributes the accumulated old component as the sibling
set of the newly attached leaf.  Thus no mixed merge disappears from `(RIA1)`.
It disappeared previously only because all root rows were multiplied together
and the resultant compressed the cross-distance factors to critical values.

## 2. Weighted and block forms

Let `w_i` be arbitrary integer weights.  Multiplying `(RIA1)` with weight
`w_i` gives

```text
product_i q_i^(w_i)
 = [product_i beta_(p(i))^(w_i)]
   / [product_(i<j) d_ij^(w_i+w_j)]                       (RIA2)

 = [product_i beta_(p(i))^(w_i)]
   / [product_v product_(i in L_v,j in R_v)
                         d_ij^(w_i+w_j)].
```

The second equality holds because the lowest-common-ancestor cuts
`L_v x R_v` partition the unordered leaf pairs.  The unweighted choice
`w_i=1` recovers the global square-distance denominator and hence the
resultant identity.  Every nonconstant choice retains root-indexed cross-cut
data, including every mixed comb cut.

For a subset `S` of leaves, take `w_i=1` on `S` and zero outside.  Then

```text
product_(i in S) q_i
 = product_(i in S) beta_(p(i))
   / [ product_(i<j, i,j in S) d_ij^2
       product_(i in S, j notin S) d_ij ].                 (RIA3)
```

If `S` is the leaf set below one tree node, the second denominator is exactly
the product of the boundary cuts encountered above that node.  Formula
`(RIA3)` is therefore an attachment-compatible block observable: internal
distances have exponent two, while every distance crossing the component
boundary has exponent one.

## 3. Exact relation to the global cancellation

Taking `S=I` in `(RIA3)` removes the boundary product and yields

```text
product_i q_i
 = product_i beta_(p(i)) / product_(i<j)d_ij^2.
```

The discriminant/resultant identity replaces the squared distance product by
`n^n product_v beta_v`, after which cherries have exponent `+1`, pure nodes
exponent `-1`, and mixed nodes exponent zero.  Thus
`LeafEntranceProductIdentity.md` is precisely the constant-weight quotient of
the stronger family `(RIA2)`; its comb blindness is a projection effect, not
absence of attachment information in the actual leaf rows.

## 4. Consumer boundary

The identities identify the missing variables but do not control them.  To
close the allocation route one still needs an inequality connecting at least
one weighted or subtree block observable to an attachment-compatible pair,
the Gram rows, or the metric cost of the corresponding descending branches.
In particular, arbitrary positive cross distances and merge labels are not
asserted to be polynomial-realizable.

The exact checker enumerates all ordered binary trees through nine leaves with
rational distance/level labels, verifies `(RIA1)--(RIA3)` for nonconstant
integer weights and every subtree block, and replays `(RIA1)` on numerical
merge trees of actual polynomials.  The Lean companion checks the
load-bearing scalar factorization and block-product algebra.
