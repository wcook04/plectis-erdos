# Erdős 1041: leaf-entrance product identity

## Status

This note proves an exact coupling between the singleton entrance terms in
`SixReturnJointAssimilation20260826.md`, the critical-value merge tree, and the
resultant.  The coupling is informative but does **not** solve unrestricted
Erdős 1041: on a comb, every mixed merge cancels and only the first cherry
level survives.

## 1. Separated binary merge tree

Let

```text
f(z) = product_(i=1)^n (z-a_i)
```

be monic with distinct roots, simple critical points, nonzero critical values,
and distinct critical-value moduli.  Use the full component merge tree, without
cutting at level one.  Its internal nodes are binary and are labelled by

```text
beta_v = |f(c_v)| > 0.
```

For a leaf `i`, let `p(i)` be its first internal parent and put

```text
sigma_i = beta_(p(i)),       q_i = sigma_i / |f'(a_i)|.
```

Classify an internal node by the number `ell_v` of its leaf children:

```text
ell_v=2 : cherry,
ell_v=1 : mixed node,
ell_v=0 : pure node (both children are nontrivial).
```

### Theorem A (exact entrance product)

```text
product_i q_i
  = n^(-n) product_v beta_v^(ell_v-1)
  = n^(-n)
      (product_(v cherry) beta_v)
      / (product_(v pure) beta_v).                       (LEP1)
```

Consequently the geometric product of the leaf terms in `(LC3)` is

```text
product_i sigma_i^2/|f'(a_i)|^2
  = n^(-2n)
      (product_(v cherry) beta_v
       / product_(v pure) beta_v)^2.                     (LEP2)
```

### Proof

Every leaf has exactly one internal parent, so

```text
product_i sigma_i = product_v beta_v^ell_v.
```

The monic resultant identity gives

```text
product_i |f'(a_i)| = n^n product_v beta_v.
```

Dividing the first identity by the second leaves exponent `ell_v-1` at
each node.  Cherries therefore contribute exponent `+1`, mixed nodes exponent
`0`, and pure nodes exponent `-1`, proving `(LEP1)`.  Squaring gives `(LEP2)`.

If `C`, `M`, and `P` are the counts of cherry, mixed, and pure nodes, counting
leaf-child edges and internal-child edges gives

```text
2C+M=n,          2P+M=n-2,
```

and hence `C=P+1`.  Thus the quotient in `(LEP1)` is scale-covariant of degree
one, as it must be: scaling every root by `r` scales every `q_i` by `r` and
their product by `r^n`, while every critical value scales by `r^n` and the
net node exponent is `C-P=1`.

## 2. Exact comb specialization

In a binary comb there is one cherry, no pure node, and every later internal
node is mixed.  If `beta_*` is the first merge level, then

```text
product_i q_i = beta_*/n^n,                              (LEP3)
product_i q_i^2 = beta_*^2/n^(2n).                       (LEP4)
```

All later comb ratios disappear exactly.  This is stronger information than
the scalar allocation no-go: the actual polynomial charges are coupled by the
resultant, but the coupling has precisely the same blind spot as the surviving
rapid-comb topology.

## 3. What this changes

The leaf charges are not independent free parameters, so a successful
allocation theorem may use `(LEP1)`.  But positivity plus their product cannot
by itself penalize a long comb: only its bottom cherry is visible.  A closing
consumer must therefore do at least one of the following:

1. couple the first cherry level to the metric length of its actual two
   descending branches;
2. retain additive, root-indexed information discarded by the product;
3. combine the product with Gram rows or attachment ancestry so that mixed
   nodes cease to cancel; or
4. prove that a polynomial realizing the hard near-Fekete shell cannot have
   the required comb labels.

No realizability claim for arbitrary labelled abstract trees is made.  Equal
critical levels and higher critical multiplicity require a grouped-node
version; they follow as limits for applications continuous in the roots, but
that extension is not asserted as a new exact formula here.

## Verification

`LeafEntranceProductIdentity.lean` checks the node-count balance and the exact
algebraic cancellations.  The independent checker enumerates all ordered
binary trees through ten leaves with exact rational node labels, verifies
`(LEP1)--(LEP4)`, and separately replays the identity on numerical merge trees
of actual polynomials.  Numerical rows are regression evidence only; the proof
above is algebraic.
