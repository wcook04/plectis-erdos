# Erdős 1041: the entrance charge and propagated leaf energy have an exact ratio ledger

## Status

This note composes two previously separate source-current quantities: the
singleton entrance charges in the strengthened lifetime inequality and the
merge-propagated leaf-energy rows.  Their difference is exactly the weighted
logarithmic cost of the intervening merge ratios.  This is a new exact
identity, but not yet the metric allocation inequality needed to solve
unrestricted Erdős 1041.

## 1. One root along one ancestor chain

Fix a root `a_i`.  Let its successive nontrivial ancestor components be

```text
v_0 < v_1 < ... < v_m=v,
```

with sizes `k_r=|S_(v_r)|` and birth levels

```text
0<beta_0<=beta_1<=...<=beta_m<=1.
```

Thus `v_0=p(i)` is the first merge of the singleton root.  Put

```text
q_i=beta_0/|f'(a_i)|
```

and use the merge-propagated row from `TypeBReturnAssimilation20260826.md`:

```text
Y_(i,v_0)
 = |f'(a_i)|^(-1) beta_0^(1-1/k_0),

Y_(i,v_r)
 = Y_(i,v_(r-1)) beta_r^(1/k_(r-1)-1/k_r).          (ER1)
```

Define the attachment-age functional

```text
A_i(v)=sum_(r=1)^m (1/k_(r-1)) log(beta_r/beta_(r-1)) >=0.  (ER2)
```

### Theorem A (exact entrance-energy ratio bridge)

```text
q_i
 = beta_v^(1/k_v) Y_(i,v) exp(-A_i(v)).               (ER3)
```

Equivalently,

```text
q_i^2
 = beta_v^(2/k_v) Y_(i,v)^2 exp(-2A_i(v)).             (ER4)
```

### Proof

Divide the right side of `(ER3)` by `q_i`.  Its logarithmic level exponent is

```text
-log(beta_0)
+ (1-1/k_0)log(beta_0)
+ sum_(r=1)^m (1/k_(r-1)-1/k_r)log(beta_r)
+ (1/k_m)log(beta_m)
- sum_(r=1)^m (1/k_(r-1))
                       (log(beta_r)-log(beta_(r-1))).
```

Every coefficient cancels.  The derivative factors cancel as well, so the
quotient is one.  Squaring proves `(ER4)`.

This also identifies the tempting but false undamped comparison.  In general

```text
q_i <= beta_v^(1/k_v)Y_(i,v),
```

with equality exactly when all intervening ratios equal one.  For instance,
`k_0=2,k_1=3,beta_0=1/10,beta_1=9/10` gives attenuation
`(beta_1/beta_0)^(-1/2)=1/3`.  Therefore the singleton charge alone cannot
uniformly dominate the full ancestor energy row.

## 2. Component identity

For an internal component `v`, let

```text
E_v=sum_(i in S_v)Y_(i,v)^2,
Qleaf_v=sum_(i in S_v)q_i^2.
```

Summing `(ER4)` gives the exact discounted-energy law

```text
Qleaf_v
 = beta_v^(2/k_v)
   sum_(i in S_v) exp(-2A_i(v))Y_(i,v)^2.               (ER5)
```

Hence, with `Amax_v=max_(i in S_v)A_i(v)`,

```text
beta_v^(2/k_v) exp(-2Amax_v) E_v
 <= Qleaf_v
 <= beta_v^(2/k_v) E_v.                                (ER6)
```

The lower bound is sharp as an identity-level statement: a very old leaf in
a component assembled across a large merge ratio can have arbitrarily large
`A_i(v)`.  The new information is that the loss is not a free scalar.  It is
the same root-labelled sequence of merge ratios already priced by the
lifetime terms `I_(k_r)(beta_(r-1)/beta_r)`.

## 3. What the closing inequality must now prove

The live allocation problem can be stated without an unspecified coupling.
It must combine

```text
sum_v I_(k_v)(r_v)
+ (1/2)sum_v J_v
+ (1/4)sum_i q_i^2 < n/4
```

with `(ER5)` and an attachment-compatible metric consumer.  There are two
precise surviving routes:

1. prove that a large attachment age forces enough accumulated lifetime cost
   on the same root path, while a small age makes `q_i^2` a fixed fraction of
   the propagated energy; or
2. use transported antichains or Gram-good weights to select a component in
   which two roots have simultaneously bounded attachment age.

Any argument replacing `exp(-2A_i(v))` by a universal positive constant is
false on abstract labelled combs and must use additional polynomial geometry.

## Verification

The exact checker enumerates every ordered binary tree through nine leaves and
verifies the exponent ledger at every leaf-ancestor incidence.  It also
reconstructs actual polynomial merge trees in degrees three through eight and
checks `(ER3)--(ER6)` numerically.  The numerical rows are regression evidence;
the proof of `(ER3)` is the exact telescoping calculation above.  The Lean
companion checks the load-bearing discounted-square identity and its sharp
upper/lower scalar consumers.

