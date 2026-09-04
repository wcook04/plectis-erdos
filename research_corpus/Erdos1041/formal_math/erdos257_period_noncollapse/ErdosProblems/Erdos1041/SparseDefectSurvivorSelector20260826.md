# Erdős 1041: sparse Gram deletion no-go and survivor-local repair

## Status and source boundary

This note assimilates returns 001 and 002 of
`state/formal_math/type_b_return_batches/erdos1041_20260826_return_stream_02`.
The stream is a new nine-response campaign and is independent of
`return_stream_01`.

Return 002 contains a self-contained actual-polynomial obstruction to deleting
Gram-bad rows before selecting a connector.  That obstruction is valid.  Its
product-age repair is also valid, but it unnecessarily retains the product and
energy of deleted roots.  Section 3 proves a strictly more local version using
only the surviving roots; the sharp form uses the complement energy of the
selected pair.

Return 001 claims an exact quartic counterexample to the componentwise
critical-pole-plus-attachment-age inequality.  That claim is **not landed**.
The supplied ZIP does not contain the linked focused obstruction extract, an
exact definition-and-value certificate for `L_can` and `B_pole`, or an
executable check of their claimed strict inequality.  The Gaussian-rational
quartic actually named by the report is the source-current witness in
`check_erdos1041_straight_spoke_hub_criterion.py`; that checker has status
`mixed` and separates two straight-spoke containment notions.  It does not
compute the claimed pole trace.  Thus componentwise combined charge remains
open until an exact trace witness or proof is supplied.

Unrestricted Erdős 1041 is not proved here.

## 1. Exact sparse-defect star obstruction

For `n >= 3` and `0 < r < 1`, put

```text
F_(n,r)(z) = z^n-r^(n-1)z
           = z(z^(n-1)-r^(n-1)).
```

Its roots are `0` and `r omega`, where `omega^(n-1)=1`.  At `r=1`, the
normalised Vandermonde Gram rows satisfy

```text
d_0     = (n-1)/n,
d_omega = 2(n-1)/n^2,
||H-I||_F^2 = (n-1)(3n-2)/n^2,
det H   = ((n-1)/n)^(n-1).
```

For `0<r<1`, writing `N_(n,r)=sum_(m=0)^(n-1) r^(2m)`, the exact determinant is

```text
det H_(n,r) = ((n-1)r^n/N_(n,r))^(n-1).                 (SD1)
```

Hence, for every fixed `delta_G<e^(-1)` and row threshold `0<eta<1`, one can
first choose `n` large and then `r<1` sufficiently close to one so that the
Gram determinant exceeds `delta_G` and exactly the central row is exceptional.

The critical points are

```text
c_omega = r n^(-1/(n-1)) omega
```

and all have critical modulus

```text
beta_(n,r)=r^n(n-1)n^(-n/(n-1)).                       (SD2)
```

Every root is a direct child of the grouped first merge, so its attachment age
is zero.  With `q_i=beta_(n,r)/|F'_(n,r)(a_i)|`, one has

```text
q_0=(n-1)q_omega,
product_i q_i=beta_(n,r)/n^n.                          (SD3)
```

The source-current entrance-energy identity

```text
q_i^2=beta_v^(2/k)Y_(i,v)^2 exp(-2A_i(v))
```

therefore gives

```text
Y_0^2 / sum_i Y_i^2 = (n-1)/n,
sum_(omega)Y_omega^2 / sum_i Y_i^2 = 1/n,
```

and any two surviving outer roots carry only `2/[n(n-1)]` of the total mass.
Deleting the unique exceptional row can consequently erase arbitrarily close
to all of the `Y^2` mass even with a degree-free determinant floor and zero
attachment age everywhere.

This is a no-go for deletion-only allocation, not for Erdős 1041.  Indeed the
radial segment from `0` to any `r omega` has length `r<1` and stays in the
sublevel because

```text
|F_(n,r)(tr omega)|=r^n t(1-t^(n-1))<=beta_(n,r)<1.
```

The exceptional root is precisely the useful connector hub.

## 2. Returned product-age selector

Let `I` be a `k`-root component, let `E` be a deleted set, and put
`S=I\E`, `s=|S|>=2`.  For nonnegative ages `A_i` and positive entrance charges
`q_i`, the two smallest survivor ages select distinct `i,j in S` with

```text
max(A_i,A_j) <= (sum_(ell in S) A_ell)/(s-1).           (PA1)
```

For any fixed pair, AM--GM on the other `k-2` component roots proves the
returned whole-component estimate

```text
q_i q_j >= P_I ((k-2)/Q_I)^((k-2)/2),                  (PA2)
```

where `P_I=product_(ell in I)q_ell` and
`Q_I=sum_(ell in I)q_ell^2`.  Thus (PA1) and (PA2) hold for the same pair.
This is correct, but deleted charges remain in both right-hand quantities.

## 3. Stronger survivor-local selector

Define

```text
P_S = product_(ell in S) q_ell,
Q_S = sum_(ell in S) q_ell^2,
Q_comp(i,j) = sum_(ell in S\{i,j}) q_ell^2.
```

### Theorem A (sharp survivor-local product-age selector)

The pair `i,j` selected by (PA1) also satisfies, when `s>=3`,

```text
P_S^2 (s-2)^(s-2)
  <= (q_i q_j)^2 Q_comp(i,j)^(s-2)                    (SL1)
  <= (q_i q_j)^2 Q_S^(s-2).                           (SL2)
```

For `s=2`, `q_iq_j=P_S`.

#### Proof

The age selection is independent of the charges.  For its chosen pair,
AM--GM applied to the `s-2` nonnegative numbers `q_ell^2` on
`S\{i,j}` gives

```text
(s-2)^(s-2) product_(ell in S\{i,j})q_ell^2
  <= Q_comp(i,j)^(s-2).
```

Multiplication by `(q_iq_j)^2` proves (SL1), and
`Q_comp(i,j)<=Q_S` proves (SL2).  No deleted root appears.  Equality holds in
(SL1) exactly when all complementary survivor charges are equal.  In
particular, after deleting the central root of the star obstruction, (SL1) is
sharp.

This is strictly better suited to `RootIndexedEntranceAncestry`: `(RIA3)`
expresses `P_S` using the exact internal squared distances and boundary
distances of the survivor set.  The repair therefore retains polynomial
geometry instead of compressing it through deleted rows.

### Corollary A1 (entrance-energy form)

At a component `v`, `ER4` gives

```text
q_iq_j = beta_v^(2/k) Y_i Y_j exp(-(A_i+A_j)).          (SL3)
```

Consequently the same two young survivors satisfy the product lower bound
from (SL1) or (SL2) after division by `beta_v^(2/k)`, and
`Y_i^2+Y_j^2>=2Y_iY_j`.  This is a same-pair statement: the age and energy
currencies are not selected independently.

## 4. What the two returns change together

The returns remove two unsafe proof shapes:

1. a local pole estimate cannot be declared disproved from a straight-spoke
   witness without computing the actual trace quantities;
2. Gram-bad roots cannot be discarded before geometry is assigned, because a
   unique bad root may carry essentially all entrance energy and be the short
   connector hub.

The corrected proof architecture is an exceptional-or-regular dichotomy:

```text
either an exceptional root participates in a complete connector,
or a survivor-local product/age bound feeds a complete regular-pair consumer.
```

The second branch now has the stronger exact currency `(SL1)`.  The first
branch is indispensable by the star family.

## 5. Attempt at unrestricted Erdős 1041

Three structurally distinct routes were compared against the source-current
corpus.

| route | strongest asset | decisive obstruction/probe | verdict |
|---|---|---|---|
| componentwise combined charge | exact tangent-support identity and disk pole budget | return 001 lacks the claimed trace witness; the named quartic tests a different mechanism | remains open, not refuted |
| deletion-stable entrance allocation | `LC3`, `ER4`, `RIA3`, and Theorem A | no existing theorem turns the survivor product threshold into a complete metric connector, while the star forces an exceptional-root branch | strengthened but not target-deciding |
| first-merge `COVER` | exact one-root covering reduction and strong source-current numerical overlap | no proved universal intrinsic one-root cover | still the smallest global target-deciding residual |

The attempted composition stops at one exact statement, not at generic
difficulty:

> For every hard-regime component and its bounded Gram-exceptional set, prove
> either a complete connector involving an exceptional root, or that (SL1)
> crosses the threshold of a complete regular-pair metric consumer.

No source-current theorem supplies either universal branch.  Therefore a full
proof of Erdős 1041 is not claimed.  The positive delta is the exact
actual-polynomial deletion no-go, the survivor-local strengthening, the
rejection of an unsupported combined-charge no-go, and a smaller honest
allocation residual.

## Verification boundary

`SparseDefectSurvivorSelector20260826.lean` checks the algebraic fan-in,
three-survivor specialization, ER4 pair transport, and star mass identities.
`scripts/check_erdos1041_sparse_defect_survivor_selector.py` exactly replays
the rational Gram and star formulas and exhaustively checks (SL1) on a finite
rational grid.  The determinant continuity step, grouped merge geometry, and
general finite AM--GM proof above are ordinary mathematics.  No numerical
trace is promoted to a counterexample or endpoint theorem.
