# Erdős 1041: assimilation of the 2026-08-26 Type-B returns

## Status

All twenty-four supplied artifacts were read and cross-checked against the live
Erdős 1041 sources.  The unrestricted problem is **not** solved by the returned
composition.  Three exact all-degree statements survive and are retained below:

1. an actual-component merge-tree area lower bound;
2. a root-ray product contraction valid for arbitrary root moduli; and
3. convex-hull projection without either length or lemniscate loss.

The merge-tree theorem is the strongest genuinely new result in the return.  It
does not compose with `ConnectedClusterBergman.md` in the way claimed by
`Erdos1041_full_packet_composition.md`.  The exact mismatch is recorded in
§5.  The canonical target remains the original all-degree short-path theorem.

The source inventory, hashes, checker outcomes, and pipeline receipt are in
`type_b_return_assimilation_20260826_tao_pipeline_receipt.json`.

## 1. Actual-component merge-tree area forcing

Let

```text
f(z) = product_(j=1)^n (z-a_j)
```

be monic with simple roots and generic critical levels.  Let `C(R)` be a
regular branch of a component of `{|f|<R}` containing `k` roots, and let
`A(R)` be its area.

### Theorem 1 (branch monotonicity)

On every regular `k`-sheeted branch,

```text
A(R) / R^(2/k)
```

is nondecreasing.

### Proof

Let `L(R)` be the boundary length.  Parametrising the `k` inverse branches of
`f(z)=R exp(i theta)` gives, for almost every regular `R`,

```text
L(R)  = R integral_0^(2pi) sum_(j=1)^k 1/|f'(z_j)| dtheta,
A'(R) = R integral_0^(2pi) sum_(j=1)^k 1/|f'(z_j)|^2 dtheta.
```

Cauchy--Schwarz on the `k` sheets gives

```text
L(R)^2 <= 2 pi k R A'(R).
```

The planar isoperimetric inequality gives `L(R)^2 >= 4 pi A(R)`.  Hence

```text
A'(R)/A(R) >= 2/(kR),
```

which integrates to the assertion.  This proof replaces the returned
condenser-normalisation citation by a direct calculation.

### Theorem 2 (merge-tree certificate)

For a node `v` of the actual component merge tree, let `S_v` be its descendant
roots, `k_v=|S_v|`, and let `R_v` be its birth level.  Put

```text
Y_(i,i) = 1/|f'(a_i)|
```

at a leaf.  If the child `u` containing `i` merges into `v`, set

```text
Y_(i,v) = Y_(i,u) R_v^(1/k_u - 1/k_v).
```

Then at birth and at every later regular radius on the same branch,

```text
A_v(R)/(pi R^(2/k_v)) >= sum_(i in S_v) Y_(i,v)^2.       (MT1)
```

Consequently, with

```text
Q_v = k_v^k_v product_(i in S_v) Y_(i,v),
```

AM--GM gives

```text
A_v(R)/(pi R^(2/k_v)) >= Q_v^(2/k_v)/k_v.               (MT2)
```

At a `d`-fold merge the total descendant exponent of its critical modulus is
`d-1`.  Thus, counting critical multiplicity,

```text
Q_v = k_v^k_v
      product_(a_i in S_v) 1/|f'(a_i)|
      product_(c internal to v) |f(c)|^m_c.              (MT3)
```

The proof is induction using Theorem 1 and area additivity at a critical
merge.  Coalescing critical levels follow by approximation or directly from
the `d-1` exponent identity.

For a complete connected monic degree-`k` polynomial block, the resultant
identity

```text
product_i |f'(a_i)| = k^k product_c |f(c)|^m_c
```

gives `Q_v=1`; hence

```text
A(R) >= (pi/k) R^(2/k).                                  (MT4)
```

This is an exact area **lower** bound.  It is not the small-area hypothesis of
the connected-cluster Bergman certificate.

### Intrinsic form

For a regular unit-level component `U` of degree `k`, define

```text
H_U(w) = product_(z in U, f(z)=w) f'(z),
dnu_U  = |f'| ds / (2 pi k) on boundary(U).
```

Jensen's formula gives

```text
Q_U^(1/k) = k exp(- integral_boundary(U) log|f'| dnu_U).
```

This proves that the certificate is independent of a binary refinement.  For
a proper component, outside roots create a real defect; one must not replace
`Q_U` by the complete-block value `1`.

### Theorem 2b (forest product and area sandwich)

Fix a regular level `R`, and let `C_1,...,C_s` be all components of
`{|f|<R}`, with root counts `k_1+...+k_s=n` and merge certificates `Q_1,...,Q_s`.
The critical points above level `R` carry total multiplicity `s-1`, and the
resultant identity gives the exact forest product law

```text
product_(j=1)^s Q_j
 = product_j k_j^k_j /
   (n^n product_(|f(c)|>R) |f(c)|^m_c).                (FP1)
```

Equivalently,

```text
R^(s-1) product_j Q_j
 = (product_j (k_j/n)^k_j)
   product_(|f(c)|>R) (R/|f(c)|)^m_c
 <= product_j (k_j/n)^k_j.                            (FP2)
```

There is also a global additive constraint.  Summing (MT2) over the disjoint
components and using Pólya's sharp area bound
`Area({|f|<R})<=pi R^(2/n)` gives

```text
sum_(j=1)^s
  (Q_j^(2/k_j)/k_j) R^(2/k_j-2/n)
 <= 1.                                                 (FP3)
```

Thus the new component theorem produces both a multiplicative and an additive
multiscale law on the actual forest.  These are sharper proof-search inputs
than merge order or critical-level ratios alone.  They still constrain the
geometric-mean certificates `Q_j`, not the Bergman maxima `q_C`, so an
additional geometric selector remains necessary.

## 2. Root-ray product contraction for arbitrary root moduli

### Theorem 3

Let `f(z)=product_j(z-a_j)` with `|a_j|<=1`, and put
`p_m=sum_j a_j^m`.  For every `0<=t<1`,

```text
product_i |f(t a_i)|
  <= exp(-sum_(m>=1) t^m |p_m|^2/m)
  <= 1.                                                   (RR)
```

Therefore at every radius parameter `t` at least one index `i` satisfies
`|f(t a_i)|<=1`.

### Proof

For every ordered pair `(i,j)`, direct expansion gives

```text
|1-t a_i conjugate(a_j)|^2 - |t a_i-a_j|^2
  = (1-|a_j|^2)(1-t^2|a_i|^2) >= 0.
```

Multiplying and expanding the zero-free reciprocal factors,

```text
product_(i,j)|t a_i-a_j|
 <= product_(i,j)|1-t a_i conjugate(a_j)|,

log product_(i,j)|1-t a_i conjugate(a_j)|
 = -sum_(m>=1) t^m |sum_i a_i^m|^2/m.
```

This proves (RR).  It strengthens the equal-modulus radial resultant sweep to
arbitrary root moduli.  It remains an `L1` selection statement: the good index
may change with `t`, and the exact five-root one-spoke countermodel prevents a
fixed-index upgrade.

## 3. Convex-hull projection

### Theorem 4

Let `K=conv{a_1,...,a_n}` and let `pi_K` be metric projection onto `K`.  Then

```text
|pi_K(z)-a_j| <= |z-a_j|  for every j,
|f(pi_K(z))| <= |f(z)|,
```

and `pi_K` is `1`-Lipschitz.  Hence every admissible rectifiable path can be
projected into the root hull without increasing its length or its polynomial
modulus.

### Proof

For `x=pi_K(z)`, the projection inequality says
`<z-x,a_j-x><=0`.  Expanding `|z-a_j|^2` yields

```text
|z-a_j|^2
 = |z-x|^2 + |x-a_j|^2 + 2<z-x,x-a_j>
 >= |x-a_j|^2.
```

Multiply over `j` and use nonexpansiveness of metric projection.

## 4. Other returned claims

The following results survive with the stated boundaries.

| Returned object | Assimilation verdict |
|---|---|
| reciprocal coefficient inequality `|c_k-c_0 conj(c_(n-k))| <= binom(n,k)(1-|c_0|^2)` | exact; useful near the self-inversive boundary |
| first-face half-degree theorem and cyclic arithmetic classification | exact finite algebra; the checker passes through degree 1000 |
| quartic/quintic radial domination | valid lower-bound comparison; does not verify the packet consumers' missing hypotheses |
| resolved-contact transfer | correct conditional semialgebraic compactness theorem; no completed atlas or CAD sign certificate was supplied |
| exterior Blaschke component model | exact auxiliary representation of the proper-component defect |
| component existence from discriminant and Vandermonde | exact and already represented in the local corpus |
| integrated inverse-fibre/coarea bounds | exact mean bounds; they do not select a nontrivial monodromy block at a critical argument |
| convex equiangular polygon reduction for boundary roots | exact reduction; no derivative-sublevel connector theorem is supplied |
| cubic positive-weight pointwise no-go | exact mechanism no-go; the live corpus has stronger exact degree-six full-fibre and component-block no-gos |
| finite radial--chord criterion | exact sufficient criterion; its threshold--chord selector remains unproved |
| barycentric stationary-disc equations and affine-binomial equality | exact auxiliary theorems; neither proves FP--GM |

## 5. Why the claimed full composition fails

The return's endpoint chain has three independent breaks.

### 5.1 The two `q` variables are different

`ConnectedClusterBergman.md` defines

```text
q_C = max {|f(c)|/t : c in C, f'(c)=0}.
```

The return instead defines

```text
q_U = Q_U^(1/k),
```

the geometric mean in (MT3), and attributes the implication
`q_U<c_U -> short path` to `ConnectedClusterBergman`.  That implication is not
the theorem in the source.  No change of notation identifies a maximum
critical-value ratio with the derivative/critical-product geometric mean.

### 5.2 The area direction is opposite

The Bergman theorem proves

```text
length^2 <= (2 A_C/pi)
  log((1+q_C^(2/k))/(1-q_C^(2/k))).
```

It yields a short path when this **upper** expression is at most the metric
budget.  The merge-tree theorem gives a **lower** bound for `A_C`.  A lower
bound cannot establish the needed small-area inequality.

### 5.3 The named downstream notes are not endpoint consumers

`HardRegimeIsNearFekete.md` explicitly proves no length bound in either regime.
`NearFeketeCuspLaw.md`, `DegenerateHubBlaschkeReduction.md`, and
`QuarticCoreRadiusCase.md` each retain stated residual hypotheses or cover only
proper subclasses.  Their conjunction is not an all-degree complement of the
Bergman criterion.

Therefore the boxed reciprocal-area lower barrier in the return is a valid
consequence of its own assumptions, but no live theorem converts that barrier
into the unrestricted short path.

## 6. Proof-search consequence

Three structurally distinct routes were retested after assimilation.

1. **Merge area / Bergman:** rejected as an endpoint route by the exact symbol
   and inequality-direction mismatch above.  Retain (MT1)--(MT4) as auxiliary
   potential theory.
2. **Reciprocal first-face reduction:** survives, but it controls only the
   near-Fekete first Newton face and leaves both terminal chart coverage and
   away-from-Fekete forcing open.
3. **Integrated fibre/monodromy:** survives only after integration.  The cubic
   and degree-six no-gos kill pointwise positive selection, while the coarea
   mean does not charge the discrete critical arguments where monodromy joins
   root labels.

The strongest current target-deciding producers therefore remain the live
ones in `research_packet.json`: componentwise combined charge, COVER, and
free-pair FP--GM.  The new root-ray contraction and convex-hull projection are
reusable constraints on those routes, but neither is an exact equivalent of
the original theorem.

## Claim boundary

Proved here by ordinary mathematics: Theorems 1--4, including the forest laws
(FP1)--(FP3), and the exact rejection of
the returned endpoint composition.

Verified by exact/symbolic computation: the merge exponents, degeneration
multiplicity, resultants, reciprocal coefficient inequality, cyclic
classification, and the cubic pointwise no-go identities.

Not proved: the critical-angle/monodromy selector, threshold--chord selector,
FP--GM, combined charge, COVER, an all-face near-Fekete atlas, compact-away
forcing, or unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_type_b_return_assimilation.py
./repo-python -m system.lib.formal_math_frontier_integrity --repo-root . --check-currency
```
