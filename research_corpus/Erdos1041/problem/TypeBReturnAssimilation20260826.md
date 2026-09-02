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

### Theorem 3a (exact defect factor and quantitative strict selection)

The pairwise identity contains more information than (RR).  Put

```text
B_(i,j) = |1-t a_i conjugate(a_j)|^2,
X_(i,j) = (1-|a_j|^2)(1-t^2|a_i|^2) / B_(i,j).
```

For `t<1`, every `B_(i,j)` is positive and `0<=X_(i,j)<=1`.  The same
identity therefore gives the exact factorisation

```text
product_i |f(t a_i)|
 = exp(-E(t)) product_(i,j) sqrt(1-X_(i,j)),             (RR1)

E(t) = sum_(m>=1) t^m |p_m|^2/m.
```

Define the two modulus deficits

```text
D_0 = sum_j (1-|a_j|^2),
D_t = sum_i (1-t^2|a_i|^2).
```

Then

```text
min_i |f(t a_i)|
 <= exp(-E(t)/n - D_0 D_t/(2n(1+t)^2)).                 (RR2)
```

In particular, if at least one root is in the open unit disk, then for every
`0<=t<1` at least one actual root-ray point satisfies `|f(t a_i)|<1`.

### Proof

Equation (RR1) follows by writing

```text
|t a_i-a_j|^2 = B_(i,j)(1-X_(i,j))
```

and multiplying over the ordered pairs.  Next, `1-x<=exp(-x)` on `[0,1]` and

```text
B_(i,j) <= (1+t|a_i||a_j|)^2 <= (1+t)^2
```

give

```text
sum_(i,j) X_(i,j)
 >= D_0 D_t/(1+t)^2.
```

Taking the geometric mean of the `n` radial values proves (RR2).  If some
`|a_j|<1`, then `D_0>0`; also `D_t>0` for `t<1`, so the displayed exponential
is strictly below one.  Equality in the original product contraction can
therefore occur only when every root lies on the unit circle.

This is the source-current strengthening extracted while assimilating the
late 2026-08-27 return.  It upgrades the set-valued radial cover from closed
containment to a quantitative open-sublevel margin.  It still does not select
one index continuously, put two outer tails in one component, or contain the
joining chord required by `TruncatedSpokeReduction.md`.

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

## 7. Critical-arc product return: exact normalization and quantifier firewall

A later return proposed, for the canonical inverse-ray edge length `L(c)` and
critical value `v_c=f(c)`, the all-critical inequality

```text
product_c L(c)
  <= 2^(n-1) (product_c |v_c|)^(1/n).                (PG)
```

The inequality `(PG)` is **not proved** by the return.  Its discriminant
normalization is exact: the resultant identity

```text
n^n product_c |v_c| = |Delta(a_1,...,a_n)|^2
```

turns `(PG)` into the equivalent statement

```text
product_c L(c) <= (2^(n-1)/n) |Delta|^(2/n).         (PG-Delta)
```

This explains the scaling and the regular-polygon equality model without
creating a proof.  It also exposes a separate logical gap in the advertised
completion.  Let

```text
A = {c : |v_c| < 1},       B = {c : |v_c| >= 1},
q_c = L(c)/(2 |v_c|^(1/n)).
```

Then `(PG)` says only `product_(A union B) q_c <= 1`.  Fekete says `A` is
nonempty, but neither statement says that an index with `L(c)<2` belongs to
`A`.  The following exact scalar model blocks that inference already at
`n=3`:

```text
(|v_A|,L_A) = (1/16,3),       (|v_B|,L_B) = (8,1).
```

Here `|v_A v_B|=1/2<1`; the only admissible edge has length `3`; and the only
short edge has inadmissible value `8`.  Nevertheless `(PG)` holds strictly,
because

```text
L_A L_B = 3 < 4(1/2)^(1/3),
```

equivalently `(3/4)^3=27/64<1/2`.  This is a countermodel to the **scalar
deduction**, not a claim that these four numbers are realised by one
polynomial.

The corrected product completion is therefore the admissible-subproduct
inequality

```text
product_(c in A) L(c)
  <= 2^|A| (product_(c in A) |v_c|)^(1/n).            (AP)
```

Indeed every factor `|v_c|` on the right is strictly below one, so `(AP)`
gives `product_(c in A)L(c)<2^|A|` and hence some admissible `L(c)<2`.  Its
canonical inverse-ray edge lies in `{|f|<1}` and proves the parent theorem in
the generic case, with the existing closure machinery handling the boundary.

There is an exact compensation form which shows what `(PG)` is missing:

```text
(PG) plus product_(c in B) q_c >= 1  implies (AP).     (COMP)
```

The proof is division of `product_(A union B)q_c<=1` by the positive
inadmissible product.  Thus a global product attack must prove either `(AP)`
directly or a lower compensation bound on the inadmissible edges.  Equality
models and the discriminant alone do not supply that allocation.

The same return also called
`H^1(f^(-1)([0,v])) <= n|v|^(1/n)` established.  It cannot be imported: the
source-current `StraightSpokeHubCriterionLab.md` records a degree-three
continuation witness with ratio `1.065658`, and the merging pair can carry
almost the whole fibre length.  That evidence is numerical rather than a new
exact certificate here, so it rejects theorem status without being promoted
to an exact counterexample.

## 8. Return stream 07: configuration metric, strong-trace refutation, and envelope closure

Two further incomplete parent-proof returns were preserved together under
`state/formal_math/type_b_return_batches/erdos1041_20260827_return_stream_07`.
Their proof-campaign completion class is `parent_advance_incomplete`: both
contain valid auxiliary mathematics, but neither proves the parent theorem or
an exact equivalent.

The first return's convex-hull projection and discriminant/Fekete merger are
already source-current.  Its weighted `L1` convex carrier is valid.  Composing
it with `BarycentricEnvelope.md` yields the stronger exact power-mean cover
lattice `(Bp)`: every `p in [1,infinity]` gives an exact union of nested convex
carriers, with `p=1` the returned carrier, `p=2` the existing disc envelope,
and `p=infinity` an intersection of root-centred discs.  This is a genuine
cross-return/corpus consequence, but it remains auxiliary because no fixed
carrier or carrier chain is proved to keep a root attachment of intrinsic
length at most one.

The configuration metric

```text
rho(w)^2 = sum_(f(z)=w, z in U) 1/|f'(z)|^2
```

also survives review at ordinary-proof authority.  The area formula gives
`integral_D rho^2 dA = area(U)`, Minkowski bounds the Euclidean `l2` norm of
lift lengths by `rho`-length, and a ramification index `p` produces cone angle
`2*pi/p`.  These identities reduce the parent problem to a special
metric-systolic assertion, but do not prove it.  Area alone cannot control the
distance from the base fibre to a branch value because the value-disc boundary
can cut off comparison balls; the return correctly leaves that assertion open.

The second return's proposed decisive inequality

```text
L(c*) <= 2 |f(c*)|^(1/n),
```

at a minimum-modulus critical point is not a live conjecture.  It is the
source-current strong first-merge completion already refuted by the pinned
quartic in `research_packet.json::negative_results`: the recorded ratio is
`1.004246913`.  A fresh replay of
`check_erdos1041_affine_normalised_moduli.py --quick --json` again gives a
separated value above one (`1.0032927905` on the finer pinned mesh).  The
return's random degrees `2..8` scan therefore illustrates the known
threshold-search failure, not positive theorem evidence.  The weaker
minimum-over-admissible-hubs statement remains open.

Its independent lobe-radius quantity

```text
S(f) = mu sum_j 1/|f'(a_j)|
```

equals the sum of the conformal radii of the first-level univalent lobes.  A
conditioning-aware finite probe on well-separated roots through degree ten
found no value above one and approached equality only near regular polygons.
This is evidence only.  The tempting strengthening `S(f)<=mu^(1/n)` is
numerically false (observed ratio `S/mu^(1/n)=1.1208246`), so capacity alone
cannot prove the returned conjecture.  No implication from `S(f)<=1` to an
integrated two-branch length bound is established.

Terminal dispositions for the distinct new units are therefore:

| unit | disposition | authority |
|---|---|---|
| closed normalization, projection, first merger, moment identities | `superseded_by_stronger_route` | existing corpus |
| weighted `L1` convex cover | `composed_into_stronger_result` | ordinary exact proof `(Bp)` |
| configuration metric identities | `landed` | ordinary exact proof, auxiliary |
| special cone-metric systolic assertion | `blocked_external` | unproved decisive bridge |
| minimum-critical strong trace inequality | `rejected_exactly` | source-current pinned counterexample replay |
| lobe-radius sum `S(f)<=1` | `blocked_external` | conjecture with finite evidence |
| capacity strengthening of the lobe-radius sum | `rejected_exactly` | numerical falsifier only; no theorem claim |

The parent frontier is unchanged: COVER, componentwise combined charge,
FP--GM, and the weaker admissible-hub minimum remain open.  The prescribed
`p=1` attachment probe is now closed negatively and exactly.  On
`f(z)=z^4-(99/100)^4`, the origin-to-root arm is safe with length `99/100`, but
the common-carrier dual product at `t=1/2` is
`(99/100)^4*3(3+2sqrt(2))/16>1`.  Hence no fixed weighted `L1` carrier contains
the origin and a root, despite sharp COVER on that same equality family.  This
rotates the campaign away from fixed-carrier attachment and back to a
switching-carrier path, direct COVER, combined charge, or FP--GM.

## 9. Return stream 08: fixed-block quadratic premise audited exactly

Two additional returns were preserved under
`state/formal_math/type_b_return_batches/erdos1041_20260827_return_stream_08`.
The first presents a full parent proof conditional on a “fixed-block
quadratic-budget alternative”; the second correctly declines a parent-proof
claim and restates centroid and proper-cluster consumers.

The first return's post-premise selection is valid.  Cauchy--Schwarz on the
whole sheet-time product space selects an entire lift only after integration;
a nontrivial cyclic monodromy then gives distinct endpoints.  However
`FixedBlockQuadraticBudgetEquivalence.md` proves the sharper variational fact

```text
inf_(lambda>0) A(lambda)E(lambda)
  = ((1/k) sum_(nu in B) length(z_nu))^2.
```

Thus the asserted quadratic alternative is exactly the missing average-length
bound on one fixed safe monodromy block.  The source-current full-fibre theorem
explicitly leaves safe-block localization open, and the charged-lifetime and
moment results do not supply it.  The return therefore contains a correct
conditional consumer but not a proof of the premise or the parent theorem.

The second return's centroid--ellipse lemma is already canonical in
`centroid_hub_budget_tao_pipeline_receipt.json`: it settles hub level and
metric length but not spoke containment.  Its proper-cluster certificate is
already present in stronger, fully projected form in
`FourReturnPacketFailureAssimilation20260827.md`; universal proper-cluster
selection remains open.  Its normalization and strictification are also
source-current.

Terminal dispositions are:

| unit | disposition | authority |
|---|---|---|
| closed normalization and strictification | `superseded_by_stronger_route` | source-current generic closure and scaling |
| fixed-block quadratic-budget alternative as a corpus consequence | `rejected_exactly` | variational equivalence plus explicit source-current safe-block residual |
| whole-block Cauchy--Schwarz and cyclic-lift selection | `composed_into_stronger_result` | `FixedBlockQuadraticBudgetEquivalence.md` |
| convex projection to the normalized root disc | `superseded_by_stronger_route` | existing projection theorem |
| claimed full parent proof | `rejected_exactly` | depends on the unsupported fixed-block alternative |
| centroid interior and pair-ellipse budget | `superseded_by_stronger_route` | canonical all-degree theorem; quintic Lean kernel |
| centroid two-spoke containment | `blocked_external` | explicitly unproved; exact counterexamples forbid a universal promotion |
| common-envelope proper-cluster certificate | `superseded_by_stronger_route` | existing projected certificate |
| universal proper-cluster selection or complementary global connector | `blocked_external` | no proof supplied or source-current |

The parent frontier is unchanged: integrated componentwise combined charge,
COVER, FP--GM, and the weaker admissible-hub minimum remain the leading
target-deciding routes.  The fixed-block formulation is retained as an exact
equivalent target inside the integrated monodromy route, not as a completed
producer.

## Claim boundary

Proved here by ordinary mathematics: Theorems 1--4, including the quantitative
root-ray strengthening Theorem 3a, the forest laws (FP1)--(FP3), the exact rejection of
the returned endpoint composition, the discriminant normalization `(PG-Delta)`,
the admissible-product completion `(AP)`, and the compensation implication `(COMP)`.

Verified by exact/symbolic computation: the merge exponents, degeneration
multiplicity, resultants, reciprocal coefficient inequality, root-ray defect
factor and rational lower-bound kernel, cyclic classification, the cubic
pointwise no-go identities, the equivalence of `(PG)` and `(PG-Delta)` after
raising to the `n`-th power, and the exact admissible-index scalar countermodel.

Not proved: `(PG)`, `(AP)`, the inadmissible compensation premise in `(COMP)`,
the claimed whole-inverse-fibre length bound, the critical-angle/monodromy
selector, threshold--chord selector, FP--GM, combined charge, COVER, an all-face
near-Fekete atlas, compact-away forcing, the special configuration-metric
systolic assertion, `S(f)<=1`, or unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_type_b_return_assimilation.py
./repo-python -m system.lib.formal_math_frontier_integrity --repo-root . --check-currency
```
