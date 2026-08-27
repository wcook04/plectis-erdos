# Erdős 1041: eight-packet frontier coevolution after the 2026-08-26 returns

## Status and target

The target remains unrestricted Erdős 1041:

> If a monic polynomial has all listed zeros in the open unit disk, two listed
> zeros are joined inside `|f|<1` by a path of length `<2`.

This note is the source-authority design layer for eight new Type-B packets.
It is not a proof of the target.  All twenty-four artifacts in the
2026-08-26 return bundle were read before selecting the desks.  The selection
optimizes expected proof value; overlap is deliberate where two coordinates
attack the same target-deciding throat.

The returned full composition is not reused.  It identifies the derivative
geometric mean `Q_U^(1/k)` with the different Bergman maximum `q_C`, and uses
an area lower bound where the Bergman consumer needs an upper small-area
criterion.  The actual merge theorem, root-ray contraction, and hull
projection survive independently.

The post-build assimilation has now added one further exact theorem.  The
exterior component model supplies a strict degree-only capacity gap at every
proper regular node.  This does not repair the false identification above;
instead it feeds the actual Bergman and COVER variables through their valid
capacity/area interfaces.

## 1. A stronger forest law retained from the actual merge theorem

At a regular level `R`, let `C_1,...,C_s` be the components of `{|f|<R}`.
Write `k_j` for the number of roots in `C_j`.  For a root `a_i` descending to
the component node `j`, let `Y_(i,j)` be its merge-propagated inverse-derivative
weight from `TypeBReturnAssimilation20260826.md`.

Define the full leaf energy

```text
E_j = sum_(a_i in C_j) Y_(i,j)^2.
```

### Theorem A (forest leaf-energy inequality)

At every regular forest cut,

```text
sum_(j=1)^s R^(2/k_j-2/n) E_j <= 1.                 (FE)
```

### Proof

The actual-branch theorem `MT1` gives

```text
A_j(R) >= pi R^(2/k_j) E_j
```

for every component.  The components are disjoint, while Pólya's sharp
lemniscate-area inequality gives

```text
sum_j A_j(R) <= pi R^(2/n).
```

Summing the first inequalities and dividing by `pi R^(2/n)` proves (FE).
By AM--GM,

```text
E_j >= Q_j^(2/k_j)/k_j,
```

so (FE) strictly retains the leaf data discarded by the already-recorded
geometric-mean forest law `FP3`.  No metric conclusion is claimed: (FE) is an
upper budget on a derivative-weight energy produced from component-area lower
bounds.

### Why this changes the packet portfolio

`Q_j` alone cannot equal the Bergman variable, but the vector of leaf weights
can interact with root-by-root endpoint support, harmonic measure, or a
two-sheet selection.  Desks 2--4 therefore receive (FE), not the false scalar
composition.  A useful return must either construct a true metric consumer
for this vector or prove that the vector still lacks a necessary invariant.

## 2. The moving root-ray witness is a finite switching problem

Let

```text
f(z)=product_(j=1)^n (z-a_j),       |a_j|<1,
P_i(t)=|f(t a_i)|^2-1,              0<=t<=1.
```

### Theorem B (finite radial switching complex)

For each `i`, `P_i` is a real polynomial in `t` of degree at most `2n`.
Consequently

```text
S_i={t in [0,1]: |f(t a_i)|<=1}
```

is a compact semialgebraic set with at most `2n+1` interval components.  The
arbitrary-modulus root-ray product contraction implies

```text
[0,1]=union_i S_i.                                      (RS1)
```

Hence `[0,1]` has a finite interval-component cover with at most
`n(2n+1)` vertices.  It admits a finite overlap chain from `0` to `1`; at each
switch radius shared by components belonging to different indices, two
distinct root-ray points are simultaneously in the closed unit lemniscate.

### Proof

For real `t`, both `f(t a_i)` and its conjugate are polynomials in `t` of
degree at most `n`, so their product minus one has degree at most `2n` and real
coefficients.  A real degree-`2n` polynomial has at most `2n` interval
endpoints in `[0,1]`, giving the stated safe upper bound on components.
The root-ray product theorem gives at least one safe index at every `t`, which
is (RS1).  A finite interval cover of a connected interval has a greedy
overlap subchain from its left endpoint to its right endpoint.

### Exact boundary

This does not prove a connecting chord at a switch.  Nor does pointwise
goodness imply that the remaining outward tail of the same ray is good: safe
sets may be disconnected.  The exact one-spoke quintic refutes the fixed-index
upgrade.  The gain is a finite, algebraic switching object on which a chord,
potential, or interval-overlap theorem can be asked without pretending that
the good index is constant.

For concyclic roots, last-exit components give the safe truncated arms of Form
A-cut.  The missing step is therefore a switch radius and pair for which the
common-radius chord is also safe.  Desk 8 is built around exactly that finite
upgrade.

### Theorem C (safe endpoints do not force a safe switch chord)

The most direct attempted consumer of Theorem B is false, even for three
concyclic roots strictly inside the disk.  Put `r=99/100` and

```text
u_1=(3+4i)/5,   u_2=(3-4i)/5,   u_3=(-4+3i)/5,
a_j=r u_j,      f(z)=product_j (z-a_j),             t=1/2.
```

For `x=t a_2`, `y=t a_3`, and their midpoint `m=(x+y)/2`, exact Gaussian-
rational arithmetic gives

```text
|f(x)|^2 = 31834268291696013 / 40000000000000000 < 1,
|f(y)|^2 =   208067113017621 /   320000000000000 < 1,
|f(m)|^2 = 8367179814045680661 / 8000000000000000000 > 1.
```

Thus simultaneous safety of two common-radius root-ray points does not imply
containment of their straight chord.  A valid switching theorem must use the
special combinatorics of a cover-chain transition, select a different curve,
or add a potential/last-exit hypothesis.  This exact no-go is replayed by the
coevolution checker and is included in Desk 8's boundary.

## 2A. Proper components have a strict degree-only capacity gap

Let `U` be a regular component of `{|f|<t}` containing `k<n` roots and put
`q_n=(n-1)/(n+1)`.  For every root outside `U`, let `xi_j` be its preimage
under the normalized exterior Riemann map.

### Theorem D (proper-component capacity gap)

The exterior angular derivative is

```text
h(theta)=n-sum_{a_j notin U} P_{1/conj(xi_j)}(exp(i theta)) > 0.
```

Evaluating one Poisson summand at its peak gives

```text
|xi_j| > (n+1)/(n-1).
```

The exact leading-coefficient identity therefore yields

```text
cap(closure(U)) < t^(1/n) q_n^((n-k)/n),
Area(U)/pi       < t^(2/n) q_n^(2(n-k)/n).              (PCG)
```

Consequently the connected-cluster Bergman theorem closes `U` whenever

```text
q_U <= tanh(q_n^(-2(n-k)/n))^(k/2),
```

and the first-merge geodesic theorem proves COVER whenever

```text
t^(2/n) q_n^(2(n-k)/n)
  log(1/(1-(mu/t)^(2/k))) <= 1.
```

The proof, conformal-welding firewall, exact checker, and Lean scalar kernel
are in `ProperComponentCapacityGap.md`, its companion script, and
`ProperComponentCapacityGap.lean`.  The remaining producer is no longer an
unstructured thin-corridor exclusion: force one proper merge through one of
these explicit thresholds, or handle the terminal all-root node separately.

## 2B. The exterior factors obey a stronger fibre-coupled product law

The independent peak bounds in Theorem D discard the fact that all exterior
factors occur in one finite Blaschke product.  Put `m=n-k` and

```text
B(z)=product_(j=1)^m (z-a_j)/(1-conj(a_j)z),
a_j=1/conj(xi_j),
p=|B(0)|=product_j |xi_j|^(-1).
```

For every boundary value `w`, harmonic-measure pullback gives the exact fibre
identity

```text
sum_(B(zeta)=w) 1/|B'(zeta)|
  = (1-|B(0)|^2)/|w-B(0)|^2.
```

Choose `w` opposite `B(0)`.  The exterior speed inequality says
`|B'(zeta)|<n` at all `m` fibre points, so

```text
m/n < (1-p)/(1+p),
p < (n-m)/(n+m) = k/(2n-k).                              (FB)
```

### Theorem E (exterior-Blaschke fibre capacity gap)

Every proper regular `k`-root component satisfies

```text
cap(closure(U)) < t^(1/n) (k/(2n-k))^(1/n),
Area(U)/pi       < t^(2/n) (k/(2n-k))^(2/n).              (FCG)
```

Moreover

```text
k/(2n-k) <= ((n-1)/(n+1))^(n-k),
```

with equality only for one excluded root.  Hence Theorem E strictly improves
Theorem D whenever `n-k>=2`.  The valid direct Bergman and COVER thresholds are
now respectively

```text
q_U <= tanh(((2n-k)/k)^(2/n))^(k/2),

t^(2/n) (k/(2n-k))^(2/n)
  log(1/(1-(mu/t)^(2/k))) <= 1.                           (FCOVER)
```

The ordinary analytic proof, sharp boundary-map calibration, Lean-checked
scalar algebra, and exact all-degree comparison are in
`ExteriorBlaschkeFibreCapacityGap.md`, `.lean`, and its companion checker.
This still does not identify an exterior circle parameter with the interior
one, and it still does not force a merge ratio through the threshold.  It is a
strictly stronger invariant for Desks 1, 2, and 4.

### Theorem F (merge-tree discriminant dichotomy)

Cut the actual component merge tree at target level `1`.  For every internal
node `v` below the cut, let `beta_v` be its birth level, `k_v` its descendant
root count, and `p(v)` its next internal ancestor or the virtual level-one cut.
Put `r_v=beta_v/beta_p(v)`.  Counting multiple critical points with their
critical multiplicity, the exact telescoping identity is

```text
product_(|f(c)|<1) |f(c)| = product_v r_v^(k_v-1).       (MTD)
```

The exponent is forced locally: a `d`-child merge leaves
`(k_v-1)-sum_child(k_u-1)=d-1`, exactly its critical multiplicity.  Since
critical moduli above the cut are at least one, the full discriminant ratio
`D=product_c|f(c)|` dominates the left side.

Define

```text
Theta_(n,k)=tanh(((2n-k)/k)^(2/n))^(k/2).
```

Theorem E plus the connected-cluster Bergman consumer proves the target as
soon as one actual node has `r_v<=Theta_(n,k_v)`; for `k_v=n`, the same formula
is the terminal Pólya threshold `tanh(1)^(n/2)`.  Therefore either a short path
is already certified, or

```text
D > product_v Theta_(n,k_v)^(k_v-1).                    (MD)
```

This is the first exact global splice from every failed proper-node metric
test into the discriminant/near-Fekete lane.  Exact rational replay checks
2,055 ordered binary trees through nine leaves; actual-tree fixtures satisfy
the telescoping identity to floating-point noise.  Bulk fixtures have several
certified nodes.  Near-regular fixtures have none, with adjacent ratios
`0.994--0.9997`, identifying rapid near-simultaneous merging as the surviving
geometry.  The proof, Lean-checked local exponent kernel, and checker are in
`MergeTreeDiscriminantDichotomy.md`, `.lean`, and its companion script.

The remaining boundary is quantitative rather than logical: the product in
(MD) can be weak on an abstract long comb.  The next proof must either rule out
that comb for polynomial merge trees, prove a weighted aggregate Bergman
consumer, or make the finite near-Fekete transfer effective at the
topology-sensitive product bound.

## 3. Local attack of the eight candidate desks

### Desk 1 — unrestricted fan-in after the return audit

Attempted chain:

```text
actual merge forest + root-ray switching + hull projection
  -> one of combined charge / COVER / FP--GM / all-face connector
  -> closed length-two path on the normalized closed-root class
  -> strict open-disk theorem.
```

The first arrow is not proved.  The packet asks for a complete proof and gives
the three target-deciding consumers side by side, but explicitly forbids the
false `Q_U=q_C` composition.  Its fallback must be a theorem that closes a
quantified partition of the closed-root class, not another status synthesis.

### Desk 2 — a true metric consumer for the actual forest certificate

Local probe: (FE) preserves the entire leaf vector, while Theorem E supplies a
strict capacity deficit determined by the number of missing roots.  The open
arrow is now to force some node's actual `q_U` below the strengthened Bergman
threshold, using the leaf distribution, boundary `log|f'|`, or a two-sheet
inequality.

Stop rule: a lower area bound cannot be fed to a small-area Bergman criterion.
A valid return must supply a differently directed metric theorem or an exact
no-go showing which additional component invariant is indispensable.

### Desk 3 — forest-assisted combined charge

Local probe: the endpoint deficit in `CriticalTreeLengthCharge.md` is already
root-indexed, and (FE) is also root-indexed.  This is the first coordinate in
which the merge certificate could price the dangerous signed curvature term
without collapsing to a scalar component product.  The requested theorem is

```text
sum_(e in C) (D_e+K_e) >= 0
```

for each admissible component, retaining the global circumradius and every
external-root factor in `f'/f`.

Stop rules already exact in the corpus: curvature alone, root-star charge,
component-local circumradius, absolute curvature, and raw angular coarea do
not close the estimate.

### Desk 4 — forest-assisted COVER

Local probe: `VisibilityOverlapReduction.md` requires only a one-root intrinsic
cover of a minimal connected carrier, not two simultaneous spokes.  Theorem E
already converts polynomial proper-map structure into a strict upper area
loss and then into an explicit first-merge COVER threshold.  The full forest
law can now be used to force that threshold, rather than being incorrectly
substituted for the Bergman variable.

The exact endpoint is (COVER), preferably on the two descending branches from
the first merge while paths may use the entire level-one component.  A fixed
level, straight segments, nearest-root selection, and ONE-SPOKE are excluded.

### Desk 5 — genuinely free-pair FP--GM

The fixed least-critical/two-nearest-root CE--GM statement is exactly false in
degree four.  The local return audit leaves only joint minimization over the
pair and a possibly noncritical hub.  The exact open producer is a pair and
hub satisfying both the two-arm containment at the critical geometric-mean
level and the total ellipse budget `<=2`.

The two strict rational tied-face rescues are positive calibration: a correct
theorem must be flexible enough to select them.  Finite KKT enumeration is a
candidate generator only; an above-threshold stationary branch is not a
global counterexample or bound.

### Desk 6 — integrated two-sheet monodromy action

The pointwise full-fibre and exact component-block `L1` contractions are both
false.  The actual residual is the minimum weighted action of a loop whose
monodromy changes one end into another, with two selected sheets rather than
the whole block.  Fibre interpolation duality supplies the realizability
constraint; the exact no-go fibre supplies the mandatory falsifier.

The packet asks for weak majorization, an internally weighted two-sheet
Chebyshev theorem, or an integrated loop inequality with equality rigidity.
It must reproduce the known noncritical connector rescues rather than reject
their faces because an aggregate speed is too large.

### Desk 7 — cover the complement of transferred tied-face cells

Strict complex rotated-diameter tubes already transfer to actual
near-Fekete polynomials.  Exact rational connector templates and their full
polyhedral cells also occupy part of the normalized tied-face section.  The
new task is not transfer of those cells; it is coverage of their complement
and equality boundaries by finitely or recursively generated connector
templates, or a global carrier theorem.

The packet's decisive computation is a normalized-section coverage search
that returns either an exact uncovered face or a finite certificate suitable
for CAD/SOS/Lean.  Sampling is never the final certificate.

### Desk 8 — radial switching and Form A-cut

The arbitrary-modulus product theorem and Theorem B replace the false fixed
spoke by a finite switch complex.  For concyclic roots, combine its interval
components with the exact last-exit radii and seek one overlap where the
common-radius chord stays below one.  This is the exact Form A-cut producer
and reaches the regular polygon equality family.

The packet may first prove the concyclic theorem, then seek the general-root
analogue using convex-hull projection and unequal cutoffs.  It must not reuse
ONE-SPOKE, the refuted smallest-gap selector, concentric alternation, or a
plain-chord near-Fekete split.  Theorem C additionally forbids the pointwise
shortcut "two safe ray endpoints imply their chord is safe"; the selected
transition must exploit more than endpoint safety.

## 4. Portfolio comparison

| Desk | Central object | Proof currency | Parent leverage | Cheapest falsifier |
|---|---|---|---|---|
| 1 | whole normalized root class | complete path fan-in | direct | expose one missing class in the claimed partition |
| 2 | merge forest plus fibre-coupled proper-node capacity gap | leaf energy, boundary derivative, Bergman threshold | auxiliary until threshold forcing lands | matched forest/capacity invariants with different `q_U` |
| 3 | admissible critical forest | endpoint support plus signed curvature | target-deciding stronger producer | pinned two-cluster and near-Fekete rows |
| 4 | proper first-merge carrier in its ambient component | explicit capacity/area loss plus intrinsic one-root distance | target-deciding stronger producer | terminal all-root node and level nonmonotonicity |
| 5 | jointly selected pair and free hub | geometric-mean level plus ellipse budget | target-deciding stronger producer | exact quartic fixed-pair separation |
| 6 | monodromy loop and selected sheets | integrated inverse-derivative action | closes tied-face metric residual | exact six-sheet block-L1 no-go |
| 7 | normalized tied-face coefficient section | finite connector charts and overlap | closes near-Fekete boundary | uncovered normalized coefficient face |
| 8 | finite radial safe-interval complex | log potential and switch chord | proves concyclic case, possibly more | exact one-spoke and smallest-gap no-gos |

Desks 2--4 deliberately share the new leaf-energy theorem; desks 5--7 share
the requirement that noncritical connectors remain available.  This overlap
is intentional because those combinations have higher proof value than an
artificially orthogonal eighth mechanism.

## 5. Claim boundary and packet consequence

Ordinary exact mathematics proved here or in the post-build assimilation:
Theorems A, B, C, D, and E.  The scalar cores of Theorems D and E are
Lean-checked.

Previously proved and consumed: actual merge-tree branch/forest laws,
arbitrary-modulus root-ray product contraction, convex-hull projection,
visibility-overlap reduction, monodromy-loop representation, fibre
interpolation duality, complex-diameter transfer, and the named exact no-gos.

Still unproved: forcing a proper node through the strengthened
Bergman/COVER threshold (or separately closing the terminal all-root node),
componentwise combined charge, COVER in full generality, FP--GM, integrated
selected-loop contraction, all-tied-face chart coverage, Form A-cut, and
unrestricted Erdős 1041.

Every generated packet must state this boundary, expose its complete
producer-to-consumer-to-parent chain, allow a full solution to be claimed, and
require the receiver to continue through every new residual in the same
response.
