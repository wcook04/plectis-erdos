# Separate-critical contour no-go

Status: ordinary exact theorem and exact finite replay.  2026-08-27.

**This does not prove or disprove Erdős #1041.**  It closes one tempting
construction inside the integrated-monodromy route.  Resolving every simple
critical value by its own radial slit and then circling the resulting slit
tree does produce fixed-point-free monodromy.  Near a regular triangle or
square, however, it necessarily spends more than the two-unit average lift
budget.  Grouping a cluster of critical values before circling it is not
covered by the obstruction and remains a live mechanism.

## 1. Set-up

Let `f : U -> D` be the proper degree-`k` map supplied by
`AttachmentAwareReeb.md`, Theorem 1, on a ray-separated component `U` of
`{|f|<1}` containing roots `a_1,...,a_k`, where `k>=2`.  For every critical
point `c` in `U`, put

```text
v_c = f(c),                     I_c = {t v_c : 0 <= t <= 1}.
```

The arguments of the `v_c` are distinct, so

```text
S = union_c I_c
```

is a value-plane star with centre `0` and `k-1` arms.  Its two critical
inverse branches form the canonical root-to-root arc `A_c`, of length `L(c)`.
The transposition attached to `c` joins the two endpoint roots of `A_c`, and
these `k-1` transpositions form the sheet tree `T_f`.

For sufficiently small regular `delta>0`, let `Gamma_delta` be the positively
oriented boundary of a `delta`-neighbourhood of `S`, chosen inside `D`.  Join
`0` to a base point of `Gamma_delta` by a path avoiding the critical values,
traverse `Gamma_delta`, and return along the same path.  Denote this based
lollipop loop by `eta_delta`.  It lies in the closed value disk and its `k`
complete lifts start at the roots.

## 2. The contour lower bound

> **Theorem 1 (separate-star contour lower bound).**  With the notation above,
> the monodromy of `eta_delta` is a `k`-cycle.  If
> `tilde eta_{delta,j}`, `1<=j<=k`, are its complete lifts, then
>
> ```text
> liminf_{delta -> 0}
>   (1/k) sum_j length(tilde eta_{delta,j})
>     >= (2/k) sum_c L(c).                         (SC)
> ```

*Proof.*  The contour encloses every one of the `k-1` simple branch values.
Its monodromy is therefore the product, in contour order, of their local
transpositions.  A product in which every edge-transposition of a tree occurs
exactly once is a full cycle.  For completeness, remove a leaf `q` with
incident edge `(q,p)`.  All other factors fix `q`.  Moving the factors before
`(q,p)` through by conjugation turns the product into a transposition joining
`q` to one point of the cycle supplied inductively by the remaining tree;
their product is a cycle on all vertices.  Thus the monodromy is a `k`-cycle,
and in particular has no fixed sheet.

For the metric statement, first truncate every arm `I_c` away from `0` and
`v_c`.  On such a compact regular segment the inverse branches are
holomorphic.  The two sides of `Gamma_delta` adjacent to that arm converge in
`C^1` to the segment.  On each side, the two inverse branches selected by the
critical transposition converge to the two halves of `A_c`.  Consequently the
sum of the lift lengths over the two sides converges to twice the length of
the truncated `A_c`.  Distinct arms have disjoint interiors, so these lower
bounds add.  Letting the truncations exhaust the arms gives

```text
liminf length(f^{-1}(Gamma_delta) cap U) >= 2 sum_c L(c).
```

This exhaustion is legitimate at a root because it is a regular point of
`f`, and at `c` because the local form `f=v_c+zeta^2` makes the omitted tail
length `O(sqrt(epsilon))`.  During the contour portion, the `k` complete lifts
collectively traverse the full inverse image of `Gamma_delta`.  The outward
and return stems only add nonnegative length.  Divide by `k` to obtain (SC).
∎

The factor two in (SC) is the geometric cost of resolving every critical arm:
the contour must use both sides of every slit.  It is not the factor-two
root-to-root cost already internal to `L(c)`.

## 3. A chord criterion that forces failure

> **Corollary 2 (metric no-go criterion).**  Suppose every two distinct roots
> in `U` satisfy
>
> ```text
> |a_i-a_j| > k/(k-1).                            (CH)
> ```
>
> Then all sufficiently thin separate-star lollipops have
>
> ```text
> (1/k) sum_j length(tilde eta_{delta,j}) > 2.
> ```
>
> Hence the optimized fixed-block quadratic product of
> `FixedBlockQuadraticBudgetEquivalence.md` is also greater than `4` for these
> loops, despite their fixed-point-free monodromy.

*Proof.*  Every edge `A_c` joins two distinct roots, so
`L(c)>=|a_i-a_j|`.  The sheet tree has `k-1` edges.  Under (CH),

```text
sum_c L(c) > (k-1) k/(k-1) = k.
```

The right side of (SC) is therefore strictly greater than two, and the same
holds for all sufficiently small `delta`.  The fixed-block variational
identity says that the infimum of the quadratic product is the square of this
average complete-lift length. ∎

## 4. The obstruction occurs inside the normalized hard class

> **Corollary 3 (generic cubic and quartic obstructions).**  There are
> ray-separated monic cubics and quartics, with all roots in the open unit disk
> and all critical values in the open unit disk, for which every sufficiently
> thin separate-star contour has fixed-point-free monodromy but average
> complete-lift length greater than two.

*Proof.*  Start with the roots of `z^3-r^3` for `r=99/100`.  Every pairwise
distance is `r sqrt(3)>3/2`, since

```text
3(99/100)^2 > (3/2)^2.
```

For `z^4-r^4`, the smallest pairwise root distance is
`r sqrt(2)>4/3`, since

```text
2(99/100)^2 > (4/3)^2.
```

The strict chord inequalities, the open root-disk condition, and the
open critical-value-disk condition persist under sufficiently small
coefficient perturbations.  Ray-separated polynomials are dense by
`AttachmentAwareReeb.md`, Corollary G, so choose ray-separated perturbations
within those neighbourhoods.  All critical values remain in `D`; hence all
`k-1` ramification units lie in one component of `f^{-1}(D)` (otherwise
Riemann--Hurwitz over its components would give fewer than `k-1` units).
Corollary 2 applies. ∎

The exact limiting lower bounds at the unperturbed configurations are

```text
k=3:  (4 r sqrt(3))/3 > 2,
k=4:  (3 r sqrt(2))/2 > 2.
```

The inequalities have positive margins, so no length-continuity assertion for
the degenerate inverse-ray tree is needed.

## 5. Claim boundary and surviving route

The result proves three things and only three things:

1. circling the fully resolved radial critical-value star gives a derangement
   (indeed a full cycle);
2. its complete-lift average pays at least `2 sum_c L(c)/k`;
3. this exceeds two on generic normalized cubic and quartic hard examples.

It does **not** rule out a loop that encloses several nearly coincident critical
values as one cluster.  On the limiting polynomial `z^k-r^k`, a small loop
around the single multiple critical value has the desired full-cycle
monodromy without traversing all `k-1` resolved radial slits.  Thus the precise
survivor inside the fixed-point-free route is:

> construct a cluster-aware loop whose geometry charges a group of critical
> values once, rather than twice charging every edge of the resolved critical
> tree.

The fixed safe-block producer, fixed-sheet compensation, componentwise
combined charge, COVER, and FP--GM remain independent target-deciding routes.
Unrestricted Erdős #1041 remains open.

Replay the finite exact checks with

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_separate_critical_contour_no_go.py
```
