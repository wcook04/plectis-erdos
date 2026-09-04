# Erdős 1041: the partial-cluster preimage-perimeter identity

Status: ordinary exact analytic theorem with exact rational regression and
pinned numerical decomposition.  2026-08-27.

This note strengthens the usable form of
`PartialCriticalClusterMonodromyLab.md`.  It does **not** prove unrestricted
Erdős 1041.  It replaces the opaque moved-block average in that note by one
concrete geometric quantity.

## 1. Setup

Let `f` be a polynomial, let `Q` be a Jordan domain whose boundary contains no
critical value of `f`, and let `W` be a component of `f^{-1}(Q)` on which

```text
f : W -> Q
```

is proper of degree `d`.  Assume that `W` is a Jordan domain.  Fix
`q in boundary Q` and a piecewise `C^1` arc `alpha` from the regular value `0`
to `q`, with its interior disjoint from `closure(Q)` and from all critical
values.  Let `B` be the `d` sheets at `0` whose lifts of `alpha` end on
`boundary W`.  Write `alpha_j` for the lift starting at the corresponding
root and put

```text
Lambda(alpha,W) = sum_(j in B) length(alpha_j),
P(W)             = length(boundary W).
```

Let `delta` traverse `boundary Q` once positively from `q`, and form the
lollipop

```text
eta = alpha * delta * reverse(alpha).
```

For `j in B`, denote its complete lift by `tilde eta_j`.

## 2. Exact identity

> **Theorem 1 (preimage-perimeter identity).**  In the setup above,
>
> ```text
> sum_(j in B) length(tilde eta_j)
>     = 2 Lambda(alpha,W) + P(W).                         (PP1)
> ```
>
> Consequently the moved-block average criterion of
> `PartialCriticalClusterMonodromyLab.md` is exactly
>
> ```text
> 2 Lambda(alpha,W) + P(W) <= 2d.                         (PP2)
> ```

### Proof

The forward stem contributions sum to `Lambda(alpha,W)`.  If `sigma` is the
boundary monodromy, the return stem of the lift starting on sheet `j` is the
reverse of `alpha_(sigma(j))`.  Since `sigma` permutes `B`, the return stem
contributions also sum to `Lambda(alpha,W)`.

It remains to sum the boundary contributions.  At every regular point `v` of
`boundary Q`, the `d` lifted velocities have norms

```text
1 / |f'(z)|,       z in boundary W and f(z)=v.
```

Hence their total length is

```text
integral_(boundary Q)
  sum_(z in boundary W, f(z)=v) 1/|f'(z)| |dv|.
```

The one-dimensional area formula for the degree-`d` covering
`f : boundary W -> boundary Q` identifies this integral with
`length(boundary W)`.  Adding the two stem sums proves `(PP1)`, and division
by `d` gives `(PP2)`.  Notice that the proof does not select one short sheet
pointwise: selection occurs only after the complete lifted lollipops have been
integrated.  ∎

### The connected-subtree consumer

In the ray-separated generic setup of `PartialCriticalClusterMonodromyLab.md`,
a Jordan domain enclosing exactly a connected critical-edge subtree has one
branched preimage component `W` of degree `d=|B|`.  Its contour monodromy is a
full `d`-cycle.  Therefore strict value-disk containment together with

```text
2 Lambda(alpha,W) + P(W) < 2d                         (PP3)
```

produces one complete lift joining distinct roots, inside `|f|<1`, with
length below two.

This is target-deciding but strictly stronger than the parent theorem.  The
new open producer is the existence of one isolating pair `(Q,alpha)` obeying
`(PP3)`, or a complementary theorem proving a short path whenever every such
pair fails.

## 3. The grouped regular family becomes transparent

For

```text
f(z)=z^n-r^n,      0<s<r<1,
Q={v: |v+r^n|<s^n},
```

take the straight value stem from `0` to `-r^n+s^n`.  Then `W={|z|<s}`,

```text
Lambda(alpha,W)=n(r-s),       P(W)=2 pi s.
```

The average complete-lift length is therefore

```text
[2n(r-s)+2 pi s]/n
  = 2(r-s)+(2 pi/n)s
  = 2r-2(1-pi/n)s.                                      (PP4)
```

This recovers the exact formula in `GroupedCriticalClusterMonodromy.md`
without tracking the individual branches.  For `n>=4`, `(PP4)<2r<2`.  For
`n=2,3`, choosing `s` sufficiently small gives `(PP4)<2`.  Thus the grouped
construction is precisely a stem-forest-plus-perimeter certificate.

## 4. Why this changes the analytic frontier

The partial-cluster metric question is no longer an unspecified inverse-branch
average.  It is the following geometric alternative:

```text
find an admissible branched component W and access arc alpha with
        2 * (total lifted access length) + perimeter(W) < 2 deg(W),
or spend the failure on a complementary Bergman/COVER certificate.
```

This exposes three independent currencies already present in the corpus:

1. `UnconditionalConstantFactorBound.md` controls component perimeters after
   averaging over levels, but its present constants do not imply `(PP3)`;
2. `ConnectedClusterBergman.md` and
   `ExteriorBlaschkeFibreCapacityGap.md` can certify a short path from a small
   component, but do not yet control the access forest `Lambda`;
3. `FixedBlockQuadraticBudgetEquivalence.md` consumes `(PP3)` exactly and
   explains why a whole-fibre or pointwise block estimate is insufficient.

The identity therefore supplies a clean packet split: one desk should attack
the integrated perimeter/access inequality directly, while a second should
prove the dichotomy between its failure and the existing Bergman merge-node
certificate.  Neither desk should re-ask for the already-proved monodromy
topology or the already-refuted pointwise component-block `L1` contraction.

## 5. Verification boundary

`scripts/check_erdos1041_partial_cluster_preimage_perimeter.py` replays in
exact rational arithmetic the permutation bookkeeping in `(PP1)`, checks the
regular-family strict inequalities using `pi<355/113`, and confirms that the
formula is exactly the one used by the grouped-cluster theorem.

The covering-space and one-dimensional area-formula step is an ordinary
analytic proof, not a Lean-checked theorem.  The pinned degree-six and
degree-nine continuation rows in `PartialCriticalClusterMonodromyLab.md`
remain floating-point candidate evidence.  No interval certification,
universal `(PP3)` estimate, COVER theorem, combined-charge theorem, FP--GM
theorem, or unrestricted Erdős 1041 proof is claimed here.
