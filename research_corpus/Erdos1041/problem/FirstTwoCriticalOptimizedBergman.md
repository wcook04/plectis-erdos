# Erdős 1041: optimized first-two-critical-level Bergman theorem

## Status

This note assimilates the first return in the open 2026-08-26 Type-B stream.
The return's separated-critical-level argument is valid, but its fixed choice
`T = sqrt(beta_1 beta_2)` leaves avoidable slack.  The Bergman cost decreases
strictly at every regular level between the first and second critical levels,
so the level should be pushed to the largest value allowed by the original
target, namely `min(beta_2,1)`.

The resulting theorem strictly contains the returned regime.  It is an exact
all-degree sufficient theorem, not a proof of unrestricted Erdős 1041.  The
remaining tied-level shell is explicit below.

## Monotone first-merge cost

For `n > 2`, `b > 0`, and `t > b`, put

```text
C_(n,b)(t) = t^(2/n) log((t+b)/(t-b)).                    (1)
```

> **Lemma 1.** `C_(n,b)` is strictly decreasing on `(b,infinity)`.

Write `q=b/t`.  Direct differentiation gives

```text
C'_(n,b)(t)
 = t^(2/n-1)
   [(2/n) log((t+b)/(t-b)) - 2bt/(t^2-b^2)].             (2)
```

For `0<q<1`,

```text
log((1+q)/(1-q)) = 2 artanh(q) < 2q/(1-q^2).             (3)
```

Indeed, the difference `q/(1-q^2)-artanh(q)` vanishes at
zero and has derivative `2q^2/(1-q^2)^2>0`.  The logarithm
in (2) is positive and `2/n<1`, so (3) makes the bracket in
(2) strictly negative.  This proves the lemma.

## The optimized theorem

Let

```text
f(z)=product_(j=1)^n (z-a_j),             n>=3,
```

be monic with distinct roots in the open unit disk.  List the nonroot
critical-value moduli with multiplicity as

```text
0 < beta_1 < beta_2 <= ... <= beta_(n-1).
```

The strict inequality says that the first critical point is simple and the
first merge joins exactly two one-root components.  Put

```text
L = min(beta_2,1).
```

The standard critical-product/Fekete bound gives `beta_1<1`, hence
`beta_1<L`.

> **Theorem 2 (optimized first-merge Bergman theorem).**  If
>
> ```text
> L^(2/n) (1/(n-1))^(2/n)
>   log((L+beta_1)/(L-beta_1)) < 2,                       (4)
> ```
>
> then two roots are joined by a curve of length strictly less than `2`
> contained in the open lemniscate `{|f|<1}`.

### Proof

By continuity and Lemma 1, choose a regular level `t` with

```text
beta_1 < t < L
```

so close to `L` that the left side of (4), with `L` replaced by `t`, is
still below `2`.  Because `t<beta_2`, the component `U` born at the first
critical level contains exactly two roots and is a proper component.

For `k=2`, `ExteriorBlaschkeFibreCapacityGap.md` gives

```text
Area(U)/pi < t^(2/n) (1/(n-1))^(2/n).                    (5)
```

The largest normalized internal critical value in `U` is

```text
q_U = beta_1/t.
```

The actual theorem in `ConnectedClusterBergman.md` therefore supplies two
roots in `U` and a joining curve `Gamma` satisfying

```text
length(Gamma)^2
 <= 2 Area(U)/pi log((1+q_U)/(1-q_U))
 <  2 C_(n,beta_1)(t) (1/(n-1))^(2/n)
 <  4.                                                       (6)
```

Thus `length(Gamma)<2`.  Since `t<L<=1`, the component and the curve lie in
`{|f|<1}`.  This proves the theorem.

## A simpler direct-ratio corollary

Since `L<=1`, condition (4) follows from

```text
beta_1/L < tanh((n-1)^(2/n)).                             (7)
```

This is the returned radius-free criterion with two improvements: it uses the
direct ratio `beta_1/min(beta_2,1)` instead of
`sqrt(beta_1/beta_2)`, and it spends the whole target-level allowance up to
`1` rather than stopping at a geometric-mean intermediate level.

## Exact dominance over the returned theorem

The return chooses

```text
T = sqrt(beta_1 beta_2).
```

Its product inequality gives `T<=Gcrit<=R^n<1`, while `T<beta_2`; hence
`T<L`.  Its hypothesis is exactly

```text
C_(n,beta_1)(T) (1/(n-1))^(2/n) <= 2R^2 < 2.             (8)
```

Lemma 1 then gives the strict inequality (4).  Therefore every case proved
by the returned Theorem 5 is proved by Theorem 2, while Theorem 2 also covers
rows for which the geometric-mean stopping level is too low.

## Return coverage and authority dispositions

The source return is preserved by SHA-256 in
`state/formal_math/type_b_return_batches/erdos1041_20260826_return_stream_01/intake.json`.
Its distinct mathematical claims have the following current dispositions.

| Claim | Disposition | Evidence boundary |
|---|---|---|
| Convex-hull two-root distance budget | `landed` | Ordinary Euclidean proof; useful only when containment selects the same pair. |
| Barycentric stationary-point/critical-point correspondence | `landed` | Exact differentiation and inverse-square identities; consistent with `BarycentricEnvelope.md`. |
| Barycentric vertex-ray formula and second variation | `landed` | Exact algebra; explanatory, not target-deciding. |
| `Gcrit >= sqrt(beta_1 beta_2)` | `landed` | Elementary ordered-product inequality. |
| Returned first-two-level theorem | `strengthened_and_landed` | Replaced by Theorem 2 above, using the same source-current Bergman and exterior-capacity prerequisites. |
| Critical chord and augmented target-disc criteria | `landed` | Direct consumers of `CriticalTwoRootProximity.lean` and `BarycentricTargetDisc.md`; sufficient only. |
| All-pairs optimizer observations | `blocked_external` | Finite floating evidence; universal certification or a proof of the selected optimum is missing. |
| `Vfree<=beta_1` and FM--2 opposed-link route | `blocked_external` | Missing universal two-link visibility and same-pair metric budget in a first-merge one-root cell.  It remains a stronger producer, not the canonical frontier. |
| Pasted Lean interfaces | `superseded_by_stronger_route` | They were sketches, not compilation claims.  Only the load-bearing monotonicity/budget kernel is formalized in the companion Lean module. |

## Remaining boundary

Failure of (4) forces

```text
beta_1/min(beta_2,1)
```

close to one after the exact degree factor is included.  This is a sharper
rapid-near-simultaneous first-merge shell than the return's
`sqrt(beta_1/beta_2)` residual.  It does not by itself prove that this shell
is near Fekete in the full topology-sensitive sense, and it does not close
FP--GM, COVER, combined charge, or unrestricted Erdős 1041.
