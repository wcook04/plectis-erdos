# Erdős 1041: merge-tree discriminant dichotomy

## Status

This note proves an exact identity and a rigorous global dichotomy.  It combines
the actual component merge tree with the fibre-coupled exterior-capacity bound
of `ExteriorBlaschkeFibreCapacityGap.md` and the metric consumer of
`ConnectedClusterBergman.md`.

It does **not** prove unrestricted Erdős #1041.  Its remaining gap is explicit:
the topology-dependent discriminant lower bound obtained when every metric
certificate fails can be small for a long comb-shaped tree.  A quantitative
finite near-Fekete theorem strong enough at that bound, or a sharper
polynomial constraint on the allowed merge ratios, is still required.

## 1. The truncated merge forest

Normalize the target level to `1`.  Assume first that the roots and critical
points are simple and that distinct merge levels have been separated.  Cut the
actual component merge tree at level `1`.  Its internal nodes are precisely the
critical merges with modulus below `1`.

For an internal node `v`, write

```text
beta_v  = its critical modulus,
k_v     = the number of descendant roots,
p(v)    = the next internal ancestor below level 1,
           or the virtual cut node of level 1,
r_v     = beta_v / beta_p(v).
```

Thus `0 < r_v <= 1`.  If a critical point of multiplicity `d_v-1` merges
`d_v` children, its critical modulus is counted with that multiplicity.  Put

```text
M = sum_v (d_v-1),
P_<1 = product_(|f(c)|<1) |f(c)|, counted with critical multiplicity.
```

### Theorem A (truncated merge-tree product identity)

For the actual merge forest,

```text
P_<1 = product_v r_v^(k_v-1).                              (MTD1)
```

At an arbitrary cut level `tau>0`, the scale-covariant form is

```text
P_<tau = tau^M product_v (beta_v/beta_p(v))^(k_v-1),       (MTD2)
```

where virtual parents have level `tau`.

#### Proof

Expand every edge ratio.  A fixed node level `beta_u` occurs positively with
exponent `k_u-1`.  It occurs negatively once for each child node `v` of `u`,
with total exponent

```text
sum_(v child of u) (k_v-1).
```

If `u` has `d_u` children, `k_u=sum k_v`, so

```text
(k_u-1) - sum_(v child of u)(k_v-1) = d_u-1.
```

This is exactly the critical multiplicity at `u`.  Virtual cut levels retain
total exponent `M`; multiplying by `tau^M` cancels them.  This proves (MTD2),
and `tau=1` gives (MTD1).  Equal levels and multiple critical points follow
either directly from the `d_u-1` calculation or by coalescing separated
levels.  Repeated roots make the target conclusion trivial and may be removed
before forming the forest.

The Lean companion checks the load-bearing local cancellation identity

```text
R^(a+b+1) x^a y^b = R (R x)^a (R y)^b,
```

which is the binary induction step with `a=k_left-1` and `b=k_right-1`.

## 2. Metric failure forces discriminant mass

For `2 <= k <= n`, define

```text
Theta_(n,k)
  = tanh(((2n-k)/k)^(2/n))^(k/2).                         (MTD3)
```

For `k<n`, this is exactly the strengthened fibre-capacity/Bergman threshold
from `ExteriorBlaschkeFibreCapacityGap.md`.  For `k=n`, the same formula becomes
`tanh(1)^(n/2)`, the ordinary Pólya-capacity threshold for the terminal
component.

Observe node `v` at regular levels tending upward to its parent level (or to
the cut level `1`).  Its largest normalized internal critical modulus is

```text
q_v = beta_v/beta_p(v) = r_v.
```

Hence, if

```text
r_v <= Theta_(n,k_v),                                    (MTD4)
```

then `ConnectedClusterBergman.md` gives two roots joined inside the target
lemniscate by a curve of length at most `2` (and strictly below `2` after the
usual minimum-enclosing-disc normalization for roots in the open unit disk).
When equality holds in (MTD4), apply the regular-level theorem along
`t_j upward beta_p(v)` and take an arclength-parametrized subsequential limit;
the curves have uniformly bounded length and lie in the compact parent
sublevel, so Arzelà--Ascoli and lower semicontinuity preserve the bound.

Let

```text
D = product_c |f(c)|
  = product_(i<j)|a_i-a_j|^2/n^n
```

be the discriminant ratio.  Critical moduli at or above the cut level are at
least one, so `D >= P_<1`.  Combining this with Theorem A proves:

### Theorem B (metric-or-discriminant dichotomy)

Either some actual merge node satisfies (MTD4), and Erdős #1041 follows for
that polynomial, or

```text
D > product_v Theta_(n,k_v)^(k_v-1).                     (MTD5)
```

The strict inequality comes from failure of every closed threshold.  This is
not an abstract-tree heuristic: every factor is attached to an actual
lemniscate component and every exponent is forced by critical multiplicity.

## 3. What the computation decides

`scripts/check_erdos1041_merge_tree_discriminant_dichotomy.py` performs four
independent checks:

1. exact rational replay of (MTD2) on every ordered binary tree through nine
   leaves;
2. the scalar threshold comparison and its `k=n` calibration;
3. numerical actual merge trees in bulk and near-regular families, with the
   product identity checked against the critical-value product;
4. the theorem's intended discriminator: bulk rows usually contain several
   certified nodes, whereas every tested near-regular row fails every proper
   node with adjacent ratios around `0.994--0.9997`.

The fourth item is falsifier evidence, not proof.  It identifies the surviving
geometry: rapid nearly simultaneous merging near the regular polygon.

## 4. Exact remaining boundary

Theorem B closes the previously missing logical splice

```text
exterior capacity gap + actual merge tree + Bergman metric consumer
    -> a certified short path OR an explicit discriminant lower bound.
```

It does not by itself turn (MTD5) into a sufficiently small coefficient
neighbourhood of `z^n-lambda` for the all-degree finite connector theorems.
The universal product on the right can deteriorate along a long comb because
large `k` thresholds are small and carry exponent `k-1`.  Therefore the next
target is one of:

1. prove that polynomial merge trees cannot realize the worst abstract comb
   while all ratios merely clear their thresholds;
2. replace the nodewise threshold by a weighted aggregate Bergman consumer;
3. quantify the existing near-Fekete finite transfer directly in terms of the
   topology-sensitive product in (MTD5).

Any of these would compose with Theorem B.  Merely observing that `D<=1`, or
feeding the merge-tree lower area bound into an upper-area criterion, does not.
