# Partial critical-cluster monodromy lab

Status: ordinary exact conditional topology theorem plus pinned deterministic
candidate evidence.  2026-08-27.

**This does not prove Erdős #1041, nor does it rigorously certify the two
floating-point witnesses below.**  It identifies and tests the exact repair
needed when the full near-Fekete critical cluster does not fit inside the unit
value disk.

## 1. The exact subtree-cycle mechanism

Let `f : U -> D` be a ray-separated proper degree-`k` component as in
`AttachmentAwareReeb.md`.  Its simple critical values label the edges of the
sheet tree `T_f`.  Let `E` be a nonempty connected set of edges of `T_f`, let
`B` be its incident vertex set, and suppose a Jordan domain `Q` compactly
contained in `D` encloses exactly the critical values belonging to `E`.
Choose a path from `0` to `boundary Q` avoiding all critical values, circle
`Q` once, and return along the path.  Call the lollipop `eta_Q`.

> **Theorem 1 (partial-cluster cycle).**  The monodromy of `eta_Q` is a single
> `|B|`-cycle on `B` and fixes every sheet outside `B`.  Consequently, if the
> complete lifts starting on `B` satisfy
>
> ```text
> (1/|B|) sum_(j in B) length(tilde eta_(Q,j)) <= 2,       (PC)
> ```
>
> then two distinct roots are joined inside the closed unit lemniscate by a
> path of length at most two.  With strict value-disk containment and a strict
> inequality in (PC), the resulting path lies in the open lemniscate and has
> length below two.

*Proof.*  A connected edge subset of a tree is a tree on its incident vertex
set, so `|E|=|B|-1`.  The contour monodromy is the product, in contour order,
of the edge transpositions in `E`.  A product using every edge transposition
of a tree exactly once is a full cycle, by the leaf-removal argument in
`SeparateCriticalContourNoGo.md`, Theorem 1.  Those transpositions involve no
sheet outside `B`, so the remaining sheets are fixed.  The block `B` is thus
fixed-point-free.  Apply `FixedBlockQuadraticBudgetEquivalence.md` to (PC); a
selected complete lift begins and ends at distinct roots.  Its value path
keeps it in the stated lemniscate. ∎

This is the precise hybrid missing from the full-cluster theorem: one need not
enclose inadmissible critical values.  It is enough to isolate a connected
subtree of admissible branch values and pay the metric average only on the
moved block.

## 2. The two pinned hard witnesses

`StraightSpokeHubCriterionLab.md` stores exact IEEE-754 root literals for two
near-Fekete witnesses:

```text
degree 6: two critical values have modulus below one, three above;
degree 9: three critical values have modulus below one, five above.
```

The checker forms the mean `m` of the admissible critical values, shifts the
circle centre a pinned distance toward the origin, and takes radius

```text
1.02 max_(admissible v) |v-centre| + 10^(-9).
```

The shifts are

```text
degree 6: 0.0003719929580981397,
degree 9: 0.00014697796956473399.
```

Both circles lie strictly inside `D`, enclose every admissible critical value,
and exclude every inadmissible one with measured margins above `3.5e-6`.
Continuation of every fibre root around the lollipop gives:

| degree | admissible branch values | moved cycle | moved mean | largest moved lift | value-disk clearance |
|---:|---:|---:|---:|---:|---:|
| 6 | 2 | 3 | `1.84327` | `2.01615` | `2.92e-5` |
| 9 | 3 | 4 | `1.63875` | `2.03175` | `1.38e-5` |

The largest individual lift is above two in both rows.  Therefore the average
block consumer is not cosmetic: selecting a predetermined moved lift would
fail on the measured contour, while the block mean remains well below two.

The continuation is repeated at two mesh resolutions.  The moved means drift
by about `5.2e-5` and `1.1e-4`, far below their margins to two; the cycle sizes
and all inclusion/exclusion margins are unchanged.

## 3. What the computation does and does not establish

Theorem 1 is exact.  The two rows are candidate evidence because root
continuation and arclength quadrature use floating-point arithmetic without an
interval enclosure.  They do not promote the stored witnesses to proved
instances.

They do decisively select the next analytic target.  On the actual hard
examples, the admissible critical values already form one cluster whose
monodromy block has the right average budget; the inadmissible critical values
can remain outside and their sheets can remain fixed.  Thus the full-cluster
boundary in `GroupedCriticalClusterMonodromy.md` is not evidence against the
route.

The next proof step is one of:

1. derive an analytic upper bound for the moved-block lift average from the
   cluster centre, radius, and root/critical-value perturbation size;
2. interval-certify these pinned rows, then infer an open root neighbourhood;
3. compose partial-cluster failure with the existing Bergman merge-node
   certificate, so that either a subtree cycle has (PC) or a complementary
   component is already short.

Combined charge, COVER, and FP--GM remain independent routes.

Replay:

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_partial_critical_cluster_monodromy.py
```
