# Grouped critical-cluster monodromy

Status: ordinary exact all-degree local theorem, exact scalar replay, and
deterministic continuation probe.  2026-08-27.

**This does not prove unrestricted Erdős #1041.**  It proves that the
cluster-aware survivor isolated by `SeparateCriticalContourNoGo.md` is a real
mechanism: it gives a full-cycle path of length below two throughout a
coefficient neighbourhood of every strict regular polygon `z^n-r^n`, in every
degree.  What remains global is quantitative control as `r` tends to one and
the critical cluster approaches or crosses the unit value circle.

## 1. The grouped lollipop

Fix `n>=2`, `0<r<1`, and

```text
f_0(z) = z^n-r^n.
```

Choose `s>0` and put `q=s^n`, subject to

```text
q < min(r^n, 1-r^n).                                  (G1)
```

In the value plane let `eta_q` be the lollipop

```text
0  ->  -r^n+q,
one positive turn around  w=-r^n+q exp(i theta),
-r^n+q  ->  0.                                        (G2)
```

The loop groups the whole `(n-1)`-fold critical value `-r^n` inside one
circle.  By (G1), every point of the lollipop has modulus strictly below one.

> **Theorem 1 (exact grouped-loop formula).**  The monodromy of `eta_q` for
> `f_0` is the `n`-cycle `j -> j+1`.  Every complete lift has length
>
> ```text
> ell_(n,r,q)
>   = 2(r-q^(1/n)) + (2 pi/n)q^(1/n)
>   = 2r - 2(1-pi/n)s.                                (G3)
> ```

*Proof.*  Along the outward stem write `w=-t`, with `t` increasing from `0`
to `r^n-q`.  Then

```text
z^n = r^n-t,
```

so the lift from `r omega^j` is the radial segment down to `s omega^j`, of
length `r-s`.  On the circle,

```text
z^n = q exp(i theta),
```

and the lift is the radius-`s` circular arc from `s omega^j` to
`s omega^(j+1)`, of angle `2 pi/n` and length `2 pi s/n`.  The return stem is
the radial segment from `s omega^(j+1)` to `r omega^(j+1)`, again of length
`r-s`.  This proves (G3) and the full-cycle monodromy. ∎

> **Corollary 2 (a strict choice exists in every degree).**  For every
> `n>=2` and `0<r<1`, `q` may be chosen to satisfy (G1) and
> `ell_(n,r,q)<2`.

*Proof.*  If `n>=4`, then `pi<n`, so (G3) is less than `2r<2` for every
admissible positive `q`.  For `n=2,3`, choose `s` positive and small enough
that

```text
(pi/n-1)s < 1-r,
```

as well as `s^n<min(r^n,1-r^n)`.  Then (G3) is below two. ∎

This sign change explains the opposite degree dependence already observed in
`LemniscateCapacityBudget.md`: grouped value-plane monodromy costs a small
circular arc, and that arc is divided by `n` on each lift.

## 2. Stability under coefficient perturbation

> **Theorem 3 (all-degree coefficient neighbourhood).**  For every `n>=2`
> and `0<r<1`, there is an open coefficient neighbourhood `N_(n,r)` of
> `z^n-r^n` among monic degree-`n` polynomials such that every `f` in
> `N_(n,r)` has all roots in the open unit disk and admits a based value-plane
> loop in the open unit disk with full-cycle monodromy whose every complete
> lift has length less than two.  Hence Erdős #1041 holds for every polynomial
> in `N_(n,r)`.

*Proof.*  Choose `q` by Corollary 2 and keep the fixed lollipop `eta_q`.
At `f_0`, all critical values equal `-r^n`, strictly inside its circular part.
The stem and circle stay a positive distance from that value.  Critical points
and critical values vary continuously as finite multisets with the
coefficients, so after shrinking a coefficient neighbourhood, all `n-1`
critical values remain strictly inside the circle and none meets the
lollipop.  Root continuity also keeps every root in the open unit disk.

Over the compact image of `eta_q`, the equation `f(z)=w` is then unbranched.
The implicit-function theorem, applied on finitely many compact subarcs,
labels all lifted branches continuously in the coefficients and gives uniform
continuity of their derivatives.  The individual lift-length integrals are
therefore continuous.  At `f_0` all of them equal the strict value in (G3), so
after a further shrink every complete lift has length below two.

The monodromy permutation is locally constant while no critical value crosses
the loop.  At `f_0` it is an `n`-cycle by Theorem 1, hence it remains an
`n`-cycle.  Every complete lift thus joins two distinct roots, stays in
`{|f|<1}` because its value path does, and has length below two. ∎

The same conclusion can be phrased through
`FixedBlockQuadraticBudgetEquivalence.md`: the whole `n`-sheet block is
fixed-point-free and its average complete-lift length is below two.  Theorem 3
is slightly stronger locally because continuity preserves the bound on every
lift, not only on their average.

## 3. Composition with the existing global picture

This theorem connects four source-current pieces:

1. `DegenerateHubUniqueBranchRepair.md` supplies the full-cycle interpretation
   of a unique grouped critical value.
2. `LemniscateCapacityBudget.md` supplies the value-loop/lift representation.
3. `FixedBlockQuadraticBudgetEquivalence.md` supplies the exact moved-lift
   consumer for an averaged fixed-point-free block.
4. `MergeTreeDiscriminantDichotomy.md` says that failure of the existing
   Bergman node certificates forces rapid nearly simultaneous merging near the
   regular polygon.

Theorem 3 supplies the qualitative all-degree near-regular half requested by
the fourth item.  It does **not** yet complete their composition, because the
neighbourhood shrinks as `r -> 1`: the strict metric margin `2-ell` and the
value-disk clearance `1-r^n-q` both vanish.  The exact next bridge is therefore
quantitative:

> convert the topology-sensitive discriminant lower bound (MTD5), or a sharper
> merge-ratio condition, into coefficient/critical-value cluster control strong
> enough to choose `q` with both `r^n+q<1` and (G3) below two.

There is a second boundary.  The stored degree-six and degree-nine hard
witnesses contain critical values slightly outside the unit value disk.  One
cannot circle their entire critical cluster inside `D`; a full-cluster theorem
does not apply verbatim.  The next computation must therefore allow a partial
admissible cluster and track its moved sheet block, or combine the grouped loop
with the Bergman certificate on the complementary branches.

The combined-charge, COVER, and FP--GM routes remain structurally independent.

Replay the exact scalar and deterministic continuation checks with

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_grouped_critical_cluster_monodromy.py
```
