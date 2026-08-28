# Erdős 1041: admissible critical-arc product probe

Status: one exact cherry-region theorem plus deterministic floating-point
evidence, 2026-08-28. The theorem proves the rooted-subtree base outside an
explicit rapid-near-tie shell. The full rooted-subtree inequality and Erdős
1041 remain open.

## Target-deciding product

For a monic degree-`n` polynomial with simple critical points, let

```text
A = {c : |f(c)| < 1},
L(c) = length of the canonical two-arm descending inverse-ray edge at c,
q(c) = L(c)/(2 |f(c)|^(1/n)).
```

The source-current exact reduction says

```text
product_(c in A) q(c) <= 1                              (AP)
```

is sufficient for the parent theorem: because every `|f(c)|<1`, `(AP)` forces
some admissible `L(c)<2`. The all-critical analogue is not itself sufficient,
because it can spend its short factor at an inadmissible critical point.

## Deterministic probe

The checker reuses the 254 configurations of
`AdaptiveClusterSelectionLab.md`, adds fifteen controlled near-regular shells
in degrees `3..7`, and imports the source-current pinned near-tie quartic that
refutes the strong minimum-critical inequality. For every admissible simple
critical value it traces a shrinking singleton lollipop. By the exact
singleton-limit theorem, its moved-sheet mean tends to `L(c)`; at finite radius
the result remains floating-point approximation.

Across all 270 configurations:

```text
admissible-product violations:                 0
worst refined admissible-product ratio:        0.985208366268
worst row:                                     degree 3, controlled near-regular
configurations with some individual q(c)>1:   94
largest refined individual q(c):               1.102921138165
product ratio on that degree-5 row:             0.120034457190
```

The controlled cubic shell ratios at angular perturbations `10^-2`,
`3*10^-3`, and `10^-3` are respectively

```text
0.962837923730, 0.976082003578, 0.985208366268.
```

This is evidence that `(AP)` is sharp at the coalescing near-regular boundary;
it is not an asymptotic proof.

## Individual-prefix filtration is false; compensated filtration survives

Order the admissible simple critical points so that

```text
s_j = |f(c_j)|^(1/n),     s_1 <= s_2 <= ... <= s_m.
```

The first version of this probe tested the strictly stronger filtration
statement

```text
product_(j=1)^k q(c_j) <= 1               (FP_k)
```

for every `1<=k<=m`. That statement is false. The original 269-row sweep had
accidentally omitted a pinned quartic already carried by
`MergeTopologyBoundRefutation.md` and the PIN arm of
`check_erdos1041_affine_normalised_moduli.py`. After similarity-scaling its
roots into the open unit disk, a refined replay gives

```text
log P_1:                         +0.003235364137
P_1=q(c_1):                       1.003240603577
relative gap s_2/s_1-1:          1.284579109750e-10
log P_2:                         -0.065587293793
full admissible product:          0.842015172452
```

Thus the least-scale factor can overspend, even though the almost-tied next
merger immediately repays the debt and the full target-deciding product stays
well below one. This is the same near-tie mechanism that killed the strong
minimum-critical inequality; ordering the factors does not repair it.
Reversing the filtration remains decisively wrong as well: 78 configurations
have a descending prefix above one.

The corrected induction object is therefore not prefix nonpositivity but a
**filtration-debt potential**. Crossing a critical scale may create positive
log debt; the proof must charge that debt to unresolved neighbouring mergers
and show that the debt is repaid before the corresponding merger block closes,
with no debt left at the terminal admissible threshold. Equivalently, one can
seek a non-tautological block decomposition whose block products are at most
one and whose blocks are determined by exact merge-tree data rather than a
numerical gap cutoff. The terminal statement is still `(AP)`. No such debt
potential or exact block rule is yet proved.

## Exact merge-subtree normalization

The truncated merge-tree product identity supplies a non-tautological exact
block coordinate. In the actual merge forest cut at level one, let

```text
beta_v = critical modulus at a merge node v,
k_v    = number of descendant roots,
r_v    = beta_v/beta_p(v),
```

where `p(v)` is the next admissible internal ancestor or the virtual level-one
cut node. In the generic binary case define

```text
h_v = (L(v)/2) / r_v^((k_v-1)/n).
```

`MergeTreeDiscriminantDichotomy.md` proves exactly

```text
product_(c in A) |f(c)| = product_v r_v^(k_v-1).       (MTD)
```

Therefore

```text
product_v h_v
  = product_(c in A) (L(c)/2) / product_(c in A)|f(c)|^(1/n)
  = product_(c in A) q(c).                             (MB1)
```

This is an exact equivalence, not numerical evidence. Multiple nodes are read
with critical multiplicity, or obtained by separating and coalescing their
incident edges.

For a merge node `v`, let `T_v` contain `v` and every internal descendant node
and put

```text
H_v = product_(u in T_v) h_u.                          (MB2)
```

If `b_v=beta_p(v)` is the parent/cut level, the restricted telescoping identity
also gives

```text
H_v = b_v^((k_v-1)/n) product_(u in T_v) q(u).         (MB3)
```

The new candidate is

```text
H_v <= 1 for every complete rooted admissible merger subtree.  (MS)
```

The maximal admissible subtrees partition `A` and have parent level one, so
multiplying `(MS)` over them gives `(AP)` exactly. Unlike the false individual
critical-scale prefixes, complete rooted subtrees are determined by exact
merge topology and carry their descendant slack with the parent overspend.

An independent descending-pair replay evaluated 1,252 admissible rooted
subtrees across the 270 configurations and found no `(MS)` violation. The
largest subtree product is `0.991355945247` on the controlled near-regular
cubic boundary. The individual node factors `h_v` are emphatically not bounded
by one: 210 exceed one across 178 configurations, with maximum
`7.117710142467`; the full product on that degree-six row is only
`0.007304366639`. On the pinned near-tie quartic, the largest subtree product is
`0.886974885971`, the largest node factor is `1.146593848942`, and the full
descending-pair product is `0.839962067769`. The numerical telescoping error is
at most `6.751e-16`. A separate fixed-seed 800-configuration stress sweep in
degrees `3..10` mixed random-disc, random-shell, near-regular, multi-cluster,
and near-collinear families. It recovered every merge tree, found no rooted
subtree violation, and pushed the largest subtree product to
`0.998957114261` on a near-regular cubic. This strengthens falsification
pressure near the expected equality boundary without proving `(MS)`.

Thus the concrete proof attack is a bottom-up subtree induction. A cherry node
is the base case. At a larger binary node, the exact obligation is

```text
h_v H_left H_right <= 1,                               (MS-step)
```

with missing internal children interpreted as factor one. Any proof that drops
`H_left H_right` and asks for `h_v<=1` is numerically false. No proof of `(MS)`
or its coupled induction step is yet known; the next section proves the cherry
base outside an explicit rapid-near-tie shell.

## A proved Bergman certificate for the cherry base

The base case is not wholly open. Let `n>=3`, let `v` be a simple cherry node,
and put

```text
beta = beta_v,       b = beta_p(v) (or the level-one cut),
r = beta/b,          h_v = (L(v)/2)/r^(1/n).
```

Thus `0<beta<b<=1`, after separating tied levels. The component born at
`beta` contains exactly two roots until level `b`.

> **Cherry certificate.** If
>
> ```text
> b^(2/n) log((1+r)/(1-r))
>     <= 2 (n-1)^(2/n) r^(2/n),                         (CB1)
> ```
>
> then `h_v<=1`, so the complete rooted-subtree inequality holds at this
> cherry.

*Proof.* Take regular levels `t` increasing to `b` inside the two-root
lifetime. `BergmanSegmentLengthBound.md` applies to the canonical descent arc
and gives

```text
L(v)^2 <= (2 Area(U_t)/pi) log((t+beta)/(t-beta)).       (CB2)
```

The component is proper, so the sharp exterior-fibre capacity gap from
`ExteriorBlaschkeFibreCapacityGap.md`, followed by Pólya's area--capacity
inequality, gives

```text
Area(U_t)/pi < t^(2/n) (1/(n-1))^(2/n).                 (CB3)
```

Letting `t` increase to `b` in `(CB2)`--`(CB3)` yields

```text
L(v)^2
 <= 2 b^(2/n) (n-1)^(-2/n) log((1+r)/(1-r)).           (CB4)
```

Under `(CB1)`, the right side is at most `4r^(2/n)`, exactly `h_v<=1`.
Separated simple configurations imply the general limiting statement by the
same coalescing argument used for the merge-tree identity. ∎

Since `b<=1`, there is also a ratio-only certificate. Let `rho_n` be the unique
root in `(0,1)` of

```text
artanh(rho_n) = (n-1)^(2/n) rho_n^(2/n).                (CB5)
```

Then every cherry with `r<=rho_n` satisfies `(CB1)`. Uniqueness follows because
`artanh(r)/r^(2/n)` is strictly increasing: its logarithmic derivative is
positive by `artanh(r)<r/(1-r^2)` and `2/n<1`. Numerically,

```text
n:       3        4        5        6        7        8        9       10
rho_n: .901782  .931809  .934748  .931557  .926412  .920654  .914820  .909143
```

The checker now distinguishes base from grafting. In the base 270
configurations, all 436 cherries satisfy the candidate; `(CB1)` rigorously
certifies 310 and leaves 126 rapid-near-tie cherries for new geometry. The
largest sampled cherry is `0.985775178280`, a controlled near-regular cubic.
In the separate 800-configuration stress sweep, all 1,259 cherries satisfy the
candidate; `(CB1)` certifies 1,079 and leaves 180. These counts are numerical
classification of the exact theorem's reach, not proof inside the remaining
shell. The same split records 816 base-corpus and 3,029 stress grafting nodes,
again with no sampled rooted-subtree violation.

Therefore the opening residual has sharpened. The cherry base is proved in the
bulk region `(CB1)`; only its rapid-near-tie complement remains. Independently,
the coupled grafting step remains open. A packet that asks for the undivided
base case without activating `(CB1)` is stale.

## Exact adaptive pruning: most near-tie cherries are grafting debt, not bases

There is a further logical sharpening. The universal rooted-subtree statement
`(MS)` is sufficient, but it is stronger than the exact parent consumer
`(AP)`: the parent only needs the product of all admissible node factors. In
particular an uncertified cherry does **not** have to be proved below one before
its admissible parent is treated.

Call a cherry **closed** when `(CB1)` certifies it and **open** otherwise. An
open cherry has one of two exact positions in the level-one merge forest:

1. its parent is another admissible merge node; then its factor is carried as
   unresolved multiplicative debt into that parent's block;
2. its parent is the virtual level-one cut; then it is a genuine terminal
   cherry and must be controlled without a later admissible merger.

This is not a new inequality. It is an exact pruning rule for proof search.
Indeed, in the first case the cherry and its parent occur in the same maximal
admissible subtree, so proving the product of the eventual open block (or the
whole maximal subtree) is enough. Requiring the cherry factor alone to be at
most one inserts an unnecessary intermediate lemma. Certified cherries may
still contribute their quantitative Bergman slack to the ancestor estimate;
"closed" does not mean replacing their factor by one.

The checker now records this distinction. Among the 126 cherries outside
`(CB1)` in the 270-configuration corpus, all 126 have an admissible parent and
zero meet the virtual cut. Among the 180 stress misses, 178 have an admissible
parent and only two meet the virtual cut; their sampled factors are
`0.853771268558` and `0.284608313037`, so the larger is still well below one.
Those two values remain floating-point evidence, not a theorem.

Thus "rapid-near-tie cherry complement plus grafting" still double-counts most
of the live work. The source-current residual is:

```text
terminal virtual-cut cherries outside (CB1), if any;
adaptive open blocks in which every internal uncertified cherry is retained
until an ancestor estimate closes its debt;
the global admissible product (AP), without requiring (MS) at every node.
```

The dominant obstruction is therefore coupled grafting/open-block closure.
Only the virtual-cut subcase remains a standalone cherry base.

## Exact charge-to-log bridge and its numerical failure

There is a direct exact comparison with `CriticalTreeLengthCharge.md`. Let `R`
be the minimum circumradius of the roots and write

```text
x_c = L(c)/(2R),        s_c = |f(c)|^(1/n).
```

Since `log x <= x-1`,

```text
sum_A log q(c)
  <= -sum_A (2R-L(c))/(2R) + sum_A log(R/s_c).       (CL)
```

Consequently the scale-compensated charge inequality

```text
sum_A (2R-L(c))/(2R) >= sum_A log(R/s_c)             (SC)
```

would imply `(AP)`. This is the cleanest first-order bridge from combined
charge to the logarithmic product, but it is not the missing theorem: 75 of
the 270 configurations violate `(SC)` numerically while still satisfying
`(AP)`. The strongest refined failure has margin `-3.157675412061` on the
degree-four two-cluster row 8, where the admissible product is nevertheless
only `0.001701013176`. The related arithmetic sufficient condition

```text
sum_A L(c) <= 2m * geometric_mean_A(s_c)
```

fails on five rows. The reason `(CL)` loses too much is visible on clustered
examples: a very short edge contributes a large negative `log x_c` but only a
bounded linear charge `1-x_c`. The nonlinear log gain, organized by the
critical-value filtration, is essential.

## Inadmissible-compensation probe

The exact firewall also records the conditional route

```text
global all-critical product plus product_(c notin A) q(c) >= 1
  implies (AP).
```

The new checker evaluates that proposed lower compensation factor whenever an
inadmissible critical point exists. Of the 270 configurations, 62 have a
nonempty inadmissible complement, and 59 of those have sampled complement
product below one. The strongest refined failure is

```text
degree:                                      9
family:                                      random-circle, seed-1041 row 0
inadmissible critical points:                2
product_(c notin A) q(c):                    0.202884030445
individual factors:                          0.246601040580, 0.822721712643
```

The pinned hard degree-nine row has five inadmissible critical points and
refined complement product `0.311698885969`. These are numerical falsifier
candidates, not exact polynomial counterexamples. They nevertheless make a
universal lower compensation theorem a poor proof target. The direct
admissible product `(AP)` is not affected, and the global all-critical product
conjecture is neither proved nor refuted by this computation.

## Decision-changing consequence

Four proof templates are numerically rejected:

```text
q(c) <= 1 for every admissible c
product_(j=1)^k q(c_j) <= 1 for every ascending critical-scale prefix
product_(c notin A) q(c) >= 1 for every polynomial
derive the log product from combined charge through log(x)<=x-1 alone
```

The factorwise statement fails on 94 configurations, the ascending-prefix
statement on the refined pinned quartic, the inadmissible lower compensation
on 59 of the 62 applicable configurations, and the linearized bridge on 75.
The admissible product can survive only through compensation *within the
admissible set*, and that compensation can cross an individual critical-value
threshold. `(MB1)--(MS-step)` now identify the strongest exact merger-block
attack: prove the complete rooted-subtree product while retaining descendant
slack. A charge argument can still contribute, but it must retain the nonlinear
logarithmic reward of already-short edges; the first-order aggregate `(SC)` and
the nodewise bound `h_v<=1` are too weak.

The finite survival does not prove `(AP)`, the merge-subtree theorem `(MS)`, a
more general merger-block/debt theorem, the
all-critical product conjecture, the componentwise combined-charge lemma, or
the parent problem. The prefix and complement rows are numerical falsifier
evidence, not exact polynomial counterexamples; the pinned prefix row is
nevertheless source-current, stable across independent continuation
instruments, and must be present in every future packet's hard-gate corpus.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_admissible_critical_arc_product.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_admissible_critical_arc_product.py --stress-subtrees-only
```

The checker uses IEEE-754 polynomial roots, Hungarian branch matching, and
polygonal arclength. Its assertions prevent accidental promotion: it requires
zero sampled full-product violations, requires the pinned ascending-prefix
falsifier to remain above one while its full product stays below one, and also
requires zero sampled complete-subtree violations while individual node factors
exceed one. It also requires the sampled factorwise, reverse-filtration,
linearized-charge, and inadmissible-compensation templates to fail.
