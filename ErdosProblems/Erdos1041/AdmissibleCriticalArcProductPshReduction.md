# Erdős 1041: the surviving admissible-product inequality is psh cellwise

Date: 2026-08-30.  Status: ordinary exact reduction, with a deterministic
degree-five numerical regression in
`scripts/check_erdos1041_admissible_product_psh.py`.  This note does **not**
prove the admissible-product inequality or unrestricted Erdős 1041.

## 1. Why this is the right functional

For a monic polynomial `f_a(z)=prod_j(z-a_j)` with simple roots and a simple
critical point `c_k(a)`, put

```text
w_k(a) = f_a(c_k(a)),
L_k(a) = length of the two canonical descending inverse-ray arms at c_k(a),
q_k(a) = L_k(a)/(2 |w_k(a)|^(1/n)).
```

On a ray-separated configuration let

```text
A(a) = {k : |w_k(a)| < 1},
Q_A(a) = product_(k in A) q_k(a).                         (APF)
```

`AdmissibleCriticalArcProductLab.md` proves that

```text
Q_A(a) <= 1                                                (AP)
```

is target-deciding: it forces an admissible hub with `L_k<=2`, and the
source-current generic-closure wiring then proves the parent theorem.  The
arithmetic strengthenings `(AQ)` and `(CAQ)` are false, but `(AP)` itself is
unrefuted.  The logarithm is also the functional compatible with the
holomorphic arm coordinates; this is the distinction that survives the
aggregate counterexamples.

## 2. Wall-free cells

Let `U` be a connected open set in root-configuration space on which:

1. the roots and critical points are simple and every `w_k` is nonzero;
2. the set `A={k:|w_k|<1}` is fixed;
3. for each `k in A`, the segment `[0,w_k]` contains no other critical value,
   and the two descending arms have fixed continuation combinatorics.

Critical points can be labelled holomorphically after shrinking `U`.  As in
`SeparatrixAggregateReduction.md`, resolve the quadratic branch at a hub by
the parameter `u`:

```text
f_a(Z_k^+-(u;a)) = w_k(a)(1-u^2),
Z_k^+-(0;a)      = c_k(a),                  0 <= u <= 1.
```

The two signs denote the two local square-root germs.  Fixed wall-free
combinatorics continues them to the two root endpoints.  On every relatively
compact subcell, the maps

```text
G_k^+-(a) = d Z_k^+-(*;a)/du
```

are holomorphic with values in `L^1([0,1])`, and

```text
L_k(a) = ||G_k^+(a)||_1 + ||G_k^-(a)||_1.                 (BN)
```

The `u^2` chart removes the apparent square-root singularity at the hub; at
the root endpoints, simplicity gives ordinary holomorphic continuation.

## 3. The psh theorem

Stable result id: `admissible_critical_arc_product_cellwise_log_psh_reduction`.

> **Theorem (cellwise logarithmic psh).**  In the setup above,
>
> ```text
> a |-> log Q_A(a)
>      = sum_(k in A) [log L_k(a) - log 2 - (1/n)log|w_k(a)|]     (PSH)
> ```
>
> is plurisubharmonic on `U`.  Consequently `Q_A` itself is
> plurisubharmonic.

### Proof

Give `L^1([0,1]) direct-sum_1 L^1([0,1])` its sum norm and set

```text
G_k=(G_k^+,G_k^-).
```

Then `(BN)` says `L_k=||G_k||`.  If `G` is a holomorphic map into a complex
Banach space, `log||G||` is plurisubharmonic (with value `-infinity` at a
zero): on every complex line this follows by applying Hahn--Banach to the
Banach-valued power series, or equivalently by taking the locally bounded
upper envelope of the subharmonic functions `log|ell(G)|` over norm-one
linear functionals `ell`.  Here `G_k` never vanishes, since its arms have
distinct root endpoints, so `log L_k` is finite and plurisubharmonic.

The critical value `w_k` is holomorphic and nonvanishing on `U`; hence
`log|w_k|` is pluriharmonic.  Subtracting `(1/n)log|w_k|` preserves
plurisubharmonicity.  Finite sums preserve it, proving `(PSH)`.  Finally,
`exp` is convex and increasing, so `Q_A=exp(log Q_A)` is
plurisubharmonic.  `[]`

### Similarity check

For `g(z)=s^(-n)f(t+s z)`, `s != 0`, arm lengths scale by `1/|s|` and
critical-value moduli by `1/|s|^n`, so every fixed-label factor `q_k` is
unchanged.  Hence `Q_A` is unchanged whenever the same labelled set `A`
remains below the cut.  (A dilation can move a hub through `|w_k|=1`, so the
actual admissible set is not claimed to be scale-invariant across that wall.)
The checker replays the fixed-cell invariance numerically.

## 4. Target-deciding terminal-stratum reduction

Fix a degree and the closed root polydisk.  On the closure of any relatively
compact wall-free cell, a nonconstant `Q_A` cannot attain a strict maximum in
the cell interior.  Therefore any sequence approaching the cell supremum must
approach at least one of the following terminal events:

```text
root boundary:          |a_j| = 1;
admissibility wall:     |w_k| = 1;
saddle-connection wall: w_j lies on [0,w_k] and its lift meets c_j;
degenerate stratum:     a root or critical point collides.
```

This is a target-deciding reduction because the functional being pushed is
exactly `(AP)`, not the refuted arm sum.  In particular, for degree five the
interior of every generic combinatorial cell is removed from the proof
obligation: a degree-five `(AP)` certificate need only cover the root-boundary,
admissibility-wall, saddle-connection, and collision strata, together with
upper-semicontinuity when the relevant cell is approached.  Iterating the
maximum principle in root coordinates either pushes another root to the unit
circle or meets one of those walls.

This does **not** say that the only terminal configuration is the regular
pentagon.  The rotated-gon pocket and saddle walls remain real obligations.
What changes is dimensional and logical: no generic interior maximizer of the
surviving product can exist.

The first saddle-wall obligation now has an exact scalar consumer. On a
simple two-saddle wall, write `A,B` for the lower outgoing arm lengths and
`X` for the upper stem plus its unaffected arm. Then

```text
(A+B)(X+min(A,B)) <= (A+B+X)^2/2.
```

After critical-level normalization, the two wall factors are therefore at
most one under the sufficient condition

```text
A+B+X <= 2 sqrt(2) |w_low w_high|^(1/(2n)).
```

That total-length threshold is now refuted as a universal polynomial-wall
claim by `SymmetricTwoLevelWallFamily.md`. The exact surviving condition keeps
the compression slack:

```text
(A+B+X)^2-X^2-(A+B)|A-B|
  <= 8 |w_low w_high|^(1/n).
```

The same companion evaluates and proves `(AP)` on an all-even-degree two-level
wall family. General walls still require this shape-sensitive estimate or a
complete rooted-subtree argument.

## 5. Why the wall qualification is load-bearing

At a saddle connection an arm through `c_k` can split at another critical
point and exchange which outgoing branch reaches its endpoint.  The
corresponding `L^1`-valued germ need not continue holomorphically through the
real wall.  Likewise `A` changes at `|w_k|=1`.  The theorem is therefore
cellwise; it does not assert a global psh extension across either kind of
wall.

This is also why the earlier psh theorem for the additive aggregate did not
settle the problem: besides targeting a false inequality, it still retained
the wall strata.  Here the same analytic mechanism is applied to a surviving,
target-deciding multiplicative functional, and the precise residual is the
terminal-stratum certificate rather than an unspecified interior search.

## 6. Computation used as a falsifier

The checker evaluates `log Q_A` on four deterministic holomorphic disks of
quintic root configurations.  Each disk has 20 boundary samples, four fixed
admissible hubs, root-room at least `0.104`, critical-value separation at least
`0.0458`, and normalized saddle-wall clearance at least `0.0719`.  Numerical
descending-arm continuation gives the sub-mean defects

```text
mean_boundary(log Q_A) - log Q_A(center)
  = 1.10e-5, 9.13e-6, 2.22e-5, 6.82e-6,
```

all with the predicted sign.  The values are regression evidence for the
analytic theorem, not its proof.  Their role was discriminating: disks that
cross the near-regular saddle walls can show the opposite numerical sign, so
the experiment forced the exact cellwise scope instead of an invalid global
claim.

The same checker also runs a bounded terminal-stratum falsifier search with
all five roots on the unit circle (broad angular rows plus six near-pentagon
scales).  Its only logical question is whether `Q_A>1` occurs; survival is
recorded as computation, never promoted to a terminal-stratum proof.

## Claim boundary

Proved here: `(PSH)`, similarity invariance, and the resulting per-cell
terminal-stratum reduction.  Imported: the holomorphic arm chart and the
target sufficiency of `(AP)`.  Measured: the four quintic sub-mean rows.

Not proved: `(AP)` on any unclosed terminal stratum; upper-semicontinuity
through saddle walls; a degree-five finite certificate; `(COVER)`, PGLS,
FP--GM, the shape-sensitive general wall certificate of
`SaddleWallPairCompression.md`, or unrestricted Erdős 1041. No
literature-priority claim is made for the
Banach-valued psh lemma; the new point in this corpus is its application to the
surviving normalized admissible product.
