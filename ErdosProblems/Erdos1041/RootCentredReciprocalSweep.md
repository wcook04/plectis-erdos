# Erdős 1041: the reciprocal sweep can be centred at a root

Status: one theorem with an ordinary proof, two corollaries, and an explicit
construction shape. Current through 2026-08-27; the exact replay below confirms
the recorded numerical checks. This does not
prove Erdős #1041 and does not remove the degree-linear budget that
[ReciprocalSweepBoundaryLab.md](ReciprocalSweepBoundaryLab.md) identifies as the
obstruction. It answers the *precondition* of that note's first live transfer
question.

## The question this addresses

[ReciprocalSweepBoundaryLab.md](ReciprocalSweepBoundaryLab.md) assimilates
Pendyala (arXiv:2606.19178) and closes with three live transfer questions, the
first being:

> Can reciprocal sweeping be centered or normalized at a root while retaining a
> degree-free length charge?

Pendyala's construction is centred at `0` for one specific reason: with
`g(z) = prod_j (1 - conj(a_j) z)` we have `g(0) = 1` exactly, so `0` lies on the
level set `{|g| = 1}`, and `|f| <= |g|` in the disk puts that level set inside
`{|f| <= 1}`. Centring anywhere else needs a point `p` with `|g(p)| <= 1`, since
the sweep through `p` runs on `{|g| = |g(p)|}` and containment needs
`|f| <= |g| = |g(p)| <= 1`.

So the precondition for centring at a root is: **some root satisfies
`|g(a_k)| <= 1`.**

## Source and attribution boundary

The external source used here is Venkata Siddharth Pendyala, *Shortest paths in
polynomial lemniscate sublevel sets and a problem of Erdős*, arXiv:2606.19178v1
(17 June 2026). Its primary PDF was downloaded from
<https://arxiv.org/pdf/2606.19178v1>; the arXiv API record is
<https://export.arxiv.org/api/query?id_list=2606.19178>. The downloaded
34-page PDF had SHA-256
`d7902a8bc37d2aad6dea52dffbbbaaf7ff23954ece5a0c4cbab108f58df4e6df`.

Pendyala's introduction explicitly separates the marked-point-to-boundary
problem from the Erdős--Herzog--Piranian root-to-root problem (printed pp. 2--3,
extracted PDF lines 51--78). Section 9 supplies the reflected polynomial,
factor identity, and containment used here (printed pp. 27--28, extracted lines
1462--1492), and its Crofton/nodal argument ends in the linear upper bound
Proposition 9.7 (printed pp. 30--31, extracted lines 1631--1705).

Those locators support Pendyala's reciprocal-sweep containment and linear
marked-point bound only. The root-centred resultant identity (RS), its
power-sum and Gram corollaries, the extremal-family separation proposition,
and the transfer boundary in this note are repository-authored mathematics.
The note claims no novelty for (RS), and the priority search named below is
still required before any originality statement.

## The identity

Two observations that are not recorded in this directory. First, the Pendyala
comparison function is the reciprocal adjoint: `g = f*`, where
`f*(z) = z^n conj(f(1/conj(z)))`, and consequently

```text
f = g * h,      h = f / g = prod_j phi_{a_j},     phi_a(z) = (z - a)/(1 - conj(a) z),
```

so `h` is exactly the **finite Blaschke product on the unit disk with the same
zeros as `f`**, and `|f| <= |g|` is just `|h| <= 1`. Blaschke products are
Möbius-covariant where polynomials are not, which is the structural reason a
root-centred normalisation is available at all. (The corpus already uses a
Blaschke product for *component* uniformisation in
[CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md); that is a different
object — `B = f o phi` on one lemniscate component — not this global one.)

Second, for monic `f` the relevant product is a resultant:

```text
prod_k |g(a_k)|  =  |Res(f, f*)|  =  prod_{j,k} |1 - conj(a_j) a_k|.
```

Splitting diagonal from off-diagonal, and writing `s_j = 1 - |a_j|^2`,

```text
prod_{j,k} |1 - conj(a_j) a_k|
    =  prod_j s_j  *  prod_{i<j} |1 - conj(a_i) a_j|^2.        (P)
```

There is also a Gram form. Let `K` be the Szegő kernel Gram matrix,
`K_{jk} = <k_{a_j}, k_{a_k}> = 1/(1 - conj(a_j) a_k)`, positive definite. The
Cauchy determinant gives

```text
prod_{j,k} (1 - conj(a_j) a_k)  =  prod_{i<j} |a_i - a_j|^2 / det K,     (C)
```

and expanding `det K` as a product of squared distances to the span of the
earlier kernels, with the extremal function `B_{j-1} * G` supplying
`dist^2 = |B_{j-1}(a_j)|^2 / s_j`,

```text
det K  =  prod_{i<j} |phi_{a_i}(a_j)|^2  /  prod_j s_j,
```

which reproduces (P) from (C) exactly. Identity (C) was checked numerically to
relative error `4.3e-13` over degrees 2 to 6.

## The theorem

> **Theorem (RS).** Let `a_1, …, a_n` lie in the open unit disk, `f = prod_j
> (z - a_j)`, and `f*` its reciprocal adjoint. Write `p_m = sum_j a_j^m` for the
> power sums. Then
>
> ```text
> |Res(f, f*)|  =  prod_{j,k} |1 - conj(a_j) a_k|  =  exp( - sum_{m>=1} |p_m|^2 / m )  <=  1,
> ```
>
> with equality if and only if `p_m = 0` for every `m`, i.e. `f = z^n`.

*Proof.* Since `|conj(a_j) a_k| < 1`, the principal branch gives
`-log(1 - conj(a_j) a_k) = sum_{m>=1} (conj(a_j) a_k)^m / m`, so
`-log|1 - conj(a_j) a_k| = sum_{m>=1} Re((conj(a_j) a_k)^m) / m`. Summing over
all `n^2` ordered pairs and exchanging the (absolutely convergent) sums,

```text
- sum_{j,k} log|1 - conj(a_j) a_k|
   = sum_{m>=1} (1/m) Re[ (sum_j conj(a_j)^m) (sum_k a_k^m) ]
   = sum_{m>=1} |p_m|^2 / m,
```

because the bracket is `conj(p_m) p_m = |p_m|^2`, already real and nonnegative.
Absolute convergence holds since `|p_m| <= n rho^m` with `rho = max_j |a_j| < 1`.
Exponentiating gives the identity, and nonnegativity of every term gives `<= 1`.
Equality forces `p_m = 0` for all `m`; by Newton's identities `p_1 = … = p_n = 0`
already forces every elementary symmetric function to vanish, hence `f = z^n`. ∎

Two immediate consequences.

**Corollary (the precondition).** `min_k |g(a_k)| <= |Res(f,f*)|^{1/n}
= exp( - (1/n) sum_{m>=1} |p_m|^2 / m ) <= 1`, so **at least one root admits a
centred reciprocal sweep**, with an explicit deficit measured by the power-sum
energy of the root multiset.

**Corollary (Gram form).** By (C), `det K >= prod_{i<j} |a_i - a_j|^2`: the
Szegő kernel Gram determinant dominates the Vandermonde, with the same equality
case.

*Sanity of the equality case and a worked family.* For the regular `n`-gon of
radius `r`, `p_m = n r^m` when `n | m` and `0` otherwise, so
`sum_m |p_m|^2/m = n sum_k r^{2nk}/k = -n log(1 - r^{2n})` and the theorem
predicts `(1 - r^{2n})^n`. The direct product gives the same, since
`prod_{d=0}^{n-1}(1 - x omega^d) = 1 - x^n` with `x = r^2`.

*Numerical confirmation.* The identity was checked to worst relative error
`4.4e-14` over degrees 1 through 10 in three families (uniform, boundary
clustered, regular gon at `r = 0.99`), with the series truncated against an
explicit tail bound `n^2 rho^{2M} / (M(1 - rho^2))`. A first pass truncated on a
*small term* rather than a tail bound and reported spurious errors up to `5.3`;
that is an artifact of the stopping rule, since for a regular gon `p_m` vanishes
unless `n | m` and a run of zero terms triggers an early break. Recorded because
it would otherwise look like a refutation of the theorem.

The earlier evidence run remains as a secondary receipt: 28000 configurations
over degrees 2 to 10, maximum observed product `0.984926`, maximum observed
`min_k |g(a_k)|` `0.973336`, zero configurations where every root exceeded one.

## Priority check required before any claim of novelty

`Res(f, f*)` for a Schur-stable `f` is a classical object: it is the setting of
the Schur–Cohn criterion, and the positivity of the associated Schur–Cohn /
Bezoutian matrix is exactly the stability test. **Conjecture (RS) is very
plausibly a known normalisation in that literature**, and this note claims no
novelty for it. Nothing here should be described as new until a priority search
on Schur–Cohn, the Bezoutian of `f` and `f*`, and Szegő-kernel Gram determinants
has been run. This directory has already been bitten once by claiming a result
that a 2006 paper subsumed.

## The construction shape, and why it does not close #1041

Granting (RS), pick a root `a_k` with `|g(a_k)| <= 1`. The level set
`{|g| = |g(a_k)|}` is a nodal set of the harmonic function
`log|g| - log|g(a_k)|` through `a_k`, lies inside `{|f| <= 1}` (strictly, for
interior roots), and is a real algebraic curve of degree at most `2n`, so
Crofton bounds its length by `2 pi n`.

For a root-to-root path, order two roots by their sweep level, say
`|g(a_1)| <= |g(a_2)| <= 1`, and concatenate

1. the gradient trajectory of `log|g|` from `a_1` up to level `|g(a_2)|`, and
2. an arc of the level set `{|g| = |g(a_2)|}` to `a_2`.

Both pieces lie in `{|g| <= |g(a_2)|} ⊆ {|f| <= 1}`. This is a genuine
root-to-root construction inside the target lemniscate, and it is the
"root-attachment" shape that
[ReciprocalSweepBoundaryLab.md](ReciprocalSweepBoundaryLab.md) asks for in its
second transfer question.

**It does not close the problem, and the reason is the one that note already
gives.** The Crofton budget is linear in the degree: the level arc is bounded by
`2 pi n`, not by 2, and nothing here charges that linear budget down to a single
pair. The gradient leg is unbounded by this argument as well. So what is added
is the availability of a root-centred sweep and an explicit two-piece path, not
a length theorem. The second transfer question — charge the `2 pi n` nodal
length to `n` root attachments so one pair costs at most two — remains exactly
as open as before.

## Mechanism boundary: on the extremal family the sweep separates the roots

The construction above is not merely unproved at the length step. On this
problem's extremal family it is **exactly tight and offers no slack**, for a
structural reason worth recording.

> **Proposition.** Let `f = z^n - r^n` with `0 < r < 1`. Then `g = f* = 1 - r^n z^n`,
> every root has the same sweep level `|g(a_k)| = 1 - r^{2n}`, and
> `{|g| < 1} ∩ D` has **exactly `n` connected components, each containing exactly
> one root**. Hence no root-to-root path exists inside `{|g| < 1}`; any such path
> inside `{|g| <= 1}` must pass through `z = 0`, the unique point where the
> components meet, and the shortest one is the pair of radial spokes, of total
> length exactly `2r`.

*Proof.* For `a_j = r omega^j` we have
`g(z) = prod_j (1 - r omega^{-j} z) = 1 - (rz)^n`, using
`prod_{j<n}(1 - c omega^j) = 1 - c^n`. At `z = a_k`,
`g(a_k) = 1 - r^{2n} omega^{kn} = 1 - r^{2n}`, the same for every `k`. Put
`w = r^n z^n`. Then `|g| < 1` is `|1 - w| < 1`, the open disk of radius 1 centred
at 1. That disk omits `w = 0` and is simply connected without winding around the
origin, so its preimage under the `n`-to-1 map `z -> r^n z^n` is `n` disjoint
sheets, one per `n`-th root branch, each containing one `a_k`. The point `z = 0`
maps to `w = 0`, which lies exactly on the boundary `|1 - w| = 1`, so the sheets
touch only there. On the radial segment `z = t omega^k`, `t in [0,r]`, one has
`g = 1 - r^n t^n` and `|g| = 1 - r^n t^n <= 1` with equality only at `t = 0`. ∎

*Confirmed numerically:* `g = 1 - r^n z^n` to `5e-16`; component counts `3` and
`5` inside the disk at `n = 3, 5` and `r = 0.9, 0.99`, with the roots in
distinct components in every case; and `max |g| = 1.000000000` on the radial
spoke, attained only at the origin.

**What this means for transfer question 2.** The `2 pi n` Crofton budget is not
the only obstacle. On the extremal family the sweep's own sublevel set separates
the roots, so there is nothing to charge: the sweep recovers exactly the radial
spokes and exactly the constant `2r`, no better and no worse. Any use of the
reciprocal sweep for #1041 must therefore supply its own mechanism for crossing
between components at level exactly one — which on this family is the single
point `z = 0` — rather than expecting a length charge to produce the crossing.
That the sweep reproduces `2r` exactly on the family where the constant 2 is
sharp is a consistency check in its favour; it is not slack.

## Claim boundary

Proved, by ordinary mathematics: Theorem (RS) and both corollaries. The proof is
a power-series expansion plus Newton's identities and uses nothing about #1041.

Verified numerically: the power-sum identity to `4.4e-14` over degrees 1 to 10;
identity (C) to `4.05e-14`; the algebraic derivation of (P) from (C) via the
Szegő Gram factorisation. The containment `{|g| <= 1} ⊆ {|f| <= 1}` is
Pendyala's, not new here.

Not established: any length bound below `2 pi n`, any degree-free charge, any
claim of novelty for (RS) ahead of a Schur–Cohn priority search, and any
progress on the constant 2. Erdős #1041 remains open.

## Current replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_root_centred_sweep.py
```

The 2026-08-27 replay checks 28,000 configurations, with maximum Cauchy
identity relative error `4.052e-14`, maximum power-sum identity relative error
`1.185e-12`, and zero configurations in which every root exceeds one. These
are numerical confirmations of the ordinary identities above, not a formal
proof or a degree-free path bound.
