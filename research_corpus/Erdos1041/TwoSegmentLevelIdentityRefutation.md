# Erdős #1041: the proposed two-segment level identity is false

Status: **exact degree-seven refutation of `V_E = μ` and of `SPOKE≥1`**,
2026-08-24. This does **not** refute the level-one free-hub conjecture and does
not solve or refute Erdős #1041.

## The claim that fails

For a squarefree monic polynomial let

```text
μ = min_{f'(c)=0} |f(c)|
```

and let `V_E` be the least level attainable by two straight segments joining
distinct roots through a hub in their major-axis-two ellipse. Theorem 2 of
[TwoSegmentLevelIdentity.md](TwoSegmentLevelIdentity.md) proves `V_E ≥ μ`.
The same file measured equality to about `10^-6` and conjectured

```text
V_E = μ.                                                   (LI)
```

It also extracted the sharp necessary statement `SPOKE≥1`: at a least-critical
point, at least one critical-point-to-root segment must lie in `|f|≤μ`.

Both statements are false.

## Exact dyadic witness

Let `f(z)=∏_{j=0}^6(z-z_j)`, where the seven roots are the exact IEEE-754
dyadic complex numbers stored in
[the checker](scripts/check_erdos1041_two_segment_level_identity_refutation.py).
They are a small perturbation of a regular heptagon. Exact rational comparison
gives `|z_j|²<1` for every `j`, so all roots lie strictly in the unit disk.

Six disjoint disks of radius `10^-12` are centred at the pinned dyadic
approximations `d_0,…,d_5` in the checker. Expanding `f'` at `d_j`, the linear
term strictly dominates the constant term plus every Taylor term of order at
least two on the boundary of each disk. Rouché therefore puts exactly one zero
of `f'` in every disk. Since `deg f'=6`, these are all critical points.

Using the exact bound

```text
|f'(z)| < 7·3^6 = 5103
```

on the relevant unit-disk neighbourhood transfers the centre evaluations to
the whole disks. The first disk is the unique least-critical one. Its critical
value is

```text
μ = 0.81580484408495279102511630628927388…,
```

while the next is `0.8163950933409540163…`; this is not a selector tie.

For each of the seven roots the checker pins a dyadic `t_j∈(0,1)`. Exact
`Fraction` arithmetic gives

| root | `t_j` | centre squared gap `|f((1-t)d₀+t z_j)|²-|f(d₀)|²` | interval error |
|---:|---:|---:|---:|
| 0 | 0.450652 | `3.35036e-3` | `1.30e-8` |
| 1 | 0.514855 | `6.09452e-3` | `1.24e-8` |
| 2 | 0.465711 | `8.13599e-3` | `1.28e-8` |
| 3 | 0.095336 | `5.24583e-5` | `1.59e-8` |
| 4 | 0.077941 | `2.83325e-5` | `1.61e-8` |
| 5 | 0.460641 | `8.77604e-3` | `1.29e-8` |
| 6 | 0.503676 | `3.86841e-3` | `1.25e-8` |

Every exact gap dominates its interval error by at least three orders of
magnitude. Thus, for the actual least critical point `c*` inside the first
disk, **every one of the seven spokes `[c*,z_j]` leaves `|f|≤μ`**. The smallest
observed ratio is

```text
max_[c*,z_4] |f| / μ = 1.0000212851940088259438617973… .
```

No floating-point root or sampled segment maximum enters the verdict.

## Why this refutes the identity

Below `μ`, every lemniscate component contains exactly one root. At the unique
least critical point `c*`, two or more such components first merge. Therefore
any connected subset of `|f|≤μ` containing two distinct roots must contain
`c*`. In particular, if a two-arm set `[h,a]∪[h,b]` joined two roots at level
`μ`, then `c*` would lie on one arm. The subsegment from `c*` to that arm's root
would be a safe spoke, contradicting the seven certificates above.

Hence

```text
V_E > μ.
```

The subsegment implication is Lean-checked in
[TwoSegmentLevelIdentityRefutation.lean](TwoSegmentLevelIdentityRefutation.lean).
The polynomial topology and Rouché/interval certificate remain ordinary
mathematics plus exact rational replay, not a fully formalized complex-analysis
development.

## What survives

The useful free-hub mechanism is not refuted. On this witness `μ≈0.816`, so
there is substantial room between the failed identity level and the target
level `1`; direct optimisation still finds a two-segment hub far below one.
Thus the implication

```text
V_E ≤ 1  =>  Erdős #1041
```

survives untouched. What is retired is the proposed factorisation
`V_E=μ≤R^n`: Fekete still bounds `μ`, but `μ` is not the exact cost of the
two-segment mechanism.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_two_segment_level_identity_refutation.py
```
