# Erdős 1041: the harmonic majorant is refuted at degree two

Status: one new exact identity, one exact elimination at the minimal degree, and
a separation that says where the recorded majorant is lossy. 2026-08-24.
Erdős #1041 remains open; nothing below claims otherwise.

## 1. The route, and why it looked right

[RootCentredReciprocalSweep.md](RootCentredReciprocalSweep.md) records
`f = f* · B` with `B` the Blaschke product carrying the same zeros, so `|B| < 1`
strictly in the open disk and

```text
Omega  :=  { z in D : |f*(z)| <= 1 }   is contained in   { |f| < 1 }.
```

Containment inside `Omega` is therefore **free**. What makes `Omega` attractive is
that `f*` has its zeros at `1/conj(a_j)`, outside the closed disk, so

```text
G  :=  log|f*|  =  sum_j log|1 - conj(a_j) z|  =  - sum_{m>=1} Re( conj(p_m) z^m ) / m
```

is **harmonic** on a neighbourhood of the closed disk, with `G(0) = 0` and
`G = log|f|` on the unit circle: `G` is the harmonic extension of `log|f|` from the
boundary, and `G(0) = 0` is Jensen for a monic `f` with roots in the disk. So
`Omega` is a **nodal set**, not a lemniscate — the logarithmic singularities at
the roots are gone, and the whole problem would sit inside the negativity set of
an explicit harmonic function.

Combined with the free length budget of
[TruncatedSpokeReduction.md](TruncatedSpokeReduction.md), the candidate was:

> **(RS-frac).** There are distinct roots `a, b` and `t in (0,1]` with `G <= 0` on
> `[t a, a]`, on `[t b, b]` and on `[t a, t b]`.

Its path `a -> t a -> t b -> b` has length
`(1-t)(|a| + |b|) + t|a - b| <= |a| + |b| < 2` by the triangle inequality, for
**every** `t`. So RS-frac would give Erdős #1041 with no length obligation and no
singular set.

## 2. A new exact identity: the one-parameter form of Theorem (RS)

> **Proposition.** For `a_1, …, a_n` in the open unit disk and every `t in [0,1]`,
>
> ```text
> sum_k G(t a_k)  =  - sum_{m>=1} (t^m / m) |p_m|^2   <=  0.
> ```

*Proof.* `- sum_{j,k} log|1 - conj(a_j)(t a_k)| = sum_{m>=1} (1/m) Re[ (sum_j conj(a_j)^m)(t^m sum_k a_k^m) ]
= sum_m (t^m/m) |p_m|^2`, the interchange being justified by `|p_m| <= n rho^m`
with `rho = max_j |a_j| < 1`. ∎

At `t = 1` this is RootCentredReciprocalSweep.md's Theorem (RS). The
one-parameter family is what a truncated path needs, because that path visits the
**scaled** root set `t·{a_k}`.

## 3. The refutation, exact, at the minimal degree

RS-frac needs `G <= 0` on the closed arm `[t a, a]`, and that arm contains its own
endpoint. So it needs **two** roots with `|f*(a_k)| <= 1`. The identity supplies
exactly one — RootCentredReciprocalSweep.md's Corollary — and that is **sharp**.

**Witness.** `n = 2`, roots `3/10` and `-9/10`, both real and in the open unit
disk. Every quantity is rational and every comparison is a comparison of
integers:

```text
|f*( 3/10)|  =  (1 - 9/100)(1 + 27/100)   =  11557/10000  >  1
|f*(-9/10)|  =  (1 - 81/100)(1 + 27/100)  =   2413/10000  <  1
product                                    =  27887041/10^8  <=  1   (Theorem RS)
```

`11557 > 10000` is the whole refutation. Exactly one root admits a centred sweep,
so no pair of arms exists and **RS-frac is false**. Degree two is minimal, since
the statement is vacuous at degree one.

Erdős #1041 is untouched at that configuration, and easily: the chord `[3/10, -9/10]`
has `max |f| = 0.36` and length `1.2`.

**Adversarial confirmation.** Minimising the number of roots with `|f*(a_k)| <= 1`
returns `1` at every degree from 2 to 7, then `2` at 8 through 11 and `3` at 12 —
so the count is not bounded below by two at any small degree, and what grows with
degree is the count, not the guarantee.

## 4. Where the majorant is lossy, and it is not the hard regime

The mechanism is one line: **`|f(a_k)| = 0` always, but `|f*(a_k)|` need not be at
most one.** The majorant `|f| <= |f*|` throws away exactly the Blaschke factor,
which is what vanishes at the roots — so it is lossy precisely at the points the
path has to reach.

The separation is sharp in an unexpected direction. RS-frac is **feasible at every
recorded hard witness**, and by a wide margin where the true problem is hardest:

| witness | `n` | max entry fraction | `V` = best `max\|f*\|` | verdict |
|---|---|---|---|---|
| degree-3 two-segment witness | 3 | `0.262097` | `0.945931643` | feasible |
| cubic `z³−(99/100)³` | 3 | `0.000000` | `1.000000000` | feasible |
| degree-5 origin-spoke lab | 5 | `0.542954` | `0.004774300` | feasible |
| near-Fekete quintic | 5 | `0.089457` | `0.999997338` | feasible |
| degree-6 `QC = infinity` | 6 | `0.226628` | `0.999951902` | feasible |
| degree-9 `QC = infinity` | 9 | `0.349475` | `0.999946109` | feasible |
| regular `n`-gon, `r = 0.999`, `n = 3,4,5,6,8` | | `0.000000` | `1.000000000` | feasible |

At the two `QC = infinity` witnesses the harmonic majorant costs almost nothing:
`0.999952` and `0.999946` against `0.999951` and `0.999942` for the true
lemniscate. On the regular `n`-gon it is exactly `1`, attained in the limit
`t -> 0` where the crossing chord degenerates to the origin and `G(0) = 0` — the
boundary case of the whole mechanism.

**So the majorant fails where the problem is easy and holds where the problem is
hard.** The refuting configuration has mixed moduli (`0.3`, `0.9`) and a safe
chord; the near-Fekete and `QC = infinity` configurations, which defeat every
recorded path family, are comfortably inside `Omega`. A route cannot be selected
by its behaviour on the recorded hard witnesses alone.

## 5. What survives

[TruncatedSpokeReduction.md](TruncatedSpokeReduction.md)'s Form A-cut is stated
over the **true** lemniscate `{|f| < 1}` and is untouched: `|f(a_k)| = 0` at every
root, so the arms always reach their endpoints. The elimination here is of the
majorant, not of the truncated-spoke family.

Also untouched, and worth stating as the reason: any route that replaces `{|f| < 1}`
by a **zero-free** majorant must fail at the roots, because the roots are exactly
where `f` vanishes and the majorant does not. That is a structural bar on the
whole class, not a property of this particular `f*`.

## 6. Claim boundary

Proved here: the Proposition of §2 and the refutation of §3, the latter in exact
rational arithmetic with integer comparisons. Measured: the feasibility table of
§4 and the adversarial counts of §3. Nothing is retracted;
RootCentredReciprocalSweep.md's Theorem (RS) and its Corollary both stand — what
is new is that the Corollary is **sharp**, so no two-root strengthening exists.

Erdős #1041 is open.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_harmonic_majorant.py refutation
python3 research_corpus/Erdos1041/scripts/check_erdos1041_harmonic_majorant.py identity
python3 research_corpus/Erdos1041/scripts/check_erdos1041_harmonic_majorant.py coverage
python3 research_corpus/Erdos1041/scripts/check_erdos1041_harmonic_majorant.py precondition --max-degree 12
```
