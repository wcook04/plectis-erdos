# Erdős 68: the Kovač–Tao obstruction is two-sided, and nearly tight

## Claim boundary

Exact rational arithmetic over `4 ≤ n ≤ 34` with a truncated, generously bounded
tail band. It witnesses the Kovač–Tao phenomenon on our own sequence and
measures its cost. It proves nothing about `S`, and Erdős #68 remains open.

## What was recorded, and what was never run

Negative result 9 is the sharpest obstruction in the packet:

> Kovač–Tao's interval construction is a sharp growth-only obstruction: there is
> already a rational reciprocal series after **decreasing** each denominator
> `n!−1` by at most `n²+1`. Consequently no argument stable under all one-sided
> quadratic perturbations can prove the unperturbed series irrational.

The packet records the existence statement and its consequence. It never ran the
construction, so it records nothing about how much of the perturbation budget a
rational near `S` actually costs, or whether the one-sidedness is load-bearing.

## The construction, run

Greedy exact reconstruction: fix a rational target `t`, and at each `n` choose
`b_n` in the allowed window so the residual stays inside the achievable tail band
`[Σ 1/b_k^max, Σ 1/b_k^min]`. If that succeeds at every step then
`Σ 1/b_n = t` exactly.

**Downward window** `b_n ∈ [n!−n²−2, n!−1]` — terms larger, sums above `S`.

| target gap | first `n` perturbed | perturbed steps | peak use of window |
|---|---|---|---|
| `1e−20` | 14 | 21/31 | `448/485` at `n=22` — **92%** |
| `1e−30` | 18 | 17/31 | `812/901` at `n=30` — **90%** |
| `1e−40` | 22 | 13/31 | `1142/1157` at `n=34` — **99%** |
| `1e−50` | 25 | 10/31 | `671/962` at `n=31` — 70% |

All four feasible to `n = 34`. Two readings. The **first perturbed index scales
linearly with the target's decimal gap** (14, 18, 22, 25), so a closer target
simply defers the first correction. And the **peak consumes most of the allowed
window** — up to 99%. Kovač–Tao's `n²+1` is close to the smallest window that
works; there is very little slack in the recorded theorem.

## A hypothesis that looked strong, and is refuted

Every downward-window `b_n` satisfies `b_n ≤ n!−1`, hence `1/b_n ≥ 1/(n!−1)`
termwise, hence `Σ 1/b_n ≥ S` — with equality **only** for our own sequence.
Checked termwise for `4 ≤ n ≤ 60`. So in the recorded family, `S` is the unique
minimum.

That looked like a lever. A perturbation argument cannot see extremality, so an
argument that uses "`S` is the endpoint" would automatically not be
perturbation-stable, and would therefore sit outside what negative result 9
excludes.

**It is refuted.** Running the same construction with the **upward window**
`b_n ∈ [n!−1, n!+n²+2]` — terms smaller, sums *below* `S` — reaches rationals
just as easily:

| target gap | first `n` perturbed | peak use of window |
|---|---|---|
| `1e−20` | 14 | `434/443` at `n=21` — **98%** |
| `1e−30` | 18 | `1150/1158` at `n=34` — **99%** |
| `1e−40` | 22 | `735/786` at `n=28` — **94%** |
| `1e−50` | 26 | `1014/1026` at `n=32` — **99%** |

All four feasible to `n = 34`. So **`S` is interior to the two-sided quadratic
family**, and the one-sidedness of the recorded statement is about how Kovač–Tao
phrased their theorem, not a property of `S`. The extremality lever does not
exist.

The refuted hypothesis is kept here because it is the point: the obvious way to
escape negative result 9 is the one that does not work.

## What this changes

**Negative result 9 should be strengthened, not weakened.** As recorded it
excludes arguments stable under one-sided quadratic perturbation. The measurement
shows rationals of this family sit arbitrarily close to `S` **on both sides**, so
the excluded class is larger: anything stable under two-sided quadratic
perturbation fails.

Concretely, a successful proof may not use any of:

* growth or size of `n!−1`, or any bound that survives moving it by `O(n²)`;
* the position of `S` relative to nearby reciprocal series;
* any topological or extremal property of `S` within a perturbation family.

What remains available is unchanged and is the thing to use: the **exact**
recurrence `a_{n+1} = (n+1)a_n + n`, which no perturbed `b_n` satisfies, and the
arithmetic that recurrence generates — the residue coupling
`A_m = 1 − {Σ_n (m! mod (n!−1))/(n!−1)}`, the strict-successor carries, and the
factorial-residue distribution.

## A note on the achievable set

It is not an interval. The target `t = 13/10` lies inside `[S, S+Δ]` with
`Δ = 0.12561…`, yet the greedy is infeasible at `n = 4`: the window `[6, 23]`
gives `1/b` values spaced by up to `1/6 − 1/7 = 0.0238`, far coarser than the
remaining tail range `≈ 0.0124`. The achievable set is Cantor-like at small `n`
and only becomes interval-like once the window's granularity beats the tail. Any
argument that treats the perturbation family as an interval is wrong at the
bottom.

## Replay

```sh
./repo-python formal_math/probes/erdos68_perturbation_saturation.py
```

Exit code `0` iff all eight runs — four target gaps in each direction — are
feasible to `n = 34`.
