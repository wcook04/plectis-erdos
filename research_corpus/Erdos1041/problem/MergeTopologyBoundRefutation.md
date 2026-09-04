# Erdős 1041: the merge-topology bounds are refuted, one of them by exact algebra

Status: three refutations, one of them a closed-form identity. 2026-08-23. Erdős
#1041 remains open, and the weak statement `L <= 2R` is untouched by everything
here.

## What was tested and why

[CriticalBudgetLab.md](CriticalBudgetLab.md) records that **any branch-length
bound whose right-hand side is a symmetric function of the root positions
relative to `c` is dead**, because such a quantity cannot see which root the
branch actually reaches: split by landing, the ratio `L/|f(c)|^{1/n}` has median
`1.000` on nearest-root landings and median `2.523`, max `5.95`, elsewhere. A
working bound "has to see the merge topology".

Three candidates that do see it were tested.

* **(A)** the *strong* statement of
  [MinimumCriticalNewtonHubLab.md](MinimumCriticalNewtonHubLab.md):
  `L(c*) <= 2 rho` with `rho = T*^{1/n}`, which implies the weak `L <= 2R`
  because `rho <= R`.
* **(B)** `L_branch(c -> a) <= n |f(c)| / |f'(a)|`, which depends on the endpoint
  root through `f'(a)` and so is not symmetric. Equality holds on `z^n - r^n`.
* **(C)** its summed form at the minimal hub,
  `n mu (1/|f'(a)| + 1/|f'(b)|) <= 2R`, which together with (B) would close
  #1041.

All three are refuted.

## (C) is refuted by an exact identity, and is unbounded

Take the centre-plus-polygon family

```text
f(z) = z (z^{n-1} - r^{n-1}),      f'(z) = n z^{n-1} - r^{n-1}.
```

Its critical points are `c = r n^{-1/(n-1)} omega^k`, every critical value has the
same modulus, and the roots are `0` and `r omega^k`:

```text
mu = r^n (n-1) / n^{n/(n-1)},   R = r,
|f'(0)| = r^{n-1},              |f'(r omega^k)| = (n-1) r^{n-1}.
```

The branches at such a hub reach the centre root and one outer root, so

```text
ratio_C = n mu (1/|f'(0)| + 1/|f'(r omega)|) / (2R)
        = n * r^n (n-1) / n^{n/(n-1)} * (1/r^{n-1})(n/(n-1)) / (2r)
        = n^2 / n^{n/(n-1)} / 2
```

that is

> **ratio_C = n^((n-2)/(n-1)) / 2,   independent of `r`.**

`1.259921` at `n = 4`, `3.871318` at `n = 10`, `13.340007` at `n = 30`, and
asymptotically `~ n/2`. The identity was checked against direct computation for
`n = 4 … 30` and `r in {0.95, 0.999}` with maximum gap `4.8e-14`, and derived
independently by hand.

So (C) does not merely fail, it fails by an unbounded factor. It is also refuted
at degree 3 (adversarial `1.0162361`), on the corpus's own bit-exact hex
witnesses at 60 digits (`1.0003157968451788809` at degree 6,
`1.0001375773407660463` at degree 9, under both `R` conventions), and it is not a
symmetry artifact: breaking the `(n-1)`-fold symmetry with `eps = 0.01` moves the
degree-8 value only from `2.096481` to `2.074570`.

The mechanism is first-order. `ratio_C - 1` grows **linearly** in the
perturbation away from the regular gon (about `1.9x` per doubling of `eps`) while
the Fekete deficit `1 - mu/R^n` that would have to protect it grows
**superlinearly** (about `2.5x`). So (C) fails at first order in *every*
neighbourhood of the extremal family.

## (B) is refuted at every degree and appears unbounded in the degree

Equality on `z^n - r^n` was confirmed to `1e-16` at `n = 2,3,4,6,8`, and on the
Cassini family through the full numeric pipeline. A near-polygon scan then gives,
as the maximum over hubs,

```text
1.069 (n=3), 1.151, 1.258, 1.272, 1.416, 1.471, 1.438, 1.557, 1.613, 1.628,
1.721, 1.733 (n=14)
```

monotone with no ceiling. **Recorded as apparently unbounded in the degree, not
as a bound** — no supremum is claimed.

A deterministic degree-3 witness is stored in the receipt as hex literals:
branch to root 0 has `L = 1.074449026`, `|f'(a)| = 2.979243263`,
`n|f(c)| = 2.993972916`, ratio `1.069162986`, endpoint error `1.5e-13`.

**The `c*`-restricted form (B\*), which is the one the (B)+(C) route actually
needs, also fails** — at degree 3, ratio `1.006770882`, endpoint error `1.0e-14`,
and robustly: 12 of 12 perturbations at `1e-4` still violate.

## (A), the strong statement, is refuted at degree four — but only just

Worst adversarial value `1.004246913` at `n = 4`, with `mu = 0.9670225538632438`
at 50 digits, `L = 1.9917262723`, `2 rho = 1.9833033547`. The pair and length are
identical across six tolerances from `1e-8` to `1e-13`, endpoint error `1.7e-14`,
and 50-digit arithmetic confirms the hub is strictly the minimiser.

**Honest caveats, which matter here.** The two smallest critical values agree to
`2.30e-9` relative; at the runner-up hub the ratio is `0.9608`. The violation
dies under a `1e-3` perturbation (0 of 12), and every violation found has
critical-value separation below about `1e-6`. Under the corpus's own tie-tolerant
selector the `1e-9` window is *just* exceeded so the same hub is chosen and the
refutation stands — widen that window slightly and it does not.

This is exactly what [MinimumCriticalNewtonHubLab.md](MinimumCriticalNewtonHubLab.md)
anticipated: "a crossing above one kills only the strong statement; the
scale-normalized `2R` completion remains the actual solution route."

## A structural deduction of mine that was wrong

While setting this probe up I argued that (B) at the minimal hub, combined with
the recorded relation `|f'(z_a)| = n (T*)^{(n-1)/n}`, would force
`L_branch <= T*^{1/n}` — the per-branch symmetric bound already refuted — and
that (B) and the derivative relation therefore could not both hold. **That
deduction is invalid.** The relation is an *equality on `z^n - r^n`*, not a
general lower bound; the proved bound is `T*^{(n-1)/n}/4` and the tightest
observed is about `1.94 T*^{(n-1)/n}`, both far below `n T*^{(n-1)/n}`. The exact
statement is `ratio_B = (symmetric ratio) x |f'(a)| / (n T^{(n-1)/n})`, and over
1946 branches that weight has median `1.028`, min `0.0013`, max `32.6`. On all
197 symmetric-bound violators the weight is **below 1** (max `0.9834`, median
`0.370`), so (B) is strictly *weaker* than the refuted symmetric bound exactly
where that bound fails. No contradiction existed, and (C) and (B) had to be
killed on their own terms, which they now are.

A useful by-product of that check: **196 of the 197 symmetric-bound violations
sit at non-minimal hubs.** At minimum-critical hubs there is 1 violation in 480
branches (worst `1.0068`); at non-minimal hubs, 196 in 1466 (worst `1.5784`), and
the worst offenders all have `|f(c)| ~ 0.99+`. Hub selection is doing more work
than the bound's form.

## Instrument discipline, and one false counterexample caught

The primary instrument is the corpus's `descending_pair` at `rtol 1e-12 /
atol 1e-14`; `descend_branches` was not used, since its own docstring records
that it mistracks. Two further independent instruments were added: an
RK4-predictor / Newton-projection tracker with an anti-hop gate, and an *upward*
continuation from each root to the hub that decides branch identity without
touching the saddle expansion (100x to 8900x separation on reported witnesses).

**Mistrack discipline: 24 of 166 hubs (14.5%) were refused for cross-instrument
disagreement, and 137 of 176 configurations (77.8%) refused overall.** All
discarded, none reported.

**One false counterexample was generated and caught.** At a loose search
tolerance (`rtol 1e-8`) a degree-6 configuration read `A = 1.0446` and a degree-9
read `C = 3.94`; both evaporated at `rtol 1e-12` (`A -> 0.5462`). Cause: the true
minimum-critical hub failed the gates and a higher hub was silently substituted
as `c*`. Fixed by refusing any configuration whose gated star hub is not the
global critical-value minimiser. This is the corpus's own recorded failure mode
reproducing itself, and it is why loose-tolerance numbers from the first run are
not reported here.

Hard validation reproduced from the stored hex witnesses: degree 6 gives
`1.763941902238086` against the recorded `1.763942` (gap `9.8e-8`), degree 9
gives `1.5459951467596067` against `1.545995` (gap `1.5e-7`).

## Claim boundary

Refuted: (A), (B), (B\*) and (C) as stated. (C)'s failure is an exact identity,
verified by hand and to `4.8e-14` numerically, and is unbounded in the degree.

Not refuted, and not claimed either way: the weak statement `L <= 2R`, which
stayed below 1 at every witness here **including the (A) violator**, where
`L/(2R) = 0.998437`. Erdős #1041 remains open.

Receipt: [`scripts/check_erdos1041_merge_topology_bound.py`](scripts/check_erdos1041_merge_topology_bound.py).
