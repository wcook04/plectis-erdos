# Erdős 68: the predecessor-gap certificate fires for 98% of m

## Analytic consumer

`cofinal_tailfree_predecessor_gap_threshold` is one of the few producers in the
corpus stated as a **pure integer inequality**, and Lean proves that cofinally
many certificates imply irrationality outright:

> for every cutoff `B` there is `m > B` with
> `((m+2)m! − 2)·v_m ≤ m²(m!−1)·u_m`,

where `Q_m = (m−1)!·Σ_{n=2}^{m−1} 1/(n!−1)`, `v_m = den(Q_m)` and
`u_m = (⌊Q_m⌋+1)v_m − num(Q_m)`. Lean also proves `1 ≤ u_m ≤ v_m`,
`gcd(u_m,v_m)=1`, `Δ_m = u_m/v_m`, and the exact equivalence with
`1 + 1/(m!−1) + 2/m ≤ m·u_m/v_m`.

## Reading the certificate

From the definition, `u_m/v_m = ⌊Q_m⌋ + 1 − Q_m = 1 − {Q_m}`. So the certificate
fires exactly when

`{Q_m} ≤ 1 − 1/m − 2/m² − 1/(m(m!−1))`.

It is a statement about the fractional part of one explicit rational. If `{Q_m}`
behaved like a uniform variable the certificate would fail with probability about
`1/m`, so the expected number of failures up to `M` is `Σ_{m≤M} 1/m ≈ log M`.

**It had never been evaluated.** The packet records no computational coverage for
this producer.

## Exact result

Computing `Q_m` in exact rational arithmetic and testing the literal integer
inequality (not the reduced form) for `m = 3 … 210`:

- **204 of 208 certificates fire — a rate of 0.9808.**
- Exactly **four** failures, at `m = 5, 9, 23, 60`.
- Expected failures under uniformity: **4.427**. Observed/expected = **0.904**.
- **No failure at all for `m = 61 … 210`.**

The failure count matches the uniform prediction to within 10%, and the failures
thin out exactly as `1/m` demands.

## What this decides

`{Q_m}` shows **no arithmetic bias against the certificate**. The producer's event
is generic, not delicate: the certificate holds for the overwhelming majority of
`m`, and since the producer needs only *one* `m` above each cutoff, cofinality is
supported by a very large margin in everything computed.

The missing analytic input is therefore an **equidistribution statement for
`{Q_m}`** — that the fractional part of `(m−1)!·Σ_{n<m}1/(n!−1)` is not pushed
into the top `1/m` of the unit interval for all large `m`. It is not a new
arithmetic mechanism, and it is not a sharper bound on any of the factorial-gap
quantities.

This matters because it separates two readings of the residual that the packet
could not distinguish: the certificate is not "hard to satisfy and needs a
cleverer construction", it is "satisfied almost always and needs a
non-concentration theorem".

## Claim boundary

Finite computation over `m ≤ 210`, bounded by the cost of exact rational
arithmetic on denominators that grow like `Π(n!−1)`. It establishes the fire rate
and its agreement with uniformity; it does not prove cofinality, and Erdős #68
remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos68_predecessor_gap_threshold.py --max-m 210
```
