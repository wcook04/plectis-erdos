# Erdős 1041: Claim L is false away from ties — the merging pair is not the nearest pair

Status: one refutation by stored float witnesses with an auditable
classification diagnostic, one new search instrument, and a survival
measurement for the statement that actually matters. 2026-08-28.
**Erdős #1041 remains open**, conjecture (C) remains open, and nothing below
weakens either; what falls is a hoped-for closure of (C)'s metric floor.

## 1. What is refuted

[CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) §8.1 isolates:

> **Claim L.** At the minimum-critical hub `c*`, the two merging roots are the
> two roots nearest `c*`.

and records: a proof of Claim L would close the metric floor of (C) — the
bound `d_a + d_b ≤ 2ρ` for the **merging** pair — via the proved nearest-pair
theorem `exact_results::critical_pair_metric_scale`, and would close gap 1 of
[FirstMergeReductionState.md](FirstMergeReductionState.md) at the same time.
The file's own evidence was `512/512` agreement across tie-guarded sweeps,
with the sole violation sitting at a critical-value tie, and it diagnosed why
the search was weak: *"the objective is flat: it equals 1 identically on the
whole set where the merging pair is the nearest pair... Anyone testing Claim L
seriously should first build a proxy with a gradient."*

That instrument now exists, and it refutes Claim L **away from ties**.

## 2. The instrument

For a configuration with min-critical hub `c*`, merging set `S` (by upward
branch continuation from every root along the ray of `f(c*)`), distances
`d_k = |c* − z_k|` and `ρ = μ^{1/n}`, minimise the signed gap

```text
gap  =  ( min_{k ∉ S} d_k  −  max_{k ∈ S} d_k ) / ρ
```

by stochastic coordinate descent, rejecting any configuration whose two
smallest critical moduli are closer than the tie guard. `gap < 0` is exactly a
Claim L violation, the objective is continuous in the roots away from
merge-set switches, and — unlike the violation ratio — it has a gradient
toward the boundary of the good set.

## 3. The witnesses

Three stored configurations; receipt
[scripts/check_erdos1041_claim_l_refutation.py](scripts/check_erdos1041_claim_l_refutation.py)
re-derives every number below from the roots alone.

| witness | tie separation | merging set | nearest pair | gap / ρ | floor `(d_a+d_b)/2ρ` |
|---|---|---|---|---|---|
| degree 6 | `1.0010` | `{0, 5}` | `{1, 5}` | `−0.181` | `0.594` |
| degree 10 | `1.0010` | `{0, 6}` | `{1, 6}` | `−0.067` | `0.500` |
| degree 8 | `1.0500` | `{1, 7}` | `{5, 7}` | `−0.036` | `0.313` |

At the degree-6 witness the non-merging root sits at `d = 0.3292` while a
merging root sits at `d = 0.4469` — a `36%` violation, not a marginal one.
The degree-8 witness matters most: its second critical modulus is a full `5%`
above `μ`, which is the guard level at which the corpus's own diagnostic
retest table reported `1.0000000` (no violation) at every degree. The flat
objective could not see these configurations; the gradient instrument walks
straight to them.

**Classification is audited, not assumed.** The receipt traces every root's
branch at three shrink levels `1e-10, 1e-13, 1e-15`: a merging root's endpoint
distance to `c*` falls at the saddle square-root rate (e.g. degree 10:
`2.9e-6 → 9.2e-8 → 9.6e-9`), while every non-merging root's endpoint is
stable at a macroscopic distance (`≥ 0.087`) across all three levels. The
merging set has exactly two members at every witness, so the merge is well
posed and the guard rules out the ambiguous-hub class of
`negative_results` entry 28's caveat.

**Evidence class.** Float witnesses with margins `10²–10³` times the
classifier resolution; no exact rational certificate is claimed. Whoever wants
one should rationalise the degree-6 witness — its margins survive rounding at
`1e-6` — and intervalise the continuation.

## 4. What survives, precisely

* **The metric floor of (C) is untouched and now measured where it is
  genuinely at risk.** `(d_a + d_b)/2ρ ≤ 0.594` at every witness. A dedicated
  climb *maximising* the merging-pair sum inside the newly accessible
  `merging ≠ nearest` region reaches `0.7512` (degree 6, tie separation
  `1.0034`, gap `−0.24`) — above every value previously recorded for a
  merging-differs configuration, still `25%` below the budget. The floor for
  the merging pair is an **open producer in its own right** now, no longer
  closable through Claim L.
* **Scope of the violations so far.** Violations are on file at tie
  separations up to `1.05`; a search at guard `1.2` (same instrument, same
  budget) found none, best gap `+0.114`. Whether merging ≠ nearest can occur
  at large tie separation is open; the violation set may genuinely
  concentrate near the tie stratum, which would itself be usable structure.
* **The nearest-pair theorem** (`critical_pair_metric_scale`, Lean-checked) is
  untouched — it is about the nearest pair, and it is true.
* **Conjecture (C)** is untouched: its equality family and all §6–§7
  measurements of `CapacityGeodesicConjecture.md` stand.
* **Gap 1 of `FirstMergeReductionState.md` is now witnessed, not heuristic.**
  That file's line "no tie-free configuration with merging ≠ nearest is on
  file" is superseded by this note.

## 5. Decision-changing consequences

1. **The metric floor needs a merging-pair proof.** The route
   "prove Claim L, inherit the nearest-pair theorem" is dead. Any proof of
   (C)'s floor must handle the pair the lobes actually select, whose
   characterisation is the weighted touch-level order, not the Euclidean
   order. The proof sketch recorded in `CapacityGeodesicConjecture.md` §8.1
   (normalise `∏ d_k = ρ^n`, critical equation, monotone one-variable bound)
   does not transfer as stated: its first step orders by Euclidean distance.
2. **The structural remark that blocked the obvious counterexample shape is
   correctly scoped.** "A root close to `c*` forces another root close to
   `c*`" (from `Σ 1/(c*−z_k) = 0`) remains true — the witnesses do not have a
   lone stray near root; they have a near root whose **lobe** is fed too
   slowly to reach `c*` first. The corpus's heuristic lobe-size model
   (`t/|f'(z_k)|`) is the right intuition and now has certified instances.
3. **Search-methodology row.** This is the second time in this directory that
   a flat objective certified a false safety margin (`negative_results` entry
   19 is the general warning). The reusable rule: *when the good set is a
   level set of the objective, the objective cannot find its boundary; build
   the signed distance to the boundary instead.*

## 6. Claim boundary

The three witnesses and every number in §3 are float measurements re-derived
by the receipt from the stored roots; the refutation's logical form is "there
exist tie-guarded configurations where the merging set differs from the
nearest pair", and the margins are far above instrument resolution. No exact
arithmetic certificate is claimed. Claim L's failure does **not** refute (C),
the nearest-pair theorem, or any landed exact result; it removes one proposed
proof route for (C)'s metric floor. The tracked open question
`cap_quick_erdos1041_decide_merging_pair_nearest_pa_20d69b8f9d6d` is answered:
**negative**. Erdős #1041 remains open.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_claim_l_refutation.py
```
