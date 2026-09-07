# Erdős 68: the assumption every summable target rests on, tested

## Claim boundary

Finite range, `13 ≤ m ≤ 22000`. Independence confirmed on a finite stream is not
independence. The marginal line in §4 is reported unresolved, not claimed. Erdős
#68 remains open.

## 1. The untested step

Every summable target on the frontier gets its shape the same way:

* the zero-branch cylinder is `D_m = 0` together with `A_m ≤ R_m`, width
  `O(m^{−2})` — see `RationalCylinderMarginLab.md`;
* the no-consecutive-failure target has `P(fail at m and m+1) ≈ 1/m²` — see
  `PredecessorGapRecursionScanLab.md`.

Both multiply two `1/m` events **as if the digit at `m` and the digit at `m+1`
were independent in their extreme tails**, then apply Borel–Cantelli to the
convergent sum. That step is the whole reason to prefer these targets over the
divergent `1/m` window.

`FactorialDigitLawLab.md` measures the marginal law (uniform, KS `√n·D = 0.619`
against 1.95 at the 0.1% level) and the lag-one correlation of the normalised
digit (`+0.00080`, `z = 0.18`). **Neither tests the joint behaviour in the
tails**, which is the only place the heuristic is used. A correlation near zero is
perfectly compatible with strong clustering of rare events — correlation is a
second-moment statistic and the targets live in the far tail.

If extremes clustered, the `1/m²` arithmetic would be wrong and the summable
targets worth less than the frontier believes. If they repelled, the targets would
be easier. Nobody had looked.

## 2. Getting the null right

`r_m = (D_m + 1)/m` takes values `k/m` for `k = 0…m−1`, so

```
P(r_m < thr) = ⌈thr·m⌉ / m ,
```

which **exceeds** `thr` whenever `thr·m` is not an integer, badly so at small `m`.
Testing against a naive `thr·n` manufactures a spurious excess — at `thr = 0.01`
over `m ≤ 22000` the naive null is `219.9` and the correct discrete null is
`223.8`. This lab uses the discrete probability throughout.

## 3. The result: consecutive extremes are independent

Consecutive-pair counts against the discrete null, `m ≤ 22000`, both tails:

| threshold | tail size | pairs observed | expected | `z` |
|---|---|---|---|---|
| 0.5 | 10910 | 5461 | 5496.8 | −0.56 |
| 0.2 | 4339 | 876 | 879.5 | −0.12 |
| 0.1 | 2215 | 229 | 220.6 | +0.57 |
| 0.05 | 1105 | 52 | 55.3 | −0.45 |
| 0.02 | 469 | 8 | 9.0 | −0.32 |
| 0.01 | 267 | 5 | 2.3 | +1.76 |

High tail over the same ladder: `+0.35`, `−1.35`, `+0.54` at `0.1 / 0.05 / 0.01`.
A rerun at `m ≤ 6000` gives worst gated `|z| = 1.68`.

**No clustering, no repulsion, in either tail, at every threshold with enough
expected pairs to gate on.** The independence step the frontier's `1/m²`
arithmetic depends on is supported where it is actually used.

That is the useful output: not new evidence that `S` is irrational, but
confirmation that the *reason* the summable targets are worth preferring is not
an artefact.

## 4. One line that does not resolve, stated as such

The **marginal** low tail runs high at the tightest threshold. At `thr = 0.01`:
`267` observed against a discrete null of `223.8`, `z = +2.90`; restricted to
`m ≥ 1000` it is `256` against `211.5`, `z = +3.07`. It reproduces at
`m ≤ 6000` (`80` against `63.2`, `z = +2.13`). It is not a small-`m`
discretisation artefact — the correction only moves the null from `219.9` to
`223.8` — and it is not mirrored in the high tail.

It is **not** claimed, for two reasons.

*No coherent shape.* Decomposing by exact digit value over `k ∈ [−1, 23]`, the
cells are `−0.91, +0.56, +1.30, +0.56, +0.56, +0.93, +3.14, −0.17, +0.93, +2.77,
+1.30, +0.56, −0.17, −1.25, …` — two isolated cells (`k = 5`, `k = 8`) carry it,
with `k = 12` and `k = 16` running low. An arithmetic bias would show a shape:
monotone, periodic, or concentrated on a residue class. This shows none. The
aggregate over `k ∈ [−1,23]` is `212` against `182`, `z = +2.23`.

*Multiplicity.* Roughly eighteen correlated statistics were computed across
thresholds, strata and tails; a maximum `|z|` near `3` is close to what that
ladder produces on its own.

**Predeclared replication.** Extend the stream past `m = 22000` and recompute the
`thr = 0.01` marginal for `m ≥ 1000` only. If `z` stays near `+3` on genuinely new
indices it is real and the digit's far-left tail is not uniform, which would
matter — the zero branch lives in exactly that tail. If it decays toward zero it
was noise. This lab does not run that extension and does not pre-judge it.

## Replay

```sh
./repo-python formal_math/probes/erdos68_extreme_digit_independence.py               # m <= 6000
./repo-python formal_math/probes/erdos68_extreme_digit_independence.py --max-m 22000 # ~5 min
```

Exit code `0` iff no gated consecutive-pair `z` exceeds `3` in absolute value.
