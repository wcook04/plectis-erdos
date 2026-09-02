# Erdős 1049: the step-1 window divisor exists, and it is source-supported

## Analytic consumer

`QAperyTailDenominatorLab.md` retired the fixed-tail divisor target: several
primes divide a long initial block of the primitive q-Apéry denominator
coordinates and then vanish for one block whose length is the order of `3/2`
modulo the prime. It then named the next theorem-sized target, whose step 1 is

> analyze the modulo-prime block dynamics and supply, for cofinally many starts
> `s`, a moving divisor across the exact window of width `3s² + 5s + 3`.

and stated what computation is for here:

> Computation should now be used only to falsify a proposed formula for step 1 or
> a proposed uniform inequality for step 3. Extending the row cutoff alone would
> not change the mathematical status.

This probe does exactly that. It does not extend the row cutoff hunting for new
tail primes; it evaluates the step-1 predicate itself, which had never been
evaluated.

## Probe

For each start `s`, take the exact window `[s, s + 3s² + 5s + 3]`, compute the
gcd of the denominator coordinates across it, and factor it. Regression anchor:
the row generator reproduces the lab's `211 | B_j` for `5 ≤ j ≤ 255`.

Falsifier: a start whose window gcd is 1. If such starts are cofinal, step 1 as
stated is false and the target must change again.

## Exact result: the predicate holds

677 rows built; starts `s = 0 … 14`, so windows reaching index 675.

| s | window width | window gcd factors |
|---|---|---|
| 3 | 45 | 19 |
| 5 | 103 | 211 |
| 7 | 185 | 71 · 211 |
| 9 | 291 | 71 · 211 · 1009 |
| 11 | 421 | 71 · 211 · 331 · 1009 |
| 13 | 575 | 211 · 331 · 1009 · 29927 |
| 14 | 661 | 211 · 331 · 463 · 1009 · 29927 |

Only `s = 0, 1, 2, 4` have gcd 1, and they are the earliest starts. **Every tested
start in the upper half of this finite range carries a window divisor**.  This
supports the predicate on the tested range, but does not establish cofinality.

## Source and attribution boundary

The antecedent q-Apéry construction is Tewodros Amdeberhan and Doron Zeilberger,
*q-Apéry Irrationality Proofs by q-WZ pairs*, Adv. Appl. Math. 20 (1998),
275–283. The downloaded primary source is retained locally at
`annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery/source.pdf`, with the
editable source at `source.tex`. Source TeX lines 31–50 define the same
q-harmonic Lambert value, lines 72–95 give the q-WZ form and summed sequences,
lines 97–119 give the shared recurrence, lines 188–194 show the source's
q-product denominator-clearing estimate, and lines 196–207 state its decay lemma
and integer-base theorem.

The primary paper does **not** state the rational specialization at `3/2`, the
window width `3s² + 5s + 3`, the first-appearance notion of
“source-supported,” the seven displayed primes, or the finite `252 of 259`
certificate. Those are repository-authored exact computations and definitions.
The local q-Apéry row generator and the `QAperyTailDenominator.lean` consumer
provide the formal/local interfaces; neither promotes the finite window data to
cofinality, a source theorem, asymptotic decay, or irrationality of Erdős #1049.

## The source-support law is exact

"Source-supported" is a statement about **first appearance** — a prime inherited
from an earlier start is not expected to divide `3^s − 2^s` at the later one.
Testing first appearances:

| first start s | new prime | 3^s − 2^s | divides |
|---|---|---|---|
| 3 | 19 | 19 | yes |
| 5 | 211 | 211 | yes |
| 7 | 71 | 2059 = 29·71 | yes |
| 9 | 1009 | 19171 = 19·1009 | yes |
| 11 | 331 | 175099 = 23²·331 | yes |
| 13 | 29927 | 1586131 = 53·29927 | yes |
| 14 | 463 | 4766585 = 463·10295 | yes |

**Seven out of seven.** Every newly appearing prime divides `3^s − 2^s` exactly at
its first start. That is a sharp arithmetic law, and it confirms the phenomenon
is inherited from rational specialisation of the q-recurrence rather than from
generic rank-two lattice geometry — as the earlier lab suspected but could only
observe on the tail-gcd table.

## What this decides

The finite probe does not falsify the step-1 predicate: every tested upper-half
window has a divisor, and the displayed new primes are source-supported in the
finite first-appearance sense.  It does not decide the cofinal statement or
establish that step 1 is no longer the weak link.

The proof obligation is now specific: show that for every large `s` the prime
`p_s | 3^s − 2^s` selected at first appearance has no loss block meeting
`[s, s + 3s² + 5s + 3]`. Since a loss block has length `ord_p(3/2)` and the
window has width `3s² + 5s + 3`, this is a statement comparing the multiplicative
order of `3/2` modulo a prime divisor of `3^s − 2^s` against a quadratic window —
concrete, and unlike a fixed-tail divisor theorem it is not already refuted by
its own data.

## CORRECTION (2026-08-24): the residual named above is false as stated

An earlier version of `HarmonicZeroBlockLawLab.md` proposed the following
loss-block law on its generic/unit class:

> `p | B_j` for every `j ≥ d = ord_p(3/2)`, except on the whole blocks
> `[dK, dK+d−1]` with `K ∈ J_p = { K : p | numerator(H_K) }`,

the Eswarathasan–Levine harmonic zeros. Two consequences bear directly on this
note.

**The proof obligation in the section above is refuted.** "For every large `s` the prime
`p_s | 3^s − 2^s` selected at first appearance has no loss block meeting the
window" fails at `s = 2, 4, 6, 8, 10, 12, 18`. For `s = 2, 4, 6` the primitive
prime is small enough that the Wolstenholme block `K = p−1` lands inside the
width-`3s+6` window; for `s = 8, 10, 12, 18` the prime is 97, 11, 61, 577 and
carries a **sporadic** harmonic zero (`11 ∈ J_97`, `3 ∈ J_11` from `H_3 = 11/6`,
`10 ∈ J_61`, `24 ∈ J_577`).

**The "seven out of seven" table is a statement about the successes only.** It
lists the starts where a new prime entered the window gcd — `3,5,7,9,11,13,14` —
so it could not see that at `s = 6, 8, 10, 12` the window divisor is *inherited*
(211, entering at `s = 5`), not source-supported at `s`. The finding "only
`s = 0,1,2,4` have gcd 1" is exactly reproduced there by two independent methods,
and is unaffected.

What survives, and is stronger than what this note claimed: the corrected
source-supported predicate is certified without factoring for **every start from
19 to 260** (252 of 259 tested), the seven exceptions all being `≤ 18`.

## SUPERSEDED (2026-08-24): an earlier unconditional fixed-prime reading

This historical section's earlier claim that `5 | B_j` for every `j ≥ 50` is
**not an unconditional theorem**.  The corrected source route retains the
conditional strategy: using the finite classical set `J_5 = {4, 20, 24}`, the
weighted transfer would force that tail if the all-level q-Apéry
monodromy/5-adic-continuity premise holds.  The premise is certified only at
`N = 1, 2, 3` and the finite replay range; the finite checks do not establish
the tail or cofinality.

Accordingly, the `252 of 259` source-supported certificate remains a finite
arithmetic result, while the moving-prime cofinality statement and the fixed-prime
tail are both open at their respective proof boundaries.  See
[`FixedPrimeInfiniteTailProof.md`](FixedPrimeInfiniteTailProof.md) and
[`CasoratianBlockLawProof.md`](CasoratianBlockLawProof.md) for the conditional
argument and its exact limitations.

## Claim boundary

Finite computation over starts `s ≤ 14`, bounded by exact rational arithmetic on
the q-Apéry rows (677 rows, coordinates near 10⁶ bits at the top). It establishes
the predicate and the first-appearance law in that range; it proves neither
cofinality nor irrationality, and #1049 at base `3/2` remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_window_divisor_supply.py --max-start 14
```
