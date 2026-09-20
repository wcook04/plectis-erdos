<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Choices, contraction and rational membership

Erdős #257 at base 2 is equivalent to a finite-rejection statement: every
rational number that is not a finite sum of the weights `1/(2^n - 1)` is
rejected by the greedy rule at some finite index. Exact computation shows that
12,218 of the 19,653 reduced fractions with denominator at most 200 survive 60
indices, after which the remaining gaps occupy less than `2^-60` of the
interval. For the hosts of odd, squarefree and non-multiples-of-3 exponents it
excludes every rational of denominator at most 36 that is not a finite sum.
The share of survivors at a fixed depth is forced by equidistribution of
fractions and carries no information about membership; the late exclusions,
which occur at exactly the rate the gap measures predict, are the informative
data.

This investigation started from reading the eight short papers together and
belongs to no single problem. Its sharpest instance sits inside Erdős #257, and
its framing draws on #243, #249, #251 and #1049.

**Status.** Ordinary reasoning and exact rational computation. Nothing here is
checked in Lean. No prior-art search has been carried out. Membership of any
specific rational in the infinite achievement set remains open. The counts
below are reproducible with the script in this directory.

## The question

Several of the papers study a series whose value is coded digit by digit: at
each index there is a set of admissible choices, and each step contracts the
remaining tail by a known factor. Two rates can then be compared, the number of
available choices per index and the rate of contraction.

> When do the number of available choices and the rate of contraction explain
> the geometry of the attainable values, and what additional arithmetic
> information determines their rational points?

The geometry part has classical answers under explicit hypotheses. The
rational-points part is arithmetic and is where the open problems sit. This
investigation keeps the two apart.

## What the #257 short paper already establishes

Write `w_n = 1/(2^n - 1)`, let `R_N` be the sum of `w_n` over `n > N`, and let
`𝒜` be the set of all subseries sums. The
[short paper](../../../docs/papers/full-text/erdos-257-mersenne-support-subseries.md#unique-coding-and-arithmetic-membership)
proves the following.

- `2^-N < R_N < w_N` for every `N >= 1`. Every weight exceeds its tail, so a
  represented value has exactly one selector and the greedy rule recovers it.
- By Hornich's theorem, as proved by Nitecki, `𝒜` is a Cantor set of Lebesgue
  measure `lim 2^N R_N = 1`. It sits inside `[0, E]` with
  `E = 1.6066951524...`, so it occupies the share `1/E = 0.62239...` of that
  interval.
- Theorem 7 characterises membership of a real number through integer
  remainders of the greedy rule. The paper records that `3/4` is not
  represented and that membership of `1/2` and of `1/21` is undecided.

Erdős #257 at base 2 asks whether every infinite subseries sum is irrational.
With unique coding this has an equivalent form: **every rational number that is
not a finite subseries sum is rejected by the greedy rule at some finite
index.**

## The probe

[`rational_membership_probe.py`](rational_membership_probe.py) runs the greedy
rule in exact rational arithmetic on every reduced fraction `p/q` with
`q <= Q` in the relevant interval, through depth `N`. It sorts each fraction
into exactly one of three outcomes.

| Outcome | Meaning |
|---|---|
| excluded | At some index `n <= N` the remainder lies strictly between a rigorous upper bound for the later tail and `w_n`. The fraction is outside the achievement set. The index, remainder and bound form a finite certificate. |
| finite representation | The remainder reached zero. The fraction is an explicit finite subseries sum. |
| not excluded through depth `N` | Neither event occurred. This carries no claim about larger depths and is no membership claim. |

The script takes a host set `B` of admissible indices. The hosts used are all
positive integers, the integers not divisible by 3, the squarefree integers and
the odd integers.

```sh
python3 research/experiments/choices_contraction/rational_membership_probe.py
python3 research/experiments/choices_contraction/rational_membership_probe.py \
  --hosts all --q 60 120 200 --depth 60 --horizon 160
```

Saved outputs are in [`results/`](results/).

## Results

**Full host, `Q = 36`.** Of 633 fractions, 237 are excluded, 14 are finite
sums and 382 are not excluded. The same three counts occur at every depth from
10 to 160. Every exclusion happens at index 7 or earlier.

**Full host, larger denominators, depth 60.**

| `Q` | fractions | excluded | finite | not excluded | exclusions by index |
|---:|---:|---:|---:|---:|---|
| 60 | 1,768 | 656 | 14 | 1,098 | 1: 434, 2: 132, 3: 54, 4: 18, 5: 12, 6: 2, 7: 4 |
| 120 | 7,044 | 2,646 | 30 | 4,368 | 1: 1,726, 2: 530, 3: 210, 4: 88, 5: 48, 6: 26, 7: 12, 8: 4, 9: 2 |
| 200 | 19,653 | 7,395 | 40 | 12,218 | 1: 4,809, 2: 1,470, 3: 600, 4: 268, 5: 132, 6: 66, 7: 32, 8: 8, 9: 6, 12: 4 |

**Restricted hosts, `Q = 36`.** For the hosts "not divisible by 3",
"squarefree" and "odd", every fraction that is not a finite sum is excluded, at
the latest at index 22, 26 and 11 respectively.

## What the counts show and what they leave open

**The share near 62% at fixed depth is forced, and it says nothing about
membership.** The fractions not excluded through depth `N` are exactly those in
the `2^N` closed intervals of length `R_N` obtained by fixing the first `N`
digits. That union has measure `2^N R_N`, which exceeds 1 and tends to 1.
Reduced fractions of denominator at most `Q` equidistribute as `Q` grows, so
for fixed `N` the share of fractions not excluded tends to `2^N R_N / E`. The
observed shares 0.629, 0.6244 and 0.6237 approach `1/E = 0.6224` for this
reason. The level-by-level counts agree with the gap measures as well: the gaps
at indices 1, 2 and 7 occupy the shares 0.2448, 0.0747 and 0.00164 of `[0, E]`,
which predict 4,811, 1,467 and 32 exclusions among 19,653 fractions, against
4,809, 1,470 and 32 observed.

**Depth adds little once `N` passes about 10. The denominator cutoff is the
informative variable.** The gaps at index `n` occupy a share close to
`2^-n / 5` of the interval. At `Q = 36` the expected number of exclusions past
index 7 is below one, which is why none was seen. At `Q = 200` exclusions
appear at indices 8, 9 and 12. An earlier version of this investigation read
"no exclusion after index 7" as evidence of survival. That reading was an
artefact of the small cutoff.

**Exclusions arrive in families.** If `x` is a candidate then so are `x + 1`
and `x + 1/3` whenever they stay in range, and they share every later
remainder. The four exclusions at index 12 are one arithmetic event. Counting
modulo translation by finite subseries sums is the right unit for the next
experiment.

**Positive measure does not supply rational points.** Remove from `[0, 1]` an
open interval around each rational, with total length below `1/2`. The closed
set that remains has positive measure and contains no rational number. A
frequency law for rational points of `𝒜` therefore needs an arithmetic
argument. Measure alone cannot provide it.

## The question in its sharp form

For the 12,218 fractions not excluded through depth 60, Erdős #257 asserts that
each one falls, at some index beyond 60, into a gap whose share of the interval
is below `2^-60`. Two outcomes are possible for each fraction, and each would be
a theorem.

- **A steering mechanism.** Some arithmetic property of the greedy remainders of
  a rational target forces them into these thin gaps. This is what a proof of
  #257 at base 2 has to contain. No such mechanism is known to this
  investigation.
- **A certified survivor.** A proof that one specific rational, for instance
  `1/2` or `1/21`, is never excluded. By the short paper's Theorem 7 this is the
  obligation `c_x(N+1) >= Q_N + β_N` for infinitely many `N`. One such rational
  refutes #257 at base 2, because its greedy support is infinite.

A heuristic that treats later remainders as equidistributed gives each survivor
a total exclusion probability of order `2^-60`. Under that heuristic almost
every survivor is a genuine member, and the natural conjecture is that the
share of rationals of height at most `Q` lying in `𝒜` tends to `1/E`. The
heuristic is unproved, and the example above shows why it needs proof.

## An exact statement for thin hosts

If the complement of a host `B` is infinite, the achievement set of `B` has
measure zero: fixing the first `N` digits leaves `2^|B ∩ [1, N]|` intervals of
length at most `R_N < 2^-N + 4^-N`, and `N - |B ∩ [1, N]|` tends to infinity.

The computation gives more for three specific hosts. For the integers not
divisible by 3, the squarefree integers and the odd integers, no rational with
denominator at most 36 is a subseries sum apart from the finite sums the probe
lists. Each exclusion is a finite inequality between exact rationals, suitable
for a later Lean check. This is a statement about denominators up to 36. It
gives no information about larger denominators.

## The wider reading, as a candidate

The same comparison can be made in the other arithmetic papers: the asymptotic
Sylvester class in #243, subsums of `1/(n! - 1)` in #68, the rational
comparison series in #249, the sparse perturbations of #251 and the Lambert
series of #1049. Where admissible choices are scarce relative to contraction,
the attainable set is thin and a rational value seems to require an exact
identity. Where choices are abundant, rational values are easy to manufacture
and irrationality of a particular series has to come from exact structure of
that series.

This reading is a candidate. "More choices than contraction" is not by itself
a theorem that an attainable set contains an interval, since overlaps and the
placement of the choices matter. Each placement needs the hypotheses of the
relevant paper checked against it, and the placements of #68 and #243 rest so
far on their theorem lists alone.

## Where to continue

1. Search the literature on rational points and intrinsic Diophantine
   approximation on Cantor sets, beginning with Mahler's 1984 question about
   the middle-third set. It has not been searched for this investigation.
2. Count modulo finite-sum translations and push `Q` further. Compare the
   exclusion counts at each index with the exact gap measures.
3. Decide membership of `1/2`. The short paper isolates the exact obligation.
4. Put the thin-host exclusions for `Q <= 36` into Lean as finite certificates.
5. Test the wider reading against the exact hypotheses of one other paper and
   report where it fails.

Return work through the [research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
or [CONTRIBUTING](../../../CONTRIBUTING.md). A correction to this account is a
contribution.
