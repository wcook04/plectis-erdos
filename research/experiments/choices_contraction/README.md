<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Choices, contraction and rational membership

Erdős #257 at base 2 is equivalent to a finite-rejection statement: every
rational number that is not a finite sum of the weights `1/(2^n - 1)` is
rejected by the greedy rule at some finite index. Equidistribution explains
the limiting share not rejected at each fixed depth as the denominator bound
grows; it supplies neither a membership test nor a stopping depth. The exact
rejection of `189/388` at step 17 disproves the proposed cutoff near
`2 log2 Q - 3.3`. Computation at denominators up to 200 agrees closely with
the measures of the removed intervals. For
the hosts of odd, squarefree and non-multiples-of-3 exponents it excludes every
rational of denominator at most 36 that is not a finite sum.

The theorems and the record of how this computation was misread twice are in
the consolidated synthesis paper
[Reading Eight Erdős Problems Together](../../../paper/synthesis/optimal-sparse-perturbations.pdf)
([source](../../../paper/synthesis/optimal-sparse-perturbations.tex)).

This investigation started from reading the eight short papers together and
belongs to no single problem. Its sharpest instance sits inside Erdős #257, and
its framing draws on #243, #249, #251 and #1049.

**Status.** Ordinary reasoning and exact rational computation. Nothing here is
checked in Lean. A prior-art search was made on 20 September 2026 and its
findings are in that synthesis paper. Membership of any
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

**The limiting share at fixed depth does not establish membership.** For the
exact greedy criterion, the fractions not rejected through depth `N` lie in
the `2^N` closed intervals of length `R_N` obtained by fixing the first `N`
digits. That union has measure `2^N R_N`, which exceeds 1 and tends to 1.
Reduced fractions of denominator at most `Q` equidistribute as `Q` grows, so
for fixed `N` the share of fractions not excluded tends to `2^N R_N / E`. The
observed shares 0.629, 0.6244 and 0.6237 are close to `1/E = 0.6224`, but these
finite counts are not fixed by the limiting law. The level-by-level counts
agree closely with the gap measures as well: the gaps
at indices 1, 2 and 7 occupy the shares 0.2448, 0.0747 and 0.00164 of `[0, E]`,
which predict 4,811, 1,467 and 32 exclusions among 19,653 fractions, against
4,809, 1,470 and 32 observed.

**The measure-based estimate is not a stopping rule.** The gaps at index `n` occupy the
share `2^(n-1) g_n / E` of the interval, where `g_n = w_n - R_n`, which is
`2^-n / (3E)` up to a factor `1 + O(2^-n)`. The measure-based main term for the
number of fractions of height at most `Q` excluded at index `n` is
`(3 Q^2 / pi^2) 2^(n-1) g_n`. It falls below one near
`n = 2 log2 Q - 2 log2 pi`, approximately `2 log2 Q - 3.3`.
A main term below one does not make the actual integer count zero. The
fixed-depth equidistribution estimate does not justify this extrapolation to
a depth growing with `Q`.

For example, `189/388` is first rejected at step 17, beyond the proposed scale
of about 13.9. Before rejection, the greedy rule selects indices
`{2,3,7,9,10,14,15,16}`. Every earlier skipped step has remainder at most
`2^-n < R_n`. At step 17 the remaining value satisfies

```text
R_17 <= 196609/25769803776
     < 9291822600689/1217890317075045460
     < 1/131071 = w_17.
```

The upper bound follows by summing
`1/(2^k - 1) <= 2^-k + 2*4^-k` over `k > 17`.
The existing [exact certificate](../sparse_interpolation/late_rejection.py)
checks every earlier skip and the final gap, both for `189/388` and its
translate `577/388`. The [probe regression](../../../scripts/test_choices_contraction_probe.py)
also checks that both fractions are undecided at depth 16 and excluded at
depth 17. Thus deeper computation can produce new nonmembership certificates;
survival through any finite depth remains only finite evidence.

**Exclusions arrive in families.** Let `F` be finite with largest element `n`
and let `0 <= x <= R_n`. Then the greedy rule on `X_F + x` selects `F` and then
agrees with the greedy rule on `x`. The condition is `x <= R_n`; it is not
enough that the translate stays below `E`, since `1/2` is not excluded through
depth 160 while `1/2 + 1/3 = 5/6` is excluded at index 1. Because `x -> x + 1`
preserves reduced denominators, the number excluded at every index from 2 on
is even. The four exclusions at index 12 are `46/183` and its translates by
`1/3`, `1` and `4/3`, one arithmetic event. Counts should be taken modulo these
translations.

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

A model that treats later remainders as equidistributed predicts that the
share of rationals of height at most `Q` lying in `𝒜` tends to `1/E`. That is
a strong denial of #257, under which the only members are the finite sums (40
of the 19,653 fractions at `Q = 200`). The finite-depth counts do not justify
that infinite-membership prediction. Boes, Darst and Erdős (Amer.
Math. Monthly 88 (1981) 340-341) construct fat symmetric Cantor sets with
essentially no rationals, so measure cannot decide.

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

1. Extend the literature search. Counting rationals of bounded height is
   studied for null Cantor sets (Rahm, Solomon, Trauthwein and Weiss; Chow,
   Varjú and Yu). We found nothing on rational points of a subsum set of
   positive measure.
2. Count modulo finite-sum translations and push `Q` further. Compare the
   exclusion counts at each index with the exact gap measures.
3. Decide membership of `1/2`. The short paper isolates the exact obligation.
4. Put the thin-host exclusions for `Q <= 36` into Lean as finite certificates.
5. Test the wider reading against the exact hypotheses of one other paper and
   report where it fails.

Return work through the [research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
or [CONTRIBUTING](../../../CONTRIBUTING.md). A correction to this account is a
contribution.
