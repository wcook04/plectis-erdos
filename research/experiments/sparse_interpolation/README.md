<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# An exact capacity criterion for eventual congruences

For positive integer denominators `Q_n | Q_(n+1)` with
`Q_(n+1) >= 2 Q_n`, and nonnegative integer allowances with
`sum F_n/Q_n < infinity`, put

\[
U_N=Q_N\sum_{n>N} F_n/Q_n.
\]

Nonnegative integer digits, bounded by `F_n` eventually and eventually
divisible by every fixed integer, fill an interval **if and only if
`U_N -> infinity`**. Otherwise their attainable set is null and meagre.
In the positive case, every nonnegative real is attainable with at most one
allowance exception, an arbitrarily long initial zero segment, and both
individual and cumulative eventual congruences. The congruence cutoffs can
be common to all targets; the allowance-exception index may depend on the
target. Requiring the allowances at every position still permits an interval.

The theorem allows arbitrary oscillation and unbounded denominator ratios.
It is an ordinary proof developed and cross-checked during this investigation;
historical novelty and independent expert review remain unestablished.

With allowance `n^c`, eventual divisibility of every correction by each fixed
integer permits an interval of factorial-series values exactly when the
successive permitted positions eventually have gaps **strictly smaller than
c**. For `c <= 1` no support works. If the gap condition fails, the attainable
set is both null and meagre, even when the congruence cutoffs depend on the
represented value.

[The paper](../../../paper/synthesis/optimal-sparse-perturbations.tex) gives
the complete capacity proof, the contrasting classification without congruences,
and a gcd criterion for irrationality of general Cantor series.

The strongest simple example is quadratic: removing only the powers of two
from the permitted positions destroys interval filling, although the support
still has density one. For allowance `n^(2+epsilon)`, the even positions fill
an interval. Counting the total number of digits misses this distinction.

## How the question changed

The #251 construction already had a checked one-position feedback mechanism in
[ResidueFeedbackCore.lean](../../../lean/ErdosProblems/Erdos251/ResidueFeedbackCore.lean).
The supplied review isolated its improvement over separate residue repairs.
We did not rebuild that mechanism or claim its discovery. We changed the
coordinates: for support `n_j`, the effective factorial radix is
`r_j = n_j! / n_(j-1)!`. The ratio `F(n_j)/r_j` determines whether the same
selector has room for growing congruence moduli.

That first gap classification turned out to be a special case. Instead of
requiring each digit to carry enough capacity for the next step, use the
entire continuation interval. Choose nested factorial moduli below
`min(n, sqrt(inf_(k>=floor(n/2)) U_k))`. Delaying the lower envelope makes
the total future cost of rounding negligible compared with `U_N`, even for
rapidly changing denominator ratios. Discard positions whose allowances
cannot accommodate one residue class, reserve a margin on both sides of
the others, and the remaining continuation intervals still overlap.
Their overlap is uniform in the current cumulative residue. This removes
the restriction that originally made oscillating allowances look like a
separate frontier.

The converse uses a different idea. At a bounded-capacity prefix, scale by `Q_N`.
The prefix is on a lattice with spacing `q`, while the whole future capacity
stays bounded. One fixed sufficiently large `q` leaves holes at arbitrarily
fine scales. Compactness and a countable union over cutoffs give the null and
meagre conclusions. This works even for rare gaps, explaining why density is
too weak a descriptor.

This is a mathematical consequence of comparing proofs, not evidence that a
particular prompting protocol is universally better. The broader executable
experiment is in [premise_exchange](../premise_exchange/README.md).

## Exact checks

From the repository root:

```sh
python3 research/experiments/sparse_interpolation/feedback.py
python3 research/experiments/sparse_interpolation/capacity.py
python3 research/experiments/sparse_interpolation/late_rejection.py
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Synthesis
```

`feedback.py` checks the explicit residue selector for rational scaled targets,
three factorial support schedules, and a rational Cantor-series counterexample
with both individual and cumulative eventual congruences. It works in scaled
residual coordinates instead of constructing enormous factorial denominators.
`feedback-results.json` records its exact finite output. The infinite results
come from the proofs, not these samples.

`capacity.py` checks the common-continuation construction with exact dyadic
tail capacities, changing nested moduli, arbitrary incoming cumulative sums,
and endpoint targets. Its finite modulus schedule is not evidence of
divisibility by every integer. It also checks the denominator-block count
in the repeated-denominator counterexample: strict growth in the theorem
cannot be dropped merely because the denominators are nested.

`late_rejection.py` checks that `189/388` first fails the Mersenne greedy rule
at step 17 (and its translated companion `577/388` does too). This corrects
the previous extrapolation from a fixed-depth Farey asymptotic to a purported
maximum rejection depth. The fixed-depth theorem survives. The same script
checks the odd-index factorial telescope showing why a small allowance merely
along a subsequence does not imply a null attainable set.

## Evidence and attribution

- Starting public revision: `cd92136f7f0f03bd78fb8753e4e4f0527dbe3a83`.
- The operator supplied a mathematical review containing the one-coefficient
  lemma, optimal exponential sparsity argument, factorial linear/superlinear
  contrast, and the rejection certificate. Those are inputs, not discoveries
  claimed by this session.
- The exact general capacity criterion, factorial support classification, integer-exponent contrast,
  and the unbounded-gcd formulation were developed and cross-checked during
  this AI-assisted session. Historical novelty and independent expert review
  are unestablished.
- Airey, Mance and Vandehey already use restricted digit sets eventually
  divisible by every integer while retaining asymptotically full digit
  entropy: [NYJM 21 (2015), section 6, p.1321](https://nyjm.albany.edu/j/2015/21-60v.pdf).
  Their normality/dimension construction is an antecedent for the device,
  not a source for the factorial gap classification stated here.
- Classical variable-digit interval covering is treated by J. A. Fridy,
  [*Generalized Bases for the Real Numbers*, Fibonacci Quarterly 4 (1966), 193–201](https://www.fq.math.ca/Scanned/4-3/fridy.pdf).
  Its tail-overlap condition is an antecedent for the covering step. The
  residue-dependent continuation interval, the slowly increasing modulus
  schedule and the matching prefix-lattice necessity must be distinguished
  from that classical covering principle. A bounded search did not establish
  historical priority for the combined capacity criterion.
- Classical Cantor-series irrationality criteria provide context:
  [Hancl–Tijdeman, *On the irrationality of polynomial Cantor series*](https://pub.math.leidenuniv.nl/~tijdemanr/hancti17.pdf).
- [CongruenceInterpolation.lean](../../../lean/ErdosProblems/Synthesis/CongruenceInterpolation.lean)
  states the gcd obstruction for real carry recurrences. It does not formalise
  the measure argument, support asymptotics, or the analytic Cantor-tail bridge.
  [FeedbackContinuation.lean](../../../lean/ErdosProblems/Synthesis/FeedbackContinuation.lean)
  derives both eventual congruences from the native feedback endpoint and
  nested cofinal moduli. Choosing the moduli and continuation intervals for
  the general capacity theorem remains an ordinary proof. Source-bound
  validation is recorded in `validation.json`.
- No Erdős endpoint, Comparator status, Palomar status, or novelty claim is
  changed by this experiment.

The next substantial question is the Hausdorff dimension in the null case.
The criterion distinguishes interval filling from nullity and meagreness;
it does not classify the dimensions of those null sets. Extending outside
integer divisibility chains would require a new replacement for the prefix
lattice argument.
