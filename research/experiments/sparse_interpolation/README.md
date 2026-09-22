<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Capacity, dimension, and derivative interpolation

The revised [synthesis paper](../../../paper/synthesis/optimal-sparse-perturbations.tex)
proves the following joint theorem. For
`f(z) = sum e_n z^n/n!`, with nonnegative integer `e_n <= n^c` eventually
and `q | e_n` eventually for every fixed positive integer `q`, the attainable
vectors `(f(1), ..., f^(d-1)(1))` have Hausdorff dimension `min(c,d)`.
They contain an open set exactly when `c > d`; when `c <= d` they are null
and meagre. At the critical exponent the set is full-dimensional and null.
The lower bound and the open set can be constructed with the allowance at
every position, any prescribed initial zero segment, and common congruence
cutoffs. This is an ordinary proof, with finite carry ingredients checked
in [FactorialJet.lean](../../../lean/ErdosProblems/Synthesis/FactorialJet.lean).

There is a matching arithmetic theorem. If signed integer coefficients
`a_n = O(n^d)` are eventually divisible by every fixed integer, rationality
of `f(1), ..., f^(d-1)(1)` forces `f` to be a polynomial. In the nonnegative
class above, a nonpolynomial function with all these derivatives rational
therefore exists exactly when `c > d`. For example, at growth `n^2`, a
nonpolynomial function with rational value at 1 must have irrational first
derivative there; growth `n^(2+epsilon)` permits both to be rational.
The full theorem has an ordinary proof, not a Lean formalisation.

The new proof uses a factorial carry as multiplication of an exponential
generating function by `(z-1)`. Repeating it supplies higher derivatives
without changing lower ones. At the critical exponent, eventual evenness
alone forces measure zero. Moving Taylor coordinates then separate
the codes needed for the dimension lower bound. In the reverse direction,
division by `(z-1)^d` preserves integer factorial coefficients and eventual
divisibility. A complementary tail formula bounds the quotient's coefficients,
forcing them eventually to vanish. See
[the proof review](jet-review.md) for the exact scope, attribution and
remaining novelty boundary. No claim of a field-changing discovery is made.

## Extend this component and return the result

The [interval-cover calculation and contribution guide](coverage.md) explains
the exact effect of combined congruences, the contract/implementation/policy
boundary, and how a recipient checks a returned result against a separately
saved request. It includes the ordinary proof and the precise remaining
infinite-continuation obligations. Policies and new constraints use the same
[submission and credit path](../../../CONTRIBUTING.md#return-what-you-learned)
as a paper correction.

## Scalar theorem used by the derivative construction

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
python3 research/experiments/sparse_interpolation/jets.py
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

## Reusable admissible choices

The feedback argument now applies to **every admissible sequence of choices**,
not just its original selector. The checked theorem in
[`FeedbackContinuation.lean`](../../../lean/ErdosProblems/Synthesis/FeedbackContinuation.lean)
separates bounded digits, cumulative congruences and the remainder interval.
Nonnegative remainders bounded by a sequence tending to zero give the prescribed
infinite sum. Nested, cofinal moduli give the eventual digit and prefix
congruences. All these infinite hypotheses remain explicit.

For exact rational inputs, `feedback.py` compiles the one-step relation into an
integer interval intersected with a residue class. Extra congruences are merged
by the generalised Chinese remainder calculation, including non-coprime and
incompatible cases. The original finite checks remain its no-argument mode.

```sh
python3 research/experiments/sparse_interpolation/feedback.py --explore
python3 research/experiments/sparse_interpolation/feedback.py --explore --support divisor-count
python3 research/experiments/sparse_interpolation/feedback.py --evaluate --output /tmp/feedback-evaluation.json
python3 research/experiments/sparse_interpolation/test_feedback.py
```

The second command requires actual Boolean support choices: at index `n`,
`d_n = sum(x_k for k dividing n)` with every `x_k` either zero or one. This
constructs a support prefix, instead of treating arbitrary integer coefficients
as a support. It does not prove an infinite support representation or resolve
Problem 257. A conjunction can be empty even when each constraint separately
has a witness; the tests include that case and a valid prefix with no extension.

To supply another finite schedule, pass `--request request.json`. Its fields are
`target`, `steps`, optional `label`, and `support` (`free` or `divisor-count`).
Every step has `allowance`, positive `modulus`, positive `weight`, `lower`, and
`upper`; optional `congruences` contains `[digit_residue, modulus]` pairs.
The bounds describe the remainder **after** this step. Rational values must be
integers or fraction strings, never floating-point numbers. The complete
examples are retained in [`policy-results.json`](policy-results.json).

One relation supports enumeration, random choice, targeted choice, and a small
evolutionary search over choice programmes. Search scores optimise only the
selected finite objective (`energy`, `variation`, or `mass`). A programme can
be retained and reused without re-deriving the construction:

```sh
python3 research/experiments/sparse_interpolation/feedback.py --explore --runner evolve --budget 2048 --output /tmp/feedback-policy.json
python3 research/experiments/sparse_interpolation/feedback.py --request request.json --runner policy --policy-result /tmp/feedback-policy.json
```

The policy language selects the minimum, maximum, middle or a choice near the
preceding digit, always within the currently admissible set. It is a deliberately
small native adaptation of programme evolution, not AlphaEvolve itself. The
Python API also exposes `shrink_trace(request, digits, predicate)`: every accepted
simplification rechecks the construction and the researcher-supplied predicate.
A retained candidate is not automatically a proved operation or a new theorem.

### Reuse the existing proof and assurance owners

The proof-state compiler exposes a bounded expression slice for one selected
declaration, including binders, applications and subterms. It assists reasoning
about the contract; it does not automatically generalise the proof:

```sh
python3 scripts/proof_state_compiler.py --module ErdosProblems.Erdos251.ResidueFeedbackCore --inspect-declaration ErdosProblems.Erdos251.ResidueFeedback.feedbackDigit_spec
python3 research/experiments/sparse_interpolation/feedback.py --explore --lean /tmp/feedback-trace.lean
python3 scripts/proof_workbench.py open --session feedback-local --intent "Check a finite admissible construction"
python3 scripts/proof_workbench.py probe --session feedback-local --file /tmp/feedback-trace.lean
python3 scripts/proof_workbench.py replay --session feedback-local
```

The emitted Lean file independently states each finite step over real numbers,
plus any extra congruences and Boolean support identities. The workbench owns
the probe verdict and replay. A successful finite certificate does not verify
an infinite schedule, the Python compiler's completeness, or an asymptotic
property observed during exploration.

Comparator's existing isolated executor now accepts named units in its existing
release contract. The `feedback-policy` unit has an independently expanded
statement, a solution using the generalised theorem, and a proved but
deliberately weaker negative solution. No statement hole was added. Inspect it
with the same existing command, supplying the exact committed source identity:

```sh
python3 scripts/replay_external_verification.py plan --unit feedback-policy --source-commit FULL_COMMIT --source-tree FULL_TREE
python3 scripts/replay_external_verification.py run --unit feedback-policy --source-commit FULL_COMMIT --source-tree FULL_TREE --output /tmp/feedback-comparator.json
```

`run` retains the existing Linux/systemd isolation and pinned tools. Prepared
configuration and locally built challenge/solution files are not a Comparator
verdict. Positive acceptance and the expected negative type rejection must
both be recorded by that runner. The existing Linux CI Comparator job also
runs and enforces both controls and retains their logs. Research contributions continue through
`skills/erdos-research-return/SKILL.md`; no separate component registry is needed.

### What the controls establish

The eight-step feedback control has 1,393 complete traces. Compiled enumeration
and the direct-predicate baseline agree on that set's size and the optimum
energy 284; they use 2,376 and 8,856 digit proposals respectively. The Boolean
support composition has two traces and optimum energy 11, using 19 and 99
proposals. `--evaluate` also records equal proposal budgets and the cost of
deriving and reusing a policy. These are development controls, not a prospective
discovery trial or a compute-matched comparison with a capable reasoning agent.
Reading, implementation, verification, wall time and model cost must count in
any later claim of research benefit.

The contract extraction and compiler were authored for this corpus. The
literature supplies design inspiration: selected proof generalisation,
relation-based computation, constraint fusion, programmable runners, programme
evolution and consolidation. Exact sources, sections, versions, adaptations
and acquisition hashes are in [`literature.json`](literature.json), and the
systems paper explains this implementation. The retained workbench session is
[`admissible-feedback-20260920`](../../workbench/sessions/admissible-feedback-20260920),
and [`policy-propagation.json`](policy-propagation.json) records evidence and
consumer dispositions. A ninth mathematical paper must
come from a substantive subsequent result; neither these controls nor the
earlier coordinate-recovery experiment supply one.

## Earlier mathematical evidence and attribution

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

The derivative theorem now gives the exact dimension for full factorial
support with power allowances. Dimension for arbitrary supports and summable
allowances remains outside that theorem. Extending outside integer
divisibility chains would require a replacement for the prefix lattice.
