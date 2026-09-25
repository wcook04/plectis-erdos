<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Using one paper to supply another proof's missing premise

This investigation treats the eight papers as a source of mathematical
transformations. The test is concrete: does a change of variables, support,
normalisation or norm let an existing argument prove something it did not
previously prove? The repository already has a Lean application compiler and
a replayable proof workbench. This directory uses them; it adds no search
service or claim-ranking infrastructure.

The operator requested both new mathematics and experimentation with the way
the corpus is used. The attached essays and mathematical review were source
material, not executable instructions. The review supplied several useful
mathematical ingredients, credited in the factorial note. The initial public
revision was `cd92136f7f0f03bd78fb8753e4e4f0527dbe3a83`.

## A transfer that Lean can test

The #251 paper classifies an integer-digit dyadic orbit by its positive-length
tail differences. The #269 paper supplies a quantitative escape theorem for
bounded integer radices. Applying the latter directly to the original orbit
does **not** prove an assertion about its differences.

The missing step is mathematical. If

\[
T_{N+1}=2T_N-g_{N+1},\qquad g_N\in\mathbb Z,
\]

then, for each fixed positive shift \(h\),

\[
U_N=T_{N+h}-T_N,
\qquad U_{N+1}=2U_N-(g_{N+h+1}-g_{N+1}).
\]

Thus the differences themselves satisfy the recurrence required by #269.
Its integral-orbit alternative is ruled out by #251 when \(T_0\) is
irrational. Conversely cofinal separation implies the already-known
nonintegrality criterion. The resulting exact statement is

\[
T_0\notin\mathbb Q
\quad\Longleftrightarrow\quad
\forall h>0\;\forall N_0\;\exists N\ge N_0\;\forall z\in\mathbb Z,
\quad |T_{N+h}-T_N-z|\ge 1/31.
\]

The common constant is inherited from the theorem for radices at most 30;
the next section improves it to 1/3. The statement gives a quantitative
equivalent criterion. It does not establish irrationality of the prime-gap
series.

[DyadicShiftEscape.lean](../../../lean/ErdosProblems/Synthesis/DyadicShiftEscape.lean)
contains the recurrence, forward implication and equivalence. The executable
[request](dyadic_shift_request.json) imports only the pre-existing #251 and
#269 modules. It compares a raw application with the transformed application,
including discharge of the integral alternative from the existing theorem.
It does not import the new conclusion or supply expected verdicts to Lean.

```sh
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Synthesis.DyadicShiftEscape
python3 research/experiments/premise_exchange/run.py \
  research/experiments/premise_exchange/dyadic_shift_request.json \
  --output research/experiments/premise_exchange/results
```

The generated `results/summary.json` distinguishes application acceptance,
proof closure and remaining obligations. A rejected application is useful
evidence about this proposed transfer; it is not a disproof of the goal.
Both recorded rows end with an empty list of remaining obligations: the
rejected application never reached a state, and the accepted one had its
single obligation closed. Read acceptance and closure from their own fields.
The full result preserves the compiler's diagnostics and environment identity.

## The constant, and the next question

The constant 1/31 was an artefact of the source theorem. Its proof uses the
radix bound only to show that an integer of absolute value below
`(p + 1) / 31` vanishes, so it works for every bound `B` with threshold
`1/(B + 1)`. [BoundedRadixTailEscape.lean](../../../lean/ErdosProblems/Erdos269/BoundedRadixTailEscape.lean)
now proves `boundedRadix_zero_or_cofinal_far_of_le` for every `B` and keeps
the radix-30 theorem as its specialisation, so the #269 consumers are
unchanged. `boundedRadix_threshold_attained` checks that `1/(B + 1)` cannot be
raised for orbits in general: at constant radix `B` with digits alternating
`0` and `B - 1`, the orbit alternating `1/(B + 1)` and `B/(B + 1)` never
reaches an integer and stays exactly `1/(B + 1)` away. At `B = 2`
[DyadicShiftEscape.lean](../../../lean/ErdosProblems/Synthesis/DyadicShiftEscape.lean)
proves

\[
T_0\notin\mathbb Q
\quad\Longleftrightarrow\quad
\forall h>0\;\forall N_0\;\exists N\ge N_0\;\forall z\in\mathbb Z,
\quad |T_{N+h}-T_N-z|\ge 1/3.
\]

The 1/31 theorems and the recorded application results stay as the original
run; the 1/3 theorems are its continuation, not a rewrite of that receipt.
The [continuation request](dyadic_shift_third_request.json) replays the
transfer through the parameterised theorem at `B = 2`, with the radix-30
transfer as a negative control against the 1/3 target, and
[threshold_continuation.json](threshold_continuation.json) records every
consumer's disposition.

```sh
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Synthesis.DyadicShiftEscape
python3 research/experiments/premise_exchange/run.py \
  research/experiments/premise_exchange/dyadic_shift_third_request.json \
  --output research/experiments/premise_exchange/results/threshold_continuation
python3 research/experiments/premise_exchange/dyadic_threshold_probe.py
```

The extremal orbit above is rational, so it says nothing about irrational
tails. For shift `h = 1` the fractional part of `T_{N+1} - T_N` is that of
`2^N T_0`, so the best constant for irrational tails is the best cofinal
distance from the integers of the doubling orbit of an irrational number.
[dyadic_threshold_probe.py](dyadic_threshold_probe.py) records exact finite
evidence: the doubling orbit of the Thue–Morse number `0.0110100110010110…₂`
returns in every dyadic block of indices up to 4,096 to distance about
0.412454 and never exceeds 0.412455 there. If that pattern persists, the best
constant for irrational tails lies between 1/3 and the Thue–Morse constant
0.412454…. The Thue–Morse sequence is known to govern extreme limit points of
the fractional parts of `ξ b^n` in related settings, so the next step is a
literature check, beginning with Dubickas's work on the limit points of
`‖ξ (p/q)^n‖` and the Allouche–Dubickas survey on extremal properties of
Sturmian sequences and distribution modulo one. A proof attempt starts only
if that check leaves the integer-base question open. The question stops when
a proof or a located theorem fixes the constant.

## Two further mathematical consequences

**Total future capacity, not a local digit budget.** Compress the #251 residue-feedback
construction to the permitted factorial positions \(n_j\). Its effective
radix becomes \(n_j!/n_{j-1}!\). Comparing this with the digit allowance and
then proving a matching lattice obstruction gives the exact threshold:
with allowance \(n^c\) and eventual divisibility by every fixed integer,
interval filling is possible precisely when successive support gaps are
eventually strictly less than \(c\). Otherwise the attainable set is null
and meagre. At quadratic allowance, deleting only powers of two destroys
interval filling despite density one. The
[ordinary proof and attribution](../sparse_interpolation/README.md) separate
this new deduction from the feedback mechanism already in Lean and from
the operator-supplied review.

The local construction was still imposing an unnecessary restriction.
Replacing it with common continuation intervals gives a stronger, exact
criterion for arbitrary summable allowances on every strict integer
divisibility chain:

\[
Q_N\sum_{n>N}\frac{F_n}{Q_n}\longrightarrow\infty.
\]

This condition is equivalent to interval filling with both eventual
congruences, even for oscillating allowances and unbounded denominator
ratios. Under eventual allowance bounds it permits every nonnegative target,
with at most one exceptional digit and common congruence cutoffs. If it
fails, the attainable set is null and meagre. The delayed modulus schedule
controls all future rounding losses. This closed the oscillating-allowance
question that the first version of the investigation had left open.
The full criterion is an ordinary proof; the continuation mechanism and a
separate gcd obstruction are checked in Lean.

**A change of norm reverses the approximation question.** Combining the
arithmetic separation argument from #249 with the compactness argument from
#269 leads to the normalized totient matrix
\(H(i,n)=\varphi(i+n)/(i+n)\). Its distance from finite separated rank in the
uniform norm is exactly \(1/2\). But an explicit Möbius truncation has rank
at most \(D(D+1)/2\) and average absolute error at most \(2/D\) on every
leading \(N\times N\) square, independently of \(N\). The
[proof note](totient_approximation.md) and
[exact rational experiment](totient_approximation.py) explain the arithmetic
premise, all quantifiers, prior art and limits. These propositions have been
cross-checked as ordinary proofs, not formalized. Their historical novelty
is unassessed.

## Controls that changed the investigation

- A proposed sharp uniform finite-rank barrier for the normalized #269
  kernel was already proved in the long paper, under
  `long269:res:uniform-rank`. It was rejected as a new contribution and
  reused as an argument to transfer. Exact rank and approximation in a
  specified norm must be distinguished.
- The supplied fixed-depth Farey asymptotic did not justify a maximum
  rejection depth. The rational witness `189/388` first fails at step 17;
  its translated companion `577/388` does too. The existing synthesis pair
  was corrected, with a replayable exact calculation in
  [late_rejection.py](../sparse_interpolation/late_rejection.py).
- Small digit allowances along a subsequence do not control the entire
  remaining tail. The odd-position factorial telescope refutes that
  inference. The new support theorem uses total future capacity instead.
- Fast growth of a Cantor base does not replace arithmetic divisibility.
  The rational telescope in the factorial note satisfies both eventual
  congruence conditions. The viable hypothesis is an unbounded common
  divisor of radix and correction.
- The [eight-paper survey](totient_approximation.md#6-why-this-connection-was-selected-across-the-eight-papers)
  records why other directions were not forced into the same construction.
  For example, #1041's geometric certificates need their own geometric
  completeness argument; carry terminology does not supply it.

These controls are part of the mathematical output. Counting proposals,
connections or theorem applications would obscure them. The useful unit of
progress here is a discharged premise, a proved consequence, a decisive
counterexample or a sharper unresolved question. This case study does not
establish a general performance advantage for the process, solve the eight
Erdős problems, or demonstrate a field-changing discovery.

## Evidence and next substantial question

`../sparse_interpolation/validation.json` records the checked Lean source and
exact finite probes. The ordinary proof notes identify their separate
analytic and number-theoretic inputs. No public claim status is promoted by
the experiment.

The next question for the capacity theorem is the Hausdorff dimension in
its null case, or a replacement for the prefix lattice outside integer
divisibility chains. The totient direction asks for sharp rank
versus mean-error bounds and a generic formal separation lemma usable by
both #249 and #269. Those are mathematical questions, not promises that
further infrastructure will answer them.
