# Erdős #257: terminal scaled-vanishing counterexample endpoint

This package exposes the strongest exact conditional counterexample endpoint
in the current half-value programme. A terminal scaled-vanishing sequence
consists of finite Boolean support words whose depths tend to infinity, whose
ranks zero and one are absent, and whose absolute terminal carry divided by
the corresponding binary place value tends to zero. No compatibility between
successive words is assumed.

From that exact hypothesis, the compared theorem proves both:

- there is an infinite support A with
  sum over a in A of 1/(2^a-1) equal to 1/2;
- the universal irrationality assertion in Erdős Problem 257 is false.

This is a conditional implication, not a construction of the sequence. It
does not prove that one half belongs to the Mersenne achievement set and does
not settle the parent problem.

## Comparator surfaces

The exact selected declaration is

Erdos249257.ExternalVerification257TerminalScaledVanishing.terminalScaledVanishing_completeCounterexample.

Challenge.lean imports only Mathlib and states the hypothesis in literal
finite-word, divisor-incidence, affine-carry, and convergence vocabulary.
Solution.lean transports the source-current problem endpoints from
ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean; their proof chain
uses the achievement-set and infinite-support consumers in
Erdos257PeriodNoncollapse/TerminalOnlyScaledVanishing.lean.

comparator-negative-mismatch.json selects NegativeSolution.lean, where the
same-named theorem has an extra True hypothesis. A supported Comparator run
must accept the positive pair and reject that deliberate type mismatch.

## Exact paper route

The reader-facing treatment is theorem res:terminalhalf in
paper/erdos-257-mersenne-support-subseries.tex. The source-current private
staging copy is
ErdosProblems/papers/erdos-257-mersenne-support-subseries.tex, and its
cumulative public-paper patch is
ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch.

That paper theorem states the same scaled-vanishing hypothesis, the same
infinite-support value one half, the same universal-refutation consequence,
and the same unresolved producer. The paper supplies the ordinary proof
architecture: normalized-carry error control, closedness of the achievement
set, and finite-support exclusion.

## Palomar disposition

Plectis Signal 96 places this family in the summit band because it is an exact
conditional refutation endpoint immediately adjacent to the parent problem,
with a substantially weakened analytic hypothesis and an infinite-support
conclusion. The score is portfolio-relative reading priority only: it is not
proof authority, novelty certification, a Comparator verdict, Palomar
acceptance, or permission to submit.

The configuration is a serious Palomar candidate. The focused four-file Lean
build is green and the selected declaration uses exactly `propext`,
`Quot.sound`, and `Classical.choice`. The remaining mechanical gates are a
public immutable source identity and terminal positive-acceptance plus
deliberate-negative Comparator/NanoDa receipts. The supported replay entrypoint
is wired for this package; on the current macOS host it returns typed exit 75
because the required Linux systemd boundary is unavailable, which is an
environment receipt rather than a Comparator verdict. No local artifact is a
submission or registry outcome.
