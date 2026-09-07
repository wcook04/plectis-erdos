# Greedy repair criteria for arbitrary real targets

This generalizes the four-ninths repair criterion to every nonnegative real
target. All five equivalent membership conditions below, and the finite
strict-window exclusion criterion, are checked in
[GreedyRepairCriterion.lean](GreedyRepairCriterion.lean).
The target is membership in the binary Mersenne achievement set. No claim
here settles universal irrationality or membership of a particular open
rational target.

Let `x ≥ 0` be real, let `A_x` be its actual greedy Mersenne support, and put

\[
 c_x(n)=\#\{a\in A_x:a\mid n\},\qquad
 P_N=\sum_{n=1}^N c_x(n)2^{N-n},\qquad
 Q_N=\lfloor2^Nx\rfloor-P_N.
\]

The greedy Lambert prefix is at most `x`, so `Q_N` is a nonnegative
integer. This is the actual prefix coordinate, not an arbitrary sequence
assumed to resemble a greedy orbit.

**Theorem.** For every real `x ≥ 0`, the following are equivalent:

1. `x` belongs to the Mersenne achievement set.
2. For every `K`, some `N ≥ K` satisfies `Q_(N+1) ≤ Q_N`.
3. For every `K`, some `K ≤ N < K + 2 floor(sqrt K) + 12` satisfies
   `Q_(N+1) ≤ Q_N`.
4. For every `K`, some `N ≥ K` satisfies `Q_N ≤ N+1`.
5. For every `K`, some `N ≥ K` satisfies `Q_N ≤ c_x(N+1)`.

In particular, the square-root repair deadline is uniform in the target.
Neither rationality nor periodic binary digits are hypotheses. For a target
outside the achievement set the defect eventually increases at every step.

## The three ingredients

The source assets are `BooleanMobiusCarry.lean` (the actual greedy Lambert
prefix bound), `GreedyAchievementSet.lean` (survival and the persistent fatal
gap), and `BatchReturnSynthesis.lean` (the square-root strip's finite repair
deadline). The old target-specific proof is in
`FourNinthsCofinalRepairConsumer.lean`.

First, let

\[
 e_N=\lfloor2^{N+1}x\rfloor-2\lfloor2^Nx\rfloor\in\{0,1\}.
\]

The exact recurrence is

\[
 Q_{N+1}=2Q_N+e_N-c_x(N+1).
\]

Thus a repair `Q_(N+1) ≤ Q_N` implies
`Q_N ≤ c_x(N+1) ≤ N+1`. Only `e_N ≥ 0` is used: periodicity has no
role. This proves (2) ⇒ (5) ⇒ (4).

Second, if `x` is represented, greedy reconstruction identifies `A_x` with
the representing support. The Lambert prefix-tail identity gives

\[
 0\le Q_N\le T_{A_x}(N)\le2\sqrt N+4.
\]

The last inequality is the support-uniform divisor-pair bound. For a
nonnegative integer sequence in this strip, failure to repair on all of
`[K,K+2 floor(sqrt K)+12)` would force at least that many unit increases,
contradicting the strip at the final endpoint. This proves (1) ⇒ (3), and
(3) ⇒ (2) is immediate.

Third, let `r_N` be the actual greedy remainder and `a_N` the complete
Mersenne tail beyond `N`. The finite-prefix Lambert identity gives

\[
 2^N r_N
 \le 2^Nx-P_N
 < Q_N+1.
\]

Indeed, the difference between `2^Nx-P_N` and `2^Nr_N` is the
nonnegative future-multiple tail of the already selected finite support.
If `x` is not represented, greedy survival fails at some `n`. With
`δ=r_n-a_n>0`, the fatal-gap identity says
`r_(n+k)-a_(n+k)=δ` for all `k ≥ 0`. Since `a_(n+k) ≥ 0`,

\[
 2^N\delta\le Q_N+1\qquad(N\ge n).
\]

But `(N+2)/2^N → 0`, so this excludes `Q_N ≤ N+1` at every sufficiently
large `N`. It proves (4) ⇒ (1). The same geometric lower bound and the
recurrence imply `Q_(N+1)>Q_N` eventually, completing the last assertion.

## What the strengthening supplies

The four-ninths theorem becomes an instance of an achievement-set theorem
whose only target restriction is nonnegativity. The same criterion applies
to `1/2`, `1/21`, and irrational targets. Its finite failure certificates
are intervals on which the actual defect increases throughout; a certified
such interval excludes membership. Positive membership still requires
cofinal information. This keeps the distinction between a finite exclusion
test and an all-depth membership proof explicit.

The displayed proof also gives two equivalent alternative producers: a
cofinal linear defect bound and a cofinal bound by the actual next divisor
load. These require no periodic residue-class selection, and can be tested
or used by future support-specific estimates without rebuilding a separate
integer-gap argument for every rational target.

## Verification and formal entry points

The focused single-owner build completed successfully on 2026-09-05:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 1 ErdosProblems.Erdos257.GreedyRepairCriterion
```

The four `mem_iff_greedyBinaryDefect_*` declarations expose the equivalent
repair, square-root-window, next-load and linear-bound conditions.
`not_mem_of_greedyBinaryDefect_strict_sqrt_window` exposes the finite
exclusion consumer. Their printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. The accepted build is recorded by
command future `cf_fa53ed19579e413aa507`; its nested build output is
`state/command_runs/outputs/cmdrun_20260905T134145Z_17438_925155000_df66905df1c6.stdout`
relative to the private workspace root. This was a focused module build.

For a small exact check, the defect at `x=3/4` through rank 12 is

```
0, 1, 2, 3, 4, 7, 11, 21, 39, 76, 149, 297, 589.
```

All 12 steps increase, so the window at `K=0` excludes membership.
These values were independently replayed with rational arithmetic using
the actual take-if-possible support and its divisor counts. For the
represented value `x=1/3`, the greedy support is `{2}` and the defect is
identically zero. These examples display the two kinds of behavior; the
uniform criterion, rather than a finite successful replay, proves membership.
