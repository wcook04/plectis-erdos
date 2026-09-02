# Erdős 269 integral-tail gap descent

## Analytic consumer

The exact source tail already satisfies

`X_(a+1) = b_a X_a - d_a`,

and Lean proves that it either reaches an integral state or returns cofinally
far from every integer.  The remaining branch is therefore an infinite
positive integer orbit obeying the actual `{2,3,5}` source recurrence and the
proved quadratic tail cap.

Once a local product base first exceeds that cap, the possible positive
integer endpoint is the canonical least-positive residue `rho`.  While it is
still trapped, put

`g = C - rho`,

where `C` is the integer cap.  Consecutive exact source rows give

`g' = b*g - h`,  with  `h = b*C - C' - d`.

This is a new producer rather than another delay cap: if every trapped state
either escapes or reaches a strictly smaller nonnegative integer gap within
two transitions, well-founded descent rules out an infinite trapped orbit even
when the first-clear gap is arbitrarily large.

## Predeclared probe

The executable checker tests exactly that two-step statement on every
canonical denominator-one trajectory in its configured source range.  It also
replays the gap/charge identity at every transition and tests the stronger
one-step statement separately.  One trapped state with no escape or strict gap
decrease in the next two transitions is the falsifier.  If such a state is
found, the route is retired rather than repaired by increasing the lookahead
constant.

The generated receipt links the exact source engine, prior three-transition
counterexample, source recurrence, Lean dichotomy consumer, and both analytic
consequences.  Finite survival opens an all-scale inequality to prove; it is
not itself an irrationality theorem.

## Exact result: the two-step Lyapunov law is false

The canonical scan covers starts `1..3000` and 1,544 trapped post-clear
positions.  The gap/charge identity replays exactly at every trapped-to-trapped
transition.  One-step descent fails 71 times.  More decisively, two exact
positions survive two further source transitions without escaping and without
returning below their initial integer gap:

- start `2220`, length `7`: `1871381 -> 2073386 -> 2001740`;
- start `2602`, length `7`: `2776610 -> 2870292 -> 2851196`.

These are counterexamples to the predeclared two-step statement, not failures
of a finite search to find escape.  They eliminate raw cap gap as a bounded-
lookahead Lyapunov function.  The route must now change the functional by using
source-conditioned charge or genuinely nonlocal phase information; increasing
the lookahead constant would only recreate the retired fixed-delay programme.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_tail_gap_descent.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_tail_gap_descent.py --check
```
