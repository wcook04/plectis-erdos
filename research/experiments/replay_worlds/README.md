<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Replaying the recorded routes of the eight problem worlds

Three recorded routes, reopened on 26 September 2026, became theorems. The two
strongest are these.

- The distinct-height running-LCM sum of Problem 269 for the primes
  2, 3 and 5 is irrational. Erdős asserted irrationality of these sums in a
  letter of 1 January 1973 without printing an argument. Exact decoding
  certificates extend the same proof to every triple of primes up to 31.
  Evidence: [`../erdos269/distinct_height/`](../erdos269/distinct_height/).
- For coprime integers a > b ≥ 1 and every infinite divisibility chain
  n₁ | n₂ | ⋯, the Lambert subsum Σ 1/((a/b)^{n_j} − 1) is transcendental.
  This settles the first open case the synthesis paper recorded (base 4/3,
  ratios 2 with infinitely many 3s) and removes its hypothesis a² > b³.
  Evidence: [`../chain_transcendence/`](../chain_transcendence/).

Both are ordinary proofs pending specialist review. The first relies on
nothing beyond elementary arithmetic and the irrationality of log 2 / log 3;
the second cites Schlickewei's p-adic Subspace Theorem.

## Where the idea comes from

Zheng et al., [*Dream-RSI: Recursive Self-Improvement through Evolving
Worlds*](https://arxiv.org/abs/2609.14858) (arXiv:2609.14858), keep a
completed discovery run as a tree of attempts with their evaluated outcomes.
Another exploration policy can then be replayed over the tree at no
execution cost, because selecting a node only reveals its stored outcome.
Their replay is restricted to the recorded branches: a plan that goes beyond
them earns nothing, and a failure is evidence about one attempt. A separate
agent rewrites the policy while the discovery agent and evaluator stay
fixed.

Two things change in a mathematical record. A checked theorem, a
counterexample on a stated domain or an exact computation replays
identically forever, and it is a premise in every other world, so the
support of the record is closed under proof. Only a failed attempt behaves
like a stored outcome of a stochastic agent. And the reader of the record
here is the agent that makes the next attempt; the
[proof workbench](../../../scripts/proof_workbench.py) records moves and
kernel verdicts and, by its own contract, does not search, rank or decide.
So the replay below is a reading that changes where the next attempt goes,
and the attempt then follows.

## Method

Four readers each took two or three worlds, read the short paper and the
long record at commit `5d82dfac`, and classified every recorded route by how
it closed:

| class | meaning |
|---|---|
| `proved` | a theorem in the record, including exact equivalences |
| `obstruction_proved` | a theorem ruling out a class of arguments or objects on stated hypotheses |
| `counterexample` | an explicit object refuting a statement on an exact domain |
| `finite_outcome` | an exact computation with a stated finite domain |
| `attempt_closed` | a route that stalled, used too weak an estimate or stopped, with no proof that it cannot work |
| `superseded` | replaced by an equivalent or stronger formulation |
| `out_of_support` | named or implied by the record but never tried |

Only the first four close anything, and only on their own hypotheses,
domain and representation. A stalled route keeps its parent idea eligible
until the cause of the stall is located. The readers then applied three
further rules taken from the replay prompts in the source paper's Appendix B:
separate a flawed idea from a good idea let down by an estimate; when a
mechanism has been refined many times with flattening returns, try a
structurally different one; and credit nothing to a route that was never
tried. [`routes.json`](routes.json) records the decisive rows with their
loci.

## What the replay found

`python3 check_routes.py` reads every cited record at the pinned commit and
confirms each quoted phrase and each absence claim. Across the rows kept in
`routes.json` (70 rows over the eight worlds and the synthesis) the classes
are 21 proved, 16 obstruction_proved, 5 counterexample, 4 finite_outcome,
11 attempt_closed, 4 superseded and 9 out_of_support.

**R1, a stall that was specific to one world.** The Problem 251 record tried
to force a repeated tail under rationality and stopped because its tails are
unbounded and their coefficients cannot be read back from them (long record,
"Repeated tail values"). The Problem 269 record had kept Erdős's
distinct-height assertion as an attributed historical claim and proposed
only a function-theoretic route (long record, Problem 34). In the
distinct-height sum each running least common multiple counts once, so after
grouping terms into dyadic shells the normalised tails lie in
[3/10, 13/15], and the five possible shell types have pairwise disjoint
images. A tail therefore determines its whole future, rationality forces a
repeated tail, and the shell word would be eventually periodic, which the
irrationality of log 2 / log 3 forbids. For the repeated sum of the catalogue
problem the numerators grow quadratically (short paper, bound 90B(a+1)²),
the integer states are unbounded, and the argument stops there.

**R2, a local optimum in one mechanism.** The chain-transcendence line had
refined Mahler's method from eventually doubling ratios to periodic ratio
blocks and recorded nonperiodic ratio words at base 4/3 as its first open
case. None of the synthesis paper, the Problem 257 records or the Problem
1049 records mentions a Subspace, S-unit or Ridout argument. Two readers
independently replaced the engine: in S-unit coordinates the Subspace
Theorem credits the p-adic smallness that a one-form archimedean estimate
cannot see, and the theorem above follows for every chain at every rational
base.

**R3, an estimate that failed on coefficient size.** The Problem 249 record
applied Erdős's 1948 divisibility argument to the totient and recorded why it
stops: a block of totients divisible by 2^L needs 2^L ≤ N + L, so the tail of
the unreduced coefficients stays above 1. Reducing the coefficients removes
that obstruction. With a_n = φ(n) mod 2^{κ(n)} and 2^{κ(n)} = o(log n), prime
factors of Fermat numbers give, by the Chinese remainder theorem, blocks in
which 2^j divides a_{N+j} for every j ≤ L, and Erdős's argument then shows
that Σ a_n 2^{−n} is rational exactly when a_n vanishes for all large n. So
the series is irrational whenever κ(3^k) ≥ 2 infinitely often, which extends
the short paper's bounded-residue theorem to slowly growing moduli. This is
an ordinary proof from classical ingredients; it waits for propagation into
the Problem 249 long record, whose owner is working on that paper now.

## Reproduce

```sh
python3 research/experiments/replay_worlds/check_routes.py
python3 research/experiments/replay_worlds/test_check_routes.py
```

The checker needs a clone with full history, because it reads the records
at commit `5d82dfac`; a shallow clone fails with a message saying so. The
mathematical results carry their own exact checks in the directories named
above.

## Limits

The readers are the same kind of agent that wrote the record, reading it at
one commit. The replay changed where two attempts went and records what they
produced; it measures no exploration policy and supports no claim that this
reading outperforms another. `routes.json` keeps the decisive rows; the
eight records hold more routes than it lists. The two theorems are ordinary proofs; their
papers state their evidence classes, attribution and the literature searched.
