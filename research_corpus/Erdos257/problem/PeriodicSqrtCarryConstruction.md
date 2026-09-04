# Periodic digits with a positive-density square-root carry

## Status

This began as a constructive counterexample route outside the bounded-carry
class.  Exact prefix-tree enumeration has now classified the finite mechanism:
the apparent offline MILP freedom is a thin terminal-carry cylinder around the
ordinary greedy prefix of the same rational target.  A compatible prefix is
frozen through rank 300,000 and extends exactly through rank 500,000, but this
is a long greedy-survival certificate rather than a structurally distinct
construction.  It is not an infinite support or a solution of Erdős 257.

The durable instrument is
`scripts/periodic_sqrt_carry_milp.py`.  Its three current receipts are

    state/formal_math/erdos257_period_noncollapse/periodic_sqrt_carry_milp_receipt.json
    state/formal_math/erdos257_period_noncollapse/periodic_sqrt_carry_milp_extension_400000_receipt.json
    state/formal_math/erdos257_period_noncollapse/periodic_sqrt_carry_milp_extension_500000_receipt.json.

Each receipt contains the complete integer carry, a packed Boolean support,
source and payload hashes, exact recurrence validation, and—on an extension—
hashes and bytewise checks for the cropped frozen prefix inherited from the
previous receipt.

The classifier is `scripts/periodic_carry_tree_collapse.py`, with receipt

    state/formal_math/erdos257_period_noncollapse/periodic_carry_tree_collapse_receipt.json.

## 1. The exact construction problem

Fix the period-22 word

    epsilon = overline(0000100101001011000101),

whose binary value is the reduced rational

    y = 152261 / 4194303.

For integers `C_0=0,C_1,...` define

    tau(n) = 2 C_(n-1) + epsilon_n - C_n.             (1)

We ask that `tau` have a Boolean Möbius ancestor:

    b_n = sum_(d|n) mu(n/d) tau(d) in {0,1},          (2)

with `b_1=0`.  Equivalently,

    tau(n) = sum_(d|n) b_d.                           (3)

The earlier finite-state search fixed `C_n` in a bounded set.  That is the
wrong infinite class: an eventually periodic or bounded carry forces finite
support by the existing common-multiple theorem.  The new pointwise conditions
are instead

    0 <= C_n <= floor(sqrt(n)) + 1,                   (4)

and, at every dyadic checkpoint `H>=64`,

    sum_(n<=H) b_n >= H/4.                            (5)

Thus the search permits an aperiodic unbounded carry but builds tempering and
infinitude directly into the finite tree.

## 2. Why an infinite branch would be a counterexample

Multiply (1) by `2^-n` and sum through `N`.  The carry terms telescope:

    sum_(n<=N) tau(n)/2^n
      = sum_(n<=N) epsilon_n/2^n - C_N/2^N.           (6)

If compatible solutions exist along an unbounded frozen frontier, their union
is a single Boolean sequence `b`.  Condition (5) makes its support infinite.
Condition (4) gives `C_N/2^N -> 0`.  Passing to the limit in (6) and using the
Lambert divisor regrouping (3) gives

    sum_(d:b_d=1) 1/(2^d-1)
      = sum_(n>=1) tau(n)/2^n
      = sum_(n>=1) epsilon_n/2^n
      = 152261/4194303.                               (7)

That would be an explicit infinite Boolean support with rational Mersenne sum,
so it would disprove Erdős 257.

There is also a nonconstructive finite-tree consumer.  At each rank the bounds
leave finitely many carry/support choices, and all constraints through rank `N`
depend only on that prefix.  Therefore feasibility at every depth with the same
pointwise conditions would yield an infinite branch by König's lemma.  The
receding-horizon computation below grows one compatible frozen prefix rather
than sampling unrelated feasible nodes.  Section 5 records why this no longer
counts as evidence for a separate rounding mechanism: away from the terminal
suffix, the frozen prefix is exactly the ordinary greedy word.

## 3. What the computation established

The relaxed class is genuinely larger than the bounded-carry fit.  With the
same period-22 word, the exact MILP is feasible at ranks 400, 2,000, 20,000,
100,000, 200,000, 300,000, 400,000, and 500,000 under (4).  At rank 2,000 one
unconstrained feasible point already used carry 37, so the old height-one no-go
does not classify these solutions.

An important negative result changed the algorithm.  The minimum-total-carry
node at rank 200,000 had `C_200000=0` and was infeasible already at rank 200,001.
Large finite feasibility alone therefore does not identify an extendable branch.
The optimizer had spent the terminal reserve.

The repaired algorithm solves with look-ahead and freezes only an earlier
prefix:

1. solve through 300,000;
2. freeze its first 200,000 carry and support values, then solve through 400,000;
3. freeze the resulting first 300,000 values, then solve through 500,000.

The receipts verify both extension edges exactly.  Consequently one fixed
prefix through rank 300,000 has a certified continuation through rank 500,000.
On the frozen prefix it has 149,525 selected exponents (density `0.4984167`) and
maximum carry 42.  The full look-ahead solution has 249,606 selected exponents
(density `0.499212`) and maximum carry 44, while its permitted bound at the end
is 708.

## 4. Structural probes on the frozen prefix

The candidate does not collapse to an automatic or multiplicative rule.  Across
the 22 residue classes, support densities range only from about `0.494` to
`0.507`.  For multipliers `k=2,...,16`, correlations between `b_n` and `b_(kn)`
lie between `-0.0078` and `0.0074`.  The tempting online rule “select `b_n=1`
whenever the raw carry is positive” fails at 250,113 of the first 500,000 ranks:
the construction must sometimes retain carry to prevent a future divisor-load
underflow.

The carry is far smaller than the imposed square-root ceiling.  Its maximum on
successive dyadic bands is

    2, 3, 5, 6, 7, 10, 13, 16, 20, 24, 30, 36, 42,

and its mean rises by roughly `0.34` per doubling.  This suggests a logarithmic
discrepancy scale, but no logarithmic bound is claimed from the finite data.

## 5. Exact terminal-cylinder classification

The classifier enumerates every Boolean/carry prefix under (1)--(4), retaining
the entire support word rather than quotienting states heuristically.  For the
period-22 target it is nonempty through rank 32,768.  From rank 7 onward the
terminal carries are exactly the full interval

    {0,...,floor(sqrt(n))+1},

with precisely one prefix for each terminal carry.  At rank 32,768 this is 183
prefixes with terminal carries `0,...,182`.  Those prefixes share their first
32,760 support bits; only the final eight bits vary.  Their selected counts lie
between 16,258 and 16,264.

The common 32,760-bit prefix agrees bit-for-bit with the canonical
superincreasing greedy expansion of `152261/4194303`, computed independently by
directed dyadic intervals.  Thus the MILP's many variables do not describe
many competing global constructions.  They describe the already-forced greedy
prefix plus a vanishingly thin horizon suffix in which terminal carry can be
spent.

The same enumeration was run on the `1/21` periodic word `000011` as a control.
At every shared dyadic checkpoint through 8,192 it has exactly the same carry
bound, state count, full terminal interval, and one-prefix-per-carry geometry.
Its common prefix likewise agrees exactly with its ordinary greedy expansion.
The support densities differ, but the terminal-cylinder mechanism does not.

## 6. Mechanism decision

This eliminates the proposed *distinct* offline-rounding mechanism.  Allowing
square-root carry remains outside the bounded/eventually-periodic carry no-go,
and an all-depth branch would still be a counterexample by (7).  But the finite
MILP chain supplies no new way to obtain that branch: it is another coordinate
for long survival of a rational greedy orbit, with the same expanding boundary
mode already present at `1/21`.

Consequently, neither a deeper standalone MILP nor another frozen-prefix
extension counts as progress.  A revival must introduce an actual all-depth
producer—for example, a recursive support law or a proof that the common greedy
prefix continues forever—rather than terminal look-ahead.  The exact finite
tree and directed-interval comparison make this classification reproducible;
they do not claim an Erdős 257 conclusion.
