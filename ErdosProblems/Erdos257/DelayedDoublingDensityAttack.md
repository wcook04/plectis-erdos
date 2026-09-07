# Delayed doubling density: a source-sensitive zero-flux candidate

Status: exact deductions plus exact finite computation, 2026-08-20.  This is
not a reformulation of the final-gap condition.  It isolates a new sufficient
law which couples the period-six source to the fact that the correction made
by a rank `n` starts only at binary depth `2n`.  The proposed all-depth density
bound is not proved.

## 1. The delayed channel

Write

\[
 w_n=\frac1{2^n-1}=2^{-n}+e_n,
 \qquad
 e_n=\frac1{2^n(2^n-1)}=\sum_{j\ge2}2^{-jn}.
\]

Let `b_n` be the actual greedy bit for `1/21`, and put

\[
 B(N)=\sum_{n\le N}b_n.
\]

The first nonzero binary coefficient of `e_n` is at position `2n`.
Consequently the unresolved correction from ranks above `K` satisfies the
sharp scale separation

\[
 0<\sum_{n>K} e_n<\frac{2}{3}\,4^{-K}.
 \tag{1}
\]

At depth `2K`, (1) is less than one binary cell.  This localises the numerical
crossing, but it does **not** determine the selected word in `(K,2K]`: a
sub-cell change can propagate through an arbitrarily long binary suffix.  The
exact relation in `DelayedDoublingBorrowCocycleAudit.md` says that the bounded
quotient completion is the actual block numeral plus the endpoint defect.
Thus half-scale ancestry controls a full-scale word only after the resulting
carry cocycle is retained; deleting it recreates the moving-hole obstruction.

The equality

\[
 \frac1{21}=0.\overline{000011}_2
\]

supplies `2K/3+O(1)` source ones through depth `2K`.  This suggests the
following source-sensitive density law:

\[
 \boxed{
   B(N)\le \left\lfloor\frac N3\right\rfloor
          +B(\lfloor N/2\rfloor)+2.}
 \tag{DD}
\]

Equivalently, a doubling block contains at most two selected ranks for every
three positions, up to a constant endpoint allowance.  Unlike a pointwise
margin or pulse estimate, (DD) compares two scales and would directly rule
out the homogeneous all-take phase.

## 2. Why (DD) solves the prescribed target

Iterating (DD) gives

\[
 B(N)
 \le \sum_{j<\lceil\log_2N\rceil}
       \left(\frac{N}{3\,2^j}+2\right)+O(1)
 \le \frac{2N}{3}+2\lceil\log_2N\rceil+O(1).
 \tag{2}
\]

Hence the number of skipped greedy ranks through `N` tends to infinity.  The
checked cofinal-skip consumer in `GreedyAchievementSet.lean` then proves

\[
 \frac1{21}\in\texttt{mersenneAchievementSet}.
\]

Thus (DD), with any fixed additive constant, is a genuine sufficient theorem
for an explicit rational infinite Boolean Mersenne subsum.  It is stronger
than necessary but is not equivalent at one rank to the desired conclusion:
it asserts a uniform multiscale density restriction.

## 3. Exact finite evidence

The integer-enclosure greedy algorithm, using precision `2N+64`, verifies
(DD) through `N=200000`.  The maximum of

\[
 B(N)-\lfloor N/3\rfloor-B(\lfloor N/2\rfloor)
\]

in that range is exactly `2`, first attained at `N=11`.  The independent
odd-depth quotient-suffix recurrence from
`TwentyOneDensityInvariantAttack.md` verifies an analogous row bound through
`K=200000`; its maximum value of

\[
 3\,\operatorname{popcount}(H_K)-2K
\]

is `5`, attained at `K=5`.  The suffix word `H_K` is a quotient-row
completion, not the literal actual greedy block `(K,2K]`; without proved
all-depth alignment those two finite observations must not be identified.
Both calculations use integer arithmetic.  They are theorem-selection
evidence, not a proof.

## 4. The seam that a proof must amortise

A naive digit-sum lemma is false.  For an arbitrary prefix set `S`, subtracting

\[
 \sum_{n\in S}e_n
\]

from `1/21` can create a borrow through a long zero suffix and increase the
binary digit count by much more than `|S|`.  Exact enumeration already gives
such examples with `S={5}`.  Therefore (1) plus ordinary digit-sum
subadditivity does not prove (DD).

The quotient-suffix recurrence contains a model of the missing feedback.  If
rank `d` is selected in its lower word, it contributes two units to the
endpoint pulse at `2d` on the very next odd-depth recut.  In the notation of
`TwentyOneDensityInvariantAttack.md`,

\[
 L_K=2\,\operatorname{supportCoeff}(P_K,2K+2)
      +\operatorname{supportCoeff}(P_K,2K+3),
\]

and selection of `K+1` guarantees a contribution of `2` to `L_K` because
`K+1` divides `2K+2`.  For the actual support, the same self-double divisor
incidence is exact at the coefficient level, but transporting an amortised
suffix estimate from the quotient completion to the real greedy word is part
of the theorem still required.  Long binary borrows therefore cannot be
treated as free: the ones they create become divisor ancestors which feed
load back into later recuts.

The missing theorem is an amortised borrow law, not a pointwise pulse bound:

> Across a doubling recut, the carry loss between the quotient completion and
> the actual selected block is paid by the unused quotient-density slack,
> while self-double and older-divisor loads transport the remaining debt.

Proving this compensated statement would yield (DD).  Absolute bounded carry
is false: at `K=8600`, adding an endpoint defect of only `5` generates
fourteen binary carries and changes the two popcounts by twelve.  The quotient
word has `1495` units of density slack there, so the correct potential must
compare carry loss to slack rather than bound carry loss by a constant.

## 5. Exact borrow-area/divisor-incidence law

There is an exact form of the required amortisation.  Let `t_n` be the
period-six binary digit of `1/21`, let

\[
 f(n)=\sum_{d\mid n}b_d,
 \qquad
 h(n)=f(n)-b_n=\sum_{\substack{d\mid n\\d<n}}b_d,
\]

and let `Q_n=twentyOneGreedyDefect n`.  The checked one-step law is

\[
 Q_n=2Q_{n-1}+t_n-f(n),\qquad Q_0=0.                 \tag{3}
\]

Substituting `f(n)=b_n+h(n)` into (3) and summing gives

\[
 B(N)-T(N)
 =-\sum_{n\le N}h(n)+\sum_{n<N}Q_n-Q_N,             \tag{4}
\]

where `T(N)=sum_(n<=N) t_n`.  Swapping the finite divisor sum gives

\[
 \sum_{n\le N}h(n)
 =\sum_{\substack{d\le N/2\\b_d=1}}
   \left(\left\lfloor\frac Nd\right\rfloor-1\right). \tag{5}
\]

Since adding `B(floor(N/2))` to (5) replaces every `floor(N/d)-1`
by `floor(N/d)`, the stronger period-native form of (DD),

\[
 B(N)\le T(N)+B(\lfloor N/2\rfloor)+2,               \tag{6}
\]

is exactly the borrow-area inequality

\[
 \boxed{
 \sum_{n<N}Q_n
 \le Q_N+
   \sum_{\substack{d\le N/2\\b_d=1}}
      \left\lfloor\frac Nd\right\rfloor+2.}          \tag{BA}
\]

This is not a single-row restatement of membership.  Its left side is the
entire accumulated binary-borrow area; its right side is the complete table
of multiples generated by the half-scale Boolean ancestry.  It therefore
retains exactly the joint phenomenon which pointwise pulse and margin bounds
separate.

There is also a minimal cocycle form.  Define

\[
 P_N=T(N)+B(\lfloor N/2\rfloor)-B(N).
\]

Then

\[
 P_N-P_{N-1}
 =t_N-b_N+\mathbf1_{2\mid N}\,b_{N/2}.               \tag{7}
\]

Thus every selected digit costs one unit, while a source `1` or a selected
half-ancestor supplies one unit.  Exact computation through `N=200000`
finds `P_N>=-2`.  The desired new theorem can be stated as a bounded-debt
law for this source/ancestor cocycle, or equivalently as (BA).  Equation (4)
shows why it must be proved with divisor feedback: the long-borrow area
`sum Q_n` is the only term capable of violating it.

There is a slightly stronger reservoir which keeps the endpoint defect
visible.  Put

\[
 R_N=P_N+3-Q_N.
\]

Combining (3) and (7) gives the exact source-free update

\[
 R_N-R_{N-1}
 =h(N)+\mathbf1_{2\mid N}b_{N/2}-Q_{N-1}.             \tag{8}
\]

Thus proper selected divisors and the self-double ancestor are deposits,
while the preceding quotient defect is the withdrawal.  The source clock has
not disappeared: it is stored in the level `P_N`, and (8) says exactly how
divisor ancestry repays its borrow debt.  The assertion

\[
 \boxed{R_N\ge0}                                       \tag{R}
\]

would imply `P_N>=-3`, hence (DD) with constant `3`.  Exact computation
through `N=100000` finds `min R_N=0`, attained only at `N=9,13` in that
range; the largest quotient defect is `33`.  This remains finite evidence.

## 6. Support monotonicity and the greedy-exchange seam

For an arbitrary Boolean support `A`, retain the same definitions and write
`R_A(N)` for the reservoir.  If a previously absent rank `d<=N` is inserted,
then its contribution to the quotient defect is

\[
 q_d(N)=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor
       =\sum_{1\le j\le N/d}2^{N-jd}.                  \tag{9}
\]

The two counting terms in `P_N` change by
`1_(2d<=N)-1`.  Therefore the exact insertion law is

\[
 R_{A\cup\{d\}}(N)-R_A(N)
 =q_d(N)+\mathbf1_{2d\le N}-1
 =\begin{cases}
    q_d(N)-1,&d\le N<2d,\\
    q_d(N),&2d\le N.
  \end{cases}                                           \tag{10}
\]

This is always nonnegative.  In particular, the reservoir is monotone under
support inclusion even though its recurrence (8) has a negative borrow-area
term.  Formula (10) is also the exact place to use real greedy
complementarity: the actual greedy word is lexicographically maximal among
all Boolean supports whose real Mersenne sum is at most `1/21`.  A proof of
(R) can therefore be sought as a finite exchange theorem: show that inserting
the first skipped-affordable rank pays, in the coefficients (10), for every
later rank which feasibility forces one to remove.

The required exchange statement is in fact exact.  The coefficient word in
(10) is strictly superincreasing in `d`:

\[
 c_{d,N}>\sum_{e=d+1}^{N}c_{e,N}\qquad(d<N),            \tag{11}
\]

where `c_{d,N}` denotes the right side of (10).  For `2d<=N`, (11) follows
from the Lean-checked `localMersenneQuotient_dominanceGap`; for `N<2d` it is
the elementary identity

\[
 (2^{N-d}-1)-\sum_{e=d+1}^N(2^{N-e}-1)=N-d>0.
\]

Consequently lexicographic maximality makes the actual greedy prefix maximize
`R_A(N)` over every real-feasible Boolean support, or equivalently minimize
`Q_A(N)+#(A intersect (N/2,N])`.  The complete proof is recorded in
`GreedyReservoirVariationalPrinciple.md`.  This resolves the exchange use of
real greedy complementarity, but not the sign: exhibiting a feasible
comparator with nonnegative reservoir is equivalent to the desired assertion.

## 7. Adversarial boundary

The law cannot follow from greedy complementarity alone.  The cofinite greedy
countermodels in `GreedyComplementarityFluxAudit.md` have positive flux and
eventually satisfy `B(N)-B(N/2)\sim N/2`, violating (DD).  Their targets are
irrational.  Conversely, `A={d:d>=7}` uses the exact period-six source,
Boolean divisor feedback, and a nonnegative defect at every depth, but already
violates (DD) at `N=18`; it is not the real greedy orbit because it skips an
affordable early rank.  Hence a proof of (DD) must use simultaneously:

1. the exact period-six source `000011`; and
2. the divisor feedback generated by the same selected word; and
3. the exact real greedy take/skip comparison.

This is precisely the joint information absent from the local energy and
scalar margin arguments.
