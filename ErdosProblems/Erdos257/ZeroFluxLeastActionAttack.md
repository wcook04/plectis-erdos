# Zero flux and least-action: an audit

This note tests whether the homogeneous carry flux can be converted into a
least-action principle.  It separates an exact energy identity from the
additional comparison inequality that would be needed for a proof.

## 1. The normalized carry and its exact bridge

Put

\[
 C_N=\texttt{twentyOneGreedyCarry}(N),\qquad
 u_N=\frac{C_N}{2^N},\qquad
 E_N=\sum_{n=0}^{N}u_n^2.
\]

The checked theorem `twentyOneGreedyCarry_succ` gives

\[
 C_{N+1}=2C_N-21c_A(N+1),
\]

where (c_A=\texttt{supportCoeff}(A)) for the actual greedy support.  The
checked theorem `twentyOneGreedyCarry_eq_scaled_remainder_add_finitePrefixTail`
gives the exact nonnegative decomposition

\[
 C_N=21\left(2^N r_N+T_N\right),                         \tag{1}
\]

where (r_N=\texttt{greedyMersenneRemainder}(1/21,N)) and (T_N) is the
finite-prefix future-multiple tail.  Hence

\[
 u_N=21r_N+21\frac{T_N}{2^N}.                              \tag{2}
\]

The source theorem `twentyOneGreedyFinitePrefixTail_nonneg` makes the second
term nonnegative, while
`twentyOneGreedyFinitePrefixTail_le_two_sqrt_add_four` bounds it by

\[
 21(2\sqrt N+4)/2^N.                                      \tag{3}
\]

The remainder sequence is antitone and nonnegative by
`greedyMersenneRemainder_antitone` and
`greedyMersenneRemainder_nonneg`.  Let

\[
 g=\lim_{N\to\infty}r_N.
\]

Equations (2)--(3) therefore imply the exact asymptotic scaling

\[
 u_N\longrightarrow 21g.                                 \tag{4}
\]

No membership or survival assumption is used for this limit; only the
monotone remainder limit and the checked tail bound are required.

## 2. Energy law

The elementary Cesàro lemma for a convergent real sequence gives

\[
 \frac{E_N}{N+1}
 =\frac1{N+1}\sum_{n=0}^{N}u_n^2
 \longrightarrow (21g)^2.                                \tag{5}
\]

Thus the correct statement is

\[
 E_N/N\longrightarrow(21g)^2,
\]

with the immaterial (N/(N+1)) factor suppressed.  In particular,

\[
 E_N=o(N)\quad\Longleftrightarrow\quad g=0.               \tag{6}
\]

This is an exact zero-flux characterization, but it is still equivalent to
the original greedy-membership endpoint: `g=0` says that the greedy partial
sums converge to the target.  It must therefore be treated as a diagnostic
for whether a proposed inequality sees the homogeneous mode, not as progress
toward proving membership.  The existing theorem
`twentyOneGreedyCarry_scaled_tendsto_zero_of_mem` supplies the same boundary
direction in the checked corpus.

## 3. What least action would have to prove

The recurrence has the discrete flux balance

\[
 u_{N+1}-u_N=-\frac{21}{2^{N+1}}c_A(N+1).                 \tag{7}
\]

It follows that the actual greedy path is monotone in normalized carry, but
this is not a variational minimality statement.  A comparison path with fewer
selected ranks has a smaller subtraction in (7) and therefore a *larger*
future normalized carry.  A path with extra selected ranks is not admissible:
it may overshoot the target.  The greedy rule is locally minimal in the
remainder, not globally minimal in the quadratic energy (E_N).

The exact finite-prefix bridge also shows why a naive energy proof fails:

\[
 E_N=\sum_{n\le N}
 \left(21r_n+21T_n/2^n\right)^2.
\]

The cross term is positive, but the (r_n) and (T_n) terms are coupled by
divisor incidence.  No source theorem currently compares this sum with the
energy of another Boolean path having the same endpoint.

## 4. Adversarial counterexamples to naive minimality

The recurrence alone does not imply least action.  For an arbitrary binary
forcing word (b_n\in\{0,1\}), define (u_{n+1}=u_n-21b_{n+1}/2^{n+1}).  Two words can have the same terminal partial sum while their energies are ordered either way: moving a selected bit earlier lowers later (u_n) but can increase the early square, while moving it later has the opposite effect.  Thus “earliest admissible subtraction minimizes energy” is false without the Mersenne admissibility inequalities.

Likewise, normalized-carry antitonicity does not imply strict decay: a long run
with (c_A(n)=0) leaves (u_N) unchanged.  Such zero-pulse runs occur in
finite supports and in skipped gaps, so a putative strict comparison principle
would already fail on finite rows.

## 5. Best surviving conditional principle

The strongest useful statement from this coordinate is conditional:

> If one can construct, for every cutoff (N_0), an admissible Boolean
> continuation whose normalized carry has arbitrarily small terminal value
> without increasing the prefix energy by more than (o(N)), then the greedy
> path has zero flux and (6) gives (g=0).

No such comparison inequality is present in the finite-row or terminal-zero
modules inspected.  The energy law (5) is an exact reformulation, not a
reduction.  The only possible new content would be a global exchange
inequality respecting both the greedy remainder constraint and the
divisor/multiplicity pulses; local monotonicity is insufficient.
