# The shifted quotient comparator: an exact horizon monotonicity law

Status: exact deductions and an exact cross-target obstruction, 2026-08-20.
The desired square-root bound on the terminal remainder and upper digit count
is not proved here.  The main positive result is an all-depth theorem: the
shifted quotient-greedy words are strictly increasing in lexicographic order
as the horizon grows.  The proof uses the same divisor pulse which obstructs
fixed-row arguments, but here the square-root shift dominates it uniformly.

## 1. Setup

Put

\[
 H_N=\left\lfloor\frac{2^N}{21}\right\rfloor,
 \qquad S_N=2\lfloor\sqrt N\rfloor+5,
 \qquad C_N=H_N-S_N,
\]

and

\[
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

For every horizon with `C_N>=0`, run descending Boolean greedy on the ordered
weights `q_(N,1),...,q_(N,N)`.  Denote the resulting word by `x^(N)` and its
terminal integer remainder by

\[
 r_N=C_N-\sum_{d\leq N}x^{(N)}_dq_{N,d}\geq0.
\]

Let `t_n` be the period-six binary digit of `1/21`, so that

\[
 H_{N+1}=2H_N+t_{N+1}.
\]

Write `T(N)=sum_(n<=N)t_n` for its prefix digit count.

The quotient weights satisfy the exact divisor-pulse recurrence

\[
 q_{N+1,d}=2q_{N,d}+\mathbf 1_{d\mid N+1}.       \tag{1}
\]

## 2. The old word is always feasible at the next horizon

Define the selected-divisor pulse

\[
 F_N=\sum_{\substack{d\leq N\\d\mid N+1}}x^{(N)}_d
\]

and the fresh shift allowance

\[
 D_N=t_{N+1}+2S_N-S_{N+1}-F_N.                 \tag{2}
\]

Equation (1) gives the exact identity

\[
 C_{N+1}-\sum_{d\leq N}x^{(N)}_dq_{N+1,d}
 =2r_N+D_N.                                    \tag{3}
\]

The right side is not merely nonnegative.  It is at least `3`.  To see this,
write

\[
 a=\lfloor\sqrt N\rfloor,
 \qquad b=\lfloor\sqrt{N+1}\rfloor.
\]

Every divisor counted by `F_N` is a proper divisor of `N+1`, and ranks `1`
and `N+1` are absent.  Pairing complementary divisors therefore gives

\[
 F_N\leq2b-2.                                   \tag{4}
\]

If `N+1` is not a square, then `b=a` and

\[
 2S_N-S_{N+1}=2a+5,
\]

so (2)--(4) give `D_N>=7`.  If `N+1` is a square, then `b=a+1` and

\[
 2S_N-S_{N+1}=2a+3=2b+1,
\]

so `D_N>=3`.  The source bit can only increase these bounds.

Thus every old comparator word, padded by a zero in the new coordinate, is
strictly below the new integer target.  This conclusion does not assume
`r_N=0`.

## 3. All-depth lexicographic monotonicity

Descending Boolean greedy with positive weights is the lexicographically
largest feasible Boolean word.  Indeed, at a rank where greedy writes zero,
the current weight exceeds the remaining capacity; a competitor agreeing at
all earlier ranks cannot write one there.

Apply this observation at horizon `N+1` to the padded word from Section 2.
It is feasible by (3), and the unused capacity is at least `3`, so the final
unit weight is affordable if no earlier change occurs.  Consequently

\[
 \boxed{x^{(N)}0<_{\rm lex}x^{(N+1)}}.          \tag{5}
\]

This proves the recut monotonicity for the raw shifted quotient comparator at
every depth.  It is distinct from the false doubled-comparator monotonicity
recorded in `ThresholdComparatorFalsifier.md`: its proof depends on the
specific shift recurrence and the uniform proper-divisor bound.

For each fixed `K`, the prefixes `x^(N)|_[1,K]` therefore form a
nondecreasing sequence in the finite lexicographic order on `{0,1}^K`.
They eventually stabilise.  Hence the shifted rows have a canonical limiting
Boolean word `A` without passing to a subsequence.

This limiting word also obeys the real greedy decision rule at every strict
decision.  Fix `d` after the preceding `d-1` coordinates have stabilised and
divide the integer affordability inequality at rank `d` by `2^N`.  Since

\[
 \frac{q_{N,e}}{2^N}\longrightarrow\frac1{2^e-1},
 \qquad \frac{C_N}{2^N}\longrightarrow\frac1{21},
\]

the limiting digit is one when the preceding real prefix plus the rank-`d`
atom is strictly below `1/21`, and zero when it is strictly above.  The only
unclassified seam is exact finite saturation, where that finite prefix
already has value `1/21`.  Thus, away from an exact finite representation,
`A` is the actual real greedy word rather than an unrelated compactness
limit.

## 4. The terminal remainder is exactly the surviving fatal mode

Let

\[
 \phi_{N,d}=\left\{\frac{2^N}{2^d-1}\right\}.
\]

The quotient identity gives

\[
 \sum_{d\leq N}\frac{x^{(N)}_d}{2^d-1}
 =\frac{C_N-r_N+\sum_dx^{(N)}_d\phi_{N,d}}{2^N}. \tag{6}
\]

There are at most `N` fractional terms and each is less than one.  The
Mersenne tail is uniformly summable, so prefix stabilisation from (5) implies
that the left side of (6) converges to

\[
 \sum_{d\in A}\frac1{2^d-1}.
\]

Since `S_N/2^N` and `N/2^N` tend to zero, (6) proves the exact limit law

\[
 \boxed{
 \frac{r_N}{2^N}\longrightarrow
 \frac1{21}-\sum_{d\in A}\frac1{2^d-1}.}       \tag{7}
\]

Thus the comparator has only one possible macroscopic obstruction: its
terminal remainder retains the same homogeneous fatal mode as the real
greedy orbit.  In particular, the requested estimate

\[
 r_N+U_N\leq T(N)+O(\sqrt N)
\]

would kill that mode, but its `U_N` component is stronger than needed for
this purpose.  Already `r_N=o(2^N)` would force the limiting Boolean word to
have value `1/21`.  This is a genuine narrowing of the proof target: the
upper Hamming estimate is needed by the reservoir comparison, whereas the
monotone shifted rows themselves only need subexponential terminal defect.

The exact computations reporting `r_N=0` are therefore testing the strongest
possible version of the decisive assertion, not merely a convenient suffix
statistic.

## 5. A denominator-free digital theorem is false

The terminal-remainder assertion is source-specific.  Keep the same shift
`S_N`, but replace `1/21` by `1/7`.  Then

\[
 \left\lfloor\frac{2^N}{7}\right\rfloor=q_{N,3}.
\]

The shifted target `q_(N,3)-S_N` is below the rank-three coin, so descending
greedy skips that coin.  Even allowing every later coin, its remainder obeys

\[
 r_N\geq q_{N,3}-S_N-\sum_{d=4}^{N}q_{N,d}.     \tag{8}
\]

Now

\[
 q_{N,3}\geq\frac{2^N}{7}-1
\]

and, because `1/(2^d-1)<=(16/15)2^(-d)` for `d>=4`,

\[
 \sum_{d=4}^{N}q_{N,d}
 \leq2^N\sum_{d=4}^{\infty}\frac1{2^d-1}
 \leq\frac{2^{N+1}}{15}.
\]

Therefore

\[
 \boxed{r_N\geq\frac{2^N}{105}-S_N-1.}         \tag{9}
\]

The same square-root shift can coexist with an exponentially large terminal
remainder.  Hence neither the power-of-two upper row, the quotient recurrence,
nor the size of the shift can prove the desired estimate without using the
period-six `1/21` source and its selected-divisor feedback.

## 6. Remaining theorem

The raw shifted comparator no longer has a moving-recut ambiguity: (5)
settles its horizon direction exactly.  What remains is to show that the
limiting word in (7) has zero fatal gap.  The sharp observed statement is
`r_N=0`; the reservoir-compatible statement is

\[
 r_N+U_N\leq T(N)+O(\sqrt N);
\]

and the weakest statement sufficient through the monotone-limit route is
`r_N=o(2^N)`.  The cross-target bound (9) shows that any proof of one of these
must use more than generic coin-system or binary digit-sum estimates.
