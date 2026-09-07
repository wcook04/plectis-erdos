# The finite-injury boundary for moving-half quotient greedy

Status: exact theorem and exact countermodel, 2026-08-21.  Genuinely new
moving-half injuries at unbounded ranks already force a real Mersenne
representation.  If they do not occur, the fixed-horizon lower words
stabilise uniformly.  That uniform stabilisation does **not** prove the
fixed-horizon comparator: on a fatal real-greedy orbit it instead makes the
comparator fail by an exponentially growing margin.

The theorem applies to the target \(1/465\).  An existing exact fatal
unit-fraction example supplies a countermodel to any target-independent
finite-injury closure.

## 1. Real and quotient greedy words

Let \(x\in(0,1)\), put

\[
 w_d=\frac1{2^d-1},\qquad
 H_N=\lfloor2^Nx\rfloor,\qquad
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

Write \(b_1,b_2,\ldots\) for ordinary real greedy applied to \(x\), and
let

\[
 e_d=x-\sum_{a\leq d}b_aw_a
\]

be its residual.  At horizon \(N\), run Boolean integer greedy on \(H_N\)
using only \(q_{N,1},\ldots,q_{N,M}\), where
\(M=\lfloor N/2\rfloor\).  Denote this lower-half word by
\(c^{(N)}_1,\ldots,c^{(N)}_M\), and its final integer remainder by \(R_N\).

Assume that real greedy never encounters an exact comparison equality.
This holds for \(x=1/465\) by the finite-support exclusion in
`AnchorFourFiveCorridorCompatibility.md`.

For every fixed \(D\), one has

\[
 (c^{(N)}_1,\ldots,c^{(N)}_D)
 =(b_1,\ldots,b_D)                                   \tag{1}
\]

for all sufficiently large \(N\).  Indeed,
\(H_N/2^N\to x\) and \(q_{N,d}/2^N\to w_d\); induction on \(d\), using the
nonzero real comparison margin, proves (1).

## 2. The direction of a first injury

Suppose the two words agree before rank \(d\).  Put

\[
 S=H_N-\sum_{a<d}b_aq_{N,a},\qquad
 \alpha_N=\{2^Nx\},\qquad
 \Phi=\sum_{a<d}b_a\left\{\frac{2^N}{2^a-1}\right\}.
\]

The exact phase identity is

\[
 2^Ne_{d-1}=S+\alpha_N-\Phi.                         \tag{2}
\]

If real greedy takes rank \(d\), then

\[
 S+\alpha_N-\Phi
 \geq q_{N,d}+\left\{\frac{2^N}{2^d-1}\right\}.
\]

Since \(S\) is an integer, \(\alpha_N<1\), and both fractional-phase terms
are nonnegative, this implies \(S\geq q_{N,d}\).  Quotient greedy therefore
takes rank \(d\) as well.  Hence a first disagreement has only one possible
direction:

\[
 \boxed{c^{(N)}_d=1,\qquad b_d=0.}                    \tag{3}
\]

In particular, every first injury rank is an actual real-greedy skip.

## 3. Infinite injury is already a witness

Suppose there are arbitrarily large horizons at which the lower-half word
does not agree with the real word through its midpoint.  Let \(d_N\) be the
first disagreement along a chosen unbounded sequence of such horizons.
Pointwise stabilisation (1) forces \(d_N\to\infty\).  By (3), real greedy
skips every rank \(d_N\), and therefore

\[
 0\leq e_{d_N}=e_{d_N-1}<w_{d_N}\longrightarrow0.    \tag{4}
\]

The residuals \(e_d\) are nonincreasing and nonnegative.  Equation (4)
proves

\[
 \sum_{d\geq1}b_dw_d=x.                              \tag{5}
\]

For \(x=1/465\), the support in (5) is infinite by the same finite-support
exclusion.  Thus an infinite sequence of genuinely new moving-half injuries
solves the problem directly; no diagonal small-margin estimate is needed.

## 4. The finite-injury regime

Suppose instead that (5) fails, and put

\[
 L=\lim_{d\to\infty}e_d>0.                           \tag{6}
\]

Since \(w_d\to0\), real greedy takes every sufficiently late rank.  Let
\(d_0\) be its final skipped rank.  Pointwise stabilisation gives agreement
through \(d_0\) at every sufficiently large horizon.  After that, induction
using the take-preservation argument of Section 2 gives agreement at every
remaining rank through the moving midpoint.  Consequently

\[
 \boxed{
 (c^{(N)}_1,\ldots,c^{(N)}_M)=(b_1,\ldots,b_M)
 }                                                   \tag{7}
\]

for all sufficiently large \(N\), uniformly in
\(M=\lfloor N/2\rfloor\).

Thus finite injury really does imply the desired uniform word agreement.
It does not imply the desired comparator.

Let

\[
 T_M=\sum_{d>M}w_d,\qquad
 C_N=\sum_{d>M}q_{N,d}=2^{N-M}-1.
\]

Because every rank beyond \(d_0\) is selected, \(e_M=L+T_M\).  Splitting
the scaled real weights into integer and fractional parts gives, under (7),

\[
 R_N-C_N
 =2^NL-\alpha_N
 +\sum_{d\geq1}b_d
   \left\{\frac{2^N}{2^d-1}\right\},                \tag{8}
\]

where the bits above \(M\) are all one.  In particular,

\[
 R_N-C_N\geq2^NL-1.                                 \tag{9}
\]

Therefore \(R_N>C_N+K_N\) eventually for every buffer
\(K_N=o(2^N)\), including \(K_N=\lfloor N/20\rfloor\).

The same calculation controls diagonal small-margin events.  At horizon
\(2d\), the diagonal remainder \(\rho_d\) satisfies

\[
 \rho_d\geq4^dL-1.                                  \tag{10}
\]

The selected count is at most \(d\), so \(\rho_d>d\) for all sufficiently
large \(d\).  Hence only finitely many selected diagonal small-margin events
can occur on a fatal orbit, even though the moving-half comparator fails for
every sufficiently large horizon.

## 5. Exact countermodel

`UnitFractionDyadicSliverCounterexample.md` gives an exact odd unit fraction
\(x=1/D\) with

\[
 D=\frac{2^{81803}-50847}{106907}
\]

whose real-greedy residual at the skipped rank \(81803\) exceeds the entire
remaining Mersenne tail.  The accompanying exact-integer certificate proves
this strict fatal inequality.  Greedy therefore takes every later rank and
leaves a positive limit \(L\).

Equations (7)--(10) apply to this explicit target.  Its moving-half quotient
words eventually agree uniformly with its real-greedy word; it has only
finitely many selected diagonal small-margin events; nevertheless
\(R_N>C_N+\lfloor N/20\rfloor\) for every sufficiently large \(N\).

This is an exact countermodel to a target-independent finite-injury closure.
For \(1/465\), finite injury reduces the remaining branch to the assertion
\(L>0\); it does not rule that branch out.  Any closure of the fixed target
must therefore use arithmetic special to \(465\), not finite-injury logic
alone.
