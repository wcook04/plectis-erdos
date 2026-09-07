# Fractional remainders and threshold recuts

Status: exact finite identities and bounds, one exact counterexample, and
bounded exact computations, 2026-08-20.  The computations do not prove an
all-depth comparator inequality.

## 1. The divisor pulses cancel for a fixed word

Let `x` be a fixed finite Boolean word supported on ranks at least `2`.  Put

\[
 a_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor,
 \qquad
 \phi_{N,d}=\left\{\frac{2^N}{2^d-1}\right\},
\]

and write

\[
 Q_N(x)=H_N-\sum_d a_{N,d}x_d,
 \qquad
 F_N(x)=\sum_d\phi_{N,d}x_d,
\]

where `H_N=floor(2^N/21)`.  If `t_{N+1}` is the next binary digit of
`1/21`, then

\[
 Q_{N+1}(x)-F_{N+1}(x)
 =2\bigl(Q_N(x)-F_N(x)\bigr)+t_{N+1}.       \tag{1}
\]

Indeed,

\[
 a_{N+1,d}=2a_{N,d}+\mathbf 1_{d\mid N+1},
 \qquad
 \phi_{N+1,d}=2\phi_{N,d}-\mathbf 1_{d\mid N+1}.
\]

The same divisor incidence occurs with opposite signs and cancels in (1).
Thus no fixed-word evolution can cause a real-feasibility failure.  Such a
failure can arise only when the threshold algorithm changes the Boolean
word.

The fractional remainder is

\[
 \phi_{N,d}=\frac{2^{N\bmod d}}{2^d-1},      \tag{2}
\]

not `(2^(N mod d)-1)/(2^d-1)`.  Formula (2) is also valid when `d` divides
`N`; in that case the numerator is `1`.

## 2. A universal square-root bound

For every `N>=4`,

\[
 \sum_{d=2}^{N}\phi_{N,d}<2\lfloor\sqrt N\rfloor. \tag{3}
\]

To prove (3), put `R=floor(sqrt N)`.  For `N=qd+r`, with `0<=r<d`, set
`k=d-r`.  Since `d>=2`,

\[
 \phi_{N,d}=\frac{2^{-k}}{1-2^{-d}}
 \leq \frac43 2^{-k}.                         \tag{4}
\]

There are `R-1` ranks with `2<=d<=R`, and each contributes at most `2/3`.
For `d>R`, put `m=q+1`; then `k=md-N`.  The possible values of `m` lie in
`{2,...,R+1}`, and for fixed `m` the map `d -> k` is injective.  Hence the
contribution for each `m` is at most

\[
 \frac43\sum_{k\geq1}2^{-k}=\frac43.
\]

Adding the two ranges gives

\[
 \frac23(R-1)+\frac43R=2R-\frac23<2R.
\]

Consequently `S_N=2 floor(sqrt N)+5` is an unconditional allowance for all
fractional quotient remainders, independently of the selected Boolean word.

## 3. A quotient comparator with the fractional error removed

Consider the descending greedy representation of

\[
 H_N-S_N
\]

by the integer weights `a_{N,d}`.  Let `y^(N)` be the resulting Boolean word
when the greedy remainder reaches zero, and let `U_N` count its selected
ranks above `N/2`.  Its quotient defect is exactly `S_N`, and (3) proves

\[
 \sum_d\frac{y^{(N)}_d}{2^d-1}\leq\frac1{21}. \tag{5}
\]

The remaining estimate is now purely digital.  An inequality

\[
 U_N\leq T(N)+O(\sqrt N)                     \tag{6}
\]

would give the delayed-density bound with an `O(sqrt N)` error through the
reservoir extremal principle.  The upper half of the quotient row consists
of the powers of two, so `U_N` is exactly the binary digit sum of the
remainder left after the lower-half greedy decisions.  This identifies (6)
as a digit-sum estimate rather than a further real-feasibility problem.

An exact recurrence computation found no nonzero final greedy remainder and
found

\[
 U_N-T(N)\leq2
\]

for every `N<=15000` for which `H_N>=S_N`; equality first occurs at `N=19`.
This is bounded evidence only.  In particular, the square-root estimate (3)
does not imply (6): an arbitrary integer below the upper-half capacity can
have digit sum as large as `ceil(N/2)`.

There is an exact target-free counterexample.  Put
`K=N-floor(N/2)` and give the quotient-greedy algorithm capacity
`2^K-1`.  Every lower-half weight exceeds this capacity, while the
upper-half weights are

\[
 2^{K-1},2^{K-2},\ldots,2,1.
\]

The algorithm therefore selects every upper-half rank and gives `U_N=K`.
Thus no `2K/3+O(sqrt N)` digit-sum estimate follows from the quotient coin
system or the upper-half remainder bound alone.  Any proof of (6) must use
the special period-six target `H_N-S_N`.

At the isolated horizon `N=100000`, the same exact calculation again gives
zero final remainder and gives `U_N-T(N)=-8264`.  This isolated row does not
extend the exhaustive range.

## 4. Recut tests for the original comparator

For the corrected weights

\[
 c_{N,d}=a_{N,d}-1+\mathbf 1_{2d\leq N}
\]

and threshold `H_N-T(N)-3`, exact recurrence computation found no
lexicographic reversal between consecutive threshold words through
`N=10000`.  Whenever the word changed, its first changed digit was `0 -> 1`.
The first change lay within `22` ranks of the new horizon, and the threshold
overshoot was at most `15`.  The same computation certified the stronger
inequality `F_N<=Q_N` at every row in this range.  An isolated exact check at
`N=100000` also certified `F_N<=Q_N`, with `Q_N=8271` and threshold
overshoot zero.

These checks do not prove recut monotonicity or `F_N<=Q_N` at all depths.
Identity (1) isolates recutting as the only place where either conjecture
can fail.

## 5. The doubled comparator is not recut-monotone

For the sharper corrected weights

\[
 c^{(2)}_{N,d}=2a_{N,d}-\mathbf 1_{2d>N}
\]

and threshold `2H_N-T(N)-4`, let `w^(N)` be the lexicographically least
crossing word.  The proposed monotonicity

\[
 w^{(N)}\leq_{\rm lex}w^{(N+1)}              \tag{7}
\]

is false.  At `N=63` the final selected ranks are

\[
 57,58,59,60,61,
\]

whereas at `N=64` they are

\[
 57,58,59,60,62,63.
\]

The words first differ at rank `61`, where the digit changes from `1` to
`0`.  The exact threshold data are

\[
\begin{array}{c|c|c|c|c}
N&D_N^{(2)}&\sum_d c^{(2)}_{N,d}w_d^{(N)}&E_N&U_N\\ \hline
63&878416384462359576&878416384462359578&2&18\\
64&1756832768924719176&1756832768924719176&0&18.
\end{array}
\]

A second reversal occurs from `N=89` to `N=90`, at rank `89`.  Thus the
fixed-word recurrence (1) cannot be combined with a general monotone-recut
argument for this doubled comparator.

The doubled comparator nevertheless remains real-feasible in the exact
computation through `N=5000`.  Its narrowest row in that range is `N=63`:
`Q_63=2`, the fractional sum is approximately `2.3134592952`, and
`{2^63/21}=8/21`, leaving a positive margin of approximately `0.0674931`.
This row also disproves the stronger auxiliary inequality `F_N<=Q_N` for
the doubled comparator; the source fractional part is essential.
