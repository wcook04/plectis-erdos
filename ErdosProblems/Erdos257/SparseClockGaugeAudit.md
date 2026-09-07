# Finite-prefix recutting and rational source clocks

## 1. Setup

Put
\[
  w_n=\frac1{2^n-1}.
\]
For a rational target \(x\in(0,1)\), let \(b_n(x)\in\{0,1\}\) be its greedy
Mersenne digits and let
\[
  B_x(N)=\sum_{n\leq N}b_n(x),\qquad
  h_x(N)=\sum_{d\mid N}b_d(x).
\]
If \(t_n(x)\) is the \(n\)-th binary digit of \(x\), define
\[
  T_x(N)=\sum_{n\leq N}t_n(x),
  \qquad
  Q_x(N)=2Q_x(N-1)+t_N(x)-h_x(N),
  \quad Q_x(0)=0.
\]
The delayed-doubling state and its unshifted endpoint energy are
\[
  P_x(N)=T_x(N)+B_x(\lfloor N/2\rfloor)-B_x(N),
  \qquad
  F_x(N)=P_x(N)-2Q_x(N).
\]
Thus the least constant in an inequality \(P_x(N)+C-2Q_x(N)\geq0\)
is \(\sup_N(2Q_x(N)-P_x(N))\).  A bounded computation of this supremum
does not prove the all-depth inequality.

If
\[
  x=\frac{p}{2^k-1},\qquad 0<p<2^k-1,
\]
then the repeating binary word is the length-\(k\) binary expansion of
\(p\), padded on the left.  Its density is therefore
\(s_2(p)/k\), not the density of the word for \(1/(2^k-1)\).

## 2. A bounded recut cocycle

The following observation makes finite-prefix changes useful rather than
cosmetic.  Let \(E\) be a finite set of ranks, let \(M=\max E\), and suppose
\[
  x=y+\sum_{d\in E}w_d.
\]
Assume that the greedy expansion of \(x\) selects exactly \(E\) through rank
\(M\), while the greedy expansion of \(y\) selects no rank through \(M\).
The two residuals after rank \(M\) are then both \(y\), so the greedy digits
coincide at every later rank.  This is an immediate induction from the greedy
decision rule.

The corresponding quotient defects differ by a bounded floor cocycle.  For
every \(N\),
\[
\begin{split}
  Q_x(N)-Q_y(N)
  &={\left\lfloor 2^Nx\right\rfloor}
    -{\left\lfloor 2^Ny\right\rfloor}
    -\sum_{d\in E}{\left\lfloor\frac{2^N}{2^d-1}\right\rfloor}\\
  &\in\{0,1,\ldots,|E|\}.
\end{split}
\]
Indeed, after writing each summand as its integer and fractional part, the
right-hand side is the carry out of the sum of \(|E|+1\) fractional parts.
This proof is independent of the greedy algorithm.

For \(N\geq2M\), the finite prefix contributes equally to \(B_x(N)\) and
\(B_x(\lfloor N/2\rfloor)\).  Consequently
\[
  F_x(N)-F_y(N)
  =T_x(N)-T_y(N)-2\bigl(Q_x(N)-Q_y(N)\bigr).
\]
If the two rational source words have densities \(\alpha_x\) and
\(\alpha_y\), then
\[
  F_x(N)-F_y(N)=(\alpha_x-\alpha_y)N+O_E(1).
\]
This is the main structural fact of the audit.  A finite Boolean recut can
alter the source-clock contribution linearly, although its effect on the
divisor quotient is bounded.  The endpoint energy is therefore not invariant
under deletion or insertion of a finite prefix.

## 3. A short clock with zero observed allowance

Consider
\[
  x=\frac{90}{511}=\frac{90}{2^9-1}.
\]
Its source word is
\[
  001011010,
\]
which has density \(4/9<1/2\).  The exact greedy prefix is \(\{3,5\}\), and
\[
  \frac{90}{511}-w_3-w_5
  =\frac{16}{(2^5-1)(2^9-1)}
  =\frac{16}{15841}.
\]
The tail target has period \(45\), source word
\[
  000000000100001000110001100111001110111110000,
\]
and density \(17/45\).  The recut therefore changes the source density by
\(1/15\), while the preceding lemma bounds the quotient-defect change by two.

The clean initial ranks also have an algebraic explanation.  For every
integer \(a\geq2\), put
\[
  x_a=\frac{2^{a-1}+1}{2^{2a-1}-1}.
\]
A direct calculation gives
\[
  x_a=w_a+w_{2a}+x_aw_{2a}.
  \tag{1}
\]
Indeed, subtracting \(w_a\) from \(x_a\) gives
\((1+x_a)w_{2a}\).  In the present case,
\[
  \frac{90}{511}=w_3+x_5,
  \qquad x_5=\frac{17}{511}.
\]
The identity, together with direct comparison against the intervening
weights, shows that the greedy expansion selects ranks \(3,5,10\).  Its
residual after rank \(10\) is
\[
  x_5w_{10}=\frac{17}{511\cdot1023}.
\]
Exact comparison with the intervening weights gives the longer initial block
\[
  3,5,10,15,19.
\]

Identity (1) does not iterate as a shifted copy of the same decomposition.
After subtracting \(w_5,w_{10},w_{15}\) from \(x_5\), the residual is
\[
  \frac{158}{78935703},
\]
and
\[
  \frac{158}{78935703}-w_{19}
  =\frac{3901643}{41384962918761}>0.
\]
Thus rank \(19\) is selected before the rank \(20\) predicted by a naive
translation of the pair \(5,10\).  The product term in (1) explains the first
two scaled selections, but it is not a self-similar construction of the
infinite tail.

The directed-interval computation through rank \(50{,}000\) gave
\[
  \max_{N\leq50000}\bigl(2Q_x(N)-P_x(N)\bigr)=0.
\]
Both digits occur in the final thousand computed positions, and the maximum
quotient defect is \(24\).  These are finite computations.  In particular,
they do not prove that the greedy expansion attains \(90/511\).

Several simpler strengthenings fail.  The energy is not monotone: it decreases
from \(2\) to \(1\) at rank \(8\).  The defect is not bounded by the source
period, since \(Q_{1679}=10>9\), and it is not bounded by
\(\lceil\log_2N\rceil\), since \(Q_{5039}=14>13\).  Through rank \(50{,}000\),
the only zeros of \(F_x\) occur at ranks \(1,2,3,4,5\).  The last statement is
again a bounded computation.

The all-depth statement suggested by this target is simply
\[
  P_x(N)\geq2Q_x(N)\qquad(N\geq1),
  \tag{SC0}
\]
with no additive allowance.  Since \(T_x(N)=4N/9+O(1)\), (SC0) would imply
\[
  B_x(N)-B_x(\lfloor N/2\rfloor)\leq \frac49N+O(1).
\]
Iteration gives \(B_x(N)\leq(8/9)N+O(\log N)\), hence infinitely many skipped
ranks.  The usual greedy tail argument would then give an infinite Boolean
Mersenne subsum equal to \(90/511\).  Statement (SC0) remains open.

There is a more strongly amplified coordinate of the same tail:
\[
  \frac{50026}{237615}
  =\frac{16}{15841}+w_3+w_4.
\]
Its greedy prefix is \(\{3,4\}\).  Its binary period is \(180\) and contains
\(89\) ones, so its source density is \(89/180\).  The computation through
rank \(30{,}000\) again found nonnegative unshifted energy.  This longer word
is less convenient than \(90/511\), but it shows that the clock gain can be
made much larger without changing the infinite tail under study.

## 4. Two shorter comparison targets

Two further targets retain a small observed allowance and a source density
strictly below one half:
\[
\begin{array}{c|c|c|c}
  x & \text{source word} & s_2/k &
  \max_{N\leq50000}(2Q_x(N)-P_x(N))\\ \hline
  11/127 & 0001011 & 3/7 & 1\\
  5/31   & 00101   & 2/5 & 2.
\end{array}
\]
For both targets, selected and skipped ranks occur in the final thousand
computed positions.  The first target has the shorter endpoint inequality;
the second has the shortest source period among the three displayed targets.
Neither row is an unbounded assertion.

The targets \(5/31\) and \(6/31\) also exhibit the exact recut law.  Their
greedy prefixes through rank five are \(\{3\}\) and \(\{3,5\}\), respectively,
and both residuals equal \(4/217\).  Hence their greedy tails agree exactly.
The two period-five words, \(00101\) and \(00110\), have the same density.
This recut changes only a bounded periodic part of the endpoint energy rather
than its linear drift.

## 5. The guaranteed-pulse queue is insufficient

There is an exact queue form of (SC0).  Put
\[
  A_N=\sum_{n=1}^NQ_x(n),\qquad
  D_N=\sum_{\substack{d\leq N/2\\b_d(x)=1}}
      \left\lfloor\frac Nd\right\rfloor.
\]
Summing the defect recurrence gives
\[
  F_x(N)=D_N-A_N.
\]
Thus (SC0) says that the cumulative quotient demand never exceeds the service
capacity contributed by selected ranks.

The guaranteed ranks \(3\) and \(5\) do not by themselves supply such an
injection.  Freeze the support at \(\{3,5\}\), while retaining the source word
\(001011010\).  The queue energy first becomes negative at rank \(12\):
\[
  Q(12)=4,\qquad A_{12}=9,\qquad D_{12}=6,
  \qquad D_{12}-A_{12}=-3.
\]
The failure is necessarily exponential.  Since
\[
  \frac{90}{511}=w_3+w_5+y,
  \qquad y=\frac{16}{15841}>0,
\]
the frozen-support defect satisfies
\[
  Q(N)=\left\lfloor 2^N\frac{90}{511}\right\rfloor
       -\left\lfloor 2^Nw_3\right\rfloor
       -\left\lfloor 2^Nw_5\right\rfloor
       \geq \lfloor2^Ny\rfloor,
\]
whereas its service capacity is at most \(N/3+N/5\).

Later selected ranks do help at a fixed horizon.  Inserting a rank \(d\) into
a support changes the energy at horizon \(N\) by
\[
  \mathbf 1_{2d\leq N}\left\lfloor\frac Nd\right\rfloor
  +\sum_{n=d}^N\left\lfloor\frac{2^n}{2^d-1}\right\rfloor>0.
\]
This monotonicity does not prove (SC0), because the base energy is already
unbounded below.  Any queue proof must use a coupling between the times at
which greedy selection inserts new ranks and the future service pulses of
those same ranks.  The pulses at multiples of \(3\) and \(5\) alone cannot
provide the required bound.

## 6. Adversarial checks

Source density alone does not prevent a fatal gap.  Appending a zero to the
period-seven numerator \(52\) gives
\[
  \frac{52}{127}\longmapsto\frac{104}{255}.
\]
The source density decreases from \(3/7\) to \(3/8\), but the greedy expansion
of \(104/255\) has a fatal gap at rank \(17\).  Exact rational arithmetic gives
\[
  r_{17}
  =\frac{14409235178978296551780664}
  {807093212915080247739749421255}
  >2^{-16}.
\]
On the other hand,
\[
  \sum_{n>17}w_n
  <\sum_{n>17}2^{1-n}=2^{-16}.
\]
Thus even selecting every remaining rank cannot exhaust the residual.  This
is an exact counterexample to any principle asserting that a sparser source
word, or zero-extension of a favorable word, preserves greedy feasibility.

The family obtained by repeatedly appending zeros to a fixed numerator gives
the same warning in a different form.  The targets converge to a dyadic
rational.  An infinite Boolean representation of a nonintegral dyadic target
cannot have a bounded endpoint inequality with source density tending to zero,
since the resulting delayed-doubling estimate would make the support
reciprocal-summable.

The recut cocycle identifies what a proof must use.  The periodic source word
can be improved by a finite prefix at only bounded quotient cost, but neither
the digit density nor the bounded cocycle excludes a later fatal gap.  For the
target \(90/511\), the remaining problem is to prove (SC0), or an inequality
that implies it, from the interaction of greedy feasibility with the divisor
pulses.

## 7. Reproduction

The script
`scripts/sparse_clock_gauge_audit.py` uses directed dyadic intervals for every
greedy decision and integer recurrences thereafter.  Its default command is

```text
python3 scripts/sparse_clock_gauge_audit.py --depth 10000
```

The prefix identities, the bounded floor-cocycle formula, and the fatal-gap
certificate are exact rational statements.  The common-tail comparisons and
endpoint maxima printed by the script are verified only through the requested
finite depth.
