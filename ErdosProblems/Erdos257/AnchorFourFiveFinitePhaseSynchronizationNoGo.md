# Finite source history cannot force the \(1/465\) phase inequality

## Status

This note proves an exact counterfamily to a natural finite-history version of
the selected-phase lower bound.  The counterfamily keeps an arbitrary finite
prefix of the actual real-greedy word for \(1/465\), keeps the exact
period-\(20\) target and all source phases from that prefix, and has
nonnegative quotient defect at every rank.  Nevertheless it violates
\[
 F_m>Q_m+\alpha_m-1
\]
at infinitely many synchronized skipped ranks.  The continuation is not
real-greedy after the retained prefix, so this is not a counterexample on the
actual orbit.  It shows that no proof from a fixed finite source history plus
quotient admissibility can establish the required inequality.

Put
\[
 x=\frac1{465},\qquad w_d=\frac1{2^d-1},
\]
and let \(b_d\) be the real-greedy word for \(x\).  For a fixed cutoff \(N\),
write
\[
 A_N=\{d\leq N:b_d=1\},\qquad
 S_N=\sum_{d\in A_N}w_d,\qquad r_N=x-S_N.
\]
Every finite greedy residual is positive.  Define the synchronization height
\[
 L_N=\operatorname{lcm}\bigl(20,\{d:d\in A_N\}\bigr).
\]

## 1. Exact phase collapse at synchronized heights

Let \(B\) be a positive multiple of \(L_N\).  The target phase is
\[
 \alpha_B=\left\{\frac{2^B}{465}\right\}=\frac1{465}=x,
\]
because \(2^{20}\equiv1\pmod {465}\).  Every retained source is also at the
bottom of its phase clock:
\[
 \frac{2^{B\bmod d}}{2^d-1}=w_d\qquad(d\in A_N).
\]
Consequently its total selected phase is exactly
\[
 \boxed{F_B^{(N)}=S_N=x-r_N<\alpha_B.}                 \tag{1}
\]

There is a simultaneous exact formula for the quotient defect of this frozen
prefix.  Since every denominator of \(r_N\) divides \(2^B-1\),
\[
 \boxed{Q_B^{(N)}=(2^B-1)r_N\in\mathbb Z_{>0}.}        \tag{2}
\]
Indeed, the general phase identity gives
\[
 Q_B^{(N)}=2^Br_N-\alpha_B+F_B^{(N)}
           =(2^B-1)r_N.
\]
Thus the finite source contribution does not retain a positive phase buffer
at a common height.  It collapses to the real mass already spent by the
prefix, while the frozen residual becomes an integer quotient debt.

## 2. A fixed-target, quotient-admissible counterfamily

Choose a sufficiently large multiple \(B\) of \(L_N\) such that
\[
 2^Br_N>1,
 \qquad
 \frac{2}{2^{B+1}-1}<r_N.                              \tag{3}
\]
There are infinitely many such multiples.  Define a Boolean word
\[
 c_d^{(N,B)}=
 \begin{cases}
  b_d,&d\leq N,\\
  0,&N<d\leq B,\\
  1,&d>B.
 \end{cases}                                           \tag{4}
\]
The full cofinite tail satisfies
\[
 \sum_{d>B}w_d
 \leq\frac{2}{2^{B+1}-1}<r_N,
\]
so (4) has total value strictly below \(x\).  In particular every finite
partial sum is below \(x\).  Therefore its quotient defect
\[
 Q_n(c)=\left\lfloor2^nx\right\rfloor
 -\sum_{d\leq n}c_d
  \left\lfloor\frac{2^n}{2^d-1}\right\rfloor
\]
is nonnegative for every \(n\): the integer quotient sum is strictly below
\(2^nx\).

At rank \(B\), the word (4) is skipped and its residual after the retained
prefix is still \(r_N\).  Equations (1)--(3) give
\[
 \begin{aligned}
 F_B(c)-(Q_B(c)+\alpha_B-1)
 &=1-2^Br_N\\
 &<0.                                                   \tag{5}
 \end{aligned}
\]
Thus the desired selected-phase inequality fails strictly.  Equivalently,
the scaled residual satisfies \(2^Br_N>1\), so it lies above the dyadic
cutoff at this skipped rank.

## 3. Consequence for the actual-orbit proof

The construction retains, for an arbitrary \(N\), all of the following:

1. the complete actual greedy word through \(N\);
2. the fixed target \(1/465\) and its period-\(20\) phase;
3. every shifted source atom and divisor clock belonging to that prefix;
4. Boolean coefficients and nonnegative quotient defect at every depth; and
5. exact synchronization of all retained source phases.

These data do not force (5) to have the opposite sign.  The missing input is
not another statistic of a fixed collection of source clocks.  It is the
unbounded real-greedy complementarity which requires every later affordable
rank to be consumed.  In particular, an argument that freezes any finite
ownership or selected-divisor state and then seeks a uniform phase lower
bound from that state cannot prove
\(F_m>Q_m+\alpha_m-1\) on the actual orbit.

This does not rule out a full-history source invariant.  It identifies the
minimum distinction such an invariant must preserve: it must charge every
later skipped affordable rank, rather than retaining only quotient
admissibility and a finite source ledger.

## 4. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_finite_phase_synchronization_nogo.py
```

The script computes exact greedy prefixes, checks the synchronization formulas
for two concrete cutoffs, and verifies the inequalities in (3) without
floating-point arithmetic.  The all-cutoff and infinitely-many-height claims
follow from the displayed algebra.
