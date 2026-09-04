# The product source does not force terminal-corridor repayment

Status: exact ordinary deductions, 2026-08-21.  This note gives an infinite
counterfamily to a source-clock proof of half-row repayment.  The family is
Boolean, lies strictly below (1/465), and is quotient-admissible at every
depth, but it is not the real-greedy word.

Put

\[
 x=M(4,5)=\frac1{465},\qquad w_n=\frac1{2^n-1}.
\]

Let (t_n) be the binary digits of (x), and let

\[
 r_{4,5}(n)=\#\{(i,j)\in\mathbb N_{>0}^2:4i+5j=n\}.
\]

The raw product carry is defined by

\[
 K_0=0,\qquad K_n=2K_{n-1}+t_n-r_{4,5}(n).       \tag{1}
\]

For a Boolean word (b), put

\[
 f_b(n)=\sum_{d\mid n}b_d,
 \qquad
 Q_n=\left\lfloor\frac{2^n}{465}\right\rfloor
      -\sum_{d\le n}b_d
       \left\lfloor\frac{2^n}{2^d-1}\right\rfloor,
 \qquad E_n=K_n-Q_n.                              \tag{2}
\]

The purpose of the counterfamily below is to determine exactly what these
source coordinates do not remember.

## 1. Exact raw carry

The period-(20) word for (1/465) has ones at

\[
 9,13,14,17,18,19,20\pmod {20}.                  \tag{3}
\]

A direct residue count of the positive solutions to (4i+5j=n) gives

\[
 r_{4,5}(20q+s)=q+t_s\quad(1\le s\le19),
 \qquad
 r_{4,5}(20q)=q-1\quad(q\ge1).                   \tag{4}
\]

Substitution in (1) proves

\[
 \boxed{K_n=\left\lfloor\frac n{20}\right\rfloor}.
                                                               \tag{5}
\]

The primitive triangle at the first carry contains the five atoms
(9,13,14,17,19); the nonprimitive source at (18=4\cdot2+5\cdot2)
and the final source digit at (20) are absorbed by the carry in (5).
Thus the five-for-one primitive geometry and the period-(20) raw clock
are both present in the counterfamily.

Subtracting the recurrences for (K) and (Q) gives, as usual,

\[
 E_n=2E_{n-1}+f_b(n)-r_{4,5}(n).                 \tag{6}
\]

## 2. An infinite terminal counterfamily

For every integer (B\ge9), define

\[
 b_n^{(B)}=\mathbf 1_{n\ge B+1}.                  \tag{7}
\]

This cofinite Boolean word has total Mersenne value strictly below the
target.  Indeed,

\[
 \sum_{n\ge B+1}w_n
 \le \frac{1}{1-2^{-(B+1)}}\sum_{n\ge B+1}2^{-n}
 =\frac2{2^{B+1}-1}
 \le\frac2{1023}<\frac1{465}.                    \tag{8}
\]

Every finite prefix of (7) is therefore below (x).  Since the quotient
sum in (2) is an integer bounded above by (2^n) times that finite real
sum, (8) implies

\[
 Q_n^{(B)}\ge0\qquad\text{for every }n.           \tag{9}
\]

Thus the family is quotient-admissible at all depths for the exact product
source.  It also obeys (5) and (6), with no change to the primitive or raw
lattice clocks.

At the half row based at (B), the head (d\le B) is empty and every
upper rank (B<d\le2B) is selected.  These upper quotient coins are exact
powers of two, so

\[
 \sum_{B<d\le2B}
 \left\lfloor\frac{2^{2B}}{2^d-1}\right\rfloor
 =\sum_{B<d\le2B}2^{2B-d}=2^B-1.                 \tag{10}
\]

Consequently

\[
 Q_{2B}^{(B)}
 =\left\lfloor\frac{2^{2B}}{465}\right\rfloor-(2^B-1)
 \ge1,                                            \tag{11}
\]

because (2^B>465).  The suffix-hole integer is zero, and hence the
upper-suffix repayment state is

\[
 \boxed{
 D_{B,B}=-Q_{2B}^{(B)}
 =-\left(\left\lfloor\frac{2^{2B}}{465}\right\rfloor
          -(2^B-1)\right)<0.}                     \tag{12}
\]

This is an exact failure for every (B\ge9), not a finite search.

## 3. The finite ownership state does not repair the loss

The counterfamily can be made to agree with the complete certified
ownership construction through rank (102).  Let

\[
 \begin{aligned}
 \mathcal P_{102}=\{&9,13,14,17,19,21,22,23,24,25,28,29,
 34,35,36,37,42,43,47,48,52,54,55,59,61,63,64,\\
 &68,70,72,74,76,77,79,83,84,88,92,94,98,99,100,102\}.
 \end{aligned}                                    \tag{13}
\]

The exact construction in `AnchorFourFiveFirstTypeBreak.md` proves

\[
 h=M(4,5)-\sum_{d\in\mathcal P_{102}}w_d>0,
 \qquad f(h)=105.                                  \tag{14}
\]

In particular (h\ge w_{105}).  For (B\ge106), define

\[
 \widetilde b_d^{(B)}
 =\mathbf 1_{d\in\mathcal P_{102}}
  +\mathbf 1_{d>B}.                                \tag{15}
\]

The two sets in (15) are disjoint.  The new cofinite tail is smaller than
the certified residual, since

\[
 \sum_{d>B}w_d
 \le\frac2{2^{B+1}-1}
 <\frac1{2^{105}-1}\le h.                         \tag{16}
\]

Thus (15) is again a Boolean word of total value strictly below (1/465),
and its quotient defects are nonnegative at every depth.  At horizon (2B)
the head is exactly (mathcal P_{102}), while the complete upper half is
selected.  Using

\[
 \left\lfloor2^{2B}x\right\rfloor
 >2^{2B}x-1,
 \qquad
 \sum_{d\in\mathcal P_{102}}q_{2B,d}
 \le2^{2B}\sum_{d\in\mathcal P_{102}}w_d,
\]

one obtains

\[
 \begin{aligned}
 Q_{2B}(\widetilde b^{(B)})
 &>2^{2B}h-2^B\\
 &\ge\frac{2^{2B}}{2^{105}-1}-2^B>0.              \tag{17}
 \end{aligned}
\]

Hence (D_{B,B}=-Q_{2B}<0) for every (B\ge106).  This strengthened
counterfamily agrees with the exact Boolean prefix and starts from the same
front-(105), owner-sixteen cutoff state established by the finite
construction.  It does not supply an ownership-preserving continuation of
that state: it deliberately leaves part of the residual unused.  It also
fails real greediness at rank (105): (14) makes that rank affordable,
whereas (15) skips it.

Therefore the numerical and owner-label data of the certified cutoff state,
without a law governing how its full residual is subsequently consumed,
cannot force an all-depth frontier-lag or repayment statement.  A successful
ownership invariant must be propagated through every later affordability
decision and must conserve all residual mass.  The counterfamily does not
rule out such a dynamic ownership theorem; it shows exactly which extra
hypothesis that theorem must use.

## 4. The information missing from the source clock

The family (7) satisfies all of the following simultaneously:

1. Boolean coefficients and their exact divisor-count word;
2. strict real positivity below (M(4,5));
3. nonnegative quotient defect at every depth;
4. the period-(20) target digits, primitive triangle, raw carry (5), and
   difference recurrence (6);
5. an all-selected upper half; and
6. strict failure of half-row repayment.

It is not the real-greedy word.  In particular (w_9=1/511<1/465), while
(7) skips rank (9); the strengthened family (15) first discards an
affordable rank at (105).  Therefore a proof using only the product source,
quotient admissibility, and the terminal block cannot establish
(D_{B,B}\ge0).  It must charge such an early skipped affordable rank.
Equivalently, it must use real-greedy complementarity or an
ownership-preserving construction tied to the actual prefix.  The raw
quantity (E=K-Q) does not retain that information.

This does not disprove repayment for the actual (1/465) greedy word.  It
rules out the proposed source-clock route unless it is augmented by a
genuine prefix-history invariant.

## 5. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_terminal_corridor_source_nogo.py
```

The script checks the period word, the raw carry recurrence, the primitive
first triangle, the exact front-(105) residual, and instances of the closed
formulas (8)--(17) with exact integer and rational arithmetic.  The infinite
statements follow from the displayed algebra, not from the audit range.
