# The zero-buffer target (90/511): period blocks and exact seam sensitivity

Status: exact identities, one exact rational counterexample to a local proof
principle, and bounded computations, 2026-08-20.  The inequality
(P_Ngeq 2Q_N) for (90/511) is not proved here.

## 1. The endpoint energy

Let

\[
 x=\frac{90}{511},\qquad w_n=\frac1{2^n-1},
\]

and let (b_n) be the greedy Mersenne digits of (x).  The binary source word
is (001011010).  We write

\[
 T_N=\sum_{n\leq N}t_n,\qquad
 B_N=\sum_{n\leq N}b_n,
\]

and

\[
 Q_N=2Q_{N-1}+t_N-\sum_{d\mid N}b_d,
 \qquad Q_0=0.
\]

The quantity under consideration is

\[
 F_N=T_N+B_{\lfloor N/2\rfloor}-B_N-2Q_N.       \tag{1}
\]

An all-depth proof that (F_N\geq0) would imply that the greedy support has
infinitely many omissions, since the source density is (4/9).  The greedy
tail argument would then give an infinite Boolean Mersenne subsum equal to
(90/511).

Directed-interval computation through rank (80{,}000) found (F_N\geq0).
The only zero values occurred at ranks (1,\ldots,5).  The same computation
found the stronger bound

\[
 F_N\geq \left\lfloor\frac N{10}\right\rfloor
 \qquad(6\leq N\leq80{,}000),                     \tag{2}
\]

with equality first attained at rank (44).  These are finite statements.

## 2. The exact period-nine increment

Every nine consecutive source digits contain four ones.  For any (N), put

\[
 U_N=B_{N+9}-B_N,
 \qquad
 S_N=B_{\lfloor(N+9)/2\rfloor}-B_{\lfloor N/2\rfloor}.
\]

Taking the difference of (1) at (N+9) and (N) gives the exact identity

\[
 \boxed{
 F_{N+9}-F_N
 =4-U_N+S_N-2(Q_{N+9}-Q_N).}                       \tag{3}
\]

This is the source-period cocycle for the proposed linear drift.  It does not
have a fixed sign.  Among the aligned blocks (N\equiv0\pmod9) through rank
(50{,}000), the smallest nine-step increment begins at (N=38070):

\[
 (F_N,Q_N)=(7389,3),\qquad
 (F_{N+9},Q_{N+9})=(7368,13).
\]

Thus (F_{N+9}-F_N=-21).  The smallest aligned eighteen-step increment in
the same range is (-24), beginning at rank (43101).  In particular, (2)
cannot follow from monotonicity on source periods, or on two source periods.
The large positive value of (F_N) absorbs these losses in the computed
orbit, but that fact is not an inductive explanation of its earlier growth.

## 3. A same-cylinder seam crossing at rank ten

The zero additive allowance does not remove the phase-seam obstruction.  Set

\[
 x^- =x-\frac{273}{511\,2^{14}}
     =\frac{1474287}{8372224}.                       \tag{4}
\]

Since

\[
 \{2^{14}x\}=\frac{325}{511}>\frac{273}{511},
\]

we have

\[
 \lfloor2^n x^-\rfloor=\lfloor2^n x\rfloor
 \qquad(1\leq n\leq14).                            \tag{5}
\]

The two targets also have the same greedy prefix through rank (9), namely
(001010000).  Their next five digits are different:

\[
 \begin{array}{c|c|c}
 \text{target}&(b_{10},\ldots,b_{14})&F_{14}\\ \hline
 x   &10000& 3\\
 x^- &01111&-2.
 \end{array}                                        \tag{6}
\]

All entries in (5) and (6) are exact rational calculations.  To see the seam
directly, subtract the common prefix (w_3+w_5), multiply the remainder by
(2^{10}), and put

\[
 \beta_{10}=\frac{2^{10}}{2^{10}-1},\qquad
 L=2^{10}\sum_{j=11}^{14}w_j.
\]

Then

\[
 L
 <\frac{253681}{253456}
 <\beta_{10}
 <\frac{16384}{15841}.                              \tag{7}
\]

The middle-left quantity is the scaled remainder for (x^-), while the
rightmost quantity is the scaled remainder for (x).  Hence (x^-) skips
rank (10) and pays for all four later coins, whereas (x) makes the
protective selection at rank (10).  Replacing (10000) by (01111) costs
five units of endpoint energy, exactly accounting for the difference in
(6).

This gives a local exclusion result.  The period-nine source digits, the
integer defect recurrence, divisor incidence, and genuine greedy decisions
through a putative failure do not imply nonnegativity of the unshifted
energy.  A proof for (90/511) must use the exact target phase, not only its
length-nine source word or the absence of an additive buffer.

## 4. A product renormalisation behind the first two tail selections

The residual after the guaranteed prefix is

\[
 x-w_3-w_5=16w_5w_9.                                \tag{8}
\]

There is a useful exact identity behind its next selection.  If (a,b>r),
then

\[
 2^r w_aw_b-w_{a+b-r}
 =(2^a+2^b-2^r-1)w_aw_bw_{a+b-r}.                   \tag{9}
\]

This follows by putting the two fractions over the common denominator.  The
coefficient on the right is positive.  At ((a,b,r)=(5,9,4)), equation (9)
becomes

\[
 16w_5w_9-w_{10}=527w_5w_9w_{10}.                  \tag{10}
\]

Exact comparison gives

\[
 w_{15}\leq527w_5w_9w_{10}<w_{14},                 \tag{11}
\]

so (10) proves the selections at ranks (10) and (15), including all four
intervening omissions.  This product renormalisation is stronger than the
single identity (x_a=w_a+w_{2a}+x_aw_{2a}) for the first tail step: it
retains the exact positive remainder after subtracting the selected coin.
It does not presently control the later support.  In particular, iterating
only its leading-exponent prediction does not prove (1).

## 5. The remaining arithmetic statement

Before a decision at rank (m), let (Y_m=2^m r_{m-1}), where (r_{m-1})
is the real greedy remainder.  If a skipped rank is followed by (k)
selected ranks, then

\[
 2^m\sum_{j=1}^k w_{m+j}
 \leq Y_m<\frac{2^m}{2^m-1}.                        \tag{12}
\]

For (x=90/511), the rational endpoint phase

\[
 \alpha_m=\left\{\frac{90\,2^m}{511}\right\}
\]

cycles through the numerators

\[
 180,360,209,418,325,139,278,45,90
 \pmod{511}.                                        \tag{13}
\]

The exact divisor phase must therefore be shown not to place (Y_m) in
(12) whenever the resulting exchange would spend all available value of
(F).  Example (7) shows that this is a target-specific arithmetic
separation: a perturbation smaller than one binary cylinder crosses the
seam and makes the same integer energy negative.  Neither the source-period
cocycle (3) nor the product identity (9) supplies that separation at all
depths.

## 6. Reproduction

The script `scripts/zero_buffer_sparse_target_audit.py` checks (3), the
finite inequality (2), the exact perturbation (4)--(7), and the product
identity (9)--(11).  Its default command is

```text
python3 scripts/zero_buffer_sparse_target_audit.py --depth 10000
```

The seam and product calculations are exact rational statements.  The
reported endpoint orbit and period-block extrema are certified only through
the requested finite depth.
