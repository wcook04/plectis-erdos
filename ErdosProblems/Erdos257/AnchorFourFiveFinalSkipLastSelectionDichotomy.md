# The last selection before a saturated \(1/465\) skip

Let \(b_d\) and \(\rho_d\) be the fixed-\(1/465\) diagonal word and
remainders from AnchorFourFiveFixedHorizonReduction.md.  This note proves a
new restriction on the saturated final skip supplied by that note.

Suppose \(L\) is the final skipped rank on a fatal orbit, and let \(p<L\) be
the last selected rank before \(L\).  Then

\[
 \boxed{\ p>\frac L2
 \quad\text{or}\quad
 0\leq\rho_p\leq s_{p-1}.\ }                       \tag{1}
\]

Thus a long final plateau must begin at a selected small-margin event.  The
second alternative is exactly the obstruction classified in the fixed-horizon
note; it is not merely a decrease of an unreduced numerator.

## 1. Resolvent transport across the plateau

Put \(q=L-p\).  Every rank \(p+1,\ldots,L\) is skipped.  Write

\[
 u_n=2t_{2n-1}+t_{2n},\qquad
 A_n=2F_p(2n-1)+F_p(2n),
\]

where \(F_p(n)\) counts selected divisors of \(n\) among ranks at most \(p\).
The skipped recurrence is

\[
 \rho_{p+k}=4\rho_{p+k-1}+u_{p+k}-A_{p+k}.         \tag{2}
\]

Let

\[
 \alpha_n=\left\{\frac{4^n}{465}\right\},\qquad
 \mathscr R_n=
 \sum_{\substack{a\leq p\\b_a=1}}
 \left\{\frac{4^n}{2^a-1}\right\}.
\]

The base-four source digits and the future-divisor expansion of the resolvent
give the two exact tail identities

\[
 \sum_{k=1}^{q}\frac{u_{p+k}}{4^k}
 =\alpha_p-4^{-q}\alpha_L,                         \tag{3}
\]

\[
 \sum_{k=1}^{q}\frac{A_{p+k}}{4^k}
 =\mathscr R_p-4^{-q}\mathscr R_L.                 \tag{4}
\]

The final-skip saturation theorem gives \(\rho_L=2^L\).  Divide the iteration
of (2) by \(4^q\) and use (3)--(4):

\[
 \boxed{
 2^{p-q}
 =\rho_p+\alpha_p-\mathscr R_p
 -4^{-q}(\alpha_L-\mathscr R_L).}                 \tag{5}
\]

This is the full fixed-source plateau equation.  It retains both endpoint
phases rather than bounding every divisor pulse separately.

## 2. Two old selected ranks force the dichotomy

Assume \(p\leq L/2\), and write

\[
 c=L-2p=q-p\geq0.
\]

The exact initial orbit has \(b_9=b_{13}=1\) and a later skipped rank, so a
final skip has \(p\geq13\).  Suppose that \(p\) is not a selected
small-margin event.  Since \(p\) is selected,
\(\rho_p=D_p\) is a nonnegative integer.  Therefore

\[
 \rho_p\geq s_p.                                   \tag{6}
\]

For a selected rank \(a\geq2\),

\[
 \left\{\frac{4^p}{2^a-1}\right\}
 =\frac{2^{\,2p\bmod a}}{2^a-1}
 \leq\frac{2^{a-1}}{2^a-1}.
\]

The two selected ranks \(9\) and \(13\) alone consequently give

\[
\begin{aligned}
 s_p-\mathscr R_p
 &\geq
 \frac{2^8-1}{2^9-1}
 +\frac{2^{12}-1}{2^{13}-1}\\
 &=\frac{4181250}{4185601}.                       \tag{7}
\end{aligned}
\]

On the other hand, rearranging (5) and using (6) yields

\[
 s_p-\mathscr R_p
 \leq
 2^{-c}-\alpha_p
 +4^{-q}(\alpha_L-\mathscr R_L).                  \tag{8}
\]

The saturated final-skip budget has
\(0\leq\mathscr R_L<\alpha_L<1\).  Also
\(\alpha_p\geq1/465\), \(2^{-c}\leq1\), and \(q\geq p\geq13\).  Hence

\[
 s_p-\mathscr R_p
 <
 \frac{464}{465}+4^{-13}.                         \tag{9}
\]

The comparison is strict and exact:

\[
 \frac{4181250}{4185601}
 -\left(\frac{464}{465}+4^{-13}\right)
 =
 \frac{145113321685039}{130614281644277760}>0.
\]

Equations (7) and (9) contradict one another.  This proves (1).

## 3. Long predecessor edges repeat the small margin

The same argument iterates one level farther back.  Let \(p\) be any selected
small-margin rank on the actual orbit, and let \(r<p\) be the selected rank
immediately preceding it.  The initial selected ranks through \(19\) are not
small-margin, so in the case of interest \(r\geq13\).

Suppose \(r\leq p/2\), put \(q=p-r\), and write \(z=\rho_p\).  There are no
selections strictly between \(r\) and \(p\), so

\[
 0\leq z\leq s_{p-1}=s_r.
\]

Immediately before the selection at \(p\), the remainder is
\(2^p+1+z\).  Let \(\mathscr R_p^{-}\) denote the rank-\(p\) resolvent of
the support through \(r\), before adding \(p\).  The same tail calculation
as in (3)--(5) gives

\[
 \boxed{
 2^{r-q}+(1+z)4^{-q}
 =\rho_r+\alpha_r-\mathscr R_r
 -4^{-q}(\alpha_p-\mathscr R_p^{-}).}             \tag{10}
\]

If \(r\) were not small-margin, then \(\rho_r\geq s_r\).  Since
\(\mathscr R_p^{-}\geq0\), equation (10) would imply

\[
\begin{aligned}
 s_r-\mathscr R_r
 &<
 1-\frac1{465}+(z+2)4^{-q}\\
 &\leq
 \frac{464}{465}+(r+2)4^{-q}\\
 &\leq
 \frac{464}{465}+15\cdot4^{-13}.                  \tag{11}
\end{aligned}
\]

But the selected ranks \(9\) and \(13\) again give the lower bound (7), and

\[
 \frac{4181250}{4185601}
 -\left(\frac{464}{465}+15\cdot4^{-13}\right)
 =
 \frac{145086073422529}{130614281644277760}>0.    \tag{12}
\]

This contradiction proves:

> **Small-margin repeat theorem.**  If \(p\) is selected small-margin and
> \(r<p\) is its preceding selected rank, then
> \[
>  \boxed{\ r>\frac p2
>  \quad\text{or \(r\) is also selected small-margin.}\ }
> \]

Thus every backward edge of length at least half the current rank propagates
the obstruction to an earlier selected rank.  Only an upper-half predecessor
can stop this descent.

## 4. What remains

The theorem removes every long-plateau final skip whose last selection has a
large margin.  It leaves two genuinely different cases.

* If \(p\leq L/2\), the last selection is a small-margin event.  The repeat
  theorem propagates it across every earlier long predecessor edge.  A chain
  of upper-half predecessors can still terminate the descent, so this does
  not yet produce infinitely many small-margin events.
* If \(p>L/2\), the plateau is short.  The fixed-source rank-\(24\) synthetic
  gateway lies in this geometry and satisfies the local phase, load, and
  escape restrictions, although the half-window carry proves that its
  predecessor is not globally reachable.

Thus (1) is stronger than the numerator-decrease alternative in
Fixed465BackwardPowerDescent.md, but it does not yet exclude the saturated
final skip.  A closure must exclude an eventual chain of upper-half
predecessors, or combine that short-edge case with the full-prefix carry
rather than only the endpoint resolvent budget.
