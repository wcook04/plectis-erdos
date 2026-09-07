# Short-edge chains expand the fixed-source product height

This note addresses the surviving short-edge branch in
AnchorFourFiveFinalSkipLastSelectionDichotomy.md. It keeps the complete
coefficient-one numerator of the fixed source \(1/465\), rather than only the
endpoint phase. The result is a no-go for a natural product-height closure:
on every short edge, the prefix product acquires essentially the same power
of two that the plateau squeeze costs. Along a whole chain these factors
multiply in the expansive direction.

The statement below does **not** construct a fatal orbit and does not exclude
one. It proves that simultaneous Archimedean comparison of the plateau
equations with the genuine prefix product cannot supply the missing
contradiction. Any closure must use information not contained in product
height and the short-edge corridors, such as a residue or incidence
restriction that survives after the height factor is divided out.

## 1. The genuine fixed-source integers

Write \(M_n=2^n-1\). For an actual selected prefix \(F\), put

\[
 P(F)=\prod_{d\in F}M_d,
 \qquad
 N(F)=P(F)-465\sum_{d\in F}\frac{P(F)}{M_d}.
\]

Then the real residual is exactly

\[
 e(F)=\frac1{465}-\sum_{d\in F}\frac1{M_d}
     =\frac{N(F)}{465P(F)}.                       \tag{1}
\]

Thus \(N(F)\) is the complete, unreduced, coefficient-one source numerator.
No affine change of source and no locally substituted predecessor is being
used.

Suppose \(r\) is a selected rank, \(F_r\) is the actual support through
\(r\), and

\[
 P_r=P(F_r),\qquad N_r=N(F_r),\qquad
 X_r=4^r e(F_r),\qquad H_r=\frac{P_r}{4^r}.
\]

The product and plateau coordinates retain the numerator exactly:

\[
 \boxed{N_r=465H_rX_r.}                           \tag{2}
\]

Assume throughout the fatal branch that \(e(F_r)>0\).

## 2. One short edge, with both scales retained

Let \(p>r\) be the next selected rank, and assume that \(p\) is
small-margin. Hence every rank strictly between \(r\) and \(p\) is skipped.
Put \(q=p-r\). Suppose the edge is upper-half, and write

\[
 p=2r-a,\qquad a\geq1.                            \tag{3}
\]

Let \(X_p=4^pe(F_p)\) after \(p\) is selected. The exact selected-plateau
equation, in the reverse orientation needed by the chain, is

\[
\boxed{
 X_r
 =2^a+4^{-q}
  \left(X_p+1+\frac1{M_p}\right).}                \tag{4}
\]

This is the diagonal-orbit equation; it does not import an ordinary
real-greedy next-term comparison. On the fatal branch \(e(F_p)>0\), and the
small-margin identity gives
\(0<X_p<s_{p-1}+1\leq p\). Therefore

\[
\boxed{
 0<X_r-2^a<(p+2)4^{-q}.}                         \tag{5}
\]

Under the short-edge squeeze defining the surviving subcase, one has
\[
 \boxed{1\leq a<\log_2 r.}
\]
The important point for the product calculation is that the exact plateau
coordinate is on the \(2^a\) scale, with the complete endpoint correction
still present in (4).

Now retain the product update at the selected endpoint. Equations (1) give

\[
 P_p=M_pP_r,\qquad N_p=M_pN_r-465P_r.             \tag{6}
\]

The corresponding normalized height has the exact multiplier

\[
\begin{aligned}
 \frac{H_p}{H_r}
 &=M_p4^{r-p}\\
 &=(2^p-1)2^{-2(p-r)}\\
 &=\boxed{2^a(1-2^{-p}).}                         \tag{7}
\end{aligned}
\]

Thus the product height does not pay a factor \(2^{-a}\). It gains a factor
\(2^a(1-2^{-p})\), while (4)--(5) place the plateau coordinate on the
\(2^a\) scale. Formula (2) shows that these are the two complementary
factors of the genuine numerator; discarding either one creates a false
contraction.

## 3. The simultaneous identity for a whole chain

Let

\[
 r_0<r_1<\cdots<r_k
\]

be consecutive selected ranks on an actual prefix. Assume every ending
vertex \(r_1,\ldots,r_k\) is small-margin and every displayed edge is
short. Write

\[
 r_{j+1}=2r_j-a_j,\qquad a_j\geq1
 \quad(0\leq j<k).                                \tag{8}
\]

Repeated use of (6)--(7), with no loss or endpoint estimate, gives

\[
 \boxed{
 \frac{P_{r_k}}{4^{r_k}}
 =\frac{P_{r_0}}{4^{r_0}}
   2^{a_0+\cdots+a_{k-1}}
   \prod_{j=0}^{k-1}(1-2^{-r_{j+1}}).}           \tag{9}
\]

Since every ending vertex \(r_{j+1}\) is small-margin, put

\[
\begin{aligned}
 q_j&=r_{j+1}-r_j,\\
 \beta_j
 &=X_{r_{j+1}}+1+\frac1{M_{r_{j+1}}},\\
 \Theta_j&=1+2^{-a_j}4^{-q_j}\beta_j.
\end{aligned}
\]

Then (2), (4), and (9) give the simultaneous numerator identity

\[
\boxed{
 N_{r_j}
 =465\frac{P_{r_0}}{4^{r_0}}
   2^{a_0+\cdots+a_j}
   \prod_{i=0}^{j-1}(1-2^{-r_{i+1}})\Theta_j,}    \tag{10}
\]

for \(0\leq j<k\),

with the strict bounds

\[
 \boxed{
 1<\Theta_j<
 1+2^{-a_j}(r_{j+1}+2)4^{-q_j}.}                \tag{11}
\]

Thus every preceding short-edge deficit remains with a positive sign in
the complete numerator scale. There is no all-chain product-height deficit
to sum: the capacity is replenished at every selected endpoint.

The terminal saturated skip has the same scale. Suppose \(L>r_k\) is
skipped, no rank lies in the support between \(r_k\) and \(L\), and
\(\rho_L=2^L\). If \(L=2r_k-a_k\), the full fixed-source plateau equation is

\[
 \boxed{
 X_{r_k}
 =2^{a_k}+4^{r_k-L}
   (\alpha_L-\mathscr R_L).}                     \tag{12}
\]

On a fatal saturated row,
\(0<\alpha_L-\mathscr R_L<1\). Combining (2), (9), and (12) yields the
all-chain terminal identity

\[
\boxed{
\begin{aligned}
 N_{r_k}
 &=465\frac{P_{r_0}}{4^{r_0}}
   2^{a_0+\cdots+a_k}
   \prod_{j=0}^{k-1}(1-2^{-r_{j+1}})\,\Theta,\\
 1&<\Theta<1+2^{-a_k}4^{r_k-L}.
\end{aligned}}                                   \tag{13}
\]

Every short-edge deficit \(a_j\) therefore occurs with a positive sign in
the exact coefficient-one numerator scale. The endpoint correction is
strictly positive and smaller than one discounted plateau unit; it cannot
reverse the product expansion.

## 4. Product-capacity reversal theorem

> **Theorem.** On any finite short-edge chain belonging to the genuine
> fixed-\(1/465\) prefix, the exact product updates give (9). If every
> ending vertex is small-margin and the chain ends in a short saturated
> skip, simultaneous use of the exact plateau equations
> also gives (10)--(13). In either case, the normalized prefix-product
> capacity is multiplied by
>
> \[
> 2^{\sum_{j<k}a_j}
> \prod_{j<k}(1-2^{-r_{j+1}}),
> \]
>
> rather than divided by \(2^{\sum a_j}\). If \(r_{j+1}\geq9\), every
> individual multiplier is greater than
> \(2(1-2^{-9})>1\). Hence product height grows exponentially in the number
> of short edges even in the extremal case \(a_j=1\).

The proof is the exact multiplication in (7), followed by (9). Equations
(10)--(11) then follow from the exact selected-plateau equation, including
its endpoint correction, and (12)--(13) follow from the exact saturated
plateau equation. No independence assumption is used.

This decisively falsifies the proposed Archimedean closure by accumulated
prefix-product cost. A longer chain does not create an Archimedean
contraction of the scale carrying \(N_{r_k}\); it expands that scale. The
conclusion is specific to this mechanism. It does not say that the complete
fixed-source equations are consistent with a fatal orbit; congruences or
divisor-incidence correlations may still exclude the chain.

## 5. Reproducible exact audit

Run

    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/anchor_four_five_short_edge_product_capacity_audit.py

The script constructs genuine coefficient-one \(1/465\) prefix integers,
checks (1)--(2) exactly, audits the selected-plateau equation on globally
reachable edges of the fixed diagonal orbit, and audits (6)--(9) over
several short-edge chains using rational arithmetic. The appended chain
edges are algebraic product-update samples, not asserted greedy
continuations; the universal theorem is the symbolic calculation above.
