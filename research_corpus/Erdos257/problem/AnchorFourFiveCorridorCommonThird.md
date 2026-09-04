# A quantitative common prefix in the \(1/465\) quotient corridor

Status: exact theorem, 2026-08-21.  Every two complete Boolean prefixes in
the source corridor agree through one third of their depth.  More precisely,
they agree through

\[
 \left\lfloor
 \frac{n-L_n}{2}
 \right\rfloor,
 \qquad
 L_n=1+\left\lfloor
 \log_2\!\left(\frac32(K_n+1)\right)
 \right\rfloor,
 \qquad K_n=\left\lfloor\frac n{20}\right\rfloor.       \tag{1}
\]

For \(n\geq20\), one may replace \(L_n\) by
\(\lceil\log_2 n\rceil\).  The theorem is unconditional: it does not assume
that every corridor endpoint is represented, or that a representative is
unique.  It does not settle the remaining half-bit at an even rank.

## 1. Quotient coordinates

Put

\[
 M_d=2^d-1,\qquad
 q_{n,d}=\left\lfloor\frac{2^n}{M_d}\right\rfloor,
 \qquad
 H_n=\left\lfloor\frac{2^n}{465}\right\rfloor.
\]

Let \(t_n\) be the binary source digit, so that
\(H_n=2H_{n-1}+t_n\).  For a Boolean word
\(b=(b_1,\ldots,b_n)\), define

\[
 Q_0(b)=0,\qquad
 Q_j(b)=2Q_{j-1}(b)+t_j-\sum_{d\mid j}b_d.             \tag{2}
\]

The quotient weights satisfy

\[
 q_{j,d}=2q_{j-1,d}+\mathbf 1_{d\mid j}
\]

when \(d\leq j\), with the absent earlier weights interpreted as zero.
Induction in (2) therefore gives the exact formula

\[
 \boxed{
 Q_n(b)=H_n-\sum_{d=1}^n b_dq_{n,d}.
 }                                                        \tag{3}
\]

Write \(\mathcal T_n\) for the set of words satisfying

\[
 0\leq Q_j(b)\leq K_j\qquad(1\leq j\leq n).             \tag{4}
\]

Only the terminal consequence \(0\leq Q_n(b)\leq K_n\) is used in the
common-prefix proof.

## 2. The finite reverse-superincreasing gap

The Mersenne weights have the explicit tail gap

\[
\begin{aligned}
 \frac1{M_m}-\sum_{d>m}\frac1{M_d}
 &=\sum_{k\geq1}2^{-km}
   -\sum_{k\geq1}\sum_{d>m}2^{-kd} \\
 &=\sum_{k\geq2}
   2^{-km}\frac{2^k-2}{2^k-1} \\
 &\geq \frac23\,2^{-2m}.                              \tag{5}
\end{aligned}
\]

The \(k=1\) terms cancel exactly; the last line keeps only \(k=2\).
Consequently

\[
\begin{aligned}
 q_{n,m}-\sum_{d=m+1}^nq_{n,d}
 &>
 2^n\left(
 \frac1{M_m}-\sum_{d>m}\frac1{M_d}
 \right)-1 \\
 &\geq \frac23\,2^{\,n-2m}-1.                       \tag{6}
\end{aligned}
\]

The strict inequality uses
\(\lfloor x\rfloor>x-1\) for the first weight and
\(\lfloor x\rfloor\leq x\) for every later weight.  Thus (6) is an exact
finite quotient-weight separation, not an asymptotic estimate.

## 3. Common-prefix theorem

Let \(b,c\in\mathcal T_n\), and suppose that \(m\) is their first differing
rank.  After interchanging the words if necessary, take \(b_m-c_m=1\).
Equation (3) and the triangle inequality give

\[
\begin{aligned}
 |Q_n(b)-Q_n(c)|
 &=
 \left|
 \sum_{d=m}^n(b_d-c_d)q_{n,d}
 \right| \\
 &\geq q_{n,m}-\sum_{d=m+1}^nq_{n,d} \\
 &> \frac23\,2^{\,n-2m}-1.                         \tag{7}
\end{aligned}
\]

On the other hand, (4) gives

\[
 |Q_n(b)-Q_n(c)|\leq K_n.                          \tag{8}
\]

By definition, \(2^{L_n}>\frac32(K_n+1)\).  Hence (7)--(8) are
incompatible whenever \(n-2m\geq L_n\).  We have proved:

> **Quantitative common-prefix theorem.**  All words in
> \(\mathcal T_n\) agree through rank
> \(\lfloor(n-L_n)/2\rfloor\), with \(L_n\) as in (1).

For \(n\geq20\),

\[
 \frac32(K_n+1)
 \leq\frac32\left(\frac n{20}+1\right)<n.
\]

Therefore \(L_n\leq\lceil\log_2n\rceil\), and all corridor words agree
through

\[
 \boxed{
 \left\lfloor
 \frac{n-\lceil\log_2n\rceil}{2}
 \right\rfloor
 }\qquad(n\geq20).                                  \tag{9}
\]

In particular they agree through \(\lfloor n/3\rfloor\) for every \(n\).
For \(n\geq20\), this follows from
\[
 \lceil\log_2n\rceil
 \leq\log_2n+1
 \leq\frac n4+1
 \leq\frac n3.
\]
Here \(\log_2n\leq n/4\) for \(n\geq16\), for example by monotonicity of
\(x/4-\log_2x\) beyond \(x=16\).  Since the left side is an integer, it is
at most \(\lfloor n/3\rfloor\).  For \(3\leq n<20\),
we have \(K_n=0\); if \(m\leq\lfloor n/3\rfloor\), then (7) is strictly
positive, contradicting (8).  The cases \(n=1,2\) are vacuous.

## 4. Reduction of the proper-divisor load

For \(b\in\mathcal T_n\), put

\[
 g_n(b)=\sum_{\substack{d\mid n\\d<n}}b_d.
\]

Every proper divisor \(d\) of \(n\), other than \(n/2\) when \(n\) is
even, satisfies \(d\leq n/3\): the integer quotient \(n/d\) is then at
least \(3\).  The common-third theorem therefore gives a state-independent
integer \(h_n\) such that

\[
 \boxed{
 g_n(b)=
 \begin{cases}
 h_n, & n\ \text{odd},\\[2mm]
 h_n+b_{n/2}, & n\ \text{even}.
 \end{cases}
 }                                                        \tag{10}
\]

Thus the proper-divisor load is completely coherent at odd ranks.  At an
even rank, all state dependence is confined to the single half-rank bit.
This is exactly the bit responsible for the missing-endpoint calculation in
AnchorFourFiveCorridorCompatibility.md; no other divisor ancestry can enter
that seam.
