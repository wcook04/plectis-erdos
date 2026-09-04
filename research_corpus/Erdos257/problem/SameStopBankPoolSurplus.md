# Same-stop bank pools pay the complete carry tax

Status: exact positive rewrite, 2026-08-20.  This note proves the pooled form
of the bank intuition.  It is stronger than assigning one old-coordinate bank
to each tax separately: shallow overpayment is recycled inside one exact
positive residual.  The resulting rewrite is future-directed and contracts a
natural two-branch anchored load.  A global mixed-deadline parking theorem is
still required before this becomes a Booleanisation of \(1/21\).

Write

\[
 w_m=\frac1{2^m-1},\qquad M(a,b)=w_aw_b.
\]

## 1. The complete binary carry tax

For \(j\geq0\), define

\[
 \mathcal T_{n,j}=w_{n-j}-2^jw_n.
\]

Repeated use of \(w_{k-1}=2w_k+M(k-1,k)\) gives

\[
 \mathcal T_{n,j}
 =\sum_{q=1}^j2^{j-q}M(n-q,n-q+1).                 \tag{1}
\]

Thus \(\mathcal T_{n,j}\) is exactly the tax for carrying \(2^j\) copies
of \(w_n\) to one copy of \(w_{n-j}\).

## 2. The pooled bank-surplus identity

Assume

\[
 2\leq a\leq b,\qquad n=a+b,\qquad 0\leq j\leq b.
\]

Splitting a stop-\(n\) cylinder gives

\[
 M(a,b)=w_n+M(a,n)+M(n,b).                         \tag{2}
\]

The \(2^j\) copies of \(M(a,n)\) are the old-coordinate bank pool.  They
pay the whole tax (1), not tax-by-tax but in one exact identity:

\[
\begin{aligned}
 \mathcal B_{a,b,j}
 &:=2^jM(a,n)-\mathcal T_{n,j}\\
 &=2^jM(a,n)+2^jw_n-w_{n-j}\\
 &=2^{a+j}M(a,n)-w_{n-j}.                           \tag{3}
\end{aligned}
\]

The last equality uses \(1+w_a=2^aw_a\).  The final expression is the
first-atom residual of the power block \(2^{a+j}M(a,n)\).  Its leading
rank is

\[
 a+n-(a+j)=n-j,
\]

and \(a+j\leq a+b=n\).  Hence the exact digital comparison gives

\[
 \boxed{\mathcal B_{a,b,j}>0}.                     \tag{4}
\]

More precisely, this residual is certified to the old endpoint \(a\), so
its remaining carry depth after paying the \(j\)-level raw tax is

\[
 n-(a+j)=b-j.                                      \tag{5}
\]

This is the hereditary \(+1\) bank in pooled form.  Individual banks need
not dominate individual deep taxes.  All unused value from shallower
payments is retained in the single positive residual (3).

Combining (2) and (3) yields the full same-stop rewrite

\[
 \boxed{
 2^jM(a,b)
 =w_{n-j}+\mathcal B_{a,b,j}+2^jM(n,b).
 }                                                  \tag{6}
\]

Every term after the Boolean front is positive and belongs to a different
physical summand.  There is no reserve double-counting in (6).

## 3. Exact cylinder recoding and future direction

Put \(r=n-j\) and \(H=\operatorname{lcm}(n,r)\).  The anchored residual
transform gives

\[
 \mathcal B_{a,b,j}=B M(a,H),                       \tag{7}
\]

where

\[
 B=(2^H-1)
 \left(\frac{2^{a+j}}{2^n-1}
       -\frac{2^a-1}{2^r-1}\right)\in\mathbb N.    \tag{8}
\]

Every binary power block of (7) has deadline \(a\) and first front strictly
to the right of \(r\).  The other child in (6), oriented as
\(2^jM(b,n)\), has first front

\[
 b+n-j=r+b>r.                                      \tag{9}
\]

Thus (6) emits one rank-\(r\) atom and moves both residual branches strictly
right before any later carries.

## 4. A uniform two-branch load contraction

Use \(2^{j-b}\) as the anchored load of the parent \(2^jM(a,b)\).  For
this special bank residual, the scaled-value ratio is

\[
 R_{\rm bank}
 =\frac1{2^a-2^{-(b-j)}}
   \left(1-\frac{2^a(2^j-1)}{2^{a+b}-1}\right).     \tag{10}
\]

Its actual anchored load is strictly smaller than
\(R_{\rm bank}2^{j-b}\).  The untouched other child has load

\[
 2^{j-n}=2^{-a}2^{j-b}.
\]

If \(j=0\), the sum \(R_{\rm bank}+2^{-a}\) is maximized at
\(a=b=2\), where it is \(4/15+1/4=31/60\).  If \(a\geq3\), the bound

\[
 R_{\rm bank}+2^{-a}
 \leq\frac1{2^a-1}+2^{-a}<\frac{31}{60}
\]

suffices.  In the remaining case \(a=2,\ j\geq1\), direct
cross-multiplication gives \(R_{\rm bank}<1/4\), so the sum is less than
\(1/2\).  Therefore the total child load in (6) is strictly less than

\[
 \frac{31}{60}2^{j-b}.                              \tag{11}
\]

For the root \(M(2,3)\), the sum of the loads of the entire formally
unfolded two-branch tree is consequently bounded by

\[
 \frac{1/8}{1-31/60}=\frac{15}{58}<1.              \tag{12}
\]

This controls total generated packet load, but it is not by itself the
mixed-deadline Hall theorem.  Binary cohorts born at different stops can
meet at one rank with different remaining depths.  The still-open global
claim is that the physical surplus banks in (3), recursively recoded by
(7), can always be assigned to those mixed collisions without a deadline
overload or infinitely many rewrites of one fixed rank.

## 5. First generated LCM cohort

The first lift produces \(340M(10,11)\).  Its \(256\)-block has \(n=21\)
and \(j=8\).  A single bank \(M(10,21)\) is smaller than the deepest tax
\(M(13,14)\), so the literal one-bank-per-tax matching fails.  Nevertheless
(3) proves that all (256) banks pay the complete tax, leaving

\[
 \mathcal B_{10,11,8}
 =2^{18}M(10,21)-w_{13}>0                           \tag{13}
\]

with remaining depth \(3\).  This is why the pooled law, rather than the
slot count alone, is the invariant that survives generated LCM cohorts.

## 6. Reproduction

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/same_stop_bank_pool_surplus_audit.py

The script checks (1), (3), (6), (8), future direction, the load bound, and
the exact \(256M(10,11)\) receipt over bounded integer ranges.  The displayed
identities and inequalities are algebraic; the finite loop is only an audit.
