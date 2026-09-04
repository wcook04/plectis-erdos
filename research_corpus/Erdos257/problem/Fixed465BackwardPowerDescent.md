# Backward constraints at a first dyadically unsafe skip for \(1/465\)

## Result

Let

\[
 M_n=2^n-1,\qquad w_n=M_n^{-1},
\]

and run the ordinary greedy algorithm from \(1/465\). Suppose that rank
\(m\) is skipped and that its residual \(r_m\) is dyadically unsafe:

\[
 2^{-m}\leq r_m<w_m.                                  \tag{1}
\]

Let \(p<m\) be the last selected rank before \(m\). This note proves two
exact backward constraints.

First, reversing the selection at \(p\) does not produce an earlier unsafe
state. The reciprocal before that selection lies strictly above
\(2^{p-1}\), so every skipped rank on the whole preceding constant-residual
plateau is dyadically safe. Thus an unsafe state cannot descend to an earlier
unsafe state by reversing only its last selection.

Second, if \(m\geq2p\), the unreduced numerator of the fixed-source residual
strictly decreases at the selection \(p\). Consequently every unsafe state
satisfies the exact alternative

\[
 \boxed{p>m/2\quad\hbox{or the fixed-source numerator decreases at }p.}
                                                               \tag{2}
\]

The numerator decrease in (2) is not presently excluded. Hence these facts
do not prove dyadic undershoot for \(1/465\). They rule out the direct
backward-descent argument and identify the additional statement that such an
argument would require.

There is also an exact replacement for the missing decrease when
\(p>m/2\).  Put \(q=m-p\) and
\[
 \kappa_{p,m}
 =\left\lfloor\frac{M_p-1}{2^q+1}\right\rfloor.
\]
Then the Euclidean quotient of the post-selection numerator by the preceding
numerator is forced:
\[
 \boxed{
 \kappa_{p,m}<\frac ER<\kappa_{p,m}+1,
 \qquad
 0<E-\kappa_{p,m}R<R.}
\]
Thus every unsafe state produces a smaller positive least representative.
For \(p\leq m/2\), \(\kappa_{p,m}=0\) and this is the original numerator
contraction.  In the upper-half branch \(\kappa_{p,m}>0\), so the smaller
integer is not the actual post-selection numerator and need not remain on the
greedy prefix orbit.

In fact, the latter orbit-closure possibility can be excluded. Legal take,
skip, and denominator-refinement operations preserve the source coefficient
in the enlarged lattice. More decisively, the primitive prime divisor of the
largest newly selected Mersenne denominator prevents either least
representative from being the residual numerator of any later finite prefix.
Thus the Euclidean representative descent cannot be repaired by a finite
forward re-entry argument. An infinite tail has no largest rank, so this
obstruction does not decide infinite Boolean representability.

## 1. The fixed-source integer identity

Let \(F\) be the actual selected support below \(p\), and put

\[
 P=\prod_{d\in F}M_d,\qquad
 S=\sum_{d\in F}\frac{P}{M_d},\qquad
 R=P-465S.                                             \tag{3}
\]

For \(F=\varnothing\), use \(P=1\) and \(S=0\). The residual immediately
before the selection at \(p\) is exactly

\[
 \frac1{465}-\sum_{d\in F}w_d=\frac{R}{465P}.          \tag{4}
\]

This is the complete prefix identity for the fixed source; no freely chosen
cylinder start is introduced. Selection at \(p\) leaves

\[
 r_m=\frac{E}{465PM_p},\qquad
 E=M_pR-465P.                                          \tag{5}
\]

All intervening ranks are skipped, so the residual in (5) is unchanged up
to rank \(m\). Its displayed denominator is odd. Equality in the lower
bound of (1) is therefore impossible. After clearing the two strict
inequalities in (1), we obtain

\[
 \boxed{0<G:=2^mE-465PM_p<E.}                          \tag{6}
\]

Equation (6) is the unreduced version of the coprime corridor, and it retains
the complete fixed-source prefix product and numerator. It will be used
below only to locate the reversed state, not as a new formulation of the
original problem.

## 2. The exact reversed interval

Write \(z=1/r_m\), and let \(x\) be the reciprocal residual immediately
before the selection at \(p\). The reciprocal selection map and its inverse
are

\[
 z=\frac{M_px}{M_p-x},\qquad
 x=\psi_p(z):=\frac{M_pz}{M_p+z}.                      \tag{7}
\]

By (1),

\[
 M_m<z<2^m.
\]

Since \(\psi_p\) is strictly increasing,

\[
 \boxed{
 \frac{M_pM_m}{M_p+M_m}
 <x<
 \frac{M_p2^m}{M_p+2^m}.}                             \tag{8}
\]

The width of this interval is exactly

\[
 \boxed{
 \frac{M_p^2}{(M_p+M_m)(M_p+2^m)}.}                   \tag{9}
\]

Equivalently, the distance of the reversed reciprocal from the selected
Mersenne threshold satisfies

\[
 \boxed{
 \frac{M_p^2}{M_p+2^m}
 <M_p-x<
 \frac{M_p^2}{M_p+M_m}.}                              \tag{10}
\]

The fixed-source integers in (3)--(5) recover the same quantity without
reduction:

\[
 x=\frac{465P}{R},\qquad M_p-x=\frac ER.               \tag{11}
\]

Thus (8)--(10) are exact constraints on the actual prefix, rather than on
an arbitrary reciprocal state.

## 3. The previous plateau is strictly safe

For \(p\geq3\), direct expansion gives

\[
 \psi_p(M_{p+1})-2^{p-1}
 =\frac{2^{2p-1}-2^{p+1}+1}{3\cdot2^p-2}>0.           \tag{12}
\]

Here \(m\geq p+1\), and hence \(z>M_m\geq M_{p+1}\). Equations (7) and
(12) imply

\[
 \boxed{x>2^{p-1}.}                                    \tag{13}
\]

Let \(q<p\) be the selected rank preceding \(p\), if it exists. The
residual reciprocal is constant and equal to \(x\) at every skipped rank
\(j\) with \(q<j<p\). Since \(j\leq p-1\), (13) gives

\[
 r_j=\frac1x<2^{-(p-1)}\leq2^{-j}.                    \tag{14}
\]

Every such skipped rank is therefore dyadically safe. This conclusion does
not merely say that the first-unsafe hypothesis forbids an earlier event;
it follows from the inverse Mersenne map for any unsafe state. The first
reverse step necessarily leaves the unsafe power cell.

Consequently a backward proof cannot map an unsafe rank to an unsafe rank on
the immediately preceding plateau. It must reverse at least one additional
selection and introduce a different invariant; the 25-bit predecessor word
alone cannot supply that invariant.

## 4. A numerator contraction for long jumps

Equations (10) and (11) give

\[
 0<\frac ER<\frac{M_p^2}{M_p+M_m}.                    \tag{15}
\]

If \(m\geq2p\), then

\[
 M_p+M_m\geq M_p+M_{2p}>M_p^2.
\]

Therefore

\[
 \boxed{0<E<R.}                                       \tag{16}
\]

This proves (2). More quantitatively, (15) records the exact contraction
factor, which is asymptotic to \(2^{2p-m}\) when \(m-p\) is large.

The integer \(R\) starts at \(1\) before the first selection, but it need
not be monotone under later selections: the update is

\[
 R\longmapsto M_pR-465P.                              \tag{17}
\]

No theorem here excludes a decrease after previous increases. Thus (16) is
a necessary condition for a long-jump unsafe event, not a contradiction.
An actual backward descent would require a source-specific invariant showing
that the update (17) cannot decrease on the \(1/465\) greedy orbit, or a
different well-founded quantity which remains coupled to (3).

## 5. The forced least representative

The reciprocal interval determines more than the long-jump inequality.
Put
\[
 q=m-p,\qquad
 A=M_p,\qquad
 B=2^q,\qquad
 \kappa=\left\lfloor\frac{A-1}{B+1}\right\rfloor. \tag{18}
\]
Write
\[
 A-1=\kappa(B+1)+r,\qquad 0\leq r\leq B.          \tag{19}
\]
Since \(2^m=(A+1)B\), direct Euclidean division gives
\[
\begin{aligned}
 A^2-\kappa(A+2^m)
 &=A(r+1)-\kappa B>0,\\
 (A+2^m)-\bigl(A^2-\kappa(A+2^m)\bigr)
 &=A(B-r)+B(\kappa+1)>0.                          \tag{20}
\end{aligned}
\]
The same calculation with \(M_m=2^m-1\) gives
\[
\begin{aligned}
 A^2-\kappa(A+M_m)&>0,\\
 (A+M_m)-\bigl(A^2-\kappa(A+M_m)\bigr)
 &=A(B-r)+(B-1)(\kappa+1)>0.                     \tag{21}
\end{aligned}
\]
Equations (20)--(21), together with (10)--(11), say that both endpoints of
the exact interval for \(E/R\) lie strictly between \(\kappa\) and
\(\kappa+1\).  Hence
\[
 \boxed{\kappa<\frac ER<\kappa+1.}                \tag{22}
\]
Because \(E\) and \(R\) are positive integers, the least representative
\[
 \boxed{
 J:=E-\kappa R
 =(M_p-\kappa)R-465P}
 \tag{23}
\]
satisfies
\[
 \boxed{0<J<R.}                                   \tag{24}
\]

This includes both geometric branches.  If \(p\leq m/2\), then \(q\geq p\)
and \(\kappa=0\), so (24) is exactly (16).  If \(p>m/2\), then
\(\kappa\geq1\).  In the first part of that upper-half branch,
\[
 \frac m2<p<\frac{2m}{3},
\]
putting \(h=2p-m\) gives \(q>h\) and the explicit power quotient
\[
 \boxed{\kappa=M_h=2^h-1.}                        \tag{25}
\]
For shorter final plateaux, (18) gives the corresponding alternating binary
quotient without approximation.

> **Upper-half least-representative theorem.**  A saturated fatal gate whose
> last selected rank lies in \((m/2,m)\) forces the complete fixed-source
> prefix integers \(P,R,E\) into the single Euclidean cell (22), and its
> remainder \(J\) is strictly smaller than \(R\).

This is a genuine global-prefix restriction: \(R\) and \(E\) are the
unreduced numerators obtained from the actual support beginning at
\(1/465\).  It also identifies why the restriction does not yet close the
upper-half branch.  The integer \(J\) is a least representative of \(E\)
modulo \(R\), not the residual numerator at an earlier selected rank.
Consequently the small-margin repeat theorem cannot iterate (24) along the
actual predecessor chain without an additional identity placing \(J\) back
on that chain. A finite-prefix proof by this route would therefore require
orbit closure of the least-representative descent. Section 6 shows that this
required assertion is false.

The arithmetic obstruction can be stated sharply.  Put
\[
 g=\gcd(R,465P).
\]
Since \(E=M_pR-465P\) and \(J=E-\kappa R\),
\[
 \boxed{
 \gcd(E,R)=\gcd(J,R)=g.}                           \tag{26}
\]
Thus \(J/g\) and \(R/g\) are coprime.  The common factor is not generally
one: the unreduced prefix product can share factors with \(465\), which is
why (3)--(6) deliberately retain unreduced numerators.

There is a formal source representation for \(J\), but only after leaving
the Boolean fixed-source orbit.  With \(c=M_p-\kappa\), equations (3) and
(23) give
\[
 \boxed{
 J=cP-465(cS+P).}                                  \tag{27}
\]
Hence \(J\) is a numerator in the enlarged integer-coefficient lattice
\((C,T)\mapsto CP-465T\), with
\[
 (C,T)=(c,cS+P).                                   \tag{28}
\]
It is not an actual prefix numerator \(P'-465S'\) for the original
coefficient \(C=1\): the old selected terms acquire multiplicity \(c\), and
the additional term \(P\) has no Boolean selection interpretation.

The complementary representative is
\[
 \boxed{
 C:=(\kappa+1)R-E=R-J,\qquad
 0<C<R,\qquad \gcd(C,R)=g.}                       \tag{29}
\]
It is the smaller-looking representative in the middle upper-half range.
Indeed, when \(m/2<p<2m/3\), use \(h=2p-m\), \(q=m-p\),
\(x=2^h\), \(y=2^q\), and \(A=M_p=xy-1\).  Since
\(\kappa=M_h=x-1\),
\[
 \boxed{
 C=xR-E
 =465P-(2^hM_q-1)R.}                              \tag{30}
\]
Subtracting the two endpoints in (10)--(11) from \(x\) gives the exact
bounds
\[
 \boxed{
 \frac{x^2y+2xy-2x-1}{A+M_m}
 <\frac CR<
 \frac{x^2y+2xy-x-1}{A+2^m}.}                    \tag{31}
\]
The ratio is of order \(2^{h-q}\), so \(C\) can be exponentially smaller
than \(R\).  It still cannot contradict gcd preservation.  Since \(C\) is a
positive multiple of \(g\), the right side of (31) merely forces
\[
 \boxed{
 \frac Rg>
 \frac{A+2^m}{x^2y+2xy-x-1}.}                    \tag{32}
\]
The right side is of order \(2^{q-h}\).  No current fixed-source theorem
upper-bounds the reduced height \(R/g\); it can be vastly larger than this
power scale.  Thus there is no nontrivial subrange in which (31) alone gives
\(C<g\).  The complementary representative sharpens the required reduced
height but does not violate divisibility.

There is a concise anti-compression form.  Since
\(E\equiv-465P\pmod R\), \(J\) and \(C\) are the two positive oriented
representatives of \(-465P\) and \(465P\) modulo \(R\).  Therefore
\[
 \boxed{
 \mu:=\min\{J,C\}
 =\min\bigl\{[465P]_R,[-465P]_R\bigr\},
 \quad
 0<\mu\leq\frac R2,
 \quad
 \gcd(\mu,R)=g.}                                  \tag{33}
\]
Here \([z]_R\) denotes the least nonnegative residue.  The upper-half power
cell chooses the orientation and gives the much sharper bound (31), but the
bare least-residue inequality in (33) is universal arithmetic, not a greedy
contradiction.

Iterating ordinary Euclidean remainders therefore gives no reachability-free
contradiction.  It terminates at the expected common divisor \(g\) for every
positive integer pair, while the lattice coefficient in (28) changes
without an accompanying greedy support update. A finite-prefix descent would
have to place a subsequent least representative back on the actual
coefficient-one orbit; the next section proves that no such finite re-entry
is possible.

## 6. Legal generalized states and finite non-re-entry

It is useful first to make the legal state dynamics explicit. For an integer
coefficient \(a\), denominator product \(P\), and integer \(T\), put
\[
 \mathcal N_a(P,T)=aP-465T,
 \qquad
 \frac{\mathcal N_a(P,T)}{465P}=\frac a{465}-\frac TP.
                                                               \tag{34}
\]
Refining the displayed denominator by a fresh factor \(M_n\), without
selecting \(w_n\), gives
\[
 (P,T)\longmapsto(PM_n,M_nT),
 \qquad
 \mathcal N_a\longmapsto M_n\mathcal N_a.          \tag{35}
\]
Selecting \(w_n\) gives instead
\[
 (P,T)\longmapsto(PM_n,M_nT+P),
 \qquad
 \mathcal N_a\longmapsto M_n\mathcal N_a-465P.     \tag{36}
\]
An actual skip leaves the displayed state unchanged. In all three cases the
coefficient \(a\) is invariant. The representation (27) of \(J\) has
\(a=c=M_p-\kappa\), whereas an ordinary fixed-source prefix has \(a=1\).
Consequently no iteration of (35)--(36) can by itself turn (27) into an
ordinary prefix representation. Such a return would require a second,
arithmetically equal representation of the same rational number.

The complementary representative identifies exactly what that equality
would require. If
\[
 \rho=\frac{R}{465P},\qquad
 \rho_J=\frac{J}{465P},\qquad
 \rho_C=\frac{C}{465P},
\]
then (29) gives
\[
 \boxed{
 \rho-\rho_J=\frac{C}{465P},
 \qquad
 \rho-\rho_C=\frac{J}{465P}.}                     \tag{37}
\]
Thus a finite continuation from the prefix \(F\) could reach \(\rho_J\)
only if a nonempty finite set of fresh ranks had Boolean sum
\(C/(465P)\); reaching \(\rho_C\) would similarly require the sum
\(J/(465P)\).

The following standard consequence of the Bang--Zsigmondy theorem rules out
both equalities.

> **Private-prime lemma.** Let \(p\geq7\), let \(P\) be a product of
> Mersenne numbers \(M_d\) with \(d<p\), and let
> \(G\subseteq\{p,p+1,\ldots\}\) be finite and nonempty. The reduced
> denominator of
> \[
>  \sum_{n\in G}\frac1{M_n}
> \]
> has a prime divisor which does not divide \(465P\).

Indeed, put \(N=\max G\). Since \(N\geq7\), the exceptional Mersenne rank
\(6\) is avoided, and Bang--Zsigmondy supplies a prime \(\ell\mid M_N\)
which divides no \(M_k\) with \(k<N\). The prime \(\ell\) does not divide
\(P\). It also does not divide \(465=3\cdot5\cdot31\), since these three
primes already divide \(M_2,M_4,M_5\), respectively. On the product
denominator
\[
 Q=\prod_{n\in G}M_n,
\]
the numerator of the displayed sum is
\[
 U=\sum_{n\in G}\frac{Q}{M_n}.                    \tag{38}
\]
Modulo \(\ell\), every summand except \(Q/M_N\) vanishes, while
\(Q/M_N\not\equiv0\pmod\ell\). Hence \(\ell\nmid U\), and reduction cannot
remove \(\ell\) from the denominator.

For the fixed source \(1/465\), no rank below \(9\) can be selected because
\(M_n<465\) there. Thus the last selected rank \(p\) in the unsafe-gate
setting satisfies \(p\geq9\), and the private-prime lemma applies to every
finite continuation beginning with rank \(p\). Since both fractions on the
right of (37) have reduced denominator dividing \(465P\), neither can be
such a continuation sum. Residuals before the selection at \(p\) are at
least \(\rho\), while \(0<\rho_J,\rho_C<\rho\). Therefore
\[
 \boxed{
 \rho_J\ \text{and}\ \rho_C\ \text{are not residuals at any finite
 fixed-\(465\) prefix}.}                            \tag{39}
\]

This settles the finite orbit-closure question negatively. It does not
exclude an infinite Boolean tail with sum \(C/(465P)\) or \(J/(465P)\): an
infinite support has no maximal rank to which the private-prime argument can
be applied. Any use of the least representatives in a full proof must
therefore couple them directly to an infinite-tail invariant, rather than
attempting to re-enter the finite greedy-prefix orbit.

There is, however, an exact consumer for such an infinite tail. Suppose that
\(G\subseteq\{p,p+1,\ldots\}\) satisfies either
\[
 \sum_{n\in G}\frac1{M_n}=\frac{C}{465P}
 \qquad\text{or}\qquad
 \sum_{n\in G}\frac1{M_n}=\frac{J}{465P}.
\]
The private-prime lemma makes \(G\) infinite. Either equality is therefore
already a rational infinite Boolean Mersenne subseries, rather than an
intermediate finite-prefix closure certificate.

The machine-checked reciprocal-support theorem further implies
\[
 \boxed{\sum_{n\in G}\frac1n=\infty.}              \tag{40}
\]
Indeed,
`irrational_erdosSupportSeries_two_of_summable_reciprocal` proves that every
infinite support with summable reciprocal rank mass has irrational Mersenne
sum. The displayed rational equality gives the contrapositive. Thus the
existing reciprocal-summable theory does not contradict an infinite
correction support; it forces that support into the remaining
reciprocal-divergent regime.

The rational-support carry theorem has the same status here. Applied to
either displayed rational value, it produces an unbounded positive shifted
integer tail state and the common-multiple lower bounds. Those conclusions
are compatible with rationality and do not by themselves exclude the
correction support. Consequently an infinite-tail version of re-entry is
not a weaker repair of the Euclidean descent: constructing it would already
construct a rational infinite Boolean support, while excluding it in the
reciprocal-divergent regime is the unresolved dense-support problem.

## 7. Finite check

The companion program verifies (3)--(5) along the exact \(1/465\) greedy
orbit through a chosen finite depth. At depth \(2000\), it finds no unsafe
skip and no decrease of the unreduced numerator \(R\). These are finite
observations only.

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/fixed465_backward_power_descent.py
```

The proof of (6)--(16) and (18)--(40) is the integer and rational calculation
above together with the stated Bang--Zsigmondy input; the finite program is
not used to promote those statements to greater logical scope. It checks the
forced Euclidean cell and gcd preservation on exact rational samples across
both geometric branches. It also verifies the primitive-prime input for
Mersenne ranks \(7\) through \(30\). This last computation is a finite check
only; the universal existence statement used in the private-prime lemma is
the classical theorem.
