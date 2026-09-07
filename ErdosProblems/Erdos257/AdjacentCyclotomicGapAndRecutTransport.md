# Adjacent cyclotomic gaps and the forced recut transport

Write \(M_n=2^n-1\).  Let \(H\) be divisible by each of \(15,r,r-1\), and put
\[
 D=D_{H,r}=\prod_{\substack{d\mid H\\d\le r}}\Phi_d(2).
\]
After the factors above \(r\) have been removed, the root coefficient and a
protected divisor-prefix genealogy \(F\subseteq\{n:n\mid H,\ n\le r-2\}\)
give
\[
 K=1510\frac D{M_{15}}-3\sum_{n\in F}\frac D{M_n}. \tag{1}
\]
The rank-\(r\) fatal corridor is
\[
 L=6\frac D{M_r}\le K<U=3\frac D{M_{r-1}},         \tag{2}
\]
with width
\[
 W=U-L=\frac{3D}{M_{r-1}M_r}.                     \tag{3}
\]

## 1. The adjacent-gap semigroup obstruction

Assume \(r\ge16\).  Every term of (1) is divisible by both
\(\Phi_r(2)\) and \(\Phi_{r-1}(2)\).  For \(r>16\), this is immediate because
all denominators have rank below \(r-1\).  When \(r=16\), the root denominator
cancels \(\Phi_{15}(2)=151\), but its coefficient restores that factor because
\(151\mid1510\).

The lower endpoint \(L\) is divisible by \(\Phi_{r-1}(2)\), and the upper
endpoint \(U\) is divisible by \(\Phi_r(2)\).  Therefore a corridor hit has
\[
 E:=K-L=a\Phi_{r-1}(2),
 \qquad
 G:=U-K=b\Phi_r(2)                                 \tag{4}
\]
for integers \(a\ge0\) and \(b\ge1\).

In fact \(a>0\).  If \(E=0\), then \(K=L\).  Let \(p_r\) be a primitive
prime divisor of \(M_r\).  Such a prime exists for \(r\ge16\).  It divides
every term in (1), hence \(K\), but after the factor \(M_r\) is removed it
does not divide \(L=6D/M_r\); also \(p_r>3\).  Thus \(K\ne L\).

Adding the two gaps in (4) gives the necessary condition
\[
 \boxed{
 W=a\Phi_{r-1}(2)+b\Phi_r(2),\qquad a,b\in\mathbb N_{>0}.} \tag{5}
\]
This is stronger than either one-sided primitive residue.  In particular,
\[
 W<\Phi_{r-1}(2)+\Phi_r(2)                         \tag{6}
\]
excludes the corridor immediately, while larger widths can still fail the
positive two-coin congruence (5).

### The first transported height

At \(H=240,r=16\), exact cyclotomic cancellation gives
\[
 W=1287,\qquad \Phi_{15}(2)=151,\qquad\Phi_{16}(2)=257.
\]
There are no positive integers \(a,b\) with
\[
 1287=151a+257b.                                   \tag{7}
\]
Indeed \(1\le b\le4\), and the four remainders
\(1287-257b\) are \(1030,773,516,259\), none divisible by \(151\).
Hence the complete divisor-only root genealogy cannot enter the moving
rank-\(16\) corridor at height \(240\).  No Boolean subset enumeration is
used.

## 2. Exact transport to the next rank

The lower gap \(E\) is also the state variable controlling the next recut.
Suppose all old coefficients are lifted from \(D\) to \(D'=\theta D\).
At rank \(r+1\), the new upper endpoint is
\[
 U'=3\frac{D'}{M_r}.
\]
The two literal extensions of the old genealogy have coefficients
\[
 \begin{aligned}
 K_{\rm skip}&=\theta K,\\
 K_{\rm take}&=\theta K-3\frac{D'}{M_r}
               =U'+\theta E.                     \tag{8}
 \end{aligned}
\]
Thus \(K_{\rm skip}>U'\), and \(K_{\rm take}\ge U'\).  Neither lies in the
next half-open fatal corridor.  A fatal genealogy can never track through
two consecutive ranks by literal extension.

More precisely, let \(B=K_{\rm take}\), let \(W'\) be the next corridor
width, and let another genealogy \(G\) have charge increment
\[
 \Delta=
 \sum_{n\in G}\frac{D'}{M_n}
 -\left(\sum_{n\in F}\frac{D'}{M_n}+\frac{D'}{M_r}\right).
\]
Its coefficient is \(B-3\Delta\).  It hits the next corridor if and only if
\[
 \boxed{\theta E<3\Delta\le\theta E+W'.}           \tag{9}
\]
In particular \(\Delta>0\): the next exceptional genealogy, if one exists,
must be a genuine lexicographic recut to a larger Boolean charge.  The
normalized lower debt \(e=E/W\) would obey
\[
 e'=1+\lambda e-q,\qquad
 \lambda=\frac{M_{r+1}}{M_{r-1}}>4,\qquad
 q=\frac{3\Delta}{W'},                            \tag{10}
\]
with \(\lambda e<q<\lambda e+1\).  The strict upper inequality follows
because the next lower endpoint is itself excluded by the primitive
rank-\(r+1\) charge.

## 3. The debt cannot survive one rank

In fact no Boolean \(\Delta\) can satisfy the requirements for a consecutive
fatal hit.  This holds even if the second genealogy is unrelated to the
first one.

Put \(w_n=1/M_n\).  The elementary inequality
\[
 w_n>2w_{n+1}                                     \tag{11}
\]
follows by cross multiplication.  Consequently, for any finite string
\(w_j,\ldots,w_N\), two distinct Boolean subset sums differ in absolute
value by at least \(w_N\).  To see this, take the first differing rank.  If
it is \(N\), the difference is \(w_N\).  Otherwise use (11) inductively:
\[
 w_j-\sum_{k=j+1}^{N}w_k>w_N.                    \tag{12}
\]

Now suppose genealogies \(F\) and \(G\) hit the rank-\(r\) and rank-\(r+1\)
corridors for the same incoming root charge.  Set
\[
 Q=\sum_{n\in G}w_n-\sum_{n\in F}w_n.
\]
Subtracting their two residuals gives
\[
 \frac1{M_r}<Q<
 \frac1{M_{r-1}}-\frac2{M_{r+1}}
 <\frac1{M_{r-1}}.                               \tag{13}
\]
Both genealogies use only ranks at most \(r-1\).  But (12) says that a
nonzero difference of their Boolean sums has magnitude at least
\(1/M_{r-1}\), contradicting (13).  Therefore
\[
 \boxed{\text{fatal corridors at consecutive ranks are disjoint for every
 incoming charge and every pair of Boolean genealogies}.}              \tag{14}
\]

Thus the normalized recurrence (10) has no admissible Boolean transition:
every fatal debt dies immediately rather than increasing or decreasing
along a multi-recut chain.

## 4. A skipped rank still cannot revive the debt

Fatal corridors two ranks apart are also disjoint.  Suppose ranks \(r\) and
\(r+2\) were both hit, and let
\[
 Q=\sum_{n\in G}w_n-\sum_{n\in F}w_n
\]
be the difference of the two genealogical charges.  Subtracting the
corridor inequalities now forces
\[
 2w_r-w_{r+1}<Q<w_{r-1}-2w_{r+2}.                \tag{15}
\]
Both genealogies use ranks at most \(r\).

Take the first differing rank \(j\).  With the positive sign fixed there,
the smallest possible charge difference is
\[
 m_{j,r}=w_j-\sum_{k=j+1}^{r}w_k.                \tag{16}
\]
Every other difference with the same first rank is obtained from \(m_{j,r}\)
by adding nonnegative integer combinations of later \(w_k\), so its first
possible increment is at least \(w_r\).  If \(j=r\), the only value is
\(w_r\), which is below (15).  If \(j<r\), then \(m_{j,r}>w_r\) by (12),
while
\[
 w_{r-1}-2w_{r+2}<2w_r.                           \tag{17}
\]
Consequently (15) can contain a charge only if it contains the baseline
\(m_{j,r}\) itself.

The baseline admits an exact head-tail decomposition.  Define
\[
 T_r=\sum_{k=r+1}^{\infty}w_k,\qquad
 \delta_j=w_j-\sum_{k=j+1}^{\infty}w_k.
\]
Then \(m_{j,r}=T_r+\delta_j\), and geometric expansion gives
\[
 \delta_j
 =\sum_{\ell=2}^{\infty}
 \frac{2^\ell-2}{2^\ell-1}\,2^{-j\ell}.           \tag{18}
\]
In particular,
\[
 \frac23\,2^{-2j}<\delta_j
 <\frac23\,2^{-2j}+
 \frac{2^{-3j}}{1-2^{-j}}.                        \tag{19}
\]

Subtract \(T_r\) from (15).  Expanding the two endpoints in the same way
shows, for \(r\ge9\),
\[
 \begin{aligned}
 2w_r-w_{r+1}-T_r&>\frac12\,2^{-r},\\
 w_{r-1}-2w_{r+2}-T_r&<\frac23\,2^{-r}.           \tag{20}
 \end{aligned}
\]
If \(2j\le r\), the lower bound in (19) is at least
\((2/3)2^{-r}\), above the interval (20).  If \(2j\ge r+1\), the upper bound
in (19) is less than \((1/2)2^{-r}\), below it.  These two integer cases
exhaust all \(j\).  Hence no baseline \(m_{j,r}\) lies in (15), proving
\[
 \boxed{\text{fatal corridors at ranks }r\text{ and }r+2\text{ are
 disjoint for every incoming charge and every pair of genealogies}.}    \tag{21}
\]

Equations (5), (9), (14), and (21) are the fixed-root transport law.  The
adjacent cyclotomic pulses first quantize the old lower and upper gaps; the
lower gap then becomes the exact debt which a different genealogy must pay at the
next rank; reverse superincreasingness proves that this debt cannot be paid.
This is the algebraic identity shared by zero-buffer failure, borrow failure,
and seam recutting.

The theorem excludes propagation across zero or one skipped ranks.  It does
not yet exclude an isolated first hit or re-entry after skipping at least
two ranks.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/adjacent_cyclotomic_gap_and_recut_transport.py

for exact semigroup exclusions and transport identities.
