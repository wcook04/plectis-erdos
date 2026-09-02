# Anchor-Four-Five Dynamic Ownership Flow

## Purpose and status

This note replaces the static-bank and laminar-owner snapshots at the first
post-prefix collision for the target \(x=1/465\).  It proves four exact facts.

1. The take at rank \(102\) has an ownership recut that leaves the residual
   \(H_{105}\) with only its original \(M(25,29)\) ancestry.
2. Every later exact residual below \(w_{25}\) has a lossless, forward-only
   anchor-25 ownership DAG that survives every greedy take or skip.
3. The first live anchor packet and the scalar greedy front differ by at most
   one rank.
4. A fatal gap forces a run of 25 leading ones in a precisely defined periodic
   binary coefficient.

These are ordinary exact deductions.  They do **not** prove that the forced
25-run never occurs, and therefore do not finish the dense-support case.

Write
\[
  w_n=\frac1{2^n-1},\qquad
  M(a,b)=\frac1{(2^a-1)(2^b-1)}.
\]

## 1. The rank-102 ownership recut

The exact physical construction through rank \(102\) has, immediately before
the take at \(102\), two positive cohorts:

- \(C_{104}\), whose ancestry is the one original \(M(25,29)\) cohort;
- \(R_{103}\), whose ancestry is the fifteen original \(M(4,5)\) cohorts.

The previously certified inequalities are
\[
  0<C_{104}<w_{102},\qquad
  0<R_{103}<w_{102},\qquad
  C_{104}+R_{103}>w_{102},
\]
and the post-take residual is
\[
  H_{105}=C_{104}+R_{103}-w_{102}>0.
\]
Define the exact slice
\[
  p=w_{102}-R_{103}.
\]
Then
\[
  0<p<C_{104},\qquad
  R_{103}+p=w_{102},\qquad
  C_{104}=p+H_{105}.
\]
Cylinder common refinement therefore permits the following lossless physical
recut: split \(C_{104}\) into the disjoint subcohorts \(p\) and \(H_{105}\),
use \(R_{103}\sqcup p\) for the rank-102 atom, and retain \(H_{105}\).
Consequently the residual after rank \(102\) need not carry a merged
sixteen-owner label.  It may retain the single original anchor-25 ancestry.

This is an ownership statement, not merely a scalar identity: common cylinder
refinement realizes any rational cut whose denominator divides a sufficiently
high binary cylinder level, and the displayed pieces are all positive.

## 2. The anchor-25 packet DAG

Let \(X\) be any nonzero later residual satisfying \(X<w_{25}\), and put
\[
  c=(2^{25}-1)X\in(0,1).
\]
Every residual in this orbit has odd denominator, so \(c\) is not a nonzero
dyadic rational.  Use its unique nonterminating binary expansion
\[
  c=\sum_{k\ge1}\varepsilon_k2^{-k},
  \qquad \varepsilon_k\in\{0,1\}.
\]
Define the protected anchor packets
\[
  P_k=2^{-k}w_{25}.
\]
Then, exactly,
\[
  X=\sum_{k\ge1}\varepsilon_kP_k.
\]
Each packet has the same hard anchor deadline \(25\), while its scalar leading
rank is \(25+k\).

For a prospective atom at rank \(n>25\), scale its demand by \(w_{25}\):
\[
  \beta_n=\frac{w_n}{w_{25}}
         =\frac{2^{25}-1}{2^n-1}.
\]
Its binary expansion is the periodic block identity
\[
  \beta_n
  =\sum_{q\ge1}\sum_{i=0}^{24}2^{-(qn-i)}.
\]
Thus one copy of \(w_n\) is exactly the union of the anchor packets at
positions
\[
  qn-24,qn-23,\ldots,qn \quad(q\ge1).
\]

### Lossless refinement lemma

Suppose \(0\le y\le x<1\).  A packet forest representing the binary mass
\(x\) can be partitioned into packet forests of masses \(y\) and \(x-y\)
using only the forward split
\[
  2^{-k}\longmapsto 2\cdot2^{-(k+1)}.
\]

Indeed, recursively split precisely those nodes whose dyadic interval meets
the boundary between the initial masses \(y\) and \(x-y\).  At every finite
depth the children partition their parent, no child has two parents, and the
unresolved boundary mass tends to zero.  The limiting forests are disjoint and
have the required exact masses.  This is ordinary binary borrowing expressed
as a locally finite directed acyclic graph; it neither clones nor spends an
ancestral root twice.

Apply the lemma with \(x=c\) and \(y=\beta_n\).  If the exact greedy rule takes
rank \(n\), then \(c\ge\beta_n\); refine the current roots into the periodic
demand forest for \(\beta_n\) and the residual forest for
\(c-\beta_n\).  Consume the former and retain the latter.  If the rule skips,
retain the forest unchanged.  Hence this state is closed under an arbitrary
sequence of exact take/skip decisions.  All ancestry moves forward along the
DAG, so the backward-crossing failure of laminar interval labels is absent.

## 3. One-rank frontier lag

Let
\[
  k=\min\{j:\varepsilon_j=1\},\qquad r=25+k.
\]
Then
\[
  P_k\le X<2P_k=P_{k-1}.
\]
For \(r>26\), the standard power-packet front inequalities give
\[
  w_r<P_k<w_{r-1},
  \qquad
  P_{k-1}<w_{r-2}.
\]
If
\[
  f(X)=\min\{m:w_m\le X\}
\]
is the scalar greedy front, it follows that
\[
  f(X)\in\{r-1,r\}.
\]
Thus the live ownership front has a uniform one-rank lag from the true scalar
front at every later state, even though its binary coefficient is globally
recut after a take.

## 4. Fatal gap implies 25 leading ones

Assume the scalar front is \(f(X)=r\).  Then the fatal-gap condition is
\[
  X\ge2w_r,
\]
or, after anchor scaling,
\[
  c\ge2\beta_r.
\]
Since \(k=r-25\), the first block in the binary expansion of
\(2\beta_r\) occupies exactly the positions
\[
  k,k+1,\ldots,k+24.
\]
There is no earlier nonzero digit.  Also the definition of \(k\) gives
\(c<2^{-k+1}\).  Lexicographic comparison of the two nonterminating binary
expansions therefore proves
\[
  \varepsilon_k=\varepsilon_{k+1}=\cdots=
  \varepsilon_{k+24}=1.
\]

So a fatal gap is possible only if the current anchor coefficient begins with
25 consecutive ones at its first nonzero digit.  This is necessary, not
sufficient.

## 5. Exact finite coefficient dynamics

The packet state has a finite periodic encoding at every finite time.  Choose
\(L\) divisible by \(20\), by \(25\), and by every exponent already subtracted
from \(1/465\).  Then
\[
  R=(2^L-1)X\in\mathbb Z,
  \qquad
  B=(2^{25}-1)R,
\]
and, while \(0<X<w_{25}\),
\[
  0<B<2^L-1,
  \qquad
  c=\frac{B}{2^L-1}.
\]
Therefore the binary expansion of \(c\) is the purely periodic repetition of
the \(L\)-bit word for \(B\), padded on the left with zeros.

At a decision rank \(n\), put
\[
  L'=\operatorname{lcm}(L,n),\qquad
  U=\frac{2^{L'}-1}{2^L-1},\qquad
  T_n=\frac{2^{L'}-1}{2^n-1}.
\]
The exact state update is
\[
  (L,R)\longmapsto
  \begin{cases}
    (L',UR),&\text{skip},\\
    (L',UR-T_n),&\text{take}.
  \end{cases}
\]
Equivalently, \(B'=(2^{25}-1)R'\).  A take is admissible precisely when
\(UR\ge T_n\); it leaves a same-rank duplicate precisely when
\(UR-T_n\ge T_n\), or \(UR\ge2T_n\).

This answers the fixed-expansion question sharply.  Between takes the physical
packet forest may be retained, but the canonical coefficient is not merely a
shift or an affine image of one fixed binary word: the common height changes by
an lcm lift, and each take subtracts a rank-dependent periodic mask.  It is,
however, an exact finite periodic automaton state \((L,R)\) with the displayed
integer transition law.

## 6. The remaining theorem

The ownership problem and the scalar/ownership frontier comparison are closed
for the post-rank-102 orbit.  What remains is purely arithmetic:

> Along the exact recurrence above, prove that whenever the scalar front equals
> \(r\), the periodic word \(B/(2^L-1)\) cannot begin with 25 ones at its first
> nonzero digit.

The companion script checks the source identities, the coefficient update, the
periodic demand block, and a few named finite states.  Those finite observations
are diagnostics only; they are not evidence for an all-depth proof.
