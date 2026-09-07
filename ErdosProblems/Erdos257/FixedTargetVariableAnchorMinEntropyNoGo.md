# Fixed-target variable-anchor anti-compression no-go

## Status

This note gives an exact counterfamily to a tempting strengthening of the
least-representative route.  The starting rational is fixed: it is \(1/v\),
and in particular may be \(1/21\) or \(1/465\).  The greedy decisions are
genuine decisions for the Mersenne reciprocals.  Only the initial rank is
allowed to vary.

The conclusion is deliberately limited.  Fixed target, greedy
admissibility, an arbitrarily long admissible block, and an arbitrarily
large state do **not** force a state-size lower bound for the least
representative.  Any such estimate for the original process beginning at
rank \(1\) must use the omitted source ancestry.  The construction does not
produce a dangerous skipped state on the original \(1/465\) orbit and does
not contradict a theorem conditional on the full saturated-gate geometry.

Put

\[
 M_j=2^j-1.
\]

For a tail anchored at rank \(N\), run the ordinary greedy algorithm for the
fixed target \(1/v\) using

\[
 \frac1{M_N},\frac1{M_{N+1}},\ldots .
\]

## 1. The tail word is genuinely greedy

For every \(j\geq1\),

\[
 \frac1{M_j}<2^{1-j}.
\]

Consequently

\[
 \sum_{j=N}^{\infty}\frac1{M_j}<2^{2-N}.          \tag{1}
\]

If \(2^{N-2}>v\), the whole tail sum is smaller than \(1/v\).  Therefore
every greedy decision in the tail is \(1\): before any term is considered,
the residual still exceeds that term because even the sum of all terms
from that point onward is smaller than the residual.  Thus the word

\[
 111\cdots                                                   \tag{2}
\]

is not a freely prescribed cylinder.  It is the deterministic fixed-target
tail orbit.

## 2. One term has a bounded least representative

After its first selected term, retain the unreduced prefix state

\[
 P=M_N,\qquad R=M_N-v,
\]

so that

\[
 \frac1v-\frac1{M_N}=\frac{R}{vP}.
\]

Since \(P=R+v\),

\[
 vP\equiv v^2\pmod R.                              \tag{3}
\]

Let

\[
 \mu_v(P,R)=\min\{[vP]_R,[-vP]_R\}.
\]

Whenever \(R>2v^2\), equation (3) gives the exact identity

\[
 \boxed{\mu_v(P,R)=v^2.}                           \tag{4}
\]

The modulus \(R=M_N-v\) tends to infinity while the least representative
is constant.  In particular, for every function \(F(R)\to\infty\), the
anchor-uniform claim

\[
 \mu_v(P,R)\geq F(R)                               \tag{5}
\]

fails on genuine greedy prefixes for the fixed target \(1/v\).

For the two targets used in the present problem, (4) reads

\[
 \mu_{21}=441\quad(N\geq10),
 \qquad
 \mu_{465}=216225\quad(N\geq19).                  \tag{6}
\]

The slightly stronger lower bounds on \(N\) needed for the infinite word
(2) are already implied by the displayed ranges in (6).

## 3. Arbitrarily long blocks remain relatively compressed

The same phenomenon is not confined to a one-letter cylinder.  After the
first \(L\) terms of (2), put

\[
 P=\prod_{j=N}^{N+L-1}M_j,
 \qquad
 A=\sum_{j=N}^{N+L-1}\frac{P}{M_j},
 \qquad
 R=P-vA.                                           \tag{7}
\]

Then

\[
 \frac1v-\sum_{j=N}^{N+L-1}\frac1{M_j}
   =\frac{R}{vP}
\]

and

\[
 vP-vR=v^2A.                                       \tag{8}
\]

If \(v^2A<R/2\), the nearest multiple of \(R\) to \(vP\) is \(vR\), hence

\[
 \boxed{\mu_v(P,R)=v^2A.}                          \tag{9}
\]

Writing

\[
 s=\frac AP=\sum_{j=N}^{N+L-1}\frac1{M_j},
\]

equations (1), (7), and (9) give

\[
 \frac{\mu_v(P,R)}R
 =\frac{v^2s}{1-vs}
 <\frac{v^2 2^{2-N}}{1-v2^{2-N}}.                 \tag{10}
\]

The sufficient condition

\[
 v(2v+1)2^{2-N}<1                                  \tag{11}
\]

ensures \(v^2A<R/2\), uniformly in \(L\).  Thus for every prescribed block
length \(L\) and every \(\varepsilon>0\), a sufficiently late anchor gives
an actual fixed-target greedy block with

\[
 \frac{\mu_v(P,R)}R<\varepsilon.                  \tag{12}
\]

This does not say that the absolute integer in (9) stays bounded when
\(L\to\infty\).  The exact bounded statement is (4); the long-block
statement is the relative estimate (12).

## 4. Consequence for the fixed-\(465\) route

The Collatz-style hope was that greedy admissibility plus a large affine
cylinder might itself prevent a very small least representative.  Equations
(4) and (12) rule out that principle in the variable-anchor Mersenne
setting, even after the arbitrary starting residual from the earlier
affine-cylinder counterexample is replaced by the exact target \(1/v\).

What distinguishes the original orbit is precisely the history which this
tail re-anchoring deletes.  In the process beginning at rank \(1\), a late
rank \(N\) cannot be the first selected term: once \(M_j\geq v\), the target
residual forces a selection.  Therefore any viable min-entropy theorem must
remain coupled to the complete source prefix (or to an equivalent
unbounded source-carry invariant).  A block law which permits re-anchoring
cannot prove it.

The companion audit checks the exact identities, the greedy word, and the
uniform long-block inequality for \(v=21\) and \(v=465\).
