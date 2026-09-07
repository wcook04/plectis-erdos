# Winding and the future-divisor resolvent for \(90/511\)

Status: exact identities and exact counterexamples, with finite audits recorded
separately, 2026-08-20.  No result below proves the all-depth inequality

\[
  F_N=P_N-2Q_N\geq 0. \tag{SC0}
\]

## 1. The nine-phase clock

Let \(x=90/511\), and let \(b_n\) be its greedy Mersenne digits.  Write

\[
  h_n=\sum_{d\mid n}b_d,
  \qquad
  Q_n=2Q_{n-1}+t_n-h_n,
  \qquad
  F_n=P_n-2Q_n,
\]

where the binary source word is \(t_1\ldots t_9=001011010\).  If

\[
  p_n=h_n-b_n,
  \qquad
  s_n={\bf1}_{2\mid n}b_{n/2},
\]

then direct subtraction of the \(P\)- and \(Q\)-recurrences gives

\[
  \boxed{F_n-F_{n-1}=p_n+s_n-Q_n.}                 \tag{1}
\]

Thus a first negative value at \(n\) must satisfy

\[
  Q_n\geq F_{n-1}+p_n+s_n+1.                       \tag{2}
\]

This is an exact necessary and sufficient local condition once the state at
\(n-1\) is fixed.  It is not a reduction of (SC0).

Put \(\alpha_n=\{2^nx\}\).  At the even horizons \(n=2R\), the complete
nine-phase table is

\[
\begin{array}{c|rrrrrrrrr}
R\bmod9&0&1&2&3&4&5&6&7&8\\ \hline
511\alpha_{2R}&90&360&418&139&45&180&209&325&278\\
(t_{2R+1},t_{2R+2})
 &(0,0)&(1,0)&(1,1)&(0,1)&(0,0)&(0,1)&(0,1)&(1,0)&(1,0).
\end{array}                                         \tag{3}
\]

This table determines the source forcing, but not the selected-divisor
ancestry appearing in (1).

## 2. The protective winding transfers, but becomes the desired sign

At a rejected rank \(m\), force \(b_m=1\) and put all later digits equal to
zero.  Denote this protective alternate by \(a^{(m)}\).  If \(Y_m\) is the
actual scaled remainder before the decision at \(m\), put

\[
  \Delta_m=\frac{2^m}{2^m-1}-Y_m>0.
\]

Exactly as for the target \(1/21\), the alternate phase satisfies

\[
  \Phi^{(m)}_{m+k}-\alpha_{m+k}
  =Q^{(m)}_{m+k}+2^k\Delta_m.                       \tag{4}
\]

Consequently the integer height

\[
  H_{m,k}=F^{(m)}_{m+k}-k-\lceil2^k\Delta_m\rceil   \tag{5}
\]

has the same exact winding recurrence as in PhaseWindingBarrier.md.  If the
actual word beginning at \(m\) is \(0\,1^k\) and \(k<m\), the exchange of the
two upper-half words \(1\,0^k\) and \(0\,1^k\) gives

\[
  \boxed{H_{m,k}=F_{m+k}+1-\lceil2^k\Delta_m\rceil.}\tag{6}
\]

Therefore \(H_{m,k}\geq0\) is exactly (SC0) on that seam whenever the ceiling
is one, and is stronger when the ceiling is larger.  The winding height is
then a useful decomposition, but not an independent route to (SC0).

The exact finite audit through rank \(5000\), with \(k\leq64\), found:

* \(H_{2,1}=H_{4,1}=-1\);
* \(H_{m,k}\geq1\) for every audited rejected \(m\geq6\);
* every realised \(0\,1^k\) seam with \(m\geq6\) had
  \(\lceil2^k\Delta_m\rceil=1\).

The last line means that, on every later realised seam in the audit, (5) was
literally \(F_{m+k}\).  It is finite evidence of equivalence, not an
all-depth sign law.

## 3. Why the order-\(73\) phase cannot decide the payment bit

Since \(511=7\cdot73\) and \({\rm ord}_{73}(2)=9\), it is natural to retain
the principal \(73\)-adic residue of (4).  For a protective support \(D\), a
horizon \(n<657=9\cdot73\), and

\[
  u_d=\frac{2^d-1}{73}\quad(9\mid d),
\]

every relevant \(u_d\) is invertible modulo \(73\).  Multiplying the phase by
\(73\) gives the exact residue formula

\[
  73(\Phi_n-\alpha_n)
  \equiv
  \sum_{\substack{d\in D\\9\mid d}}
     2^{\,n\bmod d}u_d^{-1}
  - (511\alpha_n)7^{-1}\pmod {73}.                  \tag{7}
\]

Terms with \(9\nmid d\) vanish after multiplication by \(73\).  Formula (7)
is exact below the first possible double \(73\)-pole, but it does not
determine the Boolean winding payment

\[
  \epsilon_{m,k}
  =2\lceil2^{k-1}\Delta_m\rceil-\lceil2^k\Delta_m\rceil.
\]

There is already a small counterexample.  The rejected ranks \(m=6\) and
\(m=8\) have

\[
  \Delta_6=\frac{135616}{142569},
  \qquad
  \Delta_8=\frac{3010816}{4039455}.
\]

At the common phase horizon \(n=9\), the pair \((\text{residue in (7)},
n\bmod9)\) is \((8,0)\) in both cases.  Nevertheless

\[
\begin{array}{c|cc|c}
(m,k)&\lceil2^{k-1}\Delta_m\rceil&
       \lceil2^k\Delta_m\rceil&\epsilon_{m,k}\\ \hline
(6,4)&8&16&0\\
(8,2)&2&3&1.
\end{array}                                         \tag{8}
\]

Thus even the exact principal residue together with the nine-phase class
does not determine the sign contribution in the winding recurrence.

There is also a target-level obstruction to a phase-only modulo-\(73\)
argument:

\[
  \frac{90}{511}=\frac17+\frac{17}{511}.             \tag{9}
\]

The numerators \(90\) and \(17\) are congruent modulo \(73\), so their entire
order-nine residue orbits modulo \(73\) agree.  Their greedy residuals agree
after rank \(3\), because \(90/511\) selects \(w_3=1/7\) and \(17/511\) does
not.  Yet exact recurrence gives

\[
  Q_{90/511}(9)=Q_{17/511}(9)=1,
  \qquad
  F_{90/511}(9)=1,
  \qquad
  F_{17/511}(9)=-1.                                  \tag{10}
\]

The common modulo-\(73\) target phase is blind to the rank-\(3\) ancestry and
the accompanying change of source clock.  Any successful congruence law
must retain at least the complementary factor \(7\) or equivalent labelled
support data.

## 4. The labelled future-divisor resolvent is lossless

Let \(D_R=\{d\leq R:b_d=1\}\), and define

\[
  \nu_R(c)=\#\{d\in D_R:d\mid 2R+c\},\qquad c\geq1.
\]

Its formal generating function is

\[
  \mathcal R_R(z)=\sum_{c\geq1}\nu_R(c)z^c
  =\sum_{d\in D_R}\frac{z^{\rho_R(d)}}{1-z^d},       \tag{11}
\]

where \(\rho_R(d)\in\{1,\ldots,d\}\) is the least positive integer for which
\(d\mid2R+\rho_R(d)\).  This formal coefficient sequence is a lossless
encoding of \(D_R\).  Indeed, let \(L={\rm lcm}(1,\ldots,R)\).  For each
\(1\leq n\leq R\), choose a positive \(c\) with \(2R+c\equiv n\pmod L\).
Then

\[
  \nu_R(c)=\sum_{d\mid n}b_d.                        \tag{12}
\]

The digits \(b_n\) are recovered successively from (12) by divisor
inversion.  No support information is lost if all labelled coefficients are
retained.

The coefficient transport is also exact:

\[
\begin{split}
  \nu_{R+1}(c)
   &=\nu_R(c+2)+b_{R+1}{\bf1}_{R+1\mid c},\\
  \mathcal R_{R+1}(z)
   &=z^{-2}\bigl(\mathcal R_R(z)-\nu_R(1)z-\nu_R(2)z^2\bigr)
     +b_{R+1}\frac{z^{R+1}}{1-z^{R+1}}.              \tag{13}
\end{split}
\]

At \(z=1/2\), (11) is precisely the lower-support fractional phase:

\[
  \mathcal R_R(1/2)
  =\sum_{d\in D_R}\frac{2^{\,2R\bmod d}}{2^d-1},    \tag{14}
\]

and (13) becomes

\[
  \mathcal R_{R+1}(1/2)
  =4\mathcal R_R(1/2)-2\nu_R(1)-\nu_R(2)
   +\frac{b_{R+1}}{2^{R+1}-1}.                       \tag{15}
\]

Equations (11)--(15) validate the resolvent as a lossless lift of the scalar
phase.  The loss occurs only when the coefficient sequence is evaluated at
\(1/2\).

## 5. The coefficient-shift mismatch with (SC0)

The same shift gives the exact two-step energy law

\[
  \boxed{
  F_{2R+2}-F_{2R}
   =\nu_R(1)+\nu_R(2)+2b_{R+1}
    -Q_{2R+1}-Q_{2R+2}.}                             \tag{16}
\]

At \(2R+1\), every proper divisor is at most \(R\), giving the term
\(\nu_R(1)\).  At \(2R+2\), the lower divisors give \(\nu_R(2)\), while the
rank \(R+1\) digit contributes once as a proper divisor and once as the
half-scale term \(s_{2R+2}\).

Phase transport at \(z=1/2\) removes

\[
  2\nu_R(1)+\nu_R(2),                                \tag{17}
\]

whereas the current SC0 service in (16) credits the first two arrivals with
equal weights.  More generally, a convergent scalar evaluation at
\(0<z<1\) removes \(z^{-1}\nu_R(1)+\nu_R(2)\) after the common shift factor.
These weights are equal only at \(z=1\), where the generating series diverges
as soon as \(D_R\ne\varnothing\).  Hence no single convergent positive scalar
evaluation of the resolvent simultaneously represents the fractional phase
and the unweighted two-step service.

The full coefficient sequence avoids this loss, but it does not close a
one-sided recurrence for \(F\).  To see the remaining variables explicitly,
let

\[
  U_R=\#\{R<d\leq2R:b_d=1\},
  \qquad
  \Psi_R=\sum_{\substack{R<d\leq2R\\b_d=1}}
                \frac{2^{\,2R\bmod d}}{2^d-1},
\]

and let \(z_{2R}=2^{2R}r_{2R}\) be the scaled real greedy remainder.  The
floor identity for \(Q\) gives

\[
  Q_{2R}=z_{2R}-\alpha_{2R}
          +\mathcal R_R(1/2)+\Psi_R,                 \tag{18}
\]

and therefore

\[
  F_{2R}=T(2R)-U_R+2\alpha_{2R}-2z_{2R}
           -2\mathcal R_R(1/2)-2\Psi_R.              \tag{19}
\]

The lower resolvent alone does not contain the upper support, the upper
phase, or the current real remainder.  It can reconstruct the old support
and replay the greedy orbit, but that is reconstructive equivalence rather
than a new one-sided inequality.  Notice also that a large lower resolvent
makes the current right side of (19) smaller: promised future divisor service
does not pay a present deficit retroactively.

Among the variables in the two-step transport, (SC0) is equivalent to

\[
  \boxed{
  F_{2R}+\nu_R(1)+\nu_R(2)+2b_{R+1}
  \geq Q_{2R+1}+Q_{2R+2}.}                           \tag{20}
\]

Equation (20) is the smallest target-specific inequality obtained from (16);
it is an equivalent formulation of \(F_{2R+2}\geq0\), not a reduction or a
proved invariant.  A proof would have to relate the quotient demand on its
right to labelled future arrivals without replacing those labels by the
phase evaluation (15).

## 6. Reproducible finite audit

Run

    python3 formal_math/erdos257_period_noncollapse/scripts/sparse_clock_winding_resolvent_audit.py \
      --depth 5000 --lookahead 64 --resolvent-depth 80

The script checks (13)--(16) by exact rational and integer arithmetic on the
stated finite range, prints the two order-\(73\) counterexamples, and labels
the winding-height observations as finite.  Extending those bounds is not a
proof of (SC0).
