# A final zero forces exponential lower cyclotomic height at \(1/465\)

Status: exact all-depth necessary condition, 2026-08-21. This theorem uses
both real-greedy complementarity and the complete high-order cyclotomic
charge, not a single primitive prime. It does not exclude the fatal branch:
dense lower-clock complexity can satisfy the resulting height demand.

Write

\[
 w_n=\frac1{2^n-1},\qquad x=\frac1{465},
\]

and let \(b_n\) be the real-greedy word for \(x\). Put

\[
 r_m=x-\sum_{n\le m}b_nw_n,\qquad
 T_m=\sum_{n>m}w_n,\qquad
 \delta_m=w_m-T_m.
\]

The reverse-superincreasing inequality says \(\delta_m>0\).

## 1. Strip the complete high cyclotomic vector

Fix \(m\ge5\). Let \(H\) be divisible by \(20\), by \(m\), and by every
selected rank \(n\le m\). Put

\[
 D=2^H-1,\qquad
 A=\frac D{465}-\sum_{\substack{n\le m\\b_n=1}}\frac D{2^n-1}.
                                                               \tag{1}
\]

Thus \(r_m=A/D\). Using the exact cyclotomic factorisation, define

\[
 C=\prod_{\substack{d\mid H\\d>m}}\Phi_d(2),
 \qquad
 E=\prod_{\substack{d\mid H\\d\le m}}\Phi_d(2),
 \qquad D=CE.                                      \tag{2}
\]

Every term in (1) is divisible by \(C\). For a prefix term this is because
no \(d>m\) can divide \(n\le m\). For the root term, use

\[
 465=\Phi_2(2)\Phi_4(2)\Phi_5(2);
\]

all three cancelled factors lie in the lower product \(E\). Hence

\[
 A=Ca,\qquad r_m=\frac aE                         \tag{3}
\]

for an integer \(a\). Since \(m\mid H\),

\[
 M_m:=2^m-1\mid E.
\]

Set

\[
 h=\frac E{M_m}.                                  \tag{4}
\]

The integer \(h\) is odd. Equations (3)--(4) give the exact upper-boundary
numerator

\[
 \boxed{
 w_m-r_m=\frac{h-a}{E}.}                          \tag{5}
\]

Thus stripping the *entire* high-order charge vector leaves one lower-clock
integer \(q_m:=h-a\). It does not leave a collection of independent fresh
prime errors.

## 2. The final-zero height theorem

Assume that \(m\) is the final zero:

\[
 b_m=0,\qquad b_n=1\quad(n>m).
\]

Greedy rejection gives \(r_m<w_m\). If this all-one tail is fatal rather
than an exact representation, then its limiting residual is positive:

\[
 r_m-T_m>0.
\]

Combining the two strict inequalities,

\[
 0<w_m-r_m< w_m-T_m=\delta_m.                    \tag{6}
\]

By (5), \(q_m=h-a\) is a positive integer, and (6) becomes

\[
 \boxed{1\le q_m<E\delta_m.}                     \tag{7}
\]

In particular,

\[
 \boxed{
 E\delta_m>1,\qquad
 h>\frac1{M_m\delta_m}.}                          \tag{8}
\]

This is the full-vector Archimedean separation law. A fatal final zero is
possible only if the lower cyclotomic cofactor is large enough to put an
integer grid point inside the preterminal interval.

The curvature gap has the exact expansion

\[
 \delta_m
 =\sum_{\ell\ge2}
   \frac{2^\ell-2}{2^\ell-1}\,2^{-m\ell}.         \tag{9}
\]

It follows that

\[
 \delta_m<
 \frac23\,2^{-2m}+
 \frac{2^{-3m}}{1-2^{-m}}.                        \tag{10}
\]

For \(m\ge5\), multiplying (10) by \(M_m<2^m\) gives

\[
 M_m\delta_m
 <2^{-m}\left(\frac23+\frac1{31}\right)
 <\frac34\,2^{-m}.
\]

Substitution into (8) proves the explicit all-depth bound

\[
 \boxed{
 h>\frac43\,2^m.}                                 \tag{11}
\]

The dangerous numerator-one phase is now literal: if \(q_m=1\), then

\[
 r_m=w_m-\frac1E,
\]

and fatality is equivalent to \(E\delta_m>1\). More generally, (7) says
that every fatal phase has an integer numerator strictly below the same
curvature budget.

## 3. Exact ceiling: LCM-height distortion survives

Equation (11) is not contradictory for a dense prefix. The cofactor \(h\)
contains every lower cyclotomic clock introduced by the common height but
not already present in \(M_m\). Real affordability does not upper-bound
this quantity.

For example, take arbitrarily large prime \(m\) and a Boolean set consisting
of ranks in \((m/2,m)\). Its total Mersenne value is at most

\[
 \sum_{n>m/2}2^{1-n},
\]

which tends exponentially to zero and is therefore below \(1/465\). Yet if
the set contains the primes \(p\in(m/2,m)\), its lower cofactor contains

\[
 \prod_{m/2<p<m}\Phi_p(2)
 =\prod_{m/2<p<m}(2^p-1).
\]

The prime number theorem makes the binary logarithm of this product
\(\Theta(m^2/\log m)\), far larger than the linear threshold in (11).
Thus even extremely cheap high-rank Boolean mass can create
superexponential cyclotomic height.

This is the exact ceiling of the full moving-vector attack. The high
coordinates do combine, but after triangular elimination they become the
single reduced denominator \(E\). Fatality then demands large lower LCM
height, and dense support supplies precisely that resource. Any closure
must control the *actual greedy ancestry* inside \(h\), rather than only its
value, support count, source period, or fresh primitive coordinates.

The complementary abstract source counterfamily is recorded in
AnchorFourFiveTerminalCorridorSourceNoGo.md: raw period/product data can
sustain terminal-corridor failure even while agreeing with the actual
prefix through rank \(102\). Together, the two results isolate the missing
input as an upper bound or cancellation law for the actual reduced
cyclotomic height.
