# A sharp-defect failure forces a two-row divisor pulse

Put

\[
 w_n=\frac1{2^n-1},\qquad x=M(4,5)=\frac1{465}.
\]

Let \(b_n\) be the exact real-greedy word for \(x\), let

\[
 r_N=x-\sum_{d\leq N}b_dw_d,
 \quad P_N=\sum_{d\leq N}b_d,
 \quad f_N=\sum_{d\mid N}b_d,
\]

and define the integer quotient defect

\[
 Q_N=\left\lfloor\frac{2^N}{465}\right\rfloor
      -\sum_{d\leq N}b_d
       \left\lfloor\frac{2^N}{2^d-1}\right\rfloor .       \tag{1}
\]

The proposed sharp support bound is \(P_N\geq5Q_N\).  This note does not
prove that bound.  It proves an exact necessary condition for its first
failure: unless the failure occurs after the final greedy skip, about one
fifth of the complete selected prefix must divide the product
\((N+1)(N+2)\).  Thus a first failure is forced into the same joint
suffix/LCM alignment that appears in the other dense-support coordinates.

## 1. The exact phase identity

Write

\[
 y_N=2^Nr_N,
 \qquad
 \alpha_N=\left\{\frac{2^N}{465}\right\},
 \qquad
 \rho_{N,d}=\frac{2^{N\bmod d}}{2^d-1}.
\]

Euclidean division gives

\[
 \frac{2^N}{2^d-1}
 =\left\lfloor\frac{2^N}{2^d-1}\right\rfloor+\rho_{N,d}.
\]

Consequently

\[
 \boxed{Q_N=y_N-\alpha_N+
        \sum_{\substack{d\leq N\\b_d=1}}\rho_{N,d}.}      \tag{2}
\]

Since \(465\) is odd,

\[
 \alpha_N\geq\frac1{465}.                                \tag{3}
\]

The binary expansion of \(1/465\) has period \(20\), with nonzero positions

\[
 9,13,14,17,18,19,20\pmod {20}.                            \tag{4}
\]

Thus, if \(N=20K+s\), the target bit in

\[
 Q_N=2Q_{N-1}+t_N-f_N                                    \tag{5}
\]

is determined by (4).  The exact greedy prefix through the first period is

\[
 \{9,13,14,17,19\},\qquad
 Q_N=0\ (N\leq19),\qquad (P_{20},Q_{20})=(5,1).            \tag{6}
\]

These are the five primitive boundary atoms responsible for sharpness of the
coefficient \(5\).

## 2. The exact first-crossing equation

Suppose \(N\) is the first rank at which \(P_N<5Q_N\).  Put

\[
 q=Q_{N-1},\quad e=P_{N-1}-5Q_{N-1},\quad
 b=b_N,\quad t=t_N,\quad f=f_N.
\]

Then \(e\geq0\), and direct substitution into (5) gives

\[
 P_N-5Q_N=e-5q+b-5t+5f.                           \tag{7}
\]

Therefore the crossing condition is exactly

\[
 \boxed{q+t-f\geq\left\lfloor\frac{e+b}{5}\right\rfloor+1.}
                                                               \tag{8}
\]

There is no free Boolean choice in (8): real greediness fixes

\[
 b=1\quad\Longleftrightarrow\quad
 y_{N-1}\geq\frac{2^{N-1}}{2^N-1}.                         \tag{9}
\]

Equations (4), (8), and (9) are the complete local period-\(20\) data at a
first crossing.  They do not by themselves rule it out.

## 3. One later skip bounds the scaled residual

Assume there is a skipped rank \(m>N\).  Telescoping the real-greedy
recurrence only as far as that skip gives

\[
 r_N=\sum_{N<j<m}b_jw_j+r_{m-1}
    <\sum_{N<j<m}w_j+w_m
    <\sum_{j>N}w_j.                                      \tag{10}
\]

This needs only one later skip; the orbit may enter a fatal all-selected tail
after \(m\).  Moreover

\[
 2^N\sum_{j>N}w_j
 <\frac1{1-2^{-(N+1)}}
 =1+\frac1{2^{N+1}-1}.                                  \tag{11}
\]

The first crossing cannot precede rank \(20\), by (6).  Hence (2), (3),
(10), and (11) imply

\[
 S_N:=\sum_{\substack{d\leq N\\b_d=1}}\rho_{N,d}
 >\frac{P_N}{5}-1.                                      \tag{12}
\]

## 4. Phase mass can only come from the next two divisor rows

Every selected rank is at least \(9\).  For such a rank put

\[
 h=d-(N\bmod d).
\]

If \(h=1\), then \(d\mid N+1\); if \(h=2\), then \(d\mid N+2\); otherwise
\(h\geq3\).  Define

\[
 A_N=\#\{d\leq N:b_d=1,\ d\mid N+1\},
 \qquad
 B_N=\#\{d\leq N:b_d=1,\ d\mid N+2\}.                  \tag{13}
\]

The two sets in (13) are disjoint.  Since \(d\geq9\), the three exact
uniform bounds are

\[
 \rho_{N,d}\leq
 \begin{cases}
 256/511,&h=1,\\
 128/511,&h=2,\\
 64/511,&h\geq3.
 \end{cases}                                             \tag{14}
\]

It follows that

\[
 S_N\leq\frac{64P_N+192A_N+64B_N}{511}.                  \tag{15}
\]

Combining (12) and (15) proves the weighted pulse inequality

\[
 \boxed{960A_N+320B_N>191P_N-2555.}                      \tag{16}
\]

Equivalently,

\[
 3A_N+B_N>\frac{191P_N-2555}{320}.                       \tag{17}
\]

Since \(A_N\leq f_{N+1}\) and \(B_N\leq f_{N+2}\), (17) is also an exact
lower bound on the next two divisor pulses.  Discarding the weights gives

\[
 A_N+B_N>\frac{191P_N-2555}{960}.                        \tag{18}
\]

Every rank counted on the left of (18) divides either \(N+1\) or \(N+2\).
Consequently their joint least common multiple divides

\[
 \operatorname{lcm}(N+1,N+2)=(N+1)(N+2).                \tag{19}
\]

Thus a nonterminal first crossing compresses a positive proportion of the
entire selected prefix into one polynomial-height LCM frame.  A cruder
purely numerical consequence is

\[
 191P_N<960\tau(N+1)+320\tau(N+2)+2555,                 \tag{20}
\]

where \(\tau\) is the divisor-counting function.

## 5. Exact dichotomy and boundary

At a first failure of \(P_N\geq5Q_N\), exactly one of the following holds.

1. There is no skipped rank after \(N\).  The actual greedy word is already
   on its permanent all-selected tail.
2. There is a later skip, and the exact period condition (4), crossing law
   (8), real-greedy decision (9), weighted pulse bound (16), and LCM
   compression (19) all hold.

The second alternative is substantially narrower than an arbitrary moving
hole: at least approximately one fifth of all selected ranks lie in the two
adjacent divisor rows.  It is not yet contradictory.  Existing
common-multiple carry inequalities turn (19) into a later carry lower bound;
they do not supply an upper bound that excludes this frame.  The first
alternative is the already known fatal/cofinite obstruction.  Therefore this
dichotomy identifies the exact joint suffix/LCM event that a proof must
forbid, but does not prove \(P_N\geq5Q_N\) or membership of \(1/465\).
