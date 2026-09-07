# Arithmetic gap charge for the point \(1/7\)

This note tests whether the actual point \(1/7\) can be kept inside every
six-step Bellman survivor cylinder by a fixed-prime arithmetic sign.  There is
an exact integer charge for that membership question, and it has a closed
one-step and 64-block recurrence.  The proposed primes \(7,31,151\), however,
are eventually absorbed into the denominator product independently of the
itinerary.  After removing that forced common part, their primitive residues
are not preserved.  More strongly, two points in the same six-bit branch can
have opposite gap signs and identical data modulo \(7\cdot31\cdot151\).

Thus no fixed congruence or valuation of the cleared gap proves the required
nesting.  This does not exclude an invariant using moving primitive divisors
or the full Archimedean carry state.

## 1. The exact finite cylinder

Write
\[
 q_r=2^r-1,
 \qquad
 x_r=\frac1{21}-\sum_{k=2}^{r-1}\frac{b_k}{q_k},
\]
where \(b_k\in\{0,1\}\) are the greedy Bellman digits.  Keep the following
fractions unreduced:
\[
 D_r=21\prod_{k=2}^{r-1}q_k,
 \qquad
 A_r=D_rx_r.                                      \tag{1}
\]
The digit and residual recurrences are
\[
 b_r=\mathbf1_{q_rA_r\geq D_r},
 \qquad
 D_{r+1}=q_rD_r,
 \qquad
 A_{r+1}=q_rA_r-b_rD_r.                          \tag{2}
\]

Put
\[
 P_r=\sum_{k=2}^{r-1}\frac{b_k}{q_k}.
\]
The points with this prefix whose normalized residual at rank \(r\) is in
\([0,2)\) form the exact finite survivor cylinder
\[
 I_r=\left[P_r,P_r+\frac2{q_r}\right).           \tag{3}
\]
In the root normalized coordinate \(y=3t\), its endpoints are
\[
 L_r=3P_r,
 \qquad
 U_r=3P_r+\frac6{q_r}.                            \tag{4}
\]
For \(r=2+6j\), this is the depth-\(6j\) cylinder on the actual 64-block
itinerary.  Its two distances from \(1/7\) are
\[
 \frac17-L_r=\frac{3A_r}{D_r},
 \qquad
 U_r-\frac17=\frac{3B_r}{D_rq_r},                \tag{5}
\]
where the cleared upper-gap numerator is
\[
 \boxed{B_r=2D_r-q_rA_r.}                        \tag{6}
\]
Consequently the actual point is strictly inside this finite cylinder exactly
when \(A_r>0\) and \(B_r>0\).  Formula (6), rather than a floating-point
interval margin, is the arithmetic point-location problem.

## 2. One-step and 64-block recurrences

Since \(q_{r+1}=2q_r+1\), equations (2) and (6) give
\[
 B_{r+1}=
 \begin{cases}
 q_{r+1}B_r-(q_{r+1}+1)D_r,&b_r=0,\\
 q_{r+1}B_r-D_r,&b_r=1.
 \end{cases}                                      \tag{7}
\]
This is already a signed affine cocycle: reduction modulo a fixed prime sees
both the old gap and an accumulating denominator term.

For a six-bit block \(e_i=b_{r+i}\), put
\[
 Q_r=\prod_{i=0}^5q_{r+i},
 \qquad
 E_r=\sum_{i=0}^5e_i\frac{Q_r}{q_{r+i}}.          \tag{8}
\]
Then the exact 64-branch return is
\[
 \begin{aligned}
 D_{r+6}&=D_rQ_r,\\
 A_{r+6}&=Q_rA_r-D_rE_r,\\
 B_{r+6}&=\frac{q_{r+6}Q_r}{q_r}B_r+D_rC_{r,e},  \tag{9}
 \end{aligned}
\]
with
\[
 C_{r,e}
 =2Q_r-2\frac{q_{r+6}Q_r}{q_r}+q_{r+6}E_r.       \tag{10}
\]
Every quantity in (8)--(10) is an integer.  This is the requested recurrence
under the actual 64-block itinerary; the itinerary enters only through the
linear digit charge \(E_r\).

## 3. Fixed primes are absorbed automatically

Let \(p\) be an odd prime and let \(h=\operatorname{ord}_p(2)\).  At rank
\(2h\), both \(D_{2h}\) and \(q_{2h}\) are divisible by \(p\): the product in
\(D_{2h}\) contains \(q_h\), while \(h\mid2h\).  Hence (6) gives
\[
 p\mid B_{2h}.
\]
Thereafter \(p\mid D_r\), and (7) shows inductively that \(p\mid B_r\) for
every \(r\geq2h\).  In particular,
\[
 \begin{array}{c|c|c}
 p&\operatorname{ord}_p(2)&
 \text{threshold }R_p\text{ with }p\mid B_r\ (r\geq R_p)\\ \hline
 7&3&6\\
 31&5&10\\
 151&15&30
 \end{array}                                      \tag{11}
\]
The same argument, after taking a sufficiently divisible multiple of \(h\),
absorbs every fixed power \(p^a\).  Therefore divisibility of \(B_r\) by any
fixed odd modulus is eventually automatic and contains no information about
the sign of (B_r).

One can remove the forced common denominator part by defining the primitive
charge
\[
 \widehat B_r=\frac{B_r}{\gcd(|B_r|,D_r)}.        \tag{12}
\]
That does not produce a preserved residue.  The exact actual-orbit values at
aligned ranks begin as follows:
\[
\begin{array}{c|c|c|c|c}
r& (b_r,\ldots,b_{r+5})
 & (v_7(B_r),v_{31}(B_r),v_{151}(B_r))
 & (v_7(D_r),v_{31}(D_r),v_{151}(D_r))
 & \widehat B_r\bmod(7,31,151)\\ \hline
2  &000101&(0,0,0)&(1,0,0)&(6,13,13)\\
8  &111101&(2,0,0)&(3,1,0)&(4,23,87)\\
14 &001010&(5,1,0)&(5,2,0)&(4,29,106)\\
20 &101010&(6,3,1)&(7,3,1)&(3,22,106)\\
26 &001000&(10,4,1)&(10,5,1)&(6,1,145)\\
32 &101001&(13,5,2)&(12,6,2)&(0,16,70)
\end{array}                                      \tag{13}
\]
The table is an exact falsification of residue preservation, not a proof that
the displayed positive gaps remain positive at all later ranks.

## 4. Same branch, identical fixed-prime data, opposite signs

There is also a local obstruction that does not depend on the actual orbit
continuing for many blocks.  At \(z=1/3\), use the first actual six-bit word
\(e=000101\).  Its inverse branch is
\[
 y=S_e(1/3)+\frac{Y}{85}.                         \tag{14}
\]
Take
\[
 M=7\cdot31\cdot151=32767,
 \qquad Q=1000000007,
\]
and choose terminal gap charges
\[
 c_+=1,
 \qquad c_-=1-M=-32766,
 \qquad Y_\pm=2-\frac{c_\pm}{Q}.                 \tag{15}
\]
Substitution in (14), followed by six exact Bellman steps, verifies that both
points have itinerary \(000101\) and end at the stated \(Y_\pm\).  Their
cleared upper gaps are \(c_+>0\) and \(c_-<0\), but
\[
 c_+\equiv c_-\equiv1\pmod M,
 \qquad
 v_p(c_+)=v_p(c_-)=0
 \quad(p=7,31,151).                               \tag{16}
\]
Thus the same clock, the same 64-branch itinerary, the same residues modulo
all three named primes, and the same three valuations occur on opposite sides
of the survivor-cylinder boundary.

More generally, replace \(M\) by any prescribed finite odd modulus and take
\(Q\) sufficiently large and coprime to \(M\).  The two charges \(1\) and
\(1-M\) remain congruent modulo \(M\), have the same valuations at its prime
divisors, and have opposite real signs.  Continuity of the inverse branch near
\(Y=2\), whose six intermediate states avoid the threshold \(1\), keeps both
points on the same itinerary.  Hence no fixed finite collection of congruence
and valuation tests can determine the required sign.

## 5. What survives this test

The exact gap cocycle (7)--(10) is useful, but its informative arithmetic
cannot live at fixed primes already present in the Mersenne denominator
product.  A viable invariant would have to retain information discarded by
fixed-modulus projection: for example, a moving primitive divisor of the new
Mersenne factors, a signed quotient after cancellation, or a coupled
Archimedean/\(p\)-adic state.  No such invariant is proved here.  The bounded
result is the no-go: \(7\)-, \(31\)-, and \(151\)-adic divisibility, valuation,
or fixed-precision residue signs cannot establish \(1/7\in K_{1/3}\).

The companion script checks (2), (7), (9), the absorption thresholds, the
primitive-charge table, and the opposite-sign witness entirely with integers
and rational numbers:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/arithmetic_gap_charge_nogo.py
