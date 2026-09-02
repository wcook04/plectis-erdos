# Power-block capacity and deadline packets

Put
\[
 w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note replaces the scalar digital-height estimate by an exact packet carried
by each power block.  It then applies the packet calculus to the first
\(M(2,3)\) LCM lift.

## 1. Exact surplus bound

Assume \(2\leq a\leq b\), let \(j\leq b-1\), and set
\[
 r=a+b-j,\qquad c=b-j,qquad d=r-c=a.
\]
The integer \(c\) is the collision capacity and \(d\) is its endpoint
deadline.  If
\[
 X=2^jM(a,b)=w_r+S,
\]
then direct cancellation gives
\[
 \kappa:=\frac{S}{M(r-1,r)}
 =\frac{(2^a+2^b-2^j-1)(2^{r-1}-1)}
        {(2^a-1)(2^b-1)}.                           \tag{1}
\]
The proposed lower bound is true, and is strict:
\[
 \boxed{\kappa>2^{c-1}-\frac12.}                    \tag{2}
\]

To prove it, put \(x=2^a\), \(y=2^b\), and \(q=2^c\).  After multiplying the
difference in (2) by the positive denominator \(q(x-1)(y-1)\), it is enough to
show
\[
 (x-1)\bigl(q(x+1)-3\bigr)
 +y\frac{(q-1)(q-2)}q>0.                            \tag{3}
\]
Here \(x\geq4\) and \(q\geq2\), so the first term is positive and the second
is nonnegative.

Inequality (2) proves that two rank-\(r\) atoms from blocks of positive
capacity have enough combined scalar surplus to pay the adjacent credit
\(M(r-1,r)\).  Scalar surplus alone does not record what remains after several
carries.  The exact packet below does.

## 2. The deadline packet

Define
\[
 P_{r,c}=\frac{w_{r-c}}{2^c},\qquad
 \Theta_{r,c}=\sum_{s=1}^c2^{-s}M(r-s,r-s+1).       \tag{4}
\]
Repeatedly dividing
\(w_{n-1}=2w_n+M(n-1,n)\) by two gives
\[
 \boxed{P_{r,c}=w_r+\Theta_{r,c}.}                  \tag{5}
\]
The power block contains this packet with an exact positive excess:
\[
 \boxed{2^jM(a,b)=P_{r,c}+2^{-c}M(a,b).}            \tag{6}
\]
Thus its head atom \(w_r\) can move left at most \(c\) times within the packet,
reaching but not crossing the deadline \(d=r-c=a\).

Packets at the same rank have an exact carry rule.  Suppose \(c_1\leq c_2\),
so the first packet has the later deadline.  Since \(P_{r,c}\) increases with
\(c\),
\[
 P_{r,c_1}+P_{r,c_2}
 =P_{r-1,c_1-1}+\bigl(P_{r,c_2}-P_{r,c_1}\bigr),    \tag{7}
\]
with a nonnegative excess.  The carried packet inherits the maximum endpoint
deadline and loses one capacity level.  If \(c_1=c_2\), the excess vanishes and
the Kraft load \(2^{-c}\) is preserved exactly:
\[
 2\cdot2^{-c}=2^{-(c-1)}.                           \tag{8}
\]
An attempted carry from capacity zero is an endpoint crossing.  Equations
(5)--(7), rather than the scalar ratio (1), are the lossless packet law.

## 3. First-lift root recut

After the exact prefix \(5,7,8,9,10\), choose endpoint \(e=2\) at the first
stop-11 collision.  The coefficient
\[
 340=2^8+2^6+2^4+2^2
\]
gives four packets from \(M(10,11)\):
\[
 (r,c,d)=(13,3,10),(15,5,10),(17,7,10),(19,9,10). \tag{9}
\]
The six ordinary frontier roots are
\[
\begin{array}{c|c}
\text{cylinder}&(r,c,d)\\ \hline
M(5,7)&(12,7,5)\\
M(5,8)&(13,8,5)\\
M(7,9)&(16,9,7)\\
M(3,11)&(14,11,3)\\
M(8,11)&(19,11,8)\\
M(9,11)&(20,11,9).
\end{array}                                         \tag{10}
\]

The two rank-13 packets carry as follows:
\[
 (13,3,10)+(13,8,5)\longrightarrow(12,2,10).
\]
The result meets the root packet \((12,7,5)\):
\[
 (12,2,10)+(12,7,5)\longrightarrow(11,1,10).       \tag{11}
\]
This recovers the forced atom \(w_{11}\) exactly.  The packet ends at rank 11,
one rank before its deadline 10, so neither carry crosses an endpoint.  The
rank-19 block packet and \(M(8,11)\) similarly give \((18,8,10)\).

The initial Kraft load of the ten packets in (9)--(10) is
\[
 \frac{371}{2048}.
\]
After the three root collisions it is \(559/1024<1\).  Unequal-capacity carries
need not preserve Kraft load, but this first recut is below unit load and has no
capacity-zero carry.

## 4. The next front: recovery works, but capacity does not select the normal form

Keep the exact positive excess left after replacing the original ten blocks by
their packets.  After the root collisions, its first affordable rank is 17.
It contains a rank-17 packet of capacity 15.  The following packet chain is
legal:
\[
\begin{aligned}
 (17,15,2)+(17,7,10)&\longrightarrow(16,6,10),\\
 (16,6,10)+(16,9,7)&\longrightarrow(15,5,10),\\
 (15,5,10)+(15,5,10)&\longrightarrow(14,4,10),\\
 (14,4,10)+(14,11,3)&\longrightarrow(13,3,10).
\end{aligned}                                       \tag{12}
\]
This recovers the forced rank-13 atom, again without crossing deadline 10.

Continuing the deterministic rule "extract the maximum-capacity packet at the
first affordable excess rank, then carry every collision" produces the exact
packet heads
\[
 11,13,16,18
\]
through rank 20, with remaining excess first affordable at rank 21.  The exact
greedy support through rank 20 is
\[
 11,13,16,18,20.                                    \tag{13}
\]
The parking rule has carried away the root rank-20 packet and has not yet
recovered it.  No endpoint overload explains the discrepancy: every carry
through this front has positive capacity, and the Kraft load is
\[
 \frac{329}{512}<1.                                 \tag{14}
\]

This is the first limitation of the capacity invariant.  It proves that the
rank-11 and rank-13 recoveries are legal, and it excludes deadline crossings,
but it does not decide whether a packet should be carried now or parked for a
future recut.  Rank 20 becomes a moving-hole obligation even though the Kraft
load is subcritical.  A normal-form theorem therefore needs one more labelled
state component recording parked forced ranks or future packet arrivals.

The rank-20 observation is not an impossibility theorem.  A later packet could
still return to rank 20.  It is an exact counterexample to the claim that Kraft
capacity and the maximum-deadline carry rule alone determine the Boolean
prefix.

## 5. Reproduction

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/power_block_deadline_packet_audit.py
```

The script checks the algebraic identities with exact rationals, reproduces the
two recovery chains, and stops its packet normalizer at the first unresolved
rank-20 hole.  The proofs of (2), (5)--(8), and the deadline statements are
algebraic; the exact calculation is a receipt for the stated first frontier.
