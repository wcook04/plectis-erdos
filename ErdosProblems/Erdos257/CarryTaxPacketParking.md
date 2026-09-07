# Carry-tax packets and endpoint-deadline parking

Put
\[
  w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note records a packet calculus suggested by the positive LCM-lift
rewrite.  It retains information that scalar value and effective height both
discard: how many further binary carries a particular cylinder block can pay.
It does not prove a global Boolean normal form.

## 1. The exact multilevel carry tax

The elementary identity
\[
  w_{k-1}=2w_k+M(k-1,k)                              \tag{1}
\]
iterates to
\[
  w_{r-c}=2^cw_r+\sum_{s=1}^c2^{c-s}M(r-s,r-s+1).   \tag{2}
\]
After division by \(2^c\), define
\[
  \Theta_{r,c}:=
    \sum_{s=1}^c2^{-s}M(r-s,r-s+1)
    =2^{-c}w_{r-c}-w_r.                              \tag{3}
\]
Thus \(\Theta_{r,c}\) is not an estimate.  It is the exact reserve per
packet required to merge \(2^c\) copies of an atom at rank \(r\) into one
atom at rank \(r-c\).

Call a positive packet with leading rank \(r\) and value
\(x=w_r+\sigma\) **certified to deadline \(d\)** if
\[
  d\le r,\qquad \sigma\ge \Theta_{r,r-d}.            \tag{4}
\]
The integer \(r-d\) is its carry capacity.

The certification is closed under a binary carry.  Suppose two packets at
rank \(r\) are certified to deadlines \(d_1,d_2<r\).  Set
\(d=\max(d_1,d_2)\).  Replacing their two leading atoms by the rank-
\(r-1\) atom uses (1).  The remaining reserve is
\[
  \sigma_1+\sigma_2-M(r-1,r).
\]
Writing \(c=\min(r-d_1,r-d_2)\), the exact recursion
\[
  2\Theta_{r,c}-M(r-1,r)=\Theta_{r-1,c-1}            \tag{5}
\]
shows that the merged packet is certified to deadline \(d\).  In words: a
carry consumes one capacity level and inherits the later of the two
deadlines.

## 2. Cylinder power blocks carry their endpoint as a deadline

Assume \(2\le a\le b\) and \(0\le j\le b\).  Put
\[
  r=a+b-j,\qquad c=b-j,
  \qquad X_{a,b,j}=2^jM(a,b).                        \tag{6}
\]
Direct cancellation gives
\[
  2^jM(a,b)>w_{a+b-j}
  \quad\Longleftrightarrow\quad
  2^a+2^b>2^j+1.                                    \tag{7}
\]
The inequality is strict throughout the range in (6).  Moreover
\(X_{a,b,j}<2w_r\), so the block has exactly one leading Boolean atom at
rank \(r\).

More is true.  For an integer \(s\ge0\), applying (7) to \(j+s\) gives
\[
  X_{a,b,j}>2^{-s}w_{r-s}
  \quad\Longleftrightarrow\quad j+s\le b.            \tag{8}
\]
Combining (3) and (8), the block is certified through exactly
\(c=b-j\) further carries.  Its deadline is therefore
\[
  r-c=a.                                             \tag{9}
\]
The smaller cylinder endpoint is literally the hard left boundary of its
binary packet.  This is the structural meaning of the otherwise empirical
"multiplicity versus label shift" comparison.

The reserve itself is
\[
  D_{a,b,j}:=X_{a,b,j}-w_r
  =\frac{2^a+2^b-2^j-1}
   {(2^a-1)(2^b-1)(2^r-1)}.                          \tag{10}
\]
It is strongly delayed.  Indeed
\[
  D_{a,b,j}\le 2M(a,r)<w_{a+r-2}.                   \tag{11}
\]
For the first inequality, divide the numerator in (10) by \(2^b-1\);
the quotient is at most two.  The second inequality follows after one
cross multiplication.

The delay can be retained inside the integer cylinder cone without using a
balanced common-denominator packet.  Let
\[
  P=(2^b-1)(2^r-1)
\]
and choose any \(H\) for which \(P\mid 2^H-1\), for instance the
multiplicative order of \(2\) modulo the odd integer \(P\).  Then
\[
  D_{a,b,j}=B M(a,H),\qquad
  B=(2^a+2^b-2^j-1)\frac{2^H-1}{P}\in\mathbb N.     \tag{12}
\]
The residual keeps the anchor endpoint \(a\); the LCM lift has not erased
its deadline.

## 3. A uniform contraction of anchored packet load

For a multiplicity packet \(kM(a,H)\), use \(k/2^H\) as its dyadic
anchored load.  The parent power block in (6) has load \(2^{j-b}\).
From (10)--(12),
\[
 \frac{B/2^H}{2^{j-b}}
 <R(a,b,j):=
 \frac{(2^a+2^b-2^j-1)2^{b-j}}
 {(2^b-1)(2^{a+b-j}-1)}.                             \tag{13}
\]
In fact
\[
  R(a,b,j)\le\frac8{15}.                             \tag{14}
\]
Here is a short proof.  Write
\(x=2^a\), \(y=2^j\), and \(z=2^{b-j}\).  Then
\[
 R=\frac{z(x+yz-y-1)}{(yz-1)(xz-1)}.                 \tag{15}
\]
For fixed \(z\), this expression decreases in both \(x\) and \(y\):
\[
 \partial_yR=-\frac{z}{(yz-1)^2},\qquad
 \partial_xR=-\frac{z(z-1)}{(xz-1)^2}.              \tag{16}
\]
Subject to \(x\ge4\), \(yz\ge x\), and powers of two, the only boundary
families are \((x,y)=(4,4)\) for \(z=1\), \((4,2)\) for \(z=2\), and
\((4,1)\) for \(z\ge4\).  They give respectively at most \(1/3\),
\(10/21\), and a decreasing function of \(z\) whose value at \(z=4\) is
\(8/15\).

Thus emitting the leading atom removes at least \(7/15\) of this anchored
load, uniformly.  This is a true contraction law, not a cutoff inferred
from a large finite orbit.

## 4. How the LCM lift enters the packet category

For the collision lift in PositiveCylinderBooleanisationAudit.md,
\[
  A M(n,L),\qquad
  A=\frac{2^L-1}{2^e-1}
    -\frac{2^L-1}{2^{n-1}-1},
  \quad 2\le e<n-1,                                  \tag{17}
\]
one has
\[
  0<A<\frac{2^L-1}{3}<2^{L-1}.                      \tag{18}
\]
Every occupied binary exponent \(j\) of \(A\) therefore satisfies
\(j\le L-2\).  Applied to the cylinder \(M(n,L)\), (9) gives every fresh
lift atom at least two capacity levels, while the single-lift value bound
\[
  A M(n,L)=w_n(w_e-w_{n-1})<\frac13w_n<w_{n+1}       \tag{19}
\]
prevents the isolated lift, under any positive value-preserving cleaning,
from emitting an atom at rank at most \(n+1\).

The first lift illustrates the distinction.  Its multiplicity is
\[
  340=2^8+2^6+2^4+2^2,
\]
so the four power packets of \(340M(11,10)\) lead at ranks
\(13,15,17,19\), with endpoint deadlines inherited from \(10\).  These
atoms are not final: they collide with ordinary frontier emissions and must
be parked jointly.  The packet theorem says those collisions consume
explicit reserve levels; it does not authorize irrevocable extraction of
the four atoms.

## 5. The actual global question

The preceding identities isolate a new, lossless global problem.  A live
frontier generates certified atom packets \((r,d)\).  Equal-rank packets
may be merged by (5) while their capacity is positive.  A fatal event in
this packet category is two packets colliding at their common hard deadline,
where no carry reserve remains.

What is not yet proved is the required parking theorem:

> For the packet genealogy rooted at \(M(2,3)\), there exists a fair
> sequence of binary carries and anchored residual expansions in which no
> two packets ever collide with zero remaining capacity, every rank
> eventually contains at most one atom, and the total residual cylinder
> value tends to zero.

The \(8/15\) contraction and the exact deadline inheritance make this
strictly stronger information than scalar positivity or effective height.
They do not by themselves prove the parking theorem: packets from disjoint
ancestries can coalesce, and their deadline loads must satisfy a global
Hall/Kraft-type bound.  Establishing that bound would produce an infinite
Boolean support of value
\(M(2,3)=1/21\) and settle Erdős 257 negatively.  A counterexample must be
an exact reachable deadline overload, not merely a large unrestricted
multiplicity.

## 6. Reproduction

The companion exact-arithmetic script verifies (1)--(14), the LCM bit
slack in (18), and the first-lift packet data over large bounded parameter
ranges.  These receipts are tests of the algebra; no finite depth is used
as evidence for the global parking theorem.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/carry_tax_packet_parking_audit.py
