# The anchored collision cocycle

Put
\[
  w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note tests the self-similar substitution rooted at
\[
  M(2,3)=w_5+1510M(2,15).                           \tag{1}
\]
The result is mixed but exact.  Arbitrary same-rank coalescence does not
destroy the anchored-load contraction: there is a scalar cocycle that is
averaged by carries and gives a uniform post-collision contraction.  On the
other hand, the flat substitution that emits an atom and forgets which
residual pays for it fails in the first two generations.  The remaining
obstruction is persistent reserve ownership, not load growth.

## 1. The root substitution already coalesces across generations

The binary support of the coefficient in (1) is
\[
  1510=2^1+2^2+2^5+2^6+2^7+2^8+2^{10}.             \tag{2}
\]
For an anchor-two power packet
\[
  P(b,j):=2^jM(2,b),
\]
its leading rank and dyadic anchored load are
\[
  r=2+b-j,qquad \lambda=2^{j-b}=2^{2-r}.           \tag{3}
\]
Thus every packet at the same leading rank has exactly the same load,
independently of its cylinder height.

The seven root packets in (2) lead at ranks
\[
  16,15,12,11,10,9,7.
\]
The packet \(P(15,10)\), which leads at rank seven, has the exact anchored
rewrite
\[
  P(15,10)=w_7+B M(2,105),                           \tag{4}
\]
where the binary expansion of \(B\) contains the exponents
\(97,96,95\).  Hence three of its children lead at ranks \(10,11,12\).
In particular, the rank-ten child \(P(105,97)\) collides with the
first-generation packet \(P(15,7)\).

Carrying those two fronts gives a rank-nine front.  That front immediately
collides with the first-generation packet \(P(15,8)\), whose leading rank
was nine.  Consequently, an automaton that had declared the rank-nine atom
from \(P(15,8)\) final must undo that declaration.  This is an exact
two-generation obstruction to irreversible, breadth-first atom emission.
It is not a large-depth numerical event.

## 2. A distortion cocycle closed under arbitrary carries

Consider a packet component of value \(X\) whose current front is at rank
\(r\).  Give it the dyadic carry mass
\[
  \lambda_r:=2^{2-r}
\]
and define its distortion by
\[
  \alpha(X,r):=\frac{3X}{\lambda_r}.                \tag{5}
\]
For a primitive anchored packet, (3) gives the exact formula
\[
  \alpha(P(b,j),r)=\frac{2^b}{2^b-1},
  \qquad 1<\alpha\le\frac43.                        \tag{6}
\]

Now carry two components \(X_1,X_2\) with the same front rank \(r\).
Their new front rank is \(r-1\), and
\(\lambda_{r-1}=2\lambda_r\).  Therefore
\[
  \alpha(X_1+X_2,r-1)
  =\frac{\alpha(X_1,r)+\alpha(X_2,r)}2.             \tag{7}
\]
This is the cocycle law.  Binary coalescence merely averages distortion.
In particular, every composite assembled from anchor-two power packets
continues to satisfy
\[
  1<\alpha\le\frac43.                               \tag{8}
\]
No choice of collision tree can amplify this state variable.

## 3. Uniform contraction after a complete collision component

Suppose a component has been legally carried to front rank \(r\), remains
certified to deadline two, and has value \(X=w_r+R\).  The carry-tax
certification gives \(R>0\), while the leading-rank bound gives \(R<w_r\).
Choose a common exponent \(H\) clearing every Mersenne denominator in
\(R\).  Then
\[
  R=B M(2,H),\qquad B\in\mathbb N,qquad B<2^H.      \tag{9}
\]
Binary expansion of \(B\) is therefore a positive anchored rewrite, and
every child leads strictly after rank \(r\).

Its total child load \(L'=B/2^H\) satisfies
\[
 \frac{L'}{\lambda_r}
 <\frac{3R}{\lambda_r}
 =\alpha(X,r)-g(r),
 \qquad
 g(r):=\frac{3w_r}{\lambda_r}
      =\frac{3\,2^{r-2}}{2^r-1}.                   \tag{10}
\]
Since \(g(r)>3/4\), (8) gives the uniform composite bound
\[
  \boxed{\displaystyle \frac{L'}{\lambda_r}<\frac7{12}}. \tag{11}
\]
Thus arbitrary coalescence preserves a strict contraction.  For two
primitive power packets with a common rank, their more restrictive endpoint
data improves (11) to
\[
  \frac{L'}{2\lambda_r}<\frac{10}{21}.              \tag{12}
\]
Indeed, if their heights are \(b,c\), the right side before maximisation is
\[
 \frac12\left(\frac1{1-2^{-b}}+\frac1{1-2^{-c}}\right)
 -\frac{3\,2^{r-3}}{2^{r-1}-1}.                    \tag{13}
\]
The constraints \(b,c\ge\max(2,r-2)\) give \(1/3\) at \(r=3\), at most
\(10/21\) at \(r=4\), and less than
\(8/7-3/4=11/28\) for \(r\ge5\).

The actual root genealogy has a much stronger hereditary bound.  Every
initial residual packet in (2) has height 15.  Unary rewriting replaces a
height \(b\) by a common exponent divisible by \(b\), and collision
reencoding uses a common exponent divisible by every incoming height.
Consequently every primitive descendant height is divisible by 15.  Formula
(6), followed by averaging under (7), gives
\[
  \alpha\le \frac{2^{15}}{2^{15}-1}.
\]
Hence every completely owned component in this particular genealogy obeys
the root-specific contraction
\[
 \boxed{\displaystyle
   \frac{L'}{\lambda_r}
   <\frac{2^{15}}{2^{15}-1}-\frac34
   =\frac{32771}{131068}<0.251.}                    \tag{14}
\]
The factor near one quarter is therefore structural, not an accident of the
first collision.

At the first root collision, carrying \(P(15,7)\) and \(P(105,97)\) to
rank nine and reencoding at height \(315\) has exact child-load ratio about
\(0.24854755\); all 212 children lead at rank at least 12.  Carrying that
composite once more with \(P(15,8)\) to rank eight and reencoding at height
\(840\) has ratio about \(0.24708171\); all 545 children lead at rank at
least 11.  The first actual cascade therefore contracts more strongly than
the uniform theorem predicts.

## 4. What this settles and what it does not

The normalized anchored load is not the missing obstruction.  It contracts
after unary expansion, after a primitive collision, and after an arbitrary
binary coalescence tree.  LCM height spikes also disappear from (5)--(11):
height affects the exact encoding but not the cocycle bound.

What fails is the flat state space
\[
  \{\text{emitted atom}\}\;\sqcup\;
  \{\text{unowned anchored residual packets}\}.
\]
After (4), the rank-ten collision creates a rank-nine front, and the reserve
needed to carry it against the older rank-nine front is distributed among
descendants if that older atom was already emitted.  The scalar list of
children no longer records which reserve certifies which front.  Equations
(7)--(11) apply only after the complete owned component has been recovered.

Therefore a deterministic positive automaton would need persistent packet
trees, or an equivalent reversible ownership structure, together with a
proof that every fixed rank stabilises under fair rewriting.  The contraction
cocycle makes such a proof plausible, but it does not supply confluence or
fixed-rank stabilisation.  Calling the flat substitution a Boolean
construction would be incorrect.

## 5. Reproduction

The companion exact-arithmetic script checks (1)--(14), the root bits, the
rank-ten/rank-nine cascade, both positive LCM reencodings, and the stated
child-arrival bounds:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchored_substitution_collision_cocycle.py
