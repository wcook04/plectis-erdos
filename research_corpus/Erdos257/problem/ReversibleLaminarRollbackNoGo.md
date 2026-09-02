# Reversible laminar rollback fails at the first rank-twelve return

Put
\[
  w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note tests whether the anchor-two distortion cocycle closes the global
Booleanisation argument by means of reversible laminar packet trees.  It
does not.  The proposed assertion that a newly exposed front is incomparable
with any same-rank challenger is false in the actual genealogy of
\[
  M(2,3)=w_5+1510M(2,15).                           \tag{1}
\]
The first forced overlap occurs after the provisional fronts
\(7,8,9,10,12\).  Rolling it back locally returns to the state that created
it, while carrying the two fronts as if they were disjoint double-counts a
subtree.

## 1. Pairing-independent load bounds

For a complete component with front rank \(r\), write
\[
  \lambda_r=2^{2-r},\qquad
  \alpha=\frac{3X}{\lambda_r},
  \qquad
  g(r)=\frac{3w_r}{\lambda_r}
      =\frac{3\,2^{r-2}}{2^r-1}.                   \tag{2}
\]
Every primitive height in the root genealogy is divisible by 15, and
binary carries average \(\alpha\).  Hence
\[
  1<\alpha\le A:=\frac{2^{15}}{2^{15}-1}.           \tag{3}
\]
If the component is opened and its reserve is reencoded at a common height
\(H\), then \(15\mid H\) and its exact child-load ratio is
\[
  q=(1-2^{-H})(\alpha-g(r)).                        \tag{4}
\]
Consequently the following strict bounds are independent of all pairing
choices in the preceding carry tree:
\[
 (1-2^{-15})(1-g(r))<q<A-g(r)<0.251.                \tag{5}
\]

Let \(L\) be the total active anchored load.  Complete binary normalization
of the active components conserves \(L\).  Its smallest front is the unique
rank \(r\) satisfying
\[
  \lambda_r\le L<2\lambda_r.                       \tag{6}
\]
Opening that component changes the total load by
\[
  L\longmapsto L-\lambda_r+q\lambda_r.              \tag{7}
\]
Starting from
\[
  L_0=\frac{1510}{2^{15}},                          \tag{8}
\]
the exact rational interval propagation using (5)--(7) forces the fronts
\[
  7,8,9,10,12.                                      \tag{9}
\]
Immediately before opening the rank-twelve component, write
\(L=\lambda_{12}+E\).  The same interval calculation proves
\[
  0.9363\lambda_{12}<E<0.9387\lambda_{12}.          \tag{10}
\]
The opened descendants have load between
\(0.2498\lambda_{12}\) and \(0.2499\lambda_{12}\).
Therefore
\[
  1.1861\lambda_{12}
  <E+L_{\mathrm{desc}}
  <1.1885\lambda_{12}.                              \tag{11}
\]
By (6), exact normalization of the new frontier necessarily exposes rank
12 again.  This conclusion is not a finite-search heuristic: (5)--(11) are
rational inequalities and cover every possible equal-rank pairing.

## 2. Why the challenger is not a disjoint packet

Let \(A\) be the complete rank-twelve component selected in (9), and let
\(D\) be the forest created by opening its reserve.  The external forest
has load \(E<\lambda_{12}\), so it cannot create a rank-twelve component by
binary carries on its own.  But (11) says that \(E\sqcup D\) must create
one.  Every such challenger therefore contains at least one descendant of
\(A\).

The exposed front of \(A\) and its challenger are not incomparable nodes in
a laminar ownership forest.  Their ownership sets overlap in \(D\), while
the challenger also contains external material.  Two proposed local moves
both fail:

1. Adding the complete value of \(A\) to the challenger counts the shared
   descendants twice, so it is not an identity.
2. Rolling back \(A\) removes the descendant part of the challenger.  The
   remaining external forest has load below \(\lambda_{12}\), so the
   challenger disappears and the state returns to the one before \(A\) was
   opened.  Reopening \(A\) recreates the same forced overlap.

Thus the local rule “rollback two disjoint same-rank subtrees and carry” is
not closed.  In particular, the claim that descendant contraction alone
makes same-rank exposed nodes incomparable is false.  The contraction below
one half controls value and load, but cross-branch grafting destroys
laminarity.

None of the easier closure checks causes this failure.  Every carry used
above is legal under the inherited deadline-two certificate.  Every common
height is finite and may be chosen divisible by 15, and every integer
coefficient has a finite binary expansion, so branching is finite.  The
obstruction appears only when the ownership overlap is resolved.  A fair
rule that reopens the rolled-back rank-twelve component repeats the same
state, so neither residual decay nor an infinite Boolean support follows
from the geometric load bound.

## 3. The scalar tail identifies the required nonlocal recut

There is a useful exact diagnostic at the failed state.  After the already
stable atoms \(w_5,w_7,w_8,w_9,w_{10}\), the remaining scalar value is
\[
 \begin{aligned}
 V
 &=M(2,3)-w_5-w_7-w_8-w_9-w_{10}\\
 &=\frac{508634}{806159805}.
 \end{aligned}                                      \tag{12}
\]
Direct comparison gives
\[
  w_{11}<V<2w_{11},                                 \tag{13}
\]
and
\[
  V-w_{11}=\frac{235013993}{1650209120835}>0.       \tag{14}
\]
So the correct next global front is rank 11, even though the local dyadic
packet normalization provisionally chose rank 12 and then recreated it.
Escaping the loop requires recutting the complete scalar tail, or an
equivalent nonlaminar ownership operation, and reencoding (14) at a common
Mersenne height.  That is precisely the global operation the local rollback
proposal was intended to avoid.

This result does not rule out a reversible directed acyclic ownership graph
with a proved global recut rule.  It does rule out the claimed laminar proof,
its incomparability lemma, and the associated inference from
\(\rho<1/2\) to fixed-rank stabilisation.

## 4. Reproduction

The companion script performs only exact rational interval propagation and
the scalar comparisons in (12)--(14):

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/reversible_laminar_rollback_nogo.py
