# The optimal first recut is closed under an adjacent-cylinder renormalisation

Write

\[
 w_m=\frac1{2^m-1},\qquad M(x,y)=w_xw_y.
\]

For coprime integers (2\leq a\leq b), the first repeated atom in the
ordinary cylinder genealogy rooted at (M(a,b)) occurs at

\[
 n=ab+a+b.                                         \tag{1}
\]

Two independent quantities measure the first nonlocal recut.  The binary
quantity is whether rank (n-1) is absent before the two rank-(n)
emissions are carried.  The arithmetic quantity is the least possible LCM
height used to replace (M(e,n)-M(n-1,n)), where (e) is an endpoint of
one of the two collision cylinders.  The smallest possible values are,
respectively, one empty predecessor rank and height (n-1).

The two minima are attained simultaneously by an infinite family.  The
family is closed by the LCM lift, and the resulting adjacent-cylinder spine
has an exact quadratic recurrence.  The first forced packet interactions
also distinguish (M(2,3)) from larger members of the family.

## 1. Classification of the optimal first recut

Assume

\[
 b=ka+1\quad(k\geq1),\qquad \gcd(a,k+1)>1.         \tag{2}
\]

Then (gcd(a,b)=1), and

\[
 n-1=a(b+k+1).                                     \tag{3}
\]

There is at most one primitive positive solution of
(ap+bq=n-1), because (n-1) lies below the first-collision rank.  Since
(b\equiv1\pmod a), its only possible positive solution is

\[
 (p,q)=(k+1,a).                                    \tag{4}
\]

Condition (2) makes (4) nonprimitive.  Consequently

\[
 c_{a,b}(n-1)=0.                                   \tag{5}
\]

Thus the first pair of rank-(n) atoms carries into a genuinely empty rank
(n-1); there is no predecessor cascade at this first step.

The collision nodes are

\[
 M(a,n-a),\qquad M(b,n-b).                         \tag{6}
\]

Choosing endpoint (a) in the LCM lift gives

\[
 L=\operatorname{lcm}(a,n-1)=n-1.                 \tag{7}
\]

No lift height can be smaller, since every admissible lift height is a
multiple of (n-1).  Conversely, if an ordered coprime pair (a\leq b)
has minimum lift height (n-1), then one of the four endpoints in (6)
divides (n-1).  The two large endpoints exceed ((n-1)/2), and (b\mid
n-1) would imply (b\mid a-1).  Hence (a\mid n-1), equivalently
(a\mid b-1), so (b=ka+1).  Under this condition (4) proves that the
rank (n-1) gap occurs exactly when (gcd(a,k+1)>1).  Therefore (2)
classifies the coprime anchors attaining both minima.

The smallest member is ((a,b)=(2,3)).  Other examples are
((2,7)), ((3,7)), and ((4,5)).

## 2. Exact recut and closure of the lift anchor

Put

\[
 s=\frac{n-1}{a}=b+k+1,
 \qquad
 C=\frac{2^{n-1}-1}{2^a-1}-1
   =\sum_{i=1}^{s-1}2^{ia}.                        \tag{8}
\]

Splitting the two cylinders in (6), carrying their two rank-(n) atoms,
and using

\[
 M(a,n)-M(n-1,n)=C M(n-1,n)                       \tag{9}
\]

gives the exact positive recut

\[
\boxed{
\begin{aligned}
 M(a,n-a)+M(b,n-b)
 ={}&w_{n-1}+C M(n-1,n)\\
    &+M(n-a,n)+M(b,n)+M(n-b,n).
\end{aligned}}
                                                               \tag{10}
\]

The new distinguished cylinder ((n-1,n)) again satisfies (2).  Indeed,
(n=(a+1)(b+1)-1) is odd, so (n-1) is even; for the adjacent pair one
has (k'=1) and

\[
 \gcd(n-1,k'+1)=\gcd(n-1,2)=2.                   \tag{11}
\]

Hence repeated selection of the distinguished lift defines an exact
renormalised spine.  If the current distinguished pair is
((u,u+1)), where (u) is even, its successor is

\[
 (u',u'+1),\qquad u'=u(u+3).                       \tag{12}
\]

Thus the LCM collision clocks on this spine escape quadratically.  Starting
from (M(2,3)), the lower endpoints are

\[
 2,\ 10,\ 130,\ 17290,\ldots.                     \tag{13}
\]

This is a well-founded invariant for the distinguished recut lineage.  It
does not by itself normalize the side cylinders in (10), or atom collisions
between different lineages.

## 3. Forced alignments in the first recut frontier

The binary blocks of the lift coefficient in (8) have first front ranks

\[
 \{,n+ja:1\leq j\leq s-1,\}.                    \tag{14}
\]

One alignment occurs for every anchor in (2).  The bit (2^{b-1}) is
present because (b-1=ka), and its first front is

\[
 2n-b.                                             \tag{15}
\]

The ordinary child (M(n-b,n)) in (10) has the same first front.  Thus the
arithmetic condition that minimizes the LCM height also forces a packet
collision between the lift and an ordinary child.

There is a second forced alignment when (a) is even.  Along the outer path
anchored at (b), the side cylinder discarded at step (t) has first front

\[
 2a+(2t+1)b.                                       \tag{16}
\]

At (t=a/2), equation (16) equals (n+a), the first front of the highest
binary block of (C M(n-1,n)).  That block has capacity (a+1), so the
forced carry leaves capacity (a).

For (a=2), the carried front collides once more.  The outer path anchored
at (a) has side-cylinder fronts

\[
 2b+(2t+1)a.                                       \tag{17}
\]

Condition (2) gives (b\equiv3\pmod4).  Taking
(t=(b+1)/4) in (17) gives

\[
 2b+(2t+1)a=n+a-1.                                 \tag{18}
\]

This is precisely the front produced by the carry at (n+a).  The second
carry leaves capacity one.  Conversely, equality between (17) and
(n+a-1) implies

\[
 2ta=(a-1)(b+1).
\]

Since (b\equiv1\pmod a), this requires (a\mid2).  Therefore (a=2)
is the only member of the optimal class with this immediate two-step outer
side-branch cascade.  No other first-front component can occupy
(n+a-1): the remaining lift fronts are congruent to (n) modulo (a),
the other outer-path equation would require (b\mid ab-1), and the three
children in (10) have different displayed stops.

For (M(2,3)), equations (16)--(18) are the observed chain

\[
 13\longrightarrow12\longrightarrow11,
\]

and the surviving packet has capacity one.  For (M(4,5)), the first
forced lift collision leaves capacity four and there is no second collision
at the next rank in the first-recut frontier.  In this precise sense
(M(4,5)) is a less constrained anchor than (M(2,3)) for an unbounded
recut construction, even though the universal static cut obstruction still
applies to both.

## 4. Consequence for an unbounded schedule

Equations (10)--(12) give an exact, indefinitely iterable recut lineage with
strictly increasing collision clocks.  Equations (15)--(18) show why that
lineage is not an isolated renewal process: the same divisibility that makes
the lift height minimal creates deterministic intersections with the side
forest.

The remaining construction problem is therefore narrower.  One must
normalize all side lineages while preserving the increasing clock of the
distinguished spine.  The adjacent spine itself neither cycles nor reaches a
zero-capacity collision: its lower endpoint grows by (12), and its first
forced lift packet has capacity (u+1).  Any recurring zero-buffer event must
come from intersections between distinct lineages, not from the
renormalised adjacent spine alone.

This conclusion rules out a proof that treats the first LCM lift as
arithmetically independent of the ordinary frontier.  It also identifies
(M(4,5)=1/465), rather than another (a=2) anchor, as the smallest target
that removes the exceptional two-step first-front cascade.

## 5. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/optimal_cylinder_recut_renormalisation.py
```

The script checks the classification, recut identity, coefficient bits,
quadratic spine, and forced front alignments on a bounded grid using exact
integer and rational arithmetic.  The proofs above do not depend on the
finite range of the audit.
