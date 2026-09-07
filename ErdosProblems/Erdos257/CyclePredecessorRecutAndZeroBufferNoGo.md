# Cycle-triggered predecessor recuts and the zero-buffer seam

Put
\[
  w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note isolates the valid theorem behind the rank-twelve rollback cycle.
A complete same-rank challenger always makes the global predecessor atom
affordable, and the resulting global recut contracts anchored load by less
than \(0.251\) in the height-fifteen genealogy.  However, cycle-triggered
recuts do not form a complete Booleanisation algorithm.  A two-packet exact
state reaches a scalar duplicate without ever producing a load-level
challenger.

## 1. Every complete anchor-two front carries a full first bank

For a front at rank \(r\), let
\[
  \lambda_r=2^{2-r},\qquad
  g(r)=\frac{3w_r}{\lambda_r}.
\]
Every complete anchor-two power packet at rank \(r\) has value
\[
  X=\frac{\alpha\lambda_r}{3},
  \qquad \alpha>1.                                  \tag{1}
\]
The same inequality holds for any component produced by binary carries,
because its distortion is an average of primitive distortions.

For \(r\ge4\), one has
\[
  \frac{\lambda_r}{3}
  \ge w_r+M(r-1,r)
  =w_{r-1}-w_r.                                     \tag{2}
\]
Indeed, set \(x=2^{r-1}\).  After clearing positive denominators, (2) is
equivalent to
\[
  \frac{x^2}{2}-3x+1\ge0,
\]
which holds for \(x\ge8\).  Combining (1) and (2), every complete front
satisfies the strict full-bank inequality
\[
  X>w_{r-1}-w_r.                                    \tag{3}
\]

## 2. A rollback cycle forces a global predecessor recut

Consider a normalized finite state whose smallest complete component
\(A\) has rank \(r\ge4\).  Open \(A\) tentatively as \(w_r+D\), while
retaining an external forest \(E\).  Suppose exact normalization of
\(D\sqcup E\) produces a complete challenger \(F\) at rank \(r\).  The
complete scalar state \(V=A+E\) then satisfies
\[
  V\ge w_r+F>w_r+(w_{r-1}-w_r)=w_{r-1}.             \tag{4}
\]
Thus the local overlap is not merely an obstruction: it certifies that the
whole state can be recut at the predecessor.

For the genealogy rooted at height 15, all primitive and carried
distortions satisfy
\[
  1<\alpha\le A_{15}:=\frac{2^{15}}{2^{15}-1}.      \tag{5}
\]
The normalized state has total load \(L<2\lambda_r\), so
\[
  V<\frac{2A_{15}\lambda_r}{3}<2w_{r-1}.            \tag{6}
\]
Equations (4)--(6) show that
\[
  0<V-w_{r-1}<w_{r-1}.                              \tag{7}
\]
Choose a finite common Mersenne height, divisible by 15, which clears the
denominator of (7).  Then the residual is \(B M(2,H)\) with
\(0<B<2^H\), so its binary expansion is finite, positive, and every child
front lies strictly after \(r-1\).

This global recut also contracts.  If \(L'\) is its child load, then
\[
 \frac{L'}L
 < A_{15}-\frac{3w_{r-1}}L
 < A_{15}-g(r-1)
 \le A_{15}-\frac34
 =\frac{32771}{131068}<0.251.                       \tag{8}
\]
Thus `cycle implies predecessor recut` is a theorem, not a numerical
pattern.  It explains the exact rank-twelve event, where the pooled scalar
tail affords \(w_{11}\).

## 3. Why the alternating algorithm still fails

The converse pressure is false: absence of a load-level cycle does not make
the locally released atom Boolean-safe.  Consider the two height-fifteen
packets
\[
  A=P(15,2)=4M(2,15),\qquad E=P(15,1)=2M(2,15).     \tag{9}
\]
Their fronts are respectively 15 and 16.  Opening \(A\) gives the exact
identity
\[
  P(15,2)=w_{15}+P(15,0).                           \tag{10}
\]
The child and external loads, measured in units of \(\lambda_{15}\), are
\[
  \frac14+\frac12=\frac34<1.                       \tag{11}
\]
Hence they cannot normalize back to a rank-fifteen challenger.  The cycle
trigger does not fire.

Nevertheless their scalar values satisfy
\[
 \begin{aligned}
  P(15,1)+P(15,0)&=w_{15},\\
  P(15,2)+P(15,1)&=2w_{15}<w_{14}.                  \tag{12}
 \end{aligned}
\]
After the proposed local release, the tail is exactly another copy of
\(w_{15}\).  Booleanity requires carrying the duplicate, but the complete
state lies strictly below \(w_{14}\), so the predecessor recut is illegal.
This is the zero-buffer fatal gap in exact anchor-two coordinates.

The example obeys every structural hypothesis used above: height is
divisible by 15, branching is finite, the opening contraction is exactly
\(1/4\), and the post-opening load is below the same-rank carry mass.  The
two packets also occur among the seven first-wave packets of the root
decomposition, although
the other five packets prevent this isolated state from being the complete
root tail.

Therefore alternating local releases with cycle-triggered predecessor
recuts has a strong decreasing invariant whenever a cycle occurs, but it is
not globally complete.  Any successful rule must also distinguish the
narrow scalar interval
\[
  2w_r\le V<w_{r-1}                                 \tag{13}
\]
before releasing \(w_r\).  The distortion and load bounds alone do not
forbid that interval.

## 4. Reproduction

The companion exact-arithmetic script checks (2), (5)--(12), the global
contraction bound through rank 500, and the complete two-packet
counterexample:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/cycle_predecessor_recut_zero_buffer.py
