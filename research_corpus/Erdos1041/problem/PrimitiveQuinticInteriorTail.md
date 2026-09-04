# Erdős #1041: the primitive-quintic interior two-tail theorem

Status: analytic theorem proved on 2026-08-24.  The finite harmonic-separator
argument is formalized in `PrimitiveQuinticInteriorTail.lean`.  This closes
the complete closed-disk primitive sparse quintic tail problem, including
mixed boundary/interior root configurations.  It is a genuine degree-five
subproblem of Erdős #1041, not the unrestricted problem.

## The theorem

Let

\[
 p(z)=z^5+a z^4+bz+c
\]

be monic, and suppose all five roots lie in the closed unit disk.  Then at
least two distinct roots `w_i` satisfy

\[
 |b w_i+c|\le1.                                    \tag{1}
\]

If `a != 0`, the two inequalities are strict.  If `a=0`, every root satisfies
(1), and the tail at `w_i` is strict exactly when `|w_i|<1`.

Consequently the two corresponding radial spokes are unit-sublevel paths;
they are strict when the selected tail inequalities are strict:
for `0 <= t <= 1`, Abel summation gives

\[
 |p(tw_i)|\le1,
\]

with the usual endpoint interpretation at `t=0`.  Thus the primitive sparse
quintic has two distinct roots joined to the origin inside the unit
lemniscate.

## 1. Rotate the three exact Newton moments

Write `a=r exp(i phi)` and put `z_i=exp(-i phi)w_i`.  Then `r>=0`,
`|z_i|<=1`, and the missing `z^3,z^2` coefficients give

\[
 \sum z_i=-r,\qquad \sum z_i^2=r^2,\qquad
 \sum z_i^3=-r^3.                                \tag{2}
\]

At a root,

\[
 |b w_i+c|=|w_i|^4|w_i+a|
           =|z_i|^4|z_i+r|.                     \tag{3}
\]

If `r=0`, (3) is `|z_i|^5<=1` for every root, with equality exactly on the
unit circle, so assume `r>0`.  Equation (2) also gives `r^3<=5<8`, hence
`r<2`.

Put

\[
 x=\operatorname{Re}z,\qquad s=|z|^2.
\]

Then the squared tail in (3) is

\[
 E_r(x,s)=s^4(s+r^2+2rx).                        \tag{4}
\]

## 2. Harmonicize the boundary separator

The boundary proof used

\[
 Q_r(x)=(-r/2-x)(1-x)^2.
\]

On the unit circle this has Fourier expansion

\[
 Q_r(\operatorname{Re}z)=
 1-\frac{3r}{4}
 +(r-\tfrac74)\operatorname{Re}z
 +(1-\tfrac r4)\operatorname{Re}z^2
 -\tfrac14\operatorname{Re}z^3.
\]

Use the right side as a harmonic function throughout the disk and call it
`H_r(z)`.  In real coordinates,

\[
 H_r(x,s)=Q_r(x)+(1-s)
   \left(1-\frac r4-\frac{3x}{4}\right).         \tag{5}
\]

Because only the first three power sums occur, (2) gives the exact identity

\[
 \sum_{i=1}^5 H_r(z_i)=5-2r.                    \tag{6}
\]

The maximum principle, or the elementary disk-coordinate factorization in
the Lean proof, gives

\[
 H_r(z)\le 4-2r\qquad(|z|\le1).                 \tag{7}
\]

The crucial gain is that an unsafe interior tail has a much smaller score.

## 3. An unsafe tail contributes at most `2/31`

Assume `E_r(x,s)>=1` and set

\[
 d=x+r/2,\qquad u=1-x,qquad
 A=1-r/4-3x/4.
\]

The unsafe inequality is

\[
 1\le s^4(s+2rd).
\]

Since `0<s<=1`, subtracting `s^5` and factoring `1-s^5` yields

\[
 5(1-s)\le 2rd.                                  \tag{8}
\]

In particular `d>=0`.  Formula (5) becomes

\[
 H_r=-d u^2+(1-s)A.
\]

If `A<=0`, this is nonpositive.  If `A>0`, (8) gives

\[
 H_r\le dP,qquad
 P=-u^2+\frac{2r}{5}A.
\]

Using `r=2(d+u-1)`, completion of squares gives the global estimate

\[
 \frac1{31}-P
 =\frac25\left(d-\frac{38}{31}
               +\frac14(u-\frac3{31})\right)^2
  +\frac{31}{40}\left(u-\frac3{31}\right)^2
 \ge0.                                           \tag{9}
\]

Also `0<=d<2`.  Hence, whether `P` is positive or not,

\[
 E_r(x,s)\ge1\quad\Longrightarrow\quad
 H_r(x,s)\le\frac2{31}.                          \tag{10}
\]

The constant is deliberately simple rather than sharp; numerical
optimization puts the actual unsafe maximum near `0.02194`, well below
`2/31`.

## 4. The exact contradiction

Suppose at most one of the five tails were safe.  The possible safe root
contributes at most `4-2r` by (7), and each of the other four contributes at
most `2/31` by (10).  Therefore

\[
 \sum_i H_r(z_i)
 \le 4-2r+\frac8{31}
 <5-2r,
\]

contradicting (6).  Thus at least two distinct tails satisfy (1).

## What closed, and what did not

This proves the complete closed-disk primitive quintic statement; the earlier
radial-crossing monotonicity conjecture is no longer needed.  The theorem
includes strict-interior, paraorthogonal-boundary, and mixed root
configurations in one argument, with strict selected tails whenever `a!=0`
and the exact `a=0` equality classification above.

The unrestricted degree-five polynomial and all-degree Erdős #1041 remain
open.  The exact downstream question is now whether harmonicizing suitable
Newton-moment separators can handle one or more nonzero middle coefficients,
or whether a counterexample blocks that propagation.

The Refinery should present this immediately after the boundary theorem,
retaining the distinction between the solved primitive sparse family and the
unrestricted problem.
