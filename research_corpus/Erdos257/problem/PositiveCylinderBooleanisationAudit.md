# Positive cylinder expansions and anticipatory Boolean carry

Put
\[
  w_n=\frac1{2^n-1},\qquad
  M(a,b)=w_aw_b.
\]
The positive Stern--Brocot identity is
\[
  M(a,b)=w_{a+b}+M(a+b,b)+M(a,a+b).                 \tag{1}
\]
It is an exact identity of positive real numbers.  Iterating (1) gives
\[
  M(a,b)=\sum_{n\geq1}c_{a,b}(n)w_n,                \tag{2}
\]
where
\[
  c_{a,b}(n)=\#\{(p,q)\in\mathbb N_{>0}^2:
      (p,q)=1,\ ap+bq=n\}.
\]
The convergence and the cylinder splitting law are formalised in
GcdMomentCalculus.lean.  Formula (2) is positive, but its coefficients are
not Boolean.

## 1. The lattice carry behind the denominator-six bound

Let
\[
  r_{a,b}(N)=\#\{(i,j)\in\mathbb N_{>0}^2:ai+bj=N\}.
\]
Every positive pair has a unique common divisor, so
\[
  r_{a,b}(N)=\sum_{d\mid N}c_{a,b}(d).               \tag{3}
\]
Let \(t_N\) be the \(N\)-th binary digit of \(M(a,b)\).  Define the raw
lattice carry by
\[
  K_0=0,\qquad K_N=2K_{N-1}+t_N-r_{a,b}(N).          \tag{4}
\]
This is the ordinary base-two carry which converts the nonnegative lattice
coefficients \(r_{a,b}(N)\) into the binary digits of the same number.

For \(M(2,3)=1/21\), the source digits are \(000011\) periodically and a
calculation in the six residue classes gives
\[
  K_N=\left\lfloor\frac N6\right\rfloor.             \tag{5}
\]
Indeed, (4) is equivalent to
\[
  r_{2,3}(N)=2\left\lfloor\frac{N-1}{6}\right\rfloor
      +t_N-\left\lfloor\frac N6\right\rfloor,
\]
and the right side counts the positive solutions of \(2i+3j=N\) in each
residue class modulo \(6\).

Now let \(b_n\in\{0,1\}\) be a proposed Boolean support, put
\[
  h_b(N)=\sum_{d\mid N}b_d,
\]
and let its quotient defect satisfy
\[
  Q_0=0,\qquad Q_N=2Q_{N-1}+t_N-h_b(N).
\]
The difference
\[
  E_N=K_N-Q_N
\]
therefore satisfies the exact recurrence
\[
  E_N=2E_{N-1}+h_b(N)-r_{a,b}(N).                    \tag{6}
\]
For \(1/21\), the proposed inequality
\[
  Q_N\leq\lfloor N/6\rfloor
\]
is exactly \(E_N\geq0\).  Thus the denominator-six bound is not an
unexplained feature of the period-six word.  It asserts that the Boolean
divisor pulses never fall behind the carry created by the two-dimensional
positive lattice source.

This interpretation does not prove the inequality.  It identifies its
mathematical content without changing its logical strength.

## 2. Booleanisation must anticipate the first collision

The first failure of coefficientwise Booleanity is already decisive.  The
formal module Primitive23Multiplicity.lean proves
\[
  c_{2,3}(10)=0,\qquad c_{2,3}(11)=2.                 \tag{7}
\]
On the other hand, exact greedy comparison for \(1/21\) forces the selected
prefix
\[
  5,7,8,9,10.                                        \tag{8}
\]
In particular, rank \(10\) is selected before the two primitive emissions at
rank \(11\) are encountered.  Any positive procedure which retains the
coefficients through their first collision and only moves excess mass to
larger ranks is therefore impossible.

There is also a general reason.  Strict superincreasingness gives
\[
  w_n>\sum_{m>n}w_m.
\]
After one copy of \(w_n\) has been retained, a second copy cannot be replaced
by distinct weights of ranks greater than \(n\).  A positive Booleanisation
must alter an earlier decision before the collision, or use an additional
nonlocal state.

The exact positive carry is
\[
  2w_n+M(n-1,n)=w_{n-1}.                              \tag{9}
\]
Thus a duplicate at rank \(n\) can move one step to the left only when it is
accompanied by the cylinder credit \(M(n-1,n)\).  For the first \(1/21\)
collision, (9) requires \(M(10,11)\).  This cylinder is not a node of the
primitive tree rooted at \((2,3)\): a coordinate \(10\) would require a
primitive positive solution of \(2p+3q=10\), excluded by (7).  The required
credit must therefore be assembled from several labelled frontier clocks.

At depth three, the two cylinders whose next stop has rank \(11\) are
\(M(8,3)\) and \(M(2,9)\).  Splitting both and applying (9) gives the exact
positive remainder
\[
\begin{aligned}
 &M(11,3)+M(8,11)+M(11,9)+M(2,11)-M(10,11)\\
 &\hspace{35mm}=\frac{3481}{14811335}>0.              \tag{10}
\end{aligned}
\]
There is in fact an exact positive cylinder decomposition.  Since
\[
  w_2=\frac{2^{10}-1}{2^2-1}w_{10}=341w_{10},
\]
we have
\[
\begin{aligned}
 M(8,3)+M(2,9)-w_{10}
   ={}&M(11,3)+M(8,11)+M(11,9)\\
     &+340M(10,11).                                  \tag{11}
\end{aligned}
\]
This is the anticipatory formulation: the two rank-\(11\) cylinders pay
\(w_{10}\) before either copy of \(w_{11}\) is emitted.

The same operation closes for every collision, including the first even
collision.  The mechanism is an LCM lift.  If \(2\leq e<n-1\), put
\[
  L=\mathop{\rm lcm}(e,n-1),\qquad
  A=\frac{2^L-1}{2^e-1}
      -\frac{2^L-1}{2^{n-1}-1}.
\]
Both quotients are integers and the first is larger, so \(A\) is a positive
integer.  Directly,
\[
  M(e,n)-M(n-1,n)=A M(n,L).                           \tag{12}
\]

Now let \(M(a,b)\) and \(M(c,d)\) be any two cylinders with
\(a+b=c+d=n\).  Choose either endpoint \(e\) of either cylinder.  All
endpoints in the tree rooted at \((2,3)\) are at least \(2\), hence
\(2\leq e<n-1\).  Split both cylinders by (1), use
\(w_{n-1}=2w_n+M(n-1,n)\), and apply (12) to the chosen child
\(M(e,n)\).  The result is
\[
  M(a,b)+M(c,d)
    =w_{n-1}+A M(n,L)+\text{three child cylinders}.  \tag{13}
\]
Every cylinder on the right of (13) has stop strictly larger than \(n\).
Thus the cone of finite nonnegative integer cylinder sums is closed under
one anticipatory collision rewrite.

At rank \(20\), the two primitive cylinders are \(M(11,9)\) and
\(M(17,3)\).  The endpoint-divisibility shortcut is unavailable because no
endpoint divides \(19\), but (12) with \(e=3\) gives
\[
\begin{aligned}
 L&=57,\\
 A&=\frac{2^{57}-1}{2^3-1}
       -\frac{2^{57}-1}{2^{19}-1}
     =20587609132405320,\\
 M(3,20)-M(19,20)&=20587609132405320M(20,57).         \tag{14}
\end{aligned}
\]
The large coefficient is not cosmetic.  It shows why ordering cylinders
only by their next stop is not by itself a termination proof: the LCM lift
moves the stop from \(23\) to \(77\), but creates about \(2^{54}\) copies.
The value nevertheless moves strictly into the future.  More generally,
the surplus after rewriting a pair of stop-\(n\) cylinders is positive and
smaller than \(w_n\), so it cannot itself force a rank at most \(n\).  Here
is a short bound for the latter assertion.  Among cylinders with endpoints
at least \(2\) and fixed stop \(n\), the largest is \(M(2,n-2)\).  For
\(n\geq6\),
\[
  2M(2,n-2)
   \leq \frac{128}{45}2^{-n}
   <3\cdot2^{-n}
   <w_{n-1}+w_n.
\]
The case \(n=5\) is immediate by direct substitution.  Subtracting
\(w_{n-1}\) gives the claim; positivity follows from (13).

What remains is global rather than local.  Rewrites output an atom
\(w_{n-1}\).  Atoms produced by different collisions can themselves
collide, and (13) does not specify a confluent schedule for attaching future
cylinder credit to those atoms.  A Boolean-normal-form theorem would need
to prove that every locally finite positive cylinder multiset admits an
infinite rewrite schedule such that:

1. each rank eventually carries at most one atom;
2. the cylinder frontier escapes to infinity in value, not merely in its
   displayed stop labels; and
3. the limiting atom support is infinite and retains the initial value.

Proving these three statements for the single initial cylinder \(M(2,3)\)
would construct an infinite Boolean representation of \(1/21\).

## 3. Relation to the future-divisor resolvent

For a prefix \(B\cap[1,R]\), define
\[
  \nu^B_R(c)=\sum_{\substack{d\leq R\\d\mid2R+c}}b_d,
  \qquad
  \mathscr R^B_R(z)=\sum_{c\geq1}\nu^B_R(c)z^c.
\]
The primitive cylinder source has the analogous labelled resolvent
\[
  \nu^C_R(c)=\sum_{\substack{d\leq R\\d\mid2R+c}}c_{2,3}(d),
  \qquad
  \mathscr R^C_R(z)=\sum_{c\geq1}\nu^C_R(c)z^c.       \tag{15}
\]
The coefficient difference in (15) is precisely the future contribution of
the labels at most \(R\) to (6).  There is a second, unavoidable contribution
from the middle labels.  Write
\[
  \mu^B_R(c)=\sum_{\substack{R<d\leq2R\\d\mid2R+c}}b_d,
  \qquad
  \mu^C_R(c)=\sum_{\substack{R<d\leq2R\\d\mid2R+c}}c_{2,3}(d),
\]
and let \(\mathscr M^B_R,\mathscr M^C_R\) be their generating functions.
If no labels are inserted after \(2R\), then
\[
  E_{2R+c}
  =2^cE_{2R}+\sum_{j=1}^c2^{c-j}
       \bigl(\nu^B_R(j)-\nu^C_R(j)
             +\mu^B_R(j)-\mu^C_R(j)\bigr),            \tag{16}
\]
and hence
\[
  \lim_{c\to\infty}2^{-c}E_{2R+c}
  =E_{2R}+\mathscr R^B_R(1/2)-\mathscr R^C_R(1/2)
     +\mathscr M^B_R(1/2)-\mathscr M^C_R(1/2).        \tag{17}
\]
Thus \(E\) is not itself an evaluation of the actual-prefix resolvent.
Even under frozen continuation, the lossless state consists of \(E_{2R}\),
the difference of the two old-prefix resolvents, and the difference of the
two middle-label resolvents.  In the live process, labels greater than \(2R\)
add further clocks.

There is no coefficientwise domination
\(\nu^B_R(c)\geq\nu^C_R(c)\), and there is no evaluation domination
\(\mathscr R^B_R(1/2)\geq\mathscr R^C_R(1/2)\).  Exact finite calculations
already disprove both.  At \(R=20\), for example,
\[
  \mathscr R^B_R(1/2)-\mathscr R^C_R(1/2)<0,
\]
although \(E_{40}>0\).  The integer surplus comes from earlier anticipatory
selections and from labels inserted between \(R\) and \(2R\), not from
coefficientwise payment by the old actual clocks.

This rules out a direct proof of the resolvent barrier by comparing the
actual prefix coefficientwise with the primitive lattice source.  A
minimal-socket descent would have to transport the full state in (12), as
well as the clocks inserted after \(2R\).  The primitive source identifies the
required cylinder credit, but (10) shows that this credit is aggregate and
not a single inherited cylinder.

## 4. The residual in the \(x_5\) identity

For
\[
  x_a=\frac{2^{a-1}+1}{2^{2a-1}-1},
\]
the identity
\[
  x_a=w_a+w_{2a}+x_aw_{2a}
\]
is positive.  At \(a=5\),
\[
  x_5w_{10}=17M(9,10).                                \tag{18}
\]
The first Stern--Brocot stop of \(M(9,10)\) is rank \(19\), with
multiplicity \(17\) in (14).  Exact comparison gives
\[
  17w_{19}>w_{15},
\]
and the greedy expansion of the residual begins \(15,19,24,25,\ldots\).
Thus rank \(15\) is another anticipatory carry.  It occurs four ranks before
the multiplicity at rank \(19\), which explains why translating the pair
\((5,10)\) does not iterate.

The factor \(17\) makes (14) more difficult than a single cylinder.  The raw
carry domination \(Q\leq K\) that is numerically valid for \(M(2,3)\) is
already false for \(17M(9,10)\) at rank \(29\).  Therefore the \(x_5\)
identity does not supply a coefficientwise positive recursion by itself.

## 5. Reproduction and boundary

The script
scripts/positive_cylinder_booleanisation_audit.py verifies (3)--(5), the
forced prefix (8), the carry identity (9), and finite instances of
\(E_N\geq0\) with exact arithmetic.  It also audits the initial ranks of
(14).

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/positive_cylinder_booleanisation_audit.py --depth 5000

The local obstruction is now removed: (12)--(14) prove that every pairwise
frontier collision has an exact positive LCM-lift rewrite inside the integer
cylinder cone.  The unresolved obstruction is the global interaction of
the backward atoms produced by different rewrites.  One must prove a
confluent Boolean normal form with a vanishing frontier, or prove a
minimal-socket descent for the full joint state (16).  Neither global
statement is established here.
