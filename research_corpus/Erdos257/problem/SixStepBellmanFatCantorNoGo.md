# The six-step Bellman survivor is a fat Cantor set

Put
\[
 w_n=\frac1{2^n-1},\qquad z=w_n,qquad y=\frac{x}{w_n}.
\]
The greedy Bellman step is
\[
 e=\mathbf 1_{y\geq1},\qquad
 y'=(2+z)(y-e),\qquad z'=\frac z{2+z}.             \tag{1}
\]
This note derives the exact six-step return map and the invariant bounded-orbit
set.  The invariant set is not an interval or a finite union of intervals.
It is a nonstationary fat Cantor set with gaps at every scale.  Consequently
no interval trapping inequality, even one with the exact period-six clock,
can prove the root orbit bounded.

The calculation does not decide whether the root point belongs to this set.
It identifies the type of invariant that a successful proof must control.

## 1. The six-step return map

For \(0\leq i\leq6\), define
\[
 d_i(z)=2^i+(2^i-1)z.
\]
After \(i\) steps the clock is
\[
 z_i=\frac z{d_i(z)}.                              \tag{2}
\]
Let \(e=(e_0,\ldots,e_5)\in\{0,1\}^6\) be a six-bit
itinerary, and put
\[
 S_e(z)=\sum_{i=0}^5\frac{e_i}{d_i(z)}.            \tag{3}
\]
On the branch with itinerary \(e\), six iterations of (1) give
\[
 \boxed{
 \begin{aligned}
 Y&=(64+63z)\bigl(y-S_e(z)\bigr),\\
 Z&=\frac z{64+63z}.
 \end{aligned}}                                    \tag{4}
\]
The branch domain is determined by the six intermediate threshold
inequalities in (1).  Formula (4) is affine in \(y\) and rational in \(z\).

At the ranks \(n=2+6j\) relevant to the period-six binary expansion of
\(1/21\),
\[
 z_j=\frac1{4\cdot64^j-1},
 \qquad
 z_{j+1}=\frac{z_j}{64+63z_j}.                     \tag{5}
\]
The target clock therefore returns to the same residue phase because
\(64\equiv1\pmod {21}\).  The greedy itinerary does not become periodic.
Its first block, at ranks 2 through 7, is
\[
 000101,
\]
and (4) gives
\[
 (y_2,z_2)=\left(\frac17,\frac13\right)
 \longmapsto
 (y_8,z_8)=\left(\frac{52615}{27559},\frac1{255}\right). \tag{6}
\]

## 2. The exact bounded-orbit set

For a clock value \(z>0\), let \(K_z\subset[0,2)\) be the set of initial
values whose complete forward orbit under (1) remains in \([0,2)\).  Since
an orbit that reaches \(y\geq2\) subsequently diverges, \(K_z\) is exactly
the bounded-orbit set.  Equivalently, it is the normalized achievement set
formed from the successive weights \(z_i\).  This description makes \(K_z\)
compact.

Write \(q=2+z\) and \(z'=z/q\).  Inverting the two branches of (1) gives the
set identity
\[
 \boxed{
 K_z=\frac1qK_{z'}
     \;\mathbin{\dot\cup}\;
     \left(1+\frac1qK_{z'}\right).}                \tag{7}
\]
The union is disjoint.  Its two convex hulls are
\[
 \left[0,\frac2q\right]
 \quad\hbox{and}\quad
 \left[1,1+\frac2q\right],                        \tag{8}
\]
leaving gaps of positive width because \(2/q<1\).

Iterating (7) six times gives the exact 64-branch return equation
\[
 \boxed{
 K_z=\mathop{\dot\bigcup}_{e\in\{0,1\}^6}
 \left(S_e(z)+\frac1{64+63z}K_Z\right),
 \qquad Z=\frac z{64+63z}.}                       \tag{9}
\]
Thus (9), rather than an interval around the orbit, is the invariant object
associated with the six-step map.

## 3. Exact measure and absence of interval traps

Let \(K_z^{(m)}\) be the set of points surviving the first \(m\) steps.
Each inverse step retains two copies scaled by \(1/(2+z_i)\).  Therefore
\[
 \lvert K_z^{(m)}\rvert
 =2\prod_{i=0}^{m-1}\frac2{2+z_i}.                 \tag{10}
\]
Since
\[
 z_i=\frac z{2^i+(2^i-1)z},
\]
the product has the exact limit
\[
 \prod_{i=0}^{\infty}\frac2{2+z_i}=\frac1{1+z}.
\]
Continuity of measure for the decreasing finite-survival sets gives
\[
 \boxed{\lvert K_z\rvert=\frac2{1+z}.}             \tag{11}
\]
In particular,
\[
 \lvert K_{1/3}\rvert=\frac32.                    \tag{12}
\]

Despite its positive measure, \(K_z\) has empty interior.  At depth \(m\),
every surviving component has length at most
\[
 \frac{2}{\prod_{i=0}^{m-1}(2+z_i)},              \tag{13}
\]
which tends to zero, and every such component is split at the next step by
a positive gap.  Every finite component also has two nonempty descendants,
so \(K_z\) has no isolated points.  Hence it is a fat Cantor set, and every
open interval contains a point whose orbit eventually reaches
\([2,\infty)\).

It follows that no forward-invariant region contained in \([0,2)\) and
containing a nonempty interval can prove boundedness of the root orbit.  A
finite union of interval inequalities cannot be the missing invariant.  Any
successful trapping argument must locate the single point \(1/7\) inside
the thin set \(K_{1/3}\), using arithmetic information not stable under an
interval perturbation.

## 4. The exact remaining root statement

The Bellman theorem gives
\[
 \frac1{21}\in\mathcal A_2
 \quad\Longleftrightarrow\quad
 \frac17\in K_{1/3}.                               \tag{14}
\]
If (14) holds, then \(y_n<2\) forces the real residual
\(x_n=w_ny_n\) to tend to zero.  Moreover the greedy word cannot be
eventually all one: boundedness would then express \(1/21\) as a finite
rational sum plus a cofinite tail of the full Mersenne series, contradicting
the Lean-checked full-support irrationality theorem
`irrational_erdosSum_full_support`.  Thus membership in \(K_{1/3}\) also
forces infinitely many zero digits.

Equation (14) is not proved here.  The contribution of (7)--(13) is the
structural exclusion: the target-specific invariant cannot be a robust
interval, a finite corridor, or a phase-six box.  It must resolve membership
in a positive-measure Cantor set at the exact rational point \(1/7\).

## 5. Exact receipt

The companion script verifies (2)--(6), the 64 branch formulas, and the
finite-product identity behind (10)--(12):

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/six_step_bellman_fat_cantor.py
