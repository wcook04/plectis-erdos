# Fixed-horizon reduction for the \(1/465\) corridor

Status: exact reduction, exact finite base certificate, and open comparator,
2026-08-21.  A terminal corridor bound at a sufficiently large horizon forces
all intermediate corridor bounds.  Consequently the global construction can
be reduced to a fixed-horizon subset-sum question.  The remaining
fixed-horizon comparator is not proved here.

Let

\[
 H_n=\left\lfloor\frac{2^n}{465}\right\rfloor,
 \qquad
 K_n=\left\lfloor\frac n{20}\right\rfloor,
 \qquad
 f_b(n)=\sum_{d\mid n}b_d,
\]

and let \(t_n\) be the binary digits of \(1/465\).  As before,

\[
 Q_0=0,
 \qquad
 Q_n=2Q_{n-1}+t_n-f_b(n).                         \tag{1}
\]

## 1. The exact divisor threshold is 481

Put

\[
 r_{4,5}(n)=
 \#\{(i,j)\in\mathbb Z_{>0}^2:4i+5j=n\}.
\]

The period-twenty count is

\[
 r_{4,5}(20k+s)=k+t_s\quad(1\leq s\leq19),
 \qquad
 r_{4,5}(20k)=k-1.                                \tag{2}
\]

In particular, \(r_{4,5}(n)\geq\lfloor n/20\rfloor-1\).  Exact divisor
enumeration gives

\[
 \tau(n)\leq r_{4,5}(n)\quad(481\leq n<1620),     \tag{3}
\]

while at the preceding rank

\[
 \tau(480)=24>23=r_{4,5}(480).                    \tag{4}
\]

For \(n\geq1620\), the elementary divisor pairing bound gives

\[
 \tau(n)\leq2\lfloor\sqrt n\rfloor
 \leq\left\lfloor\frac n{20}\right\rfloor-1
 \leq r_{4,5}(n).                                 \tag{5}
\]

The middle inequality holds at \(1620\), and it remains true thereafter by
checking the successive square and multiple-of-twenty blocks.  Thus 481 is
the exact least threshold after which \(\tau(n)\leq r_{4,5}(n)\) always
holds.  Since \(f_b(n)\leq\tau(n)\), the same threshold works uniformly for
every Boolean word.

## 2. Terminal bounds propagate backward

Define the upper-corridor margin

\[
 E_n=K_n-Q_n.
\]

Equation (2) is equivalent to the carry identity

\[
 K_n=2K_{n-1}+t_n-r_{4,5}(n).
\]

Combining it with (1) gives

\[
 E_n=2E_{n-1}+f_b(n)-r_{4,5}(n).                  \tag{6}
\]

Suppose a Boolean word of length \(N\geq481\) satisfies only the terminal
bounds \(0\leq Q_N\leq K_N\).  Solving the two recurrences backward gives

\[
 Q_{n-1}=\frac{Q_n-t_n+f_b(n)}2,
 \qquad
 E_{n-1}=\frac{E_n+r_{4,5}(n)-f_b(n)}2.           \tag{7}
\]

If \(Q_n\geq0\), the first numerator in (7) is at least \(-1\).  It is an
even integer, so it cannot be negative.  If \(E_n\geq0\) and \(n\geq481\),
(3)--(5) make the second numerator nonnegative.  Backward induction therefore
proves

\[
 0\leq Q_n\leq K_n\qquad(480\leq n\leq N).       \tag{8}
\]

The direction matters: \(f_b(n)\leq r_{4,5}(n)\) controls the upper margin
when (6) is read backward.  Read forward, it says only
\(E_n\leq2E_{n-1}\) and does not preserve nonnegativity.

## 3. The finite base certificate

At a fixed horizon put

\[
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

The exact expansion

\[
 q_{N,d}=\sum_{\substack{k\geq1\\kd\leq N}}2^{N-kd}               \tag{9}
\]

shows that these weights are strictly reverse-superincreasing:

\[
 q_{N,m}>\sum_{d=m+1}^Nq_{N,d}.                   \tag{10}
\]

Indeed, the \(k=1\) layer leaves exactly one after subtracting the later
weights.  For each \(k\geq2\), the term at \(m\) exceeds even the infinite
geometric tail over \(d>m\), whose ratio to it is
\(1/(2^k-1)<1\).  Thus every integer has at most one Boolean
\(q_{N,d}\)-representation, and ordinary decreasing-weight greedy finds it
whenever it exists.

At rank 480, exact greedy arithmetic gives a representation

\[
 H_{480}-q=\sum_{d=1}^{480}b_dq_{480,d}            \tag{11}
\]

for every \(q\in[0,24]\).  Direct substitution of each of these 25 unique
words into (1) verifies every inequality

\[
 0\leq Q_n\leq K_n\qquad(1\leq n\leq480).        \tag{12}
\]

This is a finite exact certificate, not an enumeration of \(2^{480}\)
words: strict superincrease proves that (11) lists every word whose terminal
defect is in the corridor.

Combining (8) and (12) yields the main reduction.

> **Terminal-to-prefix coherence theorem.**  Let \(N\geq481\).  Every
> Boolean word satisfying \(0\leq Q_N\leq K_N\) automatically satisfies
> \(0\leq Q_n\leq K_n\) for every \(n\leq N\).

No cross-horizon prefix-stabilisation theorem is required.

## 4. The remaining fixed-horizon comparator

Let \(M=\lfloor N/2\rfloor\).  For \(d>M\), the quotient coins are the
ordinary binary weights

\[
 q_{N,d}=2^{N-d},
 \qquad
 C_N=\sum_{d=M+1}^Nq_{N,d}=2^{N-M}-1.             \tag{13}
\]

Run decreasing-weight Boolean greedy on \(H_N\) using only the coins
\(q_{N,d}\) with \(d\leq M\), and call the remainder \(R_N\).  The single
inequality

\[
 \boxed{R_N\leq C_N+K_N}                          \tag{14}
\]

is sufficient to construct a corridor endpoint at horizon \(N\).  If
\(R_N\leq C_N\), the upper binary coins represent \(R_N\) and give endpoint
zero.  Otherwise take \(e=R_N-C_N\leq K_N\) and select every upper coin;
the resulting word represents \(H_N-e\).  The terminal-to-prefix theorem
then makes this word globally corridor-admissible.  Proving (14) for all
\(N\), together with the finite ranks below 481, would give arbitrarily long
valid prefixes and hence an infinite path by finite branching.

There is a tempting last-coin estimate.  If the remainder entering the coin
at \(M\) were known to be less than \(q_{N,M-1}\), then

\[
 R_N<\max\{q_{N,M},q_{N,M-1}-q_{N,M}\}.           \tag{15}
\]

For \(N=2M\), the two quantities on the right are \(C_N+2\) and
\(C_N+4\).  For \(N=2M+1\), they are \(C_N+3\) and \(C_N+7\).
Under the unproved entry bound, this would give
\(R_N-C_N\leq6\), enough for \(N\geq120\).

The entry bound is not a formal property of Boolean greedy.  Consecutive
quotient coins satisfy \(q_{N,d-1}>2q_{N,d}\), so after taking a coin once
the remainder can still exceed that coin.  An earlier such event can
propagate to the midpoint and invalidate (15).  Quotient-coin arithmetic
alone admits targets for which the lower-greedy remainder is much larger
than \(C_N+K_N\).

Pointwise stabilisation to a real-greedy prefix also does not prove (15): it
controls each fixed rank \(d\) as \(N\to\infty\), whereas (15) needs control
uniformly through the moving rank \(M=\lfloor N/2\rfloor\).  Establishing
that moving comparator, or proving (14) by a different global argument, is
the remaining boundary.

## 5. Diagonal permanence and a first-excess certificate

The lower greedy decisions admit an efficient diagonal recurrence.  Let
\(\rho_{d-1}\) be the remainder after the coins through \(d-1\) have been
processed at horizon \(2d-2\).  Let

\[
 F_{d-1}(n)=\sum_{\substack{a<d\\a\mid n}}b_a,
 \qquad
 s_{d-1}=\sum_{a<d}b_a.
\]

Transporting the remainder forward by two binary ranks shows that the
remainder immediately before the midpoint coin at horizon \(2d\) is

\[
 T_d=4\rho_{d-1}+2t_{2d-1}+t_{2d}
 -2F_{d-1}(2d-1)-F_{d-1}(2d).                    \tag{16}
\]

Put

\[
 w_d=q_{2d,d},
 \qquad
 D_d=T_d-w_d,
 \qquad
 b_d={\bf1}_{D_d\geq0},
 \qquad
 \rho_d=T_d-b_dw_d.                              \tag{17}
\]

For \(d\geq2\), one has \(w_d=2^d+1\).  Equations (16)--(17), together
with a divisor-load sieve, compute the diagonal word in
\(O(D\log D)\) arithmetic operations through rank \(D\).

There is also an exact permanence certificate.  Assuming the earlier bits
have already stabilised, define the decision margin at an arbitrary later
horizon by

\[
 \Delta_{N,d}=H_N-sum_{a<d}b_aq_{N,a}-q_{N,d}
 \qquad(N\geq2d).                                 \tag{18}
\]

The quotient transport law gives

\[
 \Delta_{N+1,d}=2\Delta_{N,d}+t_{N+1}
 -\sum_{\substack{a<d\\a\mid N+1}}b_a
 -{\bf1}_{d\mid N+1}.                            \tag{19}
\]

If \(D_d<0\), then \(\Delta_{N,d}\leq-1\) forever, because the final
three terms in (19) are at most one.  If

\[
 D_d\geq s_{d-1}+1,                               \tag{20}
\]

then \(\Delta_{N,d}\geq s_{d-1}+1\) forever, because the same pulse is
at least \(-(s_{d-1}+1)\).  Induction on \(d\) therefore proves:

> **Diagonal permanence theorem.**  Every skipped diagonal coin is
> permanently skipped.  Every selected diagonal coin satisfying (20) is
> permanently selected.  If (20) holds at every selected rank through
> \(D\), then the lower-half greedy word at every horizon \(N\leq2D\) is
> exactly \((b_1,\ldots,b_{\lfloor N/2\rfloor})\).

The sole event not decided by this theorem is the explicit small-margin
case

\[
 \boxed{0\leq D_d\leq s_{d-1}.}                  \tag{21}
\]

No assertion that (21) is impossible is made here.

Assume now that the diagonal decisions needed at a given horizon have been
certified permanent.  Put

\[
 g_n=\sum_{\substack{d\mid n\\d<n/2}}b_d,
 \qquad
 X_n=R_n-C_n-K_n.
\]

For \(n\geq4\), the midpoint coin at an even rank \(n=2m\) has value
\(C_n+2\).  Direct transport of the lower-greedy remainder gives

\[
 X_n=
 \begin{cases}
 2X_{n-1}+r_{4,5}(n)-g_n-1,&n\text{ odd},\\
 2X_{n-1}+r_{4,5}(n)-g_n-2,&n=2m,\ b_m=1,\\
 2X_{n-1}+C_n+r_{4,5}(n)-g_n,&n=2m,\ b_m=0.
 \end{cases}                                      \tag{22}
\]

The last line appears dangerous because of \(C_n\), but the greedy skip
condition removes it.  If \(b_m=0\), the pre-midpoint remainder is an
integer strictly below \(C_n+2\).  Substitution into (22) yields

\[
 X_n\leq1-K_n.                                    \tag{23}
\]

Thus, once \(n\geq40\), a skipped midpoint cannot be the first rank with
positive excess.  If \(n\) is the first rank with \(X_n>0\), then exactly
one of the following necessary conditions holds:

\[
 \boxed{
 \begin{array}{ll}
 n\text{ odd}:&2X_{n-1}+r_{4,5}(n)-g_n-1>0,\\[1mm]
 n=2m\text{ even}:&b_m=1\text{ and }
 2X_{n-1}+r_{4,5}(n)-g_n-2>0.
 \end{array}}                                     \tag{24}
\]

Formula (2) makes the source phase in (24) explicit.  Hence any future
counterexample has a compact exact certificate: either a small-margin
diagonal event (21), or a first positive excess obeying one of the two laws
in (24).  The permanence theorem and recurrence do not exclude either event
at arbitrary depth.

## 6. Exact classification of the small-margin event

When the diagonal coin is selected, (17) immediately identifies its decision
margin with the new diagonal remainder:

\[
 \boxed{D_d=\rho_d\qquad(b_d=1).}                 \tag{25}
\]

Thus (21) is not merely a close comparison between two large integers.  It
is exactly the event that the selected diagonal prefix leaves a terminal
remainder no larger than the number of its earlier selected coins.

Write

\[
 u_d=2t_{2d-1}+t_{2d},
 \qquad
 A_d=2F_{d-1}(2d-1)+F_{d-1}(2d).
\]

For \(d\geq2\), equations (16)--(17) give the exact affine formula

\[
 D_d=4\rho_{d-1}+u_d-A_d-2^d-1.                 \tag{26}
\]

Consequently a selected small-margin event occurs if and only if there is an
integer \(z\) such that

\[
 \boxed{
 \begin{aligned}
 0&\leq z\leq s_{d-1},\\
 z&\equiv u_d-A_d-1\pmod4,\\
 \rho_{d-1}&=
 \frac{2^d+1+z-u_d+A_d}{4}.
 \end{aligned}}                                  \tag{27}
\]

This is the complete local classification.  It records the source phase,
the two divisor-incidence loads, the selected-count bound, and the unique
required predecessor remainder.

The first three pieces cannot exclude the event.  To see this, suppose three
earlier selected ranks divide neither \(2d-1\) nor \(2d\).  Then
\(s_{d-1}=3\) and \(A_d=0\).  For every possible source-pair value
\(u_d\in\{0,1,2,3\}\), the integer

\[
 z_d\in\{0,1,2,3\},
 \qquad z_d\equiv u_d-1\pmod4,                   \tag{28}
\]

and the predecessor remainder prescribed by (27) produce \(D_d=z_d\).
For all sufficiently large \(d\), three such nondivisor ranks exist.  Hence
Boolean divisor ancestry, the period-twenty source phase, and the selected
count admit an exact local small-margin model in every phase.

This is a local no-go, not a counterexample on the fixed \(1/465\) orbit:
the constructed predecessor remainder has not been proved reachable from
the earlier diagonal recurrence.  Formula (27) identifies the next necessary
state precisely.  An all-depth exclusion must control the actual global
orbit of \(\rho_{d-1}\) relative to the phase- and divisor-dependent lattice
point on the last line of (27).  No argument using only
\((u_d,A_d,s_{d-1})\) can suffice.

## 7. Infinitely many obstructions produce the representation

The local obstruction has a second interpretation.  For the nested diagonal
word, define the real residual

\[
 e_d=\frac1{465}-\sum_{a=1}^d\frac{b_a}{2^a-1}.
\]

Writing \(\{y\}\) for the fractional part of \(y\), the definitions of
\(H_{2d}\), \(q_{2d,a}\), and \(\rho_d\) give the exact identity

\[
 4^de_d-\rho_d
 =\left\{\frac{4^d}{465}\right\}
 -\sum_{a=1}^db_a
  \left\{\frac{4^d}{2^a-1}\right\}.              \tag{29}
\]

If \(s_d=\sum_{a\leq d}b_a\), then

\[
 \boxed{|4^de_d-\rho_d|\leq s_d+1.}              \tag{30}
\]

No sign assertion about \(e_d\) is needed.  Suppose selected small-margin
events occur at infinitely many ranks \(d_j\).  By (25), at each such rank
\(0\leq\rho_{d_j}\leq s_{d_j-1}\), while
\(s_{d_j}=s_{d_j-1}+1\leq d_j\).  Therefore

\[
 |e_{d_j}|
 \leq\frac{\rho_{d_j}+s_{d_j}+1}{4^{d_j}}
 \leq\frac{2d_j}{4^{d_j}}\longrightarrow0.       \tag{31}
\]

Let

\[
 S_d=\sum_{a=1}^d\frac{b_a}{2^a-1}.
\]

The sequence \(S_d\) is nondecreasing, and (31) says
\(S_{d_j}\to1/465\).  If some \(S_k\) exceeded \(1/465\), every later
subsequence term would be at least \(S_k\), contradicting this convergence.
Thus \(S_d\leq1/465\) for every \(d\), and monotonicity together with the
convergent subsequence gives

\[
 \boxed{\sum_{a\geq1}\frac{b_a}{2^a-1}=\frac1{465}.}              \tag{32}
\]

The support is infinite because every small-margin event is selected and the
ranks \(d_j\) are distinct.  We have proved:

> **Obstruction-is-witness theorem.**  If the fixed \(1/465\) diagonal orbit
> has infinitely many selected small-margin events, then its diagonal word is
> itself an infinite Boolean representation of \(1/465\).

This is not a closure of the construction.  It gives a sharp dichotomy for
this orbit: either the desired representation already follows from infinitely
many obstructions, or only finitely many selected small-margin events occur.
The remaining no-solution branch must therefore analyse the eventual regime
after the last such event.

## 8. Negative remainders are finite injuries

There is a complementary consequence for a remainder that crosses below
zero.  Suppose \(d\) is the first rank with \(\rho_d<0\), and let \(j<d\)
be the last selected rank.  Such a rank exists: before the first selection,
the recurrence has \(\rho=0\), no divisor load, and nonnegative source pulse.

Every rank \(n\) with \(j<n\leq d\) is skipped.  The selected count is
therefore fixed at \(s_j\), and (16) becomes

\[
 \rho_n=4\rho_{n-1}+u_n-A_n,                     \tag{33}
\]

where

\[
 0\leq u_n\leq3,
 \qquad
 0\leq A_n
 =2F_j(2n-1)+F_j(2n)
 \leq3s_j.                                       \tag{34}
\]

Put \(L=d-j\).  Dividing the iterated recurrence by \(4^L\) gives

\[
 \frac{\rho_d}{4^L}
 =\rho_j+
 \sum_{k=1}^L\frac{u_{j+k}-A_{j+k}}{4^k}.        \tag{35}
\]

Since the left side is negative,

\[
 \rho_j
 <\sum_{k=1}^L\frac{A_{j+k}-u_{j+k}}{4^k}
 \leq3s_j\sum_{k=1}^L4^{-k}
 =s_j(1-4^{-L})<s_j.                              \tag{36}
\]

The inequality is strict even when every skipped pulse is as negative as
possible.  Equality \(\rho_j=s_j\) cannot cross: the same calculation gives
\(\rho_{j+L}\geq s_j\) for every finite \(L\).  Since \(j\) was selected,
(25) gives \(D_j=\rho_j\geq0\), while
\(s_j=s_{j-1}+1\).  Thus (36) proves

\[
 0\leq D_j=\rho_j\leq s_{j-1}.                   \tag{37}
\]

In other words, the last selection before a first negative remainder is
necessarily a selected small-margin event.

Once a remainder is negative, it remains negative forever: from (33),
\(4\rho_n+u_{n+1}-A_{n+1}\leq-1\).  Every subsequent bit is zero, so this
branch has finite support.  Combining this with the obstruction-is-witness
theorem yields a finite-injury classification:

* infinitely many selected small-margin events give the desired infinite
  representation;
* a negative crossing is charged to the last small-margin event and then
  freezes the support;
* the only remaining branch has finitely many small-margin events and an
  eventually nonnegative diagonal remainder.

This does not eliminate the finite-support overshoot branch, nor does it
prove the eventually nonnegative branch represents \(1/465\).  It proves
that negative escape is not an independent failure mechanism.

## 9. The exact gateway to a fatal orbit

The remaining branch can be narrowed once more without estimating the full
orbit.  Consider the dyadic strip

\[
 0\leq\rho_d<2^d.                                  \tag{38}
\]

Suppose \(0\leq\rho_{d-1}<2^{d-1}\).  If rank \(d\) is skipped, then
\(\rho_d=T_d<w_d=2^d+1\), so integrality gives \(\rho_d\leq2^d\).
If rank \(d\) is selected, (17), \(u_d\leq3\), and \(A_d\geq0\) give

\[
 \rho_d
 \leq4(2^{d-1}-1)+3-(2^d+1)
 =2^d-2.                                           \tag{39}
\]

Consequently a first exit from (38) cannot jump over its upper boundary.
It must land exactly at \(\rho_d=2^d\).  This equality cannot occur at a
selected rank by (39), so it is equivalent to the exact skipped comparison

\[
 \boxed{D_d=-1,\qquad b_d=0,\qquad\rho_d=2^d.}     \tag{40}
\]

Equations (16)--(17) turn (40) into the arithmetic certificate

\[
 A_d-u_d\equiv0\pmod4,
 \qquad
 \rho_{d-1}=2^{d-2}+\frac{A_d-u_d}{4}.             \tag{41}
\]

This gate is sufficient to classify the fatal branch.  If (40) never
occurs and the orbit is eventually nonnegative, then (38) holds at every
sufficiently large rank.  The rounding estimate (30) gives

\[
 |e_d|
 \leq\frac{\rho_d+s_d+1}{4^d}
 <\frac{2^d+d+1}{4^d}\longrightarrow0,             \tag{42}
\]

and hence the diagonal word represents \(1/465\).  The same conclusion
holds if (40) occurs infinitely often, by applying (30) along those ranks.

It remains to describe what a genuinely fatal orbit would have to do.  If
\(e_d\to L>0\), then (30) implies

\[
 \rho_d\geq4^dL-d-1>2^d                            \tag{43}
\]

for every sufficiently large \(d\).  Thus the orbit must pass through
(40), but only finitely many times.  Let \(d\) be its last such rank.  At
rank \(d+1\), the bound \(A_{d+1}\leq3d\) ensures selection for \(d\geq3\),
and direct substitution gives

\[
 \rho_{d+1}
 =2^{d+1}+u_{d+1}-A_{d+1}-1.                      \tag{44}
\]

The right side cannot be below \(2^{d+1}\), since a later passage from the
lower strip to the eventual regime (43) would create another boundary hit.
It cannot equal \(2^{d+1}\), by the choice of \(d\).  Therefore

\[
 \boxed{u_{d+1}-A_{d+1}\geq2.}                    \tag{45}
\]

This is already special to the fixed source.  Its pair pulse has period ten:

\[
 u_n=
 \begin{cases}
 2,&n\equiv5\pmod {10},\\
 3,&n\equiv0,7,9\pmod {10},\\
 0,&\text{otherwise}.
 \end{cases}                                      \tag{46}
\]

Hence the rank after the last gate must lie in one of the four displayed
source phases.  In phase \(5\), (45) requires \(A_n=0\); in phases
\(0,7,9\), it requires \(A_n\leq1\).  The permanently selected rank \(9\)
removes further residue classes.  If \(n\equiv5\pmod9\), then
\(9\mid2n-1\) and its contribution already gives \(A_n\geq2\), which is
impossible in every candidate phase.  If \(n\equiv0\pmod9\), then
\(9\mid2n\) and \(A_n\geq1\); this excludes phase \(5\), while in the other
three phases equality \(A_n=1\) is forced and no other selected proper
divisor may contribute.

These phase and load restrictions alone cannot exclude the gate.  The actual
selected support through rank (23) is

\[
 \{9,13,14,17,19,21,22,23\}.
\]

For that support one has

\[
 u_{24}=A_{24}=0,
 \qquad
 u_{25}=2,\quad A_{25}=0.
\]

If one inserts the synthetic predecessor \(\rho_{23}=2^{22}\), while keeping
these actual fixed-source loads, the next two updates are exactly

\[
 \rho_{24}=2^{24},\quad D_{24}=-1,
 \qquad
 \rho_{25}=2^{25}+1.                              \tag{47}
\]

This is not a counterexample on the actual orbit: the synthetic predecessor
has not been proved globally reachable.  It is an exact countermodel to any
exclusion based only on the source phase, the known selected anchors, and the
two current divisor loads.  Global prefix arithmetic is indispensable.

There is also a whole-prefix form of the gate.  Let
\(F_d=\{a\leq d:b_a=1\}\), and put

\[
 P_d=\prod_{a\in F_d}(2^a-1),
 \qquad
 N_d=P_d-465\sum_{a\in F_d}\frac{P_d}{2^a-1}.      \tag{48}
\]

Thus \(e_d=N_d/(465P_d)\).  Write

\[
 r_{0,d}\equiv4^d\pmod {465},\quad0\leq r_{0,d}<465,
 \qquad
 r_{a,d}\equiv4^d\pmod {2^a-1},\quad
 0\leq r_{a,d}<2^a-1,
\]

and define the exact phase numerator

\[
 B_d=r_{0,d}P_d
 -465\sum_{a\in F_d}r_{a,d}\frac{P_d}{2^a-1}.      \tag{49}
\]

Expanding the floors in the definition of \(\rho_d\) gives

\[
 465P_d\rho_d=4^dN_d-B_d.                         \tag{50}
\]

Therefore the gate \(\rho_d=2^d\) is equivalent to

\[
 B_d=2^d(2^dN_d-465P_d).
\]

The factor in parentheses is odd because \(P_d\) is odd.  In particular,
every gate has the global certificate \(v_2(B_d)=d\).  This condition uses
the complete selected prefix, rather than only its two current divisor
loads.  It is the exact numerator obstruction that an all-depth exclusion
must now attack.

> **Fatal-gateway theorem.**  A fixed \(1/465\) diagonal orbit with positive
> limiting real residual must contain a final skipped margin \(D_d=-1\).
> The following rank satisfies (45), and hence the explicit phase and
> rank-\(9\) restrictions above.  Conversely, any eventually nonnegative
> orbit avoiding this exact gate, or meeting it infinitely often, gives the
> desired representation.

This theorem does not exclude the final gate.  It replaces the broad
eventually-all-ones possibility by one exact globally reachable equality
and a fixed-source escape pulse.  A closure must now rule out (40)--(45) on
the actual orbit; generic positive-residual counterexamples do not decide
that fixed arithmetic question.

## 10. A two-adic recurrence for the gateway numerator

The numerator \(B_d\) has an exact recurrence that removes the enormous
prefix product from the valuation test.  Write

\[
 v_d=u_d-A_d,
 \qquad M_d=2^d-1.
\]

The updates for \(P_d,N_d,\rho_d\), substituted into (50), give

\[
 \boxed{
 B_d=4M_d^{b_d}B_{d-1}
 -465P_{d-1}\bigl(M_d^{b_d}v_d+b_d\bigr).}        \tag{51}
\]

Since every \(P_d\) is odd, it is a unit in the two-adic integers.  Put

\[
 Y_d=\frac{B_d}{P_d}\in\mathbb Z_2.
\]

Dividing (51) by \(P_d=P_{d-1}M_d^{b_d}\) gives the exact identity

\[
 Y_d=4Y_{d-1}-465
 \left(v_d+\frac{b_d}{M_d}\right).                \tag{52}
\]

Because \(M_d^{-1}\equiv-1\pmod {2^d}\), this reduces to

\[
 \boxed{Y_d\equiv4Y_{d-1}+465(b_d-v_d)\pmod {2^d}.}              \tag{53}
\]

Define the decision-load pulse and its base-four accumulator by

\[
 c_j=b_j-v_j=b_j-u_j+A_j,
 \qquad
 S_d=\sum_{j=1}^d4^{d-j}c_j.                     \tag{54}
\]

Iteration of (53) gives \(Y_d\equiv465S_d\pmod {2^d}\).  At a skipped
rank \(d\), the congruence is one bit sharper:

\[
 Y_d\equiv465S_d\pmod {2^{d+1}}.                  \tag{55}
\]

Indeed, replacing \(M_j^{-1}\) by \(-1\) at a selected rank \(j<d\)
introduces a term of two-adic valuation \(j\); after transport to rank \(d\)
its valuation is \(j+2(d-j)=2d-j\geq d+1\).  There is no rank-\(d\)
replacement error because \(b_d=0\).

It follows from (55), the oddness of \(465P_d\), and (50) that the exact
gateway valuation is equivalent to

\[
 \boxed{
 b_d=0,\quad v_2(B_d)=d
 \quad\Longleftrightarrow\quad
 S_d\equiv2^d\pmod {2^{d+1}}.}                   \tag{56}
\]

Only the final half of the pulse word enters this test.  Terms with
\(j<\lceil d/2\rceil\) vanish modulo \(2^{d+1}\), so (56) may replace
\(S_d\) by

\[
 S_d^{\mathrm{half}}
 =\sum_{j=\lceil d/2\rceil}^d4^{d-j}c_j.         \tag{57}
\]

There is a small-integer backward form of the same certificate.  Put
\(m=\lfloor d/2\rfloor\), \(h_0=0\), and, successively for
\(1\leq k\leq m\), require

\[
 h_{k-1}+c_{d-k+1}\equiv0\pmod4,
 \qquad
 h_k=\frac{h_{k-1}+c_{d-k+1}}4.                  \tag{58}
\]

If all these divisions exist, then (56) holds precisely when

\[
 \begin{cases}
 h_m+c_{d-m}\text{ is odd},&d=2m,\\
 h_m+c_{d-m}\equiv2\pmod4,&d=2m+1.
 \end{cases}                                     \tag{59}
\]

The carries stay small.  Since
\(-3\leq c_j\leq3j-2\), induction in (58) gives

\[
 -1\leq h_k\leq d-1.                             \tag{60}
\]

Thus the exponential-looking valuation condition is exactly a bounded
backward carry through half of the decision-load word.

This recurrence also explains the status of the rank-\(24\) phase/load
countermodel.  For its forced skip, \(c_{24}=0\), so \(h_1=0\).  The actual
preceding pulse is \(c_{23}=3\), and the second division in (58) already
fails.  The inserted value \(\rho_{23}=2^{22}\) was therefore incompatible
with the complete earlier prefix.  Conversely, at an actual gate, (50)
already forces \(v_2(B_d)=d\), so every division in (58) must succeed.

> **Two-adic gateway reduction.**  The full-prefix valuation target is
> equivalent to the half-window carry certificate (58)--(59).  It detects
> the failure of a locally admissible but globally unreachable predecessor,
> but it is not an independent contradiction for an actual gate.

The remaining proof obstruction is now precise: one must show that the
actual fixed-\(465\) pulse suffix fails one of the divisions in (58), or has
the wrong terminal residue in (59), at every prospective skipped gate.  A
fixed modulus, the source phase alone, or the current divisor loads do not
control this half-window carry.

## 11. The final skip is necessarily saturated

The pulse formula itself telescopes.  Rewriting (17) with
\(c_j=b_j-v_j\) gives

\[
 \boxed{c_j=4\rho_{j-1}-\rho_j-b_j2^j.}           \tag{61}
\]

Consequently, for every \(1\leq m\leq d\),

\[
 \sum_{j=m}^d4^{d-j}c_j
 =4^{d-m+1}\rho_{m-1}-\rho_d
 -\sum_{j=m}^db_j2^{2d-j}.                       \tag{62}
\]

Thus the terminal residue in the backward carry is not an independent
majorization condition.  At a gateway, (62) forces it from the remainder
equation.

There is nevertheless a stronger consequence when the orbit is fatal.
Suppose

\[
 g=\lim_{d\to\infty}e_d>0.
\]

Then (30) gives \(\rho_d>2^d\) for every sufficiently large \(d\), and the
diagonal decisions are eventually all selected.  Let \(L\) be the final
skipped rank.  A skip gives \(\rho_L\leq2^L\).  If the inequality were
strict, every later selected step would remain strictly below its dyadic
boundary by (39).  The orbit could never reach \(\rho_d>2^d\).  Hence

\[
 \boxed{\rho_L=2^L,\qquad D_L=-1.}                \tag{63}
\]

In particular, the final skip and the final gateway are the same rank.  A
fatal orbit cannot have a strict final skipped row.

This saturation supplies a fixed-source budget.  Define the future-divisor
resolvent

\[
 \mathscr R_L
 =\sum_{\substack{a\leq L\\b_a=1}}
   \left\{\frac{4^L}{2^a-1}\right\},
 \qquad
 \alpha_L=\left\{\frac{4^L}{465}\right\}.
\]

Expanding the floors gives

\[
 \rho_L=4^Le_L-\alpha_L+\mathscr R_L.             \tag{64}
\]

Since every rank after \(L\) is selected,
\(e_L=T_L+g\), where \(T_L=\sum_{n>L}(2^n-1)^{-1}\).  The exact geometric
expansion is

\[
 4^LT_L
 =2^L+\frac13+\varepsilon_L,
 \qquad
 \varepsilon_L
 =\sum_{k\geq3}\frac{2^{(2-k)L}}{2^k-1}>0.        \tag{65}
\]

Substitution of (63) into (64)--(65) yields

\[
 \boxed{
 \mathscr R_L
 =\alpha_L-\frac13-\varepsilon_L-4^Lg.}           \tag{66}
\]

The residues \(4^L\bmod465\) have period ten.  Nonnegativity of the
resolvent forces

\[
 L\bmod10\in\{4,6,8,9\}.
\]

For these four phases, (66) gives the strict bounds

\[
 \begin{array}{c|c}
 L\bmod10&\mathscr R_L<\alpha_L-\frac13\\ \hline
 4&101/465\\
 6&221/465\\
 8&281/465\\
 9&194/465.
 \end{array}                                      \tag{67}
\]

The resolvent is also the discounted future-arrival count

\[
 \mathscr R_L=\sum_{r\geq1}\nu_L(r)2^{-r},
 \qquad
 \nu_L(r)=
 \#\{a\leq L:b_a=1,\ a\mid2L+r\}.                \tag{68}
\]

Moreover,

\[
 A_{L+1}=2\nu_L(1)+\nu_L(2).                     \tag{69}
\]

The escape condition (45) therefore forces

\[
 \begin{array}{c|c}
 L\bmod10&2\nu_L(1)+\nu_L(2)\\ \hline
 4&0\\
 6,8,9&\leq1.
 \end{array}                                      \tag{70}
\]

> **Final-skip saturation theorem.**  Every fatal fixed-\(1/465\) orbit has
> one final skipped rank \(L\), and that rank is an exact gateway satisfying
> (63), the phase budgets (67), and the sparse future-arrival condition
> (70).

This removes the strict-final-row branch.  It does not yet exclude the four
saturated phases.  Equation (62) shows why a weighted source-credit
majorization over the half-window cannot by itself do so: its terminal carry
is the remainder identity in another form.  A closure now requires a
fixed-\(465\) lower bound for \(\mathscr R_L\), using the actual selected
support and the sparse first arrivals in (70), that contradicts the
corresponding row of (67).

## 12. The scalar resolvent data do not exclude a fatal gate

The phase budget is not itself a pointwise lower bound on the resolvent.
An exact local countermodel can be built from a genuine fixed-source greedy
support.  At rank

\[
 L=3056
\]

the actual diagonal prefix satisfies

\[
 b_L=0,\qquad s_L=1515,\qquad
 (u_L,A_L)=(0,16),\qquad
 (u_{L+1},A_{L+1})=(3,0).                       \tag{71}
\]

Thus it has the phase-\(6\) gateway congruence, the sparse first arrivals
\(\nu_L(1)=\nu_L(2)=0\), and the strict escape pulse.  Its first sixteen
arrival counts are

\[
 \bigl(\nu_L(r)\bigr)_{r=1}^{16}
 =(0,0,0,3,1,6,2,18,0,0,4,0,5,0,0,2).          \tag{72}
\]

Since \(\nu_L(r)\leq s_L\) at every offset, (68) and (72) give the exact
upper estimate

\[
 \mathscr R_L
 \leq\sum_{r=1}^{16}\nu_L(r)2^{-r}+s_L2^{-16}
 =\frac{27797}{65536}
 <\frac{221}{465}.                               \tag{73}
\]

The genuine row is a strict skip, not a gateway.  Nevertheless, retain its
entire selected support and its fixed-source divisor loads, and replace only
the predecessor state by

\[
 \widetilde\rho_{L-1}=2^{L-2}+4.
\]

Then (16) gives

\[
 \widetilde\rho_L
 =4\widetilde\rho_{L-1}+u_L-A_L=2^L,
 \qquad D_L=-1.                                  \tag{74}
\]

At the following ranks, select every bit and put
\(x_d=\widetilde\rho_d-2^d\).  The exact first nine excesses are

\[
 (x_{L+1},\ldots,x_{L+9})
 =(2,4,10,20,79,307,1217,4865,19456).            \tag{75}
\]

They are all positive, so these choices obey the greedy inequalities.  At
rank \(L+9\), one has \(x_{L+9}>L+10\).  Thereafter

\[
 x_{d+1}=4x_d+u_{d+1}-A_{d+1}-1,
 \qquad A_{d+1}\leq3d,
\]

and induction gives \(x_d\geq d+1\), hence every later bit remains selected.
The resulting local state is exact and source-, load-, decision-, phase-,
and escape-compatible from rank \(L-1\) onward; its attached genuine support
also satisfies the resolvent budget (73).

> **Scalar-resolvent no-go.**  Saturation, the phase budget, the first-arrival
> restrictions, and all subsequent greedy inequalities admit one exact local
> state whose support and resolvent come from a genuine fixed-\(465\) greedy
> prefix.

In least-representative language, this is an anti-compression statement.
Project the full prefix state to
\[
 (L\bmod10,\ s_L,\ A_L,\ A_{L+1},\
   \nu_L(1),\ldots,\nu_L(16),\ \mathscr R_L).
\]
That projection leaves a nontrivial predecessor fibre: the genuine strict
row and the substituted saturated row have the same projected
source/support/load/arrival data.  The exceptional cylinder therefore
survives every inference made only on that projection; its remaining
uncertainty is exactly the earlier predecessor reachability.

This failure is not confined to a short accidental row.  Fix a backward
window length \(K\) and \(\eta>0\).  Write
\(\bar u_i=u_{(6-i)\bmod10}\) for \(0\leq i<K\).  For every pair
\((i,\ell)\), \(1\leq\ell\leq\bar u_i\), choose distinct odd primes
\[
 p_{i,\ell}>2K+2
\]
and impose
\[
 L\equiv6\pmod {10},
 \qquad
 L\equiv i\pmod {p_{i,\ell}}.                   \tag{76}
\]
The Chinese remainder theorem gives arbitrarily large such \(L\); take one
larger than all the primes and \(2K\).  Select precisely the prime ranks
\(p_{i,\ell}\), and skip every rank \(L-i\) in the terminal window.

Each \(p_{i,\ell}\) divides \(L-i\), so it contributes one unit to
\(F(2(L-i))\).  Because the primes exceed \(2K+2\), no chosen prime divides
either argument belonging to a different window rank, or either argument at
rank \(L+1\).  Therefore
\[
 A_{L-i}=u_{L-i}\quad(0\leq i<K),
 \qquad A_{L+1}=0.                               \tag{77}
\]
Starting from \(\rho_L=2^L\) and running (16) backward gives
\[
 \rho_{L-i}=2^{L-2i}\quad(0\leq i\leq K).        \tag{78}
\]
Every one of these \(K\) skipped comparisons is valid, the terminal one has
\(D_L=-1\), and the phase-\(6\) pulse at \(L+1\) gives
\(\rho_{L+1}=2^{L+1}+2\).  Thus an arbitrarily long terminal backward carry
can coexist with an exact gate and escape.

For an anchor assigned at offset \(i\), congruence (76) gives
\[
 \left\{\frac{4^L}{2^{p_{i,\ell}}-1}\right\}
 =\frac{2^{2i}}{2^{p_{i,\ell}}-1}.               \tag{79}
\]
Choosing the primes sufficiently large makes the sum of (79) smaller than
\(\eta\).  Hence neither a bounded carry window nor any fixed finite-arrival
lower bound can eliminate the exceptional cylinder.  This CRT construction
uses the exact fixed-\(465\) source and valid decisions throughout its
window, but does not certify the selected prime decisions or the entrance
state back to \(\rho_0=0\).

The substituted predecessor in (74) is not claimed reachable from
\(\rho_0=0\), and therefore this is not a fixed-target counterexample.  That
is precisely the missing datum.  Any successful
anti-compression theorem must couple the saturated row to the complete
earlier carry or numerator identity; no pointwise bound derived only from
the moving resolvent, its finite arrivals, the source phase, and the escape
loads can close the proof.

## 13. Reproducible audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_fixed_horizon_reduction.py --horizon 2000 --focused-diagonal-depth 120
```

The script certifies the exact threshold, strict superincrease at the base,
all 25 base representations and their complete trajectories, and the finite
lower-greedy comparator through the requested horizon.  It also constructs
every terminal endpoint at the final requested rank and reports their common
prefix.  At rank 2,000 all 101 endpoint representations exist and share their
first 1,992 bits.  The lower greedy remainder never exceeds the upper binary
capacity in this run.  These are finite observations only; (14) remains
unproved for arbitrary \(N\).  The diagonal checker is deliberately bounded:
it verifies (16)--(24) against direct greedy arithmetic through rank 240,
checks (25)--(28), and checks the exact rational rounding bound (30).  It does
not turn the absence of (21) in that range into an all-depth claim.  A sharp
synthetic equality check also verifies that \(\rho_j=s_j\) cannot cross under
the worst admissible skipped-run pulse.  Finally, the focused checker verifies
the strip gateway (38)--(41), the exact last-gate update (44), the period-ten
and rank-\(9\) exclusions following (46), the exact phase/load countermodel
(47), and the whole-prefix identity (48)--(50).  Its bounded absence of a gate
is not used as an all-depth assertion.  It also checks the exact recurrence
(51), the normalized congruences (53)--(56), and the backward carry
certificate (58)--(60), including rejection of the synthetic rank-\(24\)
predecessor.  Finally, it verifies the pulse telescope (61)--(62), the
period-ten phase table in (67), and the exact arrival identity (69).  The
checker also certifies the exact rank-\(3056\) scalar-resolvent countermodel
(71)--(75), including its permanently selected forward continuation.  The
full-prefix reachability obstruction left by (74) remains open.
