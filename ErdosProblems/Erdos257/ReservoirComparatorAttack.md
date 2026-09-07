# Lexicographic structure of the delayed-density reservoir

Status: exact deductions from the finite quotient identities, together with
exact finite computations, 2026-08-20.  The sharp threshold comparator and
the square-root safety comparator below give two sufficient all-depth
statements, neither of which is proved here.  Erdős Problem 257 therefore
remains open.

## 1. The reservoir as a second superincreasing coordinate

Fix a horizon `N`.  For a Boolean word `x=(x_1,...,x_N)`, put

\[
 a_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor,
 \qquad
 c_{N,d}=a_{N,d}-1+\mathbf 1_{2d\leq N}.
 \tag{1}
\]

Let `H_N=floor(2^N/21)`, and let `T(N)` be the number of ones in the
first `N` binary digits of `1/21`.  Define the finite-word versions of the
defect and source/ancestor discrepancy by

\[
 Q_N(x)=H_N-\sum_{d\leq N}a_{N,d}x_d,
 \qquad
 P_N(x)=T(N)+\sum_{d\leq N/2}x_d-\sum_{d\leq N}x_d.
\]

The reservoir from `DelayedDoublingDensityAttack.md` therefore has the
exact expansion

\[
 R_N(x):=P_N(x)+3-Q_N(x)
 =T(N)+3-H_N+\sum_{d\leq N}c_{N,d}x_d.       \tag{2}
\]

The coefficients in (2) have a stronger property than mere positivity:

\[
 c_{N,N}=0,
 \qquad
 c_{N,d}>\sum_{e=d+1}^{N}c_{N,e}
 \quad(1\leq d<N).                            \tag{3}
\]

Here is a short proof.  Let `M=floor(N/2)` and
`W=2^(N-M)`.  If `d>M`, then

\[
 c_{N,d}=2^{N-d}-1
\]

and direct summation gives

\[
 c_{N,d}-\sum_{e=d+1}^{N}c_{N,e}=N-d>0.       \tag{4}
\]

If `d<=M`, then `c_{N,d}=a_{N,d}`.  The checked generic quotient-gap
inequality `localMersenneWeightsFrom_gapDominates` gives

\[
 a_{N,d}\geq W+\sum_{e=d+1}^{M}a_{N,e}.
\]

The remaining upper-half coefficients have the exact sum

\[
 \sum_{e=M+1}^{N}c_{N,e}=W-1-(N-M)<W.
\]

Combining these two formulas proves (3).  Thus the half-scale correction in
the definition of `P_N` has not destroyed the quotient weights' strong-gap
order.  It has completed their upper half into a second superincreasing
coordinate.

## 2. Exact exchange consequence

Suppose two Boolean words `x,y` first differ at a rank `d<N`, with
`x_d=1` and `y_d=0`.  Later digits may be changed arbitrarily.  Equations
(2) and (3) give

\[
 R_N(x)>R_N(y).                                \tag{5}
\]

In particular, adding rank `d` raises `R_N` by `c_{N,d}`, and even deleting
every later rank lowers it by less than `c_{N,d}`.  This is the exact
lexicographic exchange principle suggested by the positive inclusion
variation.  A change only at rank `N` leaves `R_N` unchanged.

Let

\[
 \mathcal F_N=\left\{x\in\{0,1\}^N:
   \sum_{d\leq N}\frac{x_d}{2^d-1}\leq\frac1{21}\right\}.
\]

The actual real greedy prefix is lexicographically maximal in
`mathcal F_N`.  Indeed, at the first differing rank, no feasible competitor
can take a coin which the greedy word rejected after the common prefix.
Consequently (5) proves the finite extremal identity

\[
 R_N(b)=\max_{x\in\mathcal F_N}R_N(x),          \tag{6}
\]

up to the irrelevant terminal digit `x_N`.  This is stronger than saying
that `R_N` is monotone under inclusion: arbitrary early-for-late exchanges
are ordered in the favourable direction.

## 3. What a comparator would have to supply

By (2), proving `R_N(b)>=0` by comparison is equivalent to constructing one
real-feasible word `x` satisfying

\[
 \sum_{d\leq N}c_{N,d}x_d\geq H_N-T(N)-3.      \tag{7}
\]

This is the exact remaining cross-coordinate inequality.  The capacity in
the definition of `mathcal F_N` uses the real Mersenne weights, whereas the
objective in (7) uses the corrected quotient weights `c_{N,d}`.  Each
coordinate separately has a strong lexicographic order; the missing result
controls the predecessor of the same threshold when one passes between the
two coordinates.

Such comparators cannot be obtained for free.  If `x` is feasible and
`R_N(x)>=0`, and

\[
 \delta_N=\frac1{21}-\sum_{d\leq N}\frac{x_d}{2^d-1},
\]

then, by taking integer and fractional parts after multiplication by
`2^N`,

\[
 0\leq 2^N\delta_N<Q_N(x)+1
 \leq P_N(x)+4\leq T(N)+4.                    \tag{8}
\]

Thus a comparator satisfying (7) at every horizon would itself give finite
Boolean sums converging exponentially to `1/21`; compactness would then
give an infinite representation.  The comparator problem is therefore a
genuine construction problem, not a consequence of lexicographic
maximality alone.

## 4. A canonical threshold comparator

The strong-gap order gives a more structured comparator than deleting one
digit from the quotient-greedy word.  Put

\[
 D_N=H_N-T(N)-3.
\]

Let `z^(N)` be the lexicographically least Boolean word whose corrected
quotient value crosses this threshold:

\[
 \sum_{d\leq N}c_{N,d}z^{(N)}_d\geq D_N.       \tag{9}
\]

It is obtained without search.  At rank `d`, put `z_d=0` if the sum of all
remaining coefficients can still reach the current deficit, and put
`z_d=1` otherwise.  By (3), this is the lexicographically least word
satisfying (9).  Its reservoir is nonnegative by construction.

Exact computation gives the following stronger fact:

\[
 \sum_{d\leq N}\frac{z^{(N)}_d}{2^d-1}
 \leq\frac1{21}                                  \tag{10}
\]

for every `N<=5000`.  The check uses directed integer rounding at precision
`2N+128`; it proves (10) for each audited row rather than comparing floating
point approximations.  The stronger comparison with `H_N/2^N` in (12) was
also certified at every one of those horizons.  Separate exact checks at
`N=10000` and `N=50000` found the same stronger inequality.  These are
finite computations; no counterexample was found.

If (10) holds for every `N`, then (6) and (9) immediately give
`R_N(b)>=0` for the actual greedy word at every horizon.  Consequently
`P_N(b)>=-3`, which gives the delayed density estimate with constant `3`
and proves that `1/21` has an infinite Boolean Mersenne representation.
Thus the following statement is now a sufficient all-depth theorem:

> The lexicographically least corrected-quotient threshold word `z^(N)` is
> real-Mersenne-feasible at every horizon.

This use of the quotient completion does not require it to equal the actual
greedy block.  It uses that completion as a feasible word below the actual
greedy word in lexicographic order.  This removes the alignment requirement
which prevented the independent quotient-suffix density computation from
controlling the real support directly.

The upper half of `z^(N)` also exposes the repeated suffix-density
phenomenon.  If `M=floor(N/2)`, then its upper-half coefficients are

\[
 2^{N-M-1}-1,\ 2^{N-M-2}-1,\ldots,1,0.
\]

Writing `U_N` for the number of selected upper-half digits and `E_N` for
the overshoot in (9), the corresponding quotient defect is exactly

\[
 Q_N(z^{(N)})=T(N)+3-U_N-E_N.                  \tag{11}
\]

There is an exact popcount description of this completion.  After the
lower word has been fixed, let `r` be the remaining corrected-quotient
threshold.  Encode an upper word by the binary numeral

\[
 V=\sum_{d>M}z_d2^{N-d}.
\]

Its corrected-quotient value is

\[
 \sum_{d>M}z_d(2^{N-d}-1)=V-s_2(V),
\]

where `s_2` denotes binary popcount.  Hence `V` is the least integer for
which

\[
 V-s_2(V)\geq r.                               \tag{11a}
\]

The function `v -> v-s_2(v)` is nondecreasing.  Thus `H=V-1` is the last
subthreshold suffix numeral.  If

\[
 \delta=r-(H-s_2(H))\geq1,
\]

then

\[
 U_N+E_N=V-r=s_2(H)+1-\delta\leq s_2(H).       \tag{11b}
\]

This identifies the repeated quotient-suffix popcount bound as direct
control of two terms in the comparator budget, rather than as an unproved
model of the actual greedy block.  The remaining term is the fractional
phase below.

Thus the observed one-third suffix law is not merely a possible proxy for
the actual doubling block.  It is direct control of the canonical
comparator's dyadic defect.  What remains for (10) is to compare this
integer defect with the sum of the fractional quotient remainders

\[
 \left\{\frac{2^N}{2^d-1}\right\}
 =\frac{2^{N\bmod d}}{2^d-1}\qquad(d\geq2).
\]

For `d=1` the fractional remainder is zero.  Exact computation supports the
stronger inequality

\[
 F_N:=\sum_{d\leq N}z^{(N)}_d
   \left\{\frac{2^N}{2^d-1}\right\}
 \leq Q_N(z^{(N)}).                            \tag{12}
\]

This says that the real sum of `z^(N)` lies below the `N`-digit binary
truncation `H_N/2^N`, not only below `1/21`.  Using (11), it has the compact
joint form

\[
 \boxed{\quad U_N+E_N+F_N\leq T(N)+3.\quad}    \tag{13}
\]

Without this strengthening, the exact feasibility condition is only

\[
 F_N\leq Q_N(z^{(N)})+
   \left\{\frac{2^N}{21}\right\}.              \tag{14}
\]

Equation (13) is the sharper remaining suffix/LCM inequality.  Its left
side contains the upper-suffix occupancy `U_N`, the threshold overshoot
`E_N`, and the divisor-clock phases `N mod d`; its right side is the
period-six source budget.  This is a direct place for the previously
separate suffix-density and divisor-pulse phenomena to interact.

For a fixed Boolean word, the fractional phase has the exact pulse law

\[
 F_{N+1}=2F_N-
   \sum_{\substack{d\mid N+1\\d\geq2}}z_d.   \tag{15}
\]

The same divisor count occurs in the quotient-defect recurrence, and hence

\[
 (Q-F)_{N+1}=2(Q-F)_N+t_{N+1}                 \tag{16}
\]

as long as the word is held fixed during the depth change.  Divisor/LCM
pulses therefore cancel exactly between the integer quotient and its
fractional phase.  The only nontrivial increments in (13) arise when the
least threshold word is recut.  Controlling those lexicographic recuts is a
more precise proof target than bounding arbitrary borrow lengths.

The audited threshold words are lexicographically nondecreasing with the
horizon: after padding `z^(N)` by a terminal zero, every first change in
`z^(N+1)` is from `0` to `1`.  This was checked through `N=3000`; among the
`2980` strict recuts the largest distance from the new endpoint to the first
changed rank was `21`, at horizon `2236`.  There is an exact one-inequality
criterion for this assertion.  Let `x` be the zero-padded word, let `d` be its last
selected rank, and let

\[
 \gamma_{N+1,d}=c_{N+1,d}-\sum_{e>d}c_{N+1,e}>0
\]

be the strong gap.  Since the largest word lexicographically below `x` is
obtained by clearing rank `d` and filling every later rank, monotonicity at
this transition is equivalent to

\[
 \sum_e c_{N+1,e}x_e-D_{N+1}<\gamma_{N+1,d}.   \tag{17}
\]

If `x` is below the new threshold, (17) is automatic.  When `x` already
crosses it, (17) says that its new-coordinate overshoot does not span the
single predecessor gap.  This isolates the exact recut inequality; it is
not proved here.  Once (17) holds, (16) grows `Q-F` deterministically between
successive lexicographic increases.  At a recut, the remaining requirement
is that the real scaled mass added by the early-for-late exchange is at most
the pre-recut value `2(Q-F)+t_{N+1}`.  That post-recut inequality is exactly
(12) at the new horizon.

When the last selected rank lies in the upper half, (4) gives the especially
simple identity `gamma_(N+1,d)=N+1-d`.  Thus (17) says that the new-coordinate
overshoot is smaller than the terminal zero-run length.  This is the same
digital-height quantity which appeared in the earlier cylinder arguments,
but here it controls a concrete lexicographic recut rather than a phase
return.

The left side of (17) also has an exact source/pulse expansion.  Since

\[
 D_{N+1}=2D_N+T(N)+3,
\]

write `Lambda_N` for the number of selected ranks `e<=floor(N/2)`, `e>=2`,
which divide `N+1`; write `U_N^+` for the selected ranks with `2e>N+1`; and,
when `N` is odd, put `m_N=z^((N))_((N+1)/2)` (otherwise put `m_N=0`).  Directly
from the quotient doubling law,

\[
 \sum_e c_{N+1,e}z^{(N)}_e-D_{N+1}
 =2E_N+\Lambda_N+U_N^++3m_N-T(N)-3.            \tag{18}
\]

Thus the monotone-recut condition is precisely

\[
 2E_N+\Lambda_N+U_N^++3m_N-T(N)-3
 <\gamma_{N+1,d}.                              \tag{19}
\]

This single inequality contains the threshold overshoot, an `N+1` divisor
pulse, the upper suffix occupancy, the exceptional self-double seam, the
period-six source count, and the terminal digital height.  It is an exact
joint version of the phenomena which appeared separately in the earlier
attacks.  Computation through `N=2999` finds (19) throughout; its smallest
integer margin is `1`, at the transition from `N=15` with last selected rank
`13`.  No all-depth proof is presently known.

The additive buffer `3` in the definition of `D_N` is sharp for this
construction at the initial seam.  Replacing it by `0`, `1`, or `2` makes
the least threshold word equal to `{5,6}` at horizons `7`, `8`, or `9`,
respectively.  Its real value is `94/1953`, which exceeds the common binary
truncation `3/64` by `157/124992`.  With buffer `3`, the horizon-nine word
is `{5,7,8}` and lies strictly below `3/64`.  Thus the constant performs the
first necessary lexicographic recut away from rank `6`; it is not an unused
allowance.

## 5. A square-root safety comparator

There is a less sharp comparator which removes the fractional-phase problem
at the cost of an `O(sqrt(N))` error.  This error is still small enough to
prove infinitely many skips.

Let

\[
 \rho_{N,d}=\left\{\frac{2^N}{2^d-1}\right\},
 \qquad m=\lfloor\sqrt N\rfloor.
\]

For `N>=4` there is a universal bound, independent of the Boolean word,

\[
 \sum_{d=2}^{N}\rho_{N,d}<2m.                 \tag{20}
\]

To prove this, first take `2<=d<=m`.  Each summand is at most `2/3`, so
this range contributes at most `2(m-1)/3`.  For `d>m`, group the ranks by
`k=floor(N/d)`, where `1<=k<=m`, and put

\[
 s=(k+1)d-N\geq1.
\]

Then `N mod d=d-s` and

\[
 \rho_{N,d}<2^{1-s}.
\]

Within a fixed `k`-block, successive values of `s` differ by `k+1>=2`.
The block therefore contributes at most

\[
 \sum_{j\geq0}2^{-2j}=\frac43.
\]

Summing over at most `m` blocks and adjoining the small ranks proves (20).
This is an ordinary deduction, not finite evidence.

Now put `S_N=2m+5`.  Run quotient-greedy at depth `N` with integer target

\[
 C_N=H_N-S_N,
\]

and call the resulting word `x^(N)`.  Let `r_N` be its terminal integer
remainder.  Then `Q_N(x^(N))=S_N+r_N`, while (20) gives

\[
 2^N\left(\frac{H_N}{2^N}-
   \sum_d\frac{x^{(N)}_d}{2^d-1}\right)
 =S_N+r_N-\sum_dx^{(N)}_d\rho_{N,d}>0.         \tag{21}
\]

Thus `x^(N)` is automatically real-feasible; no selected-phase or LCM
estimate remains.  Let `U_N(x)` denote its number of selected ranks above
`floor(N/2)`, and let `A_N=B(N)-B(floor(N/2))` be the corresponding actual
greedy block count.  Lexicographic reservoir extremality gives the exact
comparison

\[
 A_N+Q_N(b)\leq U_N(x)+S_N+r_N.               \tag{22}
\]

and hence `A_N<=U_N(x)+S_N+r_N`.

Consequently it is enough to prove the tolerant quotient-suffix estimate

\[
 r_N+U_N(x)\leq T(N)+O(\sqrt N).              \tag{23}
\]

Equations (22) and (23) give

\[
 B(N)-B(\lfloor N/2\rfloor)
 \leq T(N)+O(\sqrt N).
\]

Iteration yields `B(N)<=2N/3+O(sqrt(N))`, so the actual greedy word has
infinitely many zeros and `1/21` has an infinite Boolean Mersenne
representation.

Exact integer computation through `N=3000` finds `r_N=0` for every
`C_N>=0` and

\[
 \max_{\substack{N\leq3000\\C_N\geq0}}(U_N(x)-T(N))=2,
\]

first attained at `N=19` (over the restricted range `20<=N<=3000`, the
maximum is `1`, first at `N=71`).  This finite result does not prove (23) at
all depths.  Exact representability is no longer a separate hypothesis: any
terminal remainder is charged directly in (22).  Its significance is
structural:
the previously observed quotient-suffix density can be used as a comparator
with square-root slack.  It need not be identified with the actual block,
and the universal estimate (20) absorbs every fractional divisor phase.

## 6. Failure of the direct quotient-row repair

The most immediate proposed comparator is the integer quotient-greedy word
at depth `N`, followed by deletion of its latest selected rank until its
real Mersenne sum is at most `1/21`.  This fails already at `N=9`.

At that horizon the quotient-greedy word selects ranks `5` and `6` and has
`R_9=3`, but its real sum exceeds `1/21`.  Deleting rank `6` makes it
real-feasible and leaves only rank `5`; the resulting reservoir is

\[
 R_9(\{5\})=-4.
\]

The actual greedy prefix instead omits rank `6` and selects ranks `7,8,9`,
giving `R_9=0`.  This example illustrates both sides of (3): the early rank
`6` is worth more reservoir than all later ranks together, but real
feasibility forces its deletion, and recovering the threshold requires a
new later completion rather than a one-bit repair of the quotient row.

The script `scripts/reservoir_comparator_audit.py` verifies (3) by exact
integer arithmetic, reproduces this rational counterexample, and certifies
(10) through the requested finite horizon.  The finite computation does not
prove (10) at all depths.
