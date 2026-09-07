# Four-ninths diagonal: selected landings are the only remaining margin source

**Date:** 2026-08-23  
**Route:** rational counterexample candidate `4/9`  
**Status:** exact finite audit passed; selected-landing and selected-rank Lean
reductions kernel checked

## Route selection

This pass compared three structurally different attacks without giving the
latest checkpoint incumbency:

| Route | Strongest existing asset | Decisive contrary evidence | Probe used here | Stop condition |
|---|---|---|---|---|
| `1/2` reset escape | reset deviations satisfy the exact return-time band through row 2500 and already feed a Lean square-root consumer | reset alternation is qualitative and does not supply endpoint anti-concentration | search for a new deterministic reset-scale invariant | rotate unless a relation stronger than the existing band law appears |
| `1/21` affine fatal branch | nonmembership is exactly one cofinite aligned branch with a literal affine recurrence | a Lean-backed absorbing supercapacity cone shows that target periodicity and the universal pulse bound cannot force a return | inspect whether the affine law alone contradicts permanent supercapacity | rejected for this wave: the cone is a direct state-machine countermodel |
| `4/9` diagonal | exact computation through ten million ranks had no negative remainder; Lean proves a negative skip requires a preceding small selected-count margin | the existing argument did not isolate which branch must supply that margin | audit the stronger reserve `2s <= 3rho` separately on take and skip rows | continue only if the reserve survives and skip preservation is analytic |

The `4/9` probe survived and changed the proof geometry, so it was selected.

## Exact computation

The executable audit is
`scripts/four_ninths_diagonal_margin_audit.py`.  It implements exactly the
Lean recurrence

\[
T_d=4\rho_{d-1}+u_d-A_d,
\qquad
b_d={\bf1}_{2^d+1\le T_d},
\qquad
\rho_d=T_d-b_d(2^d+1),
\]

and maintains the paired divisor load by a forward sieve.  A selected rank
`a` schedules weight two at future `d` with `a | 2d-1` and weight one at
future `d` with `a | 2d`.

The selected-margin run through rank 100000 reports:

- the Lean base fixture `010110110001`, `rho_12=2460`;
- 50,254 selected ranks;
- no negative remainder;
- no violation of `2s_d <= 3rho_d`;
- the minimum all-state margin `3rho_d-2s_d` is `3`, at skipped rank 1;
- the minimum selected-landing margin is `4`, at rank 2;
- rank 2 is the only record-low selected landing in the entire run.

This is finite evidence only.  Its role is to identify the exact producer,
not to establish the all-depth statement.

A second discriminating run through rank 200000 tested the simpler sufficient
candidate

\[
b_d=1\Longrightarrow d\le\rho_d.
\tag{A}
\]

It also has zero violations.  Its minimum slack `rho_d-d` is exactly zero at
rank 2, and rank 2 is its only record low.  In fact the stronger empirical
bound `2s_d<=rho_d` has the same unique equality at rank 2.  Since `s_d<=d`,
(A) would imply the selected-landing producer immediately.  This sharper
candidate is not promoted to a theorem: local transition congruences admit
small overshoots, so an all-depth proof must still use reachability of the
actual predecessor remainder.

## Analytic collapse

Let `s` be the number of selected ranks and suppose

\[
2s\le 3\rho.
\tag{1}
\]

At a skipped step the selected count stays fixed.  The existing coprime-pair
load theorem gives `A <= 2s`, while the source pulse is nonnegative.  Hence

\[
\rho'=4\rho+u-A\ge\rho.
\]

Therefore (1) is automatically preserved across every skipped row.  A skipped
block cannot create the dangerous margin once the block begins outside it.

The only live producer is consequently

\[
\boxed{
 b_d=1 \Longrightarrow 2s_d\le3\rho_d.
}
\tag{2}

The companion Lean module
`Erdos257PeriodNoncollapse.FourNinthsDiagonalMarginProducer` packages (2) as
`FourNinthsSelectedLandingMarginProducer` and proves that it implies both the
all-depth two-thirds reserve and global nonnegativity of the exact diagonal.
The focused build for this reduction exits zero, and the printed declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.

The same module now sharpens the surviving socket.  It proves the elementary
count bound `s_d<=d`, defines the all-depth rank producer

\[
 b_d=1\Longrightarrow d\le\rho_d,
\tag{3}
\]

and connects (3) to (2) and hence to global nonnegativity.  The focused build
`cf_d5afd530b831483bb691` exits zero.  Its printed axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`; in particular, no declaration
uses `sorryAx`.  The 200000-rank run is evidence for (3), not its proof.

## Remaining mathematical throat

The narrowest current sufficient target is (3): exclude a selected transition
whose overshoot above the dyadic coin is less than its rank.  In exact terms,

\[
0\le T_d-(2^d+1)<d.
\]

The authored endpoint theorem
`fourNinthsSelectedLandingRankProducer_iff_endpointInequality` removes the
post-state notation altogether: (3) is equivalent to

\[
 2^d+1+d\le 4\rho_{d-1}+u_d-A_d
 \quad\text{whenever }b_d=1.
\tag{4}
\]

Thus a proof can attack one explicit predecessor interval; it need not reason
about an unspecified future injury.  The focused build
`cf_d6c08ceac72b462c8f70` exits zero, and its axiom audit again contains no
`sorryAx`.

## Local bounds are not enough

There is an exact abstract depth-twelve countermodel to any proof using only
the current local inequalities.  Keep the complete certified bit word
`010110110001` but change only the predecessor remainder to `2049`.  At rank
`13` it has

\[
s=6,\qquad A_{13}=3,\qquad u_{13}=1,
\qquad 2s\le3\rho.
\]

But

\[
4\cdot2049+1-3=8194=(2^{13}+1)+1,
\]

so the step selects rank `13` and lands at `rho=1`.  The new selected count is
seven, hence `3rho=3<14=2s`.  The Lean declaration
`fourNinths_localMarginCountermodel_certificate` packages the complete closed
calculation.  Focused build `cf_1b76677c9c424e818078` exits zero, and the
printed axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`; the certificate uses no native-computation or sorry axiom.  The
state is not asserted to be reachable on the executable orbit.  Its role is
sharper: even the complete certified bit prefix, phase, selected count,
incoming reserve, and paired-load bound cannot close (2) when the remainder
is detached from its history.  The missing theorem must constrain the actual
predecessor remainder through a history/reachability invariant.

## The exact history constraint

The companion module
`Erdos257PeriodNoncollapse.FourNinthsDiagonalHistory` makes that constraint
literal.  If

\[
q_j=u_{j+1}-A_{j+1}
   -b_{j+1}(2^{j+1}+1),
\]

then the executable recurrence unrolls to

\[
\boxed{
 \rho_d=\sum_{0\le j<d}4^{d-1-j}q_j.
}
\tag{5}
\]

Thus the detached value `rho=2049` in the local countermodel is impossible
for its fixed bit word: on the executable orbit every pulse, divisor load,
and selected coin fixes the right side of (5).  This is an exact reachability
identity, not yet an anti-concentration estimate.  Focused build
`cf_ca85a6daee6748dabe53` exits zero; the history identities and bad-window
equivalence use only `propext`, `Classical.choice`, and `Quot.sound`.

There is a tempting short consumer.  Modulo `4^k`, (5) depends only on the
last `k` increments.  Since a selected landing is nonnegative, the inequality

\[
 \rho_d\bmod 4^k\ge d
\]

would certify `rho_d>=d`.  The exact audit
`scripts/four_ninths_history_residue_audit.py` falsifies the smallest natural
choice, namely the least `k` with `4^k>d`: at selected rank `20`, `k=3` and
`rho_20 mod 64=12`.  Through rank `200000`, the number of additional
base-four digits needed by this residue certificate reaches `14` at rank
`146803`.  The run still has zero actual landing-rank violations.  These are
finite facts only: they reject a fixed minimal-suffix proof, but neither prove
that the required suffix excess is unbounded nor rule out a genuinely
nonlocal use of (5).

This stronger condition is sufficient, not known necessary; (2) remains the
exact weakest producer exposed by the reserve induction.  Both formulations
are one-sided selected-boundary anti-concentration statements.  Divisor load
no longer appears as an independent future injury mechanism: its only role is
in the selected overshoot itself.  Any next computation should discriminate
arithmetic descriptions of those overshoots, not merely extend the trajectory
horizon.

No solution to Erdős #257 is claimed here.

## Exact even-quotient coordinate

The companion module
`ErdosProblems.Erdos257.FourNinthsQuotientDefect` now reconnects the
executable recurrence to the finite Mersenne quotient rows from which it was
derived.  If `D_d` is the actual selected support through depth `d`, Lean
proves

\[
 \rho_d=\left\lfloor\frac{4^{d+1}}9\right\rfloor
 -\sum_{a\in D_d}\left\lfloor\frac{4^d}{2^a-1}\right\rfloor .
\]

The proof is not a numerical identification: every old quotient scales by
four plus its exact paired divisor pulse, the newest selected rank contributes
`2^(d+1)+1`, and the resulting signed defect has the same initial value and
recurrence as `rho`.  Consequently `rho_d>=0` is exactly admissibility of the
finite quotient row, while `rho_d<2^d` is exactly a square-root-sized quotient
window.  This gives the history route a compactness-ready coordinate, but it
does not supply either missing all-depth bound.  The selected-landing producer
remains the lower-bound throat.

## Compactness and the exact upper-boundary throat

`ErdosProblems.Erdos257.FourNinthsQuotientCompactness` closes the consumer
side.  If the actual diagonal satisfies

\[
 0\le \rho_d\le 2^d\qquad(d\ge0),
\]

then its finite selected supports converge to `4/9`; closedness of the
Mersenne achievement set gives exact membership.  The selected-landing rank
producer supplies the lower inequality, so no further analytic compactness
argument is missing.

The companion saturation analysis identifies the upper obstruction exactly.
A first loss of the strict strip must be a skipped row landing on `2^(d+1)`,
and its predecessor must satisfy

\[
 4\rho_d=2^{d+1}+A_{d+1}-u_{d+1}.                 \tag{6}
\]

Consequently `A_(d+1)=u_(d+1) (mod 4)` is necessary.  More sharply, coin
cancellation replaces `rho_d` in (6) by the residue of the final half of the
actual small-increment history.  Avoidance of that one explicit midline
equation implies the strict upper window at every depth and, together with
the selected-landing rank producer, implies `4/9` membership.

If a saturated state nevertheless escaped upward, the next pulse would have
to be three and its paired load at most one.  Every previously selected rank
`q>=3` would then divide neither member of the next endpoint pair; an odd
divisor contributes load two by itself, while an even divisor combines with
the permanent selected rank-two anchor to contribute two.  This is a
whole-support divisor-hole condition, not merely the earlier single missing
ancestor.

The refreshed exact audit through rank `20000` has zero saturated depths.
Of `9843` skipped rows, `2786` survive the necessary mod-four sieve.  The
maximum 2-adic valuation of a skipped remainder is only `14`, at rank
`19827`, whereas saturation there would require valuation `19827`; there are
no zero skipped remainders.  An exploratory extension through rank `250000`
raises the maximum only to `20`, at rank `127456`.  These are finite facts,
but they select the next producer cleanly: prove adaptive 2-adic
anti-concentration for the logarithmic history window.  A fixed modulus is
already excluded by `FourNinthsResidueExcessGrowth.md` and should not be
retried.

`FourNinthsSkippedTwoAdicAntiConcentration.lean` now makes the adaptive part
literal.  If `2^d` divides `rho_d`, then for every `2k<=d` the last `k`
small increments obey

\[
 4^k\mid\sum_{d-k\le j<d}4^{d-1-j}(u_{j+1}-A_{j+1}-b_{j+1}).       \tag{7}
\]

Thus hypothetical full-rank concentration supplies all suffix certificates
simultaneously, up to the half-history window; it is not one congruence to be
defeated.  The digit bounds are asymmetric and exact after rank two:

\[
 -(2j+1)\le u_{j+1}-A_{j+1}-b_{j+1}\le2.
\]

In particular the newest digit of a full-rank divisible row is a
nonpositive multiple of four.  A positive digit can occur only at a
pulse-three row with load at most two.  This converts the residual into a
finite negative-carry automaton at every fixed depth, whose transitions are
controlled by actual selected-divisor loads.  The refreshed audit checks the
adaptive suffix and newest-digit conclusions with zero violations; these are
calibration of the formal identities, not an all-depth exclusion of a carry
path.

The carry coordinate must not be mistaken for a purely local completion.
`AnchorFourFiveFixedHorizonReduction.md` already builds arbitrarily long
terminal backward carries by CRT-engineering divisor loads while keeping
every comparison in the displayed window valid.  Those synthetic windows do
not prove reachability from the source state.  The same stop condition applies
here: fixed-length carry exclusion, pointwise load congruences, or a finite
transition census cannot close (7).  A literal abstract countermodel is the
suffix with newest digit `-4` and every older digit `-3`: its length-`k`
weighted value is `-4^k`, so it passes every adaptive divisibility test while
respecting the proved upper digit bound.  This identity is Lean-checked as
`constantNegativeCarrySuffix_eq`.  A successful anti-concentration theorem
must couple the half-depth carry to the complete earlier selected ancestry or
to the exact source identity from `rho_0=0`.

The companion also packages the remaining logic without weakening it:
`four_ninths_not_mem_forces_historyBadWindow_or_skippedDivisibility` proves
that nonmembership would exhibit either an actual selected accumulated-history
bad window or an actual skipped row with full-rank dyadic divisibility.  Those
are now the two source-reachability witnesses to exclude; no third local carry
case is hidden by the reduction.

Neither the selected-landing producer nor this adaptive 2-adic producer is
proved here.  Thus `4/9` membership and Erdős #257 remain open.

## Midpoint source reachability

The adaptive carry certificates above still admit synthetic negative-carry
words because they only inspect a suffix.  Splitting the *actual* history at
its midpoint restores the missing source coordinate.  At even depth `2k`, let

\[
 S_k=\sum_{k\le j<2k}4^{2k-1-j}
       (u_{j+1}-A_{j+1}-b_{j+1})
\]

and let `W_k` be the binary word formed by the actual decisions at ranks
`k+1,...,2k`, with the newest decision least significant.  The exact history
identity gives

\[
 \rho_{2k}=4^k(\rho_k-W_k)+S_k.                 \tag{8}
\]

Consequently full-rank divisibility produces integers `z,c` with

\[
 \rho_{2k}=4^kz,\qquad S_k=4^kc,qquad
 z=\rho_k+c-W_k.                               \tag{9}
\]

Every small increment in this suffix is at most two once `k>=2`, while
`2(1+4+...+4^{k-1})<4^k`.  Hence `S_k<4^k`, and divisibility forces the
normalized carry `c<=0`.  In particular an even saturated row would require

\[
 \rho_k+c-W_k=1,qquad W_k<\rho_k.              \tag{10}
\]

The odd-depth split is equally exact.  Splitting depth `2k+1` after `k+1`
transitions leaves `k` base-four digits; after removing `4^k`, the future
take word has binary weights `2^k,...,2`.  Saturation forces

\[
 \rho_{k+1}+c-W_k^{\rm odd}=2,qquad c\le0,
 \qquad W_k^{\rm odd}+2\le\rho_{k+1}.          \tag{11}
\]

`FourNinthsMidpointCarryReachability.lean` formalizes (8)--(11).  This is a
genuine source-reachability restriction: the midpoint remainder and the
future carry word come from the same executable trajectory.  It is not yet
an exclusion theorem.  The refreshed exact audit through depth `20000`
finds zero midpoint-identity violations and no row satisfying full midpoint
divisibility.  But the unsigned word gaps themselves are common: the even
gap `rho_k-W_k` ranges from `0` to `13`, and the odd gap ranges from `0` to
`13`, with `279` odd gaps below two.  Thus (10) or (11) without the exact
carry equality is too weak.  The remaining upper-bound target is to exclude
that equality using the divisor ancestry encoded simultaneously in `c` and
the future decision word; a bare binary-word inequality should not be
retried.

The module packages those two parity-specific equalities as
`FourNinthsMidpointCarryEqualityAvoidance` and proves the exact equivalence

\[
 \text{midpoint carry-equality avoidance}
 \quad\Longleftrightarrow\quad
 \rho_d<2^d\quad\hbox{for every }d.              \tag{12}
\]

Thus this producer has no hidden slack: it is precisely the strict upper
window rewritten in source coordinates.  Combined with the independent
selected-landing rank producer, it feeds the existing quotient-compactness
consumer and yields `4/9` membership.  Equation (12) is a sharper target and
dictionary, not an analytic proof of either producer.

Neither midpoint theorem supplies the still-open selected-landing rank
producer.  No membership or Erdős #257 claim changes.
