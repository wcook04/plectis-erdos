# Centered carry at the pullback boundary

The denominator-cancellation audit closes sharper estimates in the raw
rational remainder coordinate.  The exact upper/right pullback instead has
an integer excess-multiplicity coordinate.  If its frozen support is `A`, its
backward length is `k`, its critical gap is `G`, and its pullback coordinate
is `Q`, then Lean now proves

\[
 e_{\rm end}=4^k(e_{\rm start}+1-Q)+G-1. \tag{1}
\]

This follows by substituting the existing centered-carry coboundary

\[
 C-(4^k-1)=4^k e_{\rm start}-e_{\rm end}
\]

into the exact cylinder `G+C=4^kQ`.  Equation (1) is the promised exact
bridge from the multiple-set excess variable to the seam pullback: there is
no unmeasured interior cancellation.

## Discriminator and limit

On every one of the 240 late factor-range pullbacks through row 1,000, the
coefficient `e_start + 1 - Q` is positive.  Its minimum is `1536`, at the
first late block `(source, largest false, endpoint)=(19,14,21)`.  Thus the
large endpoint excess is forced by the boundary identity rather than by a
lossy estimate.

This does **not** prove the open pullback-card margin.  The carries in (1)
belong to the frozen finite terminal seam support; the rational `X(P)`
lattice belongs to a completed infinite support.  The exact identity gives
no sign-monotone passage between them.  A successful use must control the
coupled endpoint difference, or localize the critical danger witness to the
fatal row's actual upper ancestor; bounding either carry separately merely
repackages the already observed exponential growth.

## The amplification slack has two channels

Write

\[
 S_{\rm back}=3G-(4^mQ+2Q),\qquad
 S_{\rm forward}=3R-(4^kG+2G).
\]

The composed two-block amplifier has the exact unused margin

\[
 9R-(4^{m+k}Q+2\,4^kQ+6G)
   =4^kS_{\rm back}+3S_{\rm forward}. \tag{2}
\]

Lean formalizes (2) as
`twoStage_amplification_slack_decomposition`. Exact replay through row 1,500
checks 357 applicable late blocks: both component slacks are nonnegative in
every block, the decomposition has zero failures, and the dominant
contribution alternates (`182` backward versus `175` forward). This is a
decisive no-go for collapsing the recursive packet to either one-channel
slack.

There is an essential orientation warning.  The existing Lean amplifier
theorems prove these component signs only after assuming the pullback-card
margin (and the induced critical-gap margin) that the programme is trying to
establish.  Thus (2) is presently a diagnostic decomposition, not a producer:
using those sign theorems to prove the card margin would be circular.  The
ordered pair becomes a viable induction coordinate only if selected-divisor
or pulse ancestry proves at least one component lower bound from strictly
weaker hypotheses.

## Validation

The proof-bearing source is
`ErdosProblems/Erdos257/CenteredCarryPullbackBalance.lean`. Its focused build
and final serialized authority check both pass after 3,346 jobs. The axiom
audit for the centered-carry theorem contains only `propext`,
`Classical.choice`, and `Quot.sound`; the pure slack identity uses only
`propext` and `Quot.sound`.
